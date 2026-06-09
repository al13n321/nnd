use crate::{*, types::*, error::*, expr::*, util::*, settings::*, common_ui::*, procfs::*, symbols::*};
use std::{mem, mem::MaybeUninit, ptr, fmt::Write, borrow::Cow, io::Write as ioWrite, ops::Range};
use bitflags::*;

// Apply pretty-printers and other transformations to a value. Used both for printing and expression evaluaion.
// E.g. this function may turn an std::vector<int> into a *[int; 123], making it appear as an array both when printed whole
// and when used in expression like v[10] (will index the array) or v._M_begin (will fail even if std::vector has field _M_begin).
// Note: ValueFlags::BIG_ENDIAN is intentionally ignored by pretty-printers (but propagated to elements), on the assumption that big-endianness is only relevant for simple
//       serialization-related structs that don't need pretty-printers, but such structs can appear inside normal containers; e.g. `std::vector<NetworkPacket>`.
pub fn prettify_value(val: &mut Cow<Value>, warning: &mut Option<Error>, state: &mut EvalState, context: &mut EvalContext) -> Result<()> {
    // The outer loop is for the case where a value was pretty-printed into another pretty-printable value. E.g. std::optional<std::string> -> std::string -> slice.
    // This is unusual, most pretty-printers produce a slice, array, or struct, whose elements will be automatically pretty-printed later when formatting them.
    for layer in 0..10 {
        if val.flags.contains(ValueFlags::NO_UNWRAPPING_INTERNAL) {
            return Ok(());
        }

        // Plan:
        //  1. Downcast to concrete type.
        //  2. Unravel.
        //  3. Resolve discriminated union.
        //  4. Recognize containers.
        //  5. Unwrap single-field struct.

        let mut type_ = unsafe {&*val.type_};
        let mut struct_ = match &type_.t {
            Type::Struct(s) => s,
            _ => return Ok(()),
        };

        let mut allow_full_unwrap = true;

        if let Some(off) = find_vtable_ptr_field_offset(type_, struct_) {
            if val.val.addr().is_some() {
                match downcast_to_concrete_type(val, off, context) {
                    Ok(()) => {
                        allow_full_unwrap = false;
                        type_ = unsafe {&*val.type_};
                        struct_ = match &type_.t {
                            Type::Struct(s) => s,
                            _ => return Ok(()),
                        };
                    }
                    Err(e) => *warning = Some(e),
                }
            }
        }

        let mut substruct = Substruct::new(struct_, type_);
        unravel_struct(&mut substruct);

        if resolve_discriminated_union(&val.val, &mut substruct, warning, context)? {
            allow_full_unwrap = false;
        }

        let mut prettify_again = false;
        match recognize_containers(val, &mut substruct, warning, state, context, &mut prettify_again) {
            Ok(()) if prettify_again => continue,
            Ok(()) => break,
            Err(e) if !e.is_not_container() && !e.is_no_field() => *warning = Some(e),
            _ => (),
        }

        // Final level of unwrapping: replace the whole struct with its field. Unlike unravel_struct(), this works even if the field is not a struct.
        // E.g. turns unique_ptr into plain pointer. Useful for things like strong typedefs, Box/unique_ptr, Atomic/atomic, NonzeroUsize, Pin, etc.
        //
        // If the field is a pointer to the same struct, don't unwrap it; it's probably an std::forward_list;
        // if we unwrap, it gets formatted in a single line, as a long chain of addresses with no children, which is valid but confusing.
        let is_pointer_to = |ptr: *const TypeInfo, inner: *const TypeInfo| -> bool {
            let t = unsafe {&*ptr};
            t.t.as_pointer().is_some_and(|p| p.type_ == inner)
        };
        if allow_full_unwrap && substruct.fields.len() == 1 && !is_pointer_to(substruct.fields[0].type_, type_) {
            let field_val = get_struct_field(&val.val, &substruct.fields[0], &mut context.memory)?;
            let new_val = Value {val: field_val, type_: substruct.fields[0].type_, flags: val.flags};
            *val = Cow::Owned(new_val);
            return Ok(());
        }

        // If we altered the set of fields, create a new struct type.
        if let Cow::Owned(fields) = substruct.fields {
            let val = val.to_mut();
            assert!(type_ as *const TypeInfo == val.type_);
            let mut new_type = type_.clone();
            let new_struct = new_type.t.as_struct_mut().unwrap();

            let new_fields = state.types.fields_arena.add_slice(&fields);
            new_struct.set_fields(new_fields);

            let mut w = state.types.unsorted_type_names.write();
            write!(w, "{}", type_.name).unwrap();
            new_type.name = w.finish_str(0);

            let new_type = state.types.types_arena.add(new_type);
            val.type_ = new_type;
        }

        break;
    }
    Ok(())
}

// Append a span to Option<&mut StyledText> if it's Some. The Option must be mut.
macro_rules! styled_write_maybe {
    ($out:expr, $style:ident, $($arg:tt)*) => (
        if let Some((out, palette)) = &mut ($out) {
            styled_write!(out, palette.$style, $($arg)*);
        }
    );
}

// For a value of special type like TypeInfo or StructField, tells how to show this type or field in watches window.
// The returned value is a struct that the user can explore using field access in watch expressions or by expanding the line in the watches window.
// E.g. if the value contains a *TypeInfo describing a struct, we'll return something like {name: "foo", size: 24, fields: {f1: <MetaField>, f2: <MetaField>}}.
pub fn reflect_meta_value(val: &Value, state: &mut EvalState, context: &mut EvalContext, mut out: Option<(&mut StyledText, &Palette)>) -> Value {
    let meta_t = unsafe {&*val.type_};
    let mut builder = StructBuilder::default();
    match meta_t.t {
        Type::MetaType => {
            let t = val.val.blob_ref().unwrap().get_usize().unwrap() as *const TypeInfo;
            let t = unsafe {&*t};
            let mut show_size = false;
            match &t.t {
                Type::Unknown => styled_write_maybe!(out, default, "unknown type"),
                Type::Primitive(p) => {
                    styled_write_maybe!(out, type_name, "{}",
                                        if p.contains(PrimitiveFlags::FLOAT) {
                                            "float"
                                        } else if p.contains(PrimitiveFlags::BOOL) {
                                            "bool"
                                        } else if p.contains(PrimitiveFlags::CHAR) {
                                            "char"
                                        } else if p.contains(PrimitiveFlags::SIGNED) {
                                            "signed"
                                        } else {
                                            "unsigned"
                                        });
                    show_size = true;
                }
                Type::Pointer(p) => {
                    if let Some((text, palette)) = &mut out {print_type_name(t, *text, *palette, 0);}
                    builder.add_usize_field("type", p.type_ as usize, state.builtin_types.meta_type);
                }
                Type::PointerToMember(p) => {
                    if let Some((text, palette)) = &mut out {print_type_name(t, *text, *palette, 0);}
                    builder.add_usize_field("type", p.type_ as usize, state.builtin_types.meta_type);
                    builder.add_usize_field("containing_type", p.containing_type as usize, state.builtin_types.meta_type);
                }
                Type::Function => styled_write_maybe!(out, default, "fn"),
                Type::Array(a) => {
                    if let Some((text, palette)) = &mut out {print_type_name(t, *text, *palette, 0);}
                    builder.add_usize_field("type", a.type_ as usize, state.builtin_types.meta_type);
                }
                Type::Slice(s) => {
                    if let Some((text, palette)) = &mut out {print_type_name(t, *text, *palette, 0);}
                    builder.add_usize_field("type", s.type_ as usize, state.builtin_types.meta_type);
                }
                Type::Struct(s) => {
                    styled_write_maybe!(out, keyword, "{}", if s.flags.contains(StructFlags::UNION) {"union"} else {"struct"});
                    show_size = true;
                    let mut fields = StructBuilder::default();
                    for f in s.fields() {
                        fields.add_usize_field(f.name, f as *const StructField as usize, state.builtin_types.meta_field);
                    }
                    let fields = fields.finish("", val.flags, &mut state.types);
                    builder.add_field("fields", fields);
                }
                Type::Enum(e) => {
                    styled_write_maybe!(out, keyword, "enum");
                    show_size = true;
                    let mut items = StructBuilder::default();
                    let mut size = unsafe {(*e.type_).calculate_size()};
                    if size == 0 || size > 8 {
                        size = 8;
                    }
                    for en in e.enumerands {
                        items.add_blob_field(en.name, &en.value.to_le_bytes()[..size], e.type_);
                    }
                    let items = items.finish("", val.flags, &mut state.types);
                    builder.add_field("items", items);
                    builder.add_usize_field("type", e.type_ as usize, state.builtin_types.meta_type);
                }
                Type::MetaType | Type::MetaField | Type::MetaVariable | Type::MetaCodeLocation => {
                    styled_write_maybe!(out, default, "{}", match &t.t { Type::MetaType => "type", Type::MetaField => "field", Type::MetaVariable => "variable", Type::MetaCodeLocation => "location", _ => panic!("huh") });
                    return builder.finish("", val.flags, &mut state.types);
                }
            }
            let size = t.calculate_size();
            if show_size {
                styled_write_maybe!(out, default, " ({} bytes):", size);
            }
            builder.add_usize_field("size", size, state.builtin_types.u64_);
            if t.line != LineInfo::invalid() {
                let d: [usize; 2] = t.line.serialize();
                builder.add_usize_blob_field("decl", &[t.binary_id, d[0], d[1]], state.builtin_types.meta_code_location);
            }
            if !t.name.is_empty() {
                styled_write_maybe!(out, default, " {}", t.name);
                builder.add_str_field("name", t.name, &mut state.types, &state.builtin_types);
            }
            if !t.nested_names.is_empty() {
                let mut nested = StructBuilder::default();
                for (name, n) in t.nested_names {
                    match n {
                        NestedName::Type(type_) => nested.add_usize_field(name, *type_ as usize, state.builtin_types.meta_type),
                        NestedName::Variable(v) => nested.add_usize_blob_field(name, &[t.binary_id, *v as usize], state.builtin_types.meta_variable),
                    }
                }
                let nested = nested.finish("", val.flags, &mut state.types);
                builder.add_field("nested", nested);
            }
            if t.die.0 != 0 && t.die.0 < FAKE_DWARF_OFFSET_START {
                builder.add_usize_field("dwarf_offset", t.die.0 as usize, state.builtin_types.u64_);
            }

            builder.finish("", val.flags | ValueFlags::NO_UNWRAPPING_INTERNAL, &mut state.types)
        }
        Type::MetaField => {
            let f = val.val.blob_ref().unwrap().get_usize().unwrap() as *const StructField;
            let f = unsafe {&*f};
            builder.add_str_field("name", f.name, &mut state.types, &state.builtin_types);
            builder.add_usize_field("type", f.type_ as usize, state.builtin_types.meta_type);
            if f.bit_offset % 8 == 0 {
                styled_write_maybe!(out, default, "offset {}: ", f.bit_offset / 8);
                builder.add_usize_field("offset", f.bit_offset / 8, state.builtin_types.u64_);
            } else {
                styled_write_maybe!(out, default, "bit_offset {}: ", f.bit_offset);
                builder.add_usize_field("bit_offset", f.bit_offset, state.builtin_types.u64_);
            }
            if let Some((text, palette)) = &mut out {print_type_name(f.type_, *text, *palette, 0);}
            if f.flags.contains(FieldFlags::SIZE_KNOWN) && f.bit_size != unsafe {(*f.type_).calculate_size() * 8} {
                builder.add_usize_field("bit_size", f.bit_size, state.builtin_types.u64_);
            }
            builder.add_str_field("flags", &f.readable_flags(), &mut state.types, &state.builtin_types);
            if f.flags.contains(FieldFlags::VARIANT) {
                builder.add_usize_field("discriminant_value", f.discr_value, state.builtin_types.u64_);
            }
            builder.finish("", val.flags, &mut state.types)
        }
        Type::MetaVariable => {
            let blob = val.val.blob_ref().unwrap();
            let binary_id = blob.get_usize_at(0).unwrap();
            let v = blob.get_usize_at(8).unwrap() as *const Variable;
            let v = unsafe {&*v};
            builder.add_str_field("name", unsafe {v.name()}, &mut state.types, &state.builtin_types);
            builder.add_usize_field("type", v.type_ as usize, state.builtin_types.meta_type);
            if v.line != LineInfo::invalid() {
                let d: [usize; 2] = v.line.serialize();
                builder.add_usize_blob_field("decl", &[binary_id, d[0], d[1]], state.builtin_types.meta_code_location);
            }
            let mut is_const = false;
            match v.location.unpack() {
                VariableLocation::Const(s) => {
                    is_const = true;
                    builder.add_blob_field("const_value", s, v.type_)
                }
                VariableLocation::Expr(expr) => {
                    let default_encoding = gimli::Encoding {address_size: 8, format: gimli::Format::Dwarf64, version: 5};
                    let s = match format_dwarf_expression(expr, default_encoding) {
                        Ok(s) => s,
                        Err(e) => format!("<error: {}>", e),
                    };
                    builder.add_str_field("dwarf_expr", &s, &mut state.types, &state.builtin_types);
                }
                VariableLocation::Unknown => builder.add_str_field("location", "unknown", &mut state.types, &state.builtin_types),
            }
            builder.add_str_field("flags", &v.readable_flags(), &mut state.types, &state.builtin_types);
            if let Some(die) = v.debug_info_offset() {
                builder.add_usize_field("die", die.0 as usize, state.builtin_types.u64_);
            }

            if v.flags().contains(VariableFlags::PARAMETER) {
                styled_write_maybe!(out, default_dim, "function parameter");
            } else {
                styled_write_maybe!(out, default_dim, "{} {}",
                                    if v.flags().contains(VariableFlags::GLOBAL) {"global"} else {"local"},
                                    if is_const {"constant"} else {"variable"});
            }

            builder.finish("", val.flags, &mut state.types)
        }
        Type::MetaCodeLocation => val.clone(),
        _ => panic!("expected meta type/field, got {}", meta_t.t.kind_name()),
    }
}

fn is_field_uninformative(mut f: &StructField) -> bool {
    for step in 0..100 {
        let bit_size = f.calculate_bit_size();
        if bit_size == 0 {
            return true;
        }
        if bit_size != 8 {
            return false;
        }

        // If 1 byte, this may be the C++ thing where empty struct has size 1 instead of 0.
        // This is common for comparators and allocators.
        // Here's a partial check for that. It doesn't cover the case where the struct
        // has multiple uninformative fields (and may have size > 1 byte), but that's rare.
        let t = unsafe {&*f.type_};
        f = match &t.t {
            Type::Struct(s) if s.fields().len() == 0 => return true,
            Type::Struct(s) if s.fields().len() == 1 => &s.fields()[0],
            _ => return false,
        };
    }
    false
}

// Static transformation on a struct type that makes it more digestible:
//  * Remove fields that carry no information, specifically empty structs possibly wrapped in some number of layers of single-field structs.
//    Common in C++ for allocators (often as base class, which we consider a field).
//  * If there's only one field, and it's a struct, inline that struct's fields as if they're this struct's fields.
//    Very common for various wrappers in C++ and Rust.
//  * Inline fields from base structs and anon struct fields, as if they're this struct's fields.
//  * Repeat to convergence.
// This undoes a lot of cruft in standard libraries and makes values in the watches window much more readable.
// This is a shallow operation: it changes the set of fields, but doesn't change the types inside those fields.
// When formatting a value, we apply prettification for each tree node, so end up with a deeply prettified tree.
// When unwrapping single-field structs, the names and nested_names of removed structs are added to additional_names and nested_names; they're useful for container detection,
// e.g. if the user has struct Foo {s: String}, and we inline the String, the container detection needs to know that there was a struct named "String" in there,
// to distinguish between string and array of u8.
// Returns the new set of fields if any changes were made, None otherwise.
fn unravel_struct(substruct: &mut Substruct) {
    let (mut has_inheritance, mut empty_fields) = (false, 0usize);
    for f in substruct.fields.iter() {
        has_inheritance |= f.flags.contains(FieldFlags::INHERITANCE);
        if is_field_uninformative(f) {
            empty_fields += 1;
        }
    }
    if !has_inheritance && empty_fields == 0 && substruct.fields.len() != 1 {
        // Fast path.
        return;
    }

    let mut temp_fields: Vec<StructField> = Vec::new();
    for pass in 0..100 {
        temp_fields.clear();

        // Remove uninformative fields.
        let mut changed = false;
        for f in substruct.fields.iter() {
            if is_field_uninformative(f) {
                changed = true;
            } else {
                temp_fields.push(f.clone());
            }
        }
        let mut res = match &mut substruct.fields {
            Cow::Borrowed(_) => Vec::new(),
            Cow::Owned(v) => { // reuse memory
                v.clear();
                mem::take(v)
            }
        };

        for f in &temp_fields {
            // Inline field's fields if it's base class or the only field or anonymous field.
            // This works correctly with Rust enums: the discriminant and all variants will be inlined and will work correctly
            // (as long as we inline only one field this way; there should be no base classes in Rust, so we're fine).
            let unwrap = temp_fields.len() == 1;
            let mut inlined = false;
            if f.flags.contains(FieldFlags::INHERITANCE) || f.name.is_empty() || unwrap {
                let field_type = unsafe {&*f.type_};
                if let Type::Struct(field_struct) = &field_type.t {
                    for mut ff in field_struct.fields().iter().cloned() {
                        ff.bit_offset += f.bit_offset;
                        res.push(ff);
                    }
                    inlined = true;
                    changed = true;

                    if !field_type.nested_names.is_empty() {
                        if substruct.nested_names.is_empty() {
                            substruct.nested_names = Cow::Borrowed(field_type.nested_names);
                        } else {
                            substruct.nested_names.to_mut().extend_from_slice(field_type.nested_names);
                        }
                    }

                    if !field_type.name.is_empty() {
                        substruct.additional_names.push(field_type.name);
                    }
                }
            }
            if !inlined {
                res.push(f.clone());
            }
        }

        substruct.fields = Cow::Owned(res);

        if !changed {
            break;
        }
    }
}

fn is_field_vtable_ptr(f: &StructField) -> bool {
    f.flags.contains(FieldFlags::ARTIFICIAL) && f.name.starts_with("_vptr$")
}

fn find_vtable_ptr_field_offset(t: &TypeInfo, s: &StructType) -> Option<usize> {
    // Quickly check if any inheritance is involved.
    if !s.fields().iter().any(|f| f.flags.contains(FieldFlags::INHERITANCE) || is_field_vtable_ptr(f)) {
        return None;
    }

    // DFS through all base classes of this class. (E.g. imagine multiple inheritance where some of the base classes are nonvirtual.)
    let mut bases: Vec<(usize, *const TypeInfo)> = vec![(0, t)];
    for attempt in 0..100 {
        let Some((off, t)) = bases.pop() else { return None };
        let t = unsafe {&*t};
        let Type::Struct(s) = &t.t else { continue };
        for f in s.fields() {
            if f.bit_offset % 8 != 0 {
                continue;
            }
            if is_field_vtable_ptr(f) {
                return Some(off + f.bit_offset/8);
            }
            if f.flags.contains(FieldFlags::INHERITANCE) {
                bases.push((off + f.bit_offset/8, f.type_));
            }
        }
    }
    None
}

fn downcast_to_concrete_type(val: &mut Cow<Value>, vtable_ptr_field_offset: usize, context: &mut EvalContext) -> Result<()> {
    let Some(addr) = val.val.addr() else { return err!(Runtime, "struct address not known") };
    let vptr = context.memory.read_usize(addr + vtable_ptr_field_offset)?;
    // Itanium ABI vtable layout is:
    //  * (various optional stuff)
    //  * 8 bytes: offset from vptr to start of subclass instance - that's how we downcast
    //  * 8 bytes: whatever
    //  * <vptr field points here>
    //  * function pointers
    let binary_id = context.process_info.addr_to_binary_id(vptr)?;
    let binary = context.symbols_registry.get(binary_id).unwrap();
    let symbols = binary.symbols.clone()?;
    let static_vptr = binary.addr_map.dynamic_to_static(vptr);
    let vtable = symbols.find_vtable(static_vptr)?;
    let Some(type_) = vtable.type_.clone() else { return err!(Dwarf, "unknown type: {}", vtable.name) };
    let offset = context.memory.read_usize(vptr.saturating_sub(16))?;
    let addr = (addr + vtable_ptr_field_offset).wrapping_add(offset);
    let new_val = Value {val: AddrOrValueBlob::Addr(addr), type_, flags: val.flags | ValueFlags::SHOW_TYPE_NAME};
    *val = Cow::Owned(new_val);
    Ok(())
}

// Removes fields representing inactive variants. If nothing looks broken, removes discriminant too.
fn resolve_discriminated_union(val: &AddrOrValueBlob, substruct: &mut Substruct, warning: &mut Option<Error>, context: &mut EvalContext) -> Result<bool> {
    let mut discriminant: Option<usize> = None;
    for field in substruct.fields.iter() {
        if field.flags.contains(FieldFlags::DISCRIMINANT) {
            if discriminant.is_some() {
                *warning = Some(error!(Dwarf, "multiple discriminants"));
                return Ok(false);
            }

            let mut t = unsafe {&*field.type_};
            if let Type::Enum(e) = &t.t {
                t = unsafe {&*e.type_};
            }

            let (size, signed) = match &t.t {
                Type::Primitive(p) => (t.size, p.contains(PrimitiveFlags::SIGNED)),
                _ if t.flags.contains(TypeFlags::SIZE_KNOWN) => (t.size, false),
                _ => {
                    *warning = Some(error!(Dwarf, "unexpected discriminant type"));
                    return Ok(false);
                }
            };
            if size > 8 {
                *warning = Some(error!(Dwarf, "discriminant too big: {} bytes", size));
                return Ok(false);
            }

            let val = get_struct_field(&val, field, &mut context.memory)?;
            let mut x = val.into_value(size, &mut context.memory)?.get_usize()?;

            if signed && size < 8 && size > 0 && x & 1 << (size*8-1) as u32 != 0 {
                // Sign-extend (because that's what we do to discr_values when parsing DWARF).
                x |= !((1usize << size*8)-1);
            }

            discriminant = Some(x);
        }
    }

    let discriminant = match discriminant {
        None => return Ok(false),
        Some(x) => x };

    let (mut found, mut has_default, mut has_nonvariant) = (false, false, false);
    substruct.fields.to_mut().retain(|f| {
        if f.flags.contains(FieldFlags::DEFAULT_VARIANT) {
            has_default = true;
        } else if f.flags.contains(FieldFlags::VARIANT) {
            if f.discr_value == discriminant {
                found = true;
            } else {
                return false;
            }
        } else if !f.flags.contains(FieldFlags::DISCRIMINANT) {
            has_nonvariant = true;
        }
        true
    });
    if found || has_default {
        let mut delete_if = FieldFlags::empty();
        if !has_nonvariant {
            delete_if.insert(FieldFlags::DISCRIMINANT);
        }
        if found {
            delete_if.insert(FieldFlags::DEFAULT_VARIANT);
        }
        substruct.fields.to_mut().retain(|f| !f.flags.intersects(delete_if));
    }
    Ok(true)
}


// Struct that was transformed in some way, e.g. we may have inlined some fields of fields
// (e.g. if the struct had only one field, which is a struct, we can unwrap it, i.e. the the inner struct's fields and put them in the outer struct).
// Or this may represent part of the original struct (e.g. its struct field) at offset `bit_offset` within the original struct.
struct Substruct<'a> {
    type_: *const TypeInfo,
    // When we unwrap a struct, we keep the outer struct and discard the inner one. The fields of the inner structs are added to `fields`.
    fields: Cow<'a, [StructField]>,
    // Nested names (typedefs and constants) of all unwrapped structs, in order from outer to inner.
    // We search them in reverse, so that inner typedefs take precedence. Examples:
    //  * For Rust `Option<Vec<i32>>`, both Option and Vec have typedef (template argument) "T": the inner T is i32, the outer T is Vec<i32>.
    //    Vec's pretty printer must use the inner T. Hence searching in reverse order.
    //  * For C++ `std::map<...>`, the std::map itself has typedef "value_type" that we need, and inner structs also have typedefs that we need (e.g. "__base").
    //    Hence searching the merged list rather than just the innermost struct.
    nested_names: Cow<'a, [(&'static str, NestedName)]>,
    // Names of the inner unwrapped structs.
    additional_names: Vec<&'static str>,

    bit_offset: usize, // if this represents part of a bigger struct, at this offset
    used_fields_mask: usize, // which of the `fields` were recognized by container recognizer, to check that there are no unexpected fields
}
impl<'a> Substruct<'a> {
    fn new(s: &'a StructType, type_: *const TypeInfo) -> Self { Self {type_, fields: Cow::Borrowed(s.fields()), nested_names: Cow::Borrowed(unsafe {(*type_).nested_names}), additional_names: Vec::new(), bit_offset: 0, used_fields_mask: 0} }

    fn check_all_fields_used(&self) -> Result<()> {
        if self.used_fields_mask != (!0usize >> (64-self.fields.len().min(64) as u32)) {
            err!(NotContainer, "")
        } else {
            Ok(())
        }
    }
    fn clear_used(&mut self) {
        self.used_fields_mask = 0;
    }
}

// Container stuff.
// Throughout these functions, error NoField means "this container wasn't recognized, but we should try others", while NotContainer means "stop all container recognition".

fn find_field(names: &[&str], substruct: &mut Substruct) -> Result<StructField> {
    for (i, f) in substruct.fields.iter().enumerate() {
        let name = trim_field_name(f.name);
        if names.iter().position(|n| *n == name).is_some() {
            if i < 64 {
                substruct.used_fields_mask |= 1usize << i as u32;
            }
            return Ok(f.clone());
        }
    }
    err!(NoField, "")
}

// Container begin/end/size/capacity fields are often wrapped in more structs. Peel them.
fn unravel_container_field(field: &StructField, substruct: &mut Substruct, primitive: bool) -> Result<(&'static TypeInfo, Range<usize>)> {
    let mut t = unsafe {&*field.type_};
    let mut bit_offset = substruct.bit_offset + field.bit_offset;
    let mut bit_size = if field.flags.contains(FieldFlags::SIZE_KNOWN) {field.bit_size} else {t.calculate_size()*8};
    if let Type::Struct(s) = &t.t {
        let mut ss = Substruct::new(s, t);
        unravel_struct(&mut ss);
        if ss.fields.len() != 1 {
            return err!(NoField, "");
        }
        let field = &ss.fields[0];
        t = unsafe {&*field.type_};
        bit_offset += field.bit_offset;
        bit_size = if field.flags.contains(FieldFlags::SIZE_KNOWN) {field.bit_size} else {t.calculate_size()*8};
    }
    if primitive {
        if bit_size == 0 {
            return err!(NotContainer, "");
        }
        if bit_size > 64 {
            return err!(NoField, "");
        }
    }
    Ok((t, bit_offset..bit_offset+bit_size))
}

fn container_aux_struct(type_: *const TypeInfo) -> Result<Substruct<'static>> {
    let t = unsafe {&*type_};
    match &t.t {
        Type::Struct(s) => {
            let mut ss = Substruct::new(s, t);
            unravel_struct(&mut ss);
            Ok(ss)
        }
        _ => err!(NoField, ""),
    }
}

fn find_struct_field<'a>(names: &[&str], substruct: &mut Substruct<'a>) -> Result<Substruct<'a>> {
    let f = find_field(names, substruct)?;
    let t = unsafe {&*f.type_};
    match &t.t {
        Type::Struct(s) => {
            if f.flags.contains(FieldFlags::SIZE_KNOWN) && f.bit_size != t.size * 8 {
                return err!(NotContainer, "");
            }
            let mut ss = Substruct::new(s, t);
            unravel_struct(&mut ss);
            ss.bit_offset = substruct.bit_offset + f.bit_offset;
            Ok(ss)
        }
        _ => err!(NoField, ""),
    }
}
fn find_int_field(names: &[&str], substruct: &mut Substruct) -> Result<Range<usize>> {
    let f = find_field(names, substruct)?;
    let (t, r) = unravel_container_field(&f, substruct, true)?;
    match &t.t {
        Type::Primitive(p) => {
            if p.intersects(PrimitiveFlags::FLOAT | PrimitiveFlags::UNSPECIFIED) {
                return err!(NotContainer, "");
            }
            if p.contains(PrimitiveFlags::SIGNED) && r.len() != 64 { // we'd need to sign-extend in this case
                return err!(NotContainer, "");
            }
            Ok(r)
        }
        _ => err!(NoField, ""),
    }
}
fn find_pointer_field(names: &[&str], substruct: &mut Substruct, inner_type: &mut *const TypeInfo) -> Result<Range<usize>> {
    let f = find_field(names, substruct)?;
    let (t, r) = unravel_container_field(&f, substruct, true)?;
    match &t.t {
        Type::Pointer(p) => {
            if *inner_type != ptr::null() && *inner_type != p.type_ {
                return err!(NotContainer, "");
            }
            *inner_type = p.type_;
            Ok(r)
        }
        _ => err!(NoField, ""),
    }
}
fn find_array_field(names: &[&str], substruct: &mut Substruct, inner_type: &mut *const TypeInfo) -> Result<(Range<usize>, usize)> {
    let f = find_field(names, substruct)?;
    let (t, r) = unravel_container_field(&f, substruct, false)?;
    match &t.t {
        Type::Array(a) => {
            if r.start % 8 != 0 {
                return err!(NotContainer, "");
            }
            if !a.flags.contains(ArrayFlags::LEN_KNOWN) {
                return err!(NotContainer, "");
            }
            if *inner_type != ptr::null() && *inner_type != a.type_ {
                return err!(NotContainer, "");
            }
            *inner_type = a.type_;
            let t = unsafe {&*a.type_};
            let inner_size = t.calculate_size();
            if a.stride != 0 && a.stride != inner_size {
                return err!(NotContainer, "");
            }
            if r.len() != inner_size*a.len*8 {
                return err!(NotContainer, "");
            }
            Ok((r, a.len))
        }
        _ => err!(NoField, ""),
    }
}

fn find_nested_type(name: &str, nested_names: &[(&'static str, NestedName)]) -> Result<*const TypeInfo> {
    // Search in reverse, see comment next to nested_names declaration.
    for &(nn, n) in nested_names.iter().rev() {
        if nn == name {
            match n {
                NestedName::Type(t) => return Ok(t),
                _ => (),
            }
        }
    }
    err!(NoField, "")
}

fn find_nested_usize_constant(name: &str, nested_names: &[(&'static str, NestedName)]) -> Result<usize> {
    for &(nn, n) in nested_names.iter().rev() {
        if nn == name {
            match n {
                NestedName::Variable(v) => {
                    let v = unsafe {&*v};
                    let val = match v.location.unpack() {
                        VariableLocation::Const(x) => x,
                        _ => return err!(NotContainer, ""),
                    };
                    let vt = unsafe {&*v.type_};
                    let vs = vt.calculate_size();
                    if vs == 0 || vs > 8 || vs > val.len() {
                        return err!(NotContainer, "");
                    }
                    let mut a = [0u8; 8];
                    a[..vs].copy_from_slice(&val[..vs]);
                    return Ok(usize::from_le_bytes(a));
                }
                _ => (),
            }
        }
    }
    err!(NoField, "")
}

fn optional_field<T>(r: Result<T>) -> Result<Option<T>> {
    match r {
        Ok(x) => Ok(Some(x)),
        Err(e) if e.is_no_field() => Ok(None),
        Err(e) => Err(e),
    }
}

fn one_container_name_looks_like_string(s: &str) -> bool {
    let end = s.find('<').unwrap_or(s.len());
    let s = &s[..end];
    // Hope no one will have a struct called "NotString".
    s.find("str").is_some() || s.find("Str").is_some() || s.find("Path").is_some()
}

fn container_name_looks_like_string(substruct: &Substruct) -> bool {
    if one_container_name_looks_like_string(unsafe {(*substruct.type_).name}) {
        return true;
    }
    substruct.additional_names.iter().any(|s| one_container_name_looks_like_string(*s))
}

fn trim_field_name(mut name: &str) -> &str {
    if name.starts_with("_M_") {
        name = &name[3..];
    } else if name.starts_with("c_") {
        name = &name[2..];
    }
    while name.starts_with("_") {
        name = &name[1..];
    }
    while name.ends_with("_") {
        name = &name[..name.len()-1];
    }
    name
}

// Guess the common C++ and Rust containers. Turn them into slices/arrays/pointers as needed.
// The input Value already went through unravel_struct(), so wrappers and inheritance are mostly gone.
// Returns Ok if the whole Value was replaced and doesn't need any further transformations.
// Returns NotContainer error if the value wasn't replaced (but `fields` may have been mutated, e.g. removing refcount field from shared_ptr).
// Returns other errors if we should fail the whole prettification (e.g. failed to read the struct from memory).
fn recognize_containers(val: &mut Cow<Value>, substruct: &mut Substruct, warning: &mut Option<Error>, state: &mut EvalState, context: &mut EvalContext, prettify_again: &mut bool) -> Result<()> {
    let t = unsafe {&*val.type_};
    let language = match t.language {
        LanguageFamily::Internal => return err!(NotContainer, ""),
        LanguageFamily::Rust => LanguageFamily::Rust,
        LanguageFamily::Cpp | LanguageFamily::Other | LanguageFamily::Unknown => LanguageFamily::Cpp,
    };

    // We recognize containers in a duck-typed way, by approximate field names, after unraveling the struct.
    // This way we're not too sensitive to small changes in implementation, and sometimes recognize custom containers along the way.
    // This may have some false positives, but that's not catastrophic, the user can always use .#r to see raw struct.

    match recognize_shared_ptr(substruct) {
        Ok(()) => return Ok(()),
        Err(e) if e.is_no_field() => (),
        Err(e) => return Err(e),
    }

    match recognize_slice_or_vec(substruct, val, warning, state, context) {
        Ok(()) => return Ok(()),
        Err(e) if e.is_no_field() => substruct.clear_used(),
        Err(e) => return Err(e),
    }
    match recognize_rust_vec(substruct, val, state, context) {
        Ok(()) => return Ok(()),
        Err(e) if e.is_no_field() => substruct.clear_used(),
        Err(e) => return Err(e),
    }
    match recognize_libcpp_string(substruct, val, state, context) {
        Ok(()) => return Ok(()),
        Err(e) if e.is_no_field() => substruct.clear_used(),
        Err(e) => return Err(e),
    }
    match recognize_absl_inlined_vector(substruct, val, state, context) {
        Ok(()) => return Ok(()),
        Err(e) if e.is_no_field() => substruct.clear_used(),
        Err(e) => return Err(e),
    }
    match recognize_cpp_list(substruct, val, state, context) {
        Ok(()) => return Ok(()),
        Err(e) if e.is_no_field() => substruct.clear_used(),
        Err(e) => return Err(e),
    }
    match recognize_rust_hash_table(substruct, val, state, context) {
        Ok(()) => return Ok(()),
        Err(e) if e.is_no_field() => substruct.clear_used(),
        Err(e) => return Err(e),
    }
    match recognize_libstdcpp_deque(substruct, val, state, context) {
        Ok(()) => return Ok(()),
        Err(e) if e.is_no_field() => substruct.clear_used(),
        Err(e) => return Err(e),
    }
    match recognize_libcpp_deque(substruct, val, state, context) {
        Ok(()) => return Ok(()),
        Err(e) if e.is_no_field() => substruct.clear_used(),
        Err(e) => return Err(e),
    }
    match recognize_cpp_map(substruct, val, state, context) {
        Ok(()) => return Ok(()),
        Err(e) if e.is_no_field() => substruct.clear_used(),
        Err(e) => return Err(e),
    }
    match recognize_cpp_optional(substruct, val, state, context, prettify_again) {
        Ok(()) => return Ok(()),
        Err(e) if e.is_no_field() => substruct.clear_used(),
        Err(e) => return Err(e),
    }

    err!(NotContainer, "")
}

fn make_slice(val: &mut Cow<Value>, ptr: usize, len: usize, inner_type: *const TypeInfo, is_string: bool, state: &mut EvalState) {
    let flags = if is_string {SliceFlags::UTF_STRING} else {SliceFlags::empty()};
    let slice_type = state.types.add_slice(inner_type, flags);
    let v = AddrOrValueBlob::Blob(ValueBlob::from_two_usizes([ptr, len]));
    let new_val = Value {val: v, type_: slice_type, flags: val.flags};
    *val = Cow::Owned(new_val);
}

fn make_array_of_references(val: &mut Cow<Value>, data: Vec<u8>, inner_type: *const TypeInfo, is_truncated: bool, state: &mut EvalState) {
    let flags = if is_truncated {ArrayFlags::TRUNCATED} else {ArrayFlags::empty()};
    let value_ref_type = state.types.add_pointer(inner_type, PointerFlags::REFERENCE);
    let array_type = state.types.add_array(value_ref_type, Some(data.len() / 8), flags);
    let v = AddrOrValueBlob::Blob(ValueBlob::from_vec(data));
    let new_val = Value {val: v, type_: array_type, flags: val.flags};
    *val = Cow::Owned(new_val);
}

// Slice or vector.
// Something like: {start: *T, len: usize} or {begin: *T, end: *T, end_of_storage: *T}, or {buf: {ptr: *T, cap: usize}, len: usize}.
fn recognize_slice_or_vec(substruct: &mut Substruct, val: &mut Cow<Value>, warning: &mut Option<Error>, state: &mut EvalState, context: &mut EvalContext) -> Result<()> {
    // Find field offsets.
    // (We first analyze the fields, then look at data. Not necessarily the simplest way to do this right now, but a sort of rehearsal of compiling to bytecode.)
    let mut inner_type: *const TypeInfo = ptr::null();
    let begin_field = find_pointer_field(&["begin", "start", "data_ptr", "ptr", "str", "data", "dataplus"], substruct, &mut inner_type)?;
    let len_field = optional_field(find_int_field(&["len", "length", "size", "extent", "string_length"], substruct))?;
    let end_field = optional_field(find_pointer_field(&["end", "finish"], substruct, &mut inner_type))?;
    if len_field.is_some() == end_field.is_some() {
        return err!(NoField, "");
    }
    optional_field(find_field(&["end_of_storage", "end_cap", "capacity", "cap"], substruct))?;
    optional_field(find_field(&["local_buf"], substruct))?;
    optional_field(find_field(&["allocated_capacity"], substruct))?;
    optional_field(find_field(&["mprotected"], substruct))?;
    substruct.check_all_fields_used()?;

    let mut inner_size = (unsafe {&*inner_type}).calculate_size();

    // If start/end are char*, and there's typedef value_type, cast the pointers to it. This covers clickhouse PODArray in particular.
    if inner_size == 1 {
        for name in ["value_type", "T"] {
            if let Some(t) = optional_field(find_nested_type(name, &substruct.nested_names))? {
                inner_type = t;
                inner_size = (unsafe {&*inner_type}).calculate_size();
                break;
            }
        }
    };

    // Parse the field values.
    let start = val.val.bit_range(begin_field, &mut context.memory)?;
    let len = if let Some(r) = len_field {
        val.val.bit_range(r, &mut context.memory)?
    } else {
        if inner_size == 0 {
            *warning = Some(error!(NotContainer, "element size is 0"));
            return err!(NotContainer, "");
        }
        let end = val.val.bit_range(end_field.unwrap(), &mut context.memory)?;
        if end < start {
            *warning = Some(error!(ProcessState, "end < start"));
            return err!(NotContainer, "");
        }
        let bytes = end - start;
        if bytes % inner_size != 0 {
            *warning = Some(error!(ProcessState, "slice size not divisible by element size"));
            return err!(NotContainer, "");
        }
        bytes / inner_size
    };

    // Guess whether this is a string.
    let is_string = inner_size <= 1 && container_name_looks_like_string(substruct);

    // Rust &Path (or &OsStr) is weird: it's {data_ptr: *Path, length: usize}, where Path is a struct with DW_AT_byte_size = 0, but one field of size 1 byte (in 100 wrappers);
    // I guess philosophically this Path is supposed to be a dynamically-sized struct, but there doesn't seem to be anything in the debug info to indicate that or to
    // distinguish it from a size 0 struct (except maybe the mismatch between the declared size and the size of the field).
    if is_string && inner_size == 0 {
        inner_type = state.builtin_types.char8;
    }

    // Return a slice.
    make_slice(val, start, len, inner_type, is_string, state);
    Ok(())
}

// {len, buf: {ptr, cap}}
// Or VecDeque: {head, len, buf: {ptr, cap}}
fn recognize_rust_vec(substruct: &mut Substruct, val: &mut Cow<Value>, state: &mut EvalState, context: &mut EvalContext) -> Result<()> {
    let mut buf = find_struct_field(&["buf"], substruct)?;
    let mut inner_type: *const TypeInfo = ptr::null();
    let ptr_field = find_pointer_field(&["ptr"], &mut buf, &mut inner_type)?;
    let cap_field = find_int_field(&["cap"], &mut buf)?;
    buf.check_all_fields_used()?;
    let len_field = find_int_field(&["len"], substruct)?;
    let head_field = optional_field(find_int_field(&["head"], substruct))?;
    substruct.check_all_fields_used()?;

    let mut inner_size = (unsafe {&*inner_type}).calculate_size();
    if inner_size == 1 {
        // Newer versions of Rust have u8 pointer regardless of the actual element type.
        if let Some(t) = optional_field(find_nested_type("T", &substruct.nested_names))? {
            inner_type = t;
            inner_size = (unsafe {&*inner_type}).calculate_size();
        }
    }

    let len = val.val.bit_range(len_field, &mut context.memory)?;
    let ptr = val.val.bit_range(ptr_field, &mut context.memory)?;
    let cap = val.val.bit_range(cap_field, &mut context.memory)?;

    if let Some(f) = head_field {
        // VecDeque.
        let head = val.val.bit_range(f, &mut context.memory)?;
        if head > cap || len > cap {
            return err!(Runtime, "VecDeque out of bounds");
        }
        let mut builder = StructBuilder::default();
        builder.add_slice_field("part1", ptr + head*inner_size, len.min(cap - head), inner_type, SliceFlags::empty(), &mut state.types);
        builder.add_slice_field("part2", ptr, len.saturating_sub(cap - head), inner_type, SliceFlags::empty(), &mut state.types);
        let new_val = builder.finish("VecDeque", val.flags, &mut state.types);
        *val = Cow::Owned(new_val);
    } else {
        let is_string = inner_size == 1 && container_name_looks_like_string(substruct);
        make_slice(val, ptr, len, inner_type, is_string, state);
    }
    Ok(())
}

// shared_ptr: {ptr, refcount} - just remove refcount, so that field unwrapping turns this into plain pointer
fn recognize_shared_ptr(substruct: &mut Substruct) -> Result<()> {
    if substruct.fields.len() != 2 {
        return err!(NoField, "");
    }
    let mut refcount_idx: Option<usize> = None;
    let mut found_ptr = false;
    for (i, f) in substruct.fields.iter().enumerate() {
        match trim_field_name(f.name) {
            "cntrl" | "refcount" => refcount_idx = Some(i),
            "ptr" => found_ptr = true,
            _ => return err!(NoField, ""),
        }
    }
    if let Some(i) = refcount_idx {
        if found_ptr {
            substruct.fields.to_mut().remove(i);
            return err!(NotContainer, ""); // didn't replace the value
        }
    }
    err!(NoField, "")
}

// libc++ string
// union {
//   s: {0: {is_long: 1 bit, size: 7 bits}, padding: [u8; 0], data: [u8; 23]},
//   l: {0: {is_long: 1 bit, cap: 63 bits}, size: usize, data: *u8},
//   r
// }
// (actual capacity is `cap * 2`, where 2 is `__endian_factor`)
// (ifdef _LIBCPP_ABI_ALTERNATE_STRING_LAYOUT then the fields are shuffled around a little)
fn recognize_libcpp_string(substruct: &mut Substruct, val: &mut Cow<Value>, state: &mut EvalState, context: &mut EvalContext) -> Result<()> {
    let mut s = find_struct_field(&["s"], substruct)?;
    let mut l = find_struct_field(&["l"], substruct)?;
    let _ = optional_field(find_field(&["r"], substruct))?;
    substruct.check_all_fields_used()?;

    let mut inner_type: *const TypeInfo = ptr::null();
    let s_is_long_field = find_int_field(&["is_long"], &mut s)?;
    let short_len_field = find_int_field(&["size"], &mut s)?;
    let _ = optional_field(find_field(&["padding"], &mut s))?;
    let (short_data_field, short_capacity) = find_array_field(&["data"], &mut s, &mut inner_type)?;
    s.check_all_fields_used()?;

    let l_is_long_field = find_int_field(&["is_long"], &mut l)?;
    let _ = optional_field(find_int_field(&["cap"], &mut l))?;
    let long_len_field = find_int_field(&["size"], &mut l)?;
    let long_ptr_field = find_pointer_field(&["data"], &mut l, &mut inner_type)?;
    l.check_all_fields_used()?;

    let s_is_long = val.val.bit_range(s_is_long_field, &mut context.memory)?;
    if s_is_long > 1 {
        return err!(Runtime, "bad is_long: {}", s_is_long);
    }
    let l_is_long = val.val.bit_range(l_is_long_field, &mut context.memory)?;
    if s_is_long != l_is_long {
        return err!(Runtime, "s.is_long != l.is_long: {} {}", s_is_long, l_is_long);
    }

    let inner_size = unsafe {(*inner_type).calculate_size()};
    let is_string = inner_size == 1;

    if l_is_long != 0 {
        let (ptr, len) = (val.val.bit_range(long_ptr_field, &mut context.memory)?, val.val.bit_range(long_len_field, &mut context.memory)?);
        make_slice(val, ptr, len, inner_type, is_string, state);
        Ok(())
    } else {
        let len = val.val.bit_range(short_len_field, &mut context.memory)?;
        if len > short_capacity {
            return err!(Runtime, "short len > capacity: {} {}", len, short_capacity);
        }
        return make_array_or_slice(val, short_data_field.start/8, len, inner_type, is_string, state);
    }
}

fn make_array_or_slice(val: &mut Cow<Value>, byte_offset: usize, len: usize, inner_type: *const TypeInfo, is_string: bool, state: &mut EvalState) -> Result<()> {
    let new_val = match &val.val {
        AddrOrValueBlob::Addr(addr) => {
            let slice_type = state.types.add_slice(inner_type, if is_string {SliceFlags::UTF_STRING} else {SliceFlags::empty()});
            let v = AddrOrValueBlob::Blob(ValueBlob::from_two_usizes([addr + byte_offset, len]));
            Value {val: v, type_: slice_type, flags: val.flags}
        }
        AddrOrValueBlob::Blob(blob) => {
            let array_type = state.types.add_array(inner_type, Some(len), if is_string {ArrayFlags::UTF_STRING} else {ArrayFlags::empty()});
            let inner_size = unsafe {(*inner_type).calculate_size()};
            Value {val: AddrOrValueBlob::Blob(blob.byte_range(byte_offset..byte_offset + len*inner_size)?), type_: array_type, flags: val.flags}
        }
    };
    *val = Cow::Owned(new_val);
    Ok(())
}

// absl::InlinedVector: {metadata_: usize, data_: union {allocated: {allocated_data: *T, allocated_capacity: usize}, inlined: {inlined_data: [i8; cap]}}}
// metadata_ & 1 - is_allocated
// metadata_ >> 1 - len
fn recognize_absl_inlined_vector(substruct: &mut Substruct, val: &mut Cow<Value>, state: &mut EvalState, context: &mut EvalContext) -> Result<()> {
    let metadata_field = find_int_field(&["metadata"], substruct)?;
    let mut data = find_struct_field(&["data"], substruct)?;
    substruct.check_all_fields_used()?;
    let mut allocated = find_struct_field(&["allocated"], &mut data)?;
    let mut inlined_type: *const TypeInfo = ptr::null();
    let (inlined_field, inlined_capacity) = find_array_field(&["inlined"], &mut data, &mut inlined_type)?;
    data.check_all_fields_used()?;
    let mut inner_type: *const TypeInfo = ptr::null();
    let allocated_data_field = find_pointer_field(&["allocated_data"], &mut allocated, &mut inner_type)?;
    let _ = find_int_field(&["allocated_capacity"], &mut allocated)?;
    allocated.check_all_fields_used()?;

    let metadata = val.val.bit_range(metadata_field, &mut context.memory)?;
    let (is_long, len) = (metadata & 1 != 0, metadata >> 1);
    if is_long {
        let ptr = val.val.bit_range(allocated_data_field, &mut context.memory)?;
        make_slice(val, ptr, len, inner_type, false, state);
        Ok(())
    } else {
        let inner_size = unsafe {(*inner_type).calculate_size()};
        let inlined_size = unsafe {(*inlined_type).calculate_size()};
        match (len.checked_mul(inner_size), inlined_capacity.checked_mul(inlined_size)) {
            (Some(s), Some(inl)) if s <= inl => (),
            _ => return err!(Runtime, "short len > capacity: {}*{} > {}*{} or overflow", len, inner_size, inlined_capacity, inlined_size),
        }
        return make_array_or_slice(val, inlined_field.start/8, len, inner_type, false, state);
    }
}

// std::list, std::forward_list, std::unordered_{set,map,multiset,multimap}
// libc++ list: {__end_: node, __size_alloc_: usize}, node: {__prev_: *node, __next_: *node}
// libstdc++ list: {_M_prev: *node, _M_next: *node, _M_size: usize}, node: {_M_prev: *node, _M_next: *node}
// libstdc++ forward_list: {_M_next: *node}, node: {_M_next: *node}
// libstdc++ unordered_map: {..., _M_before_begin: node}, node: {_M_nxt: *node}
// In all cases the value is right after the node struct (I wish it was just a field, then pretty printer wouldn't be needed).
// Doesn't cover libc++ forward_list: it has values as field of node struct, so it's ok without pretty printer.
fn recognize_cpp_list(substruct: &mut Substruct, val: &mut Cow<Value>, state: &mut EvalState, context: &mut EvalContext) -> Result<()> {
    let size_field = optional_field(find_int_field(&["size_alloc", "size", "element_count", "p2"], substruct))?;
    let value_type = find_nested_type("value_type", &substruct.nested_names)?;
    let mut node_type: *const TypeInfo = ptr::null();
    let first_node_field;
    let mut allow_extra_fields = false;
    let mut value_offset = 0;
    if let Some(mut before_begin) = optional_field(find_struct_field(&["before_begin"], substruct))? {
        // libstdc++ unordered_map
        allow_extra_fields = true;
        first_node_field = find_pointer_field(&["nxt"], &mut before_begin, &mut node_type)?;
        before_begin.check_all_fields_used()?;
    } else if let Some(p) = optional_field(find_pointer_field(&["p1", "first_node"], substruct, &mut node_type))? {
        // libc++ unordered_map
        first_node_field = p;
        allow_extra_fields = true;
        find_field(&["bucket_list"], substruct)?;
        // libc++ stores hash before the value
        value_offset = 8;
    } else if let Some(mut end) = optional_field(find_struct_field(&["end"], substruct))? {
        first_node_field = find_pointer_field(&["next"], &mut end, &mut node_type)?;
        optional_field(find_pointer_field(&["prev"], &mut end, &mut node_type))?;
        end.check_all_fields_used()?;
    } else {
        first_node_field = find_pointer_field(&["next"], substruct, &mut node_type)?;
        optional_field(find_pointer_field(&["prev"], substruct, &mut node_type))?;
    }
    if !allow_extra_fields {
        substruct.check_all_fields_used()?;
    }

    let mut node_struct = container_aux_struct(node_type)?;
    let next_field = find_pointer_field(&["next", "nxt"], &mut node_struct, &mut node_type)?;
    optional_field(find_pointer_field(&["prev"], &mut node_struct, &mut node_type))?;
    node_struct.check_all_fields_used()?;

    let size = match size_field {
        Some(f) => Some(val.val.bit_range(f, &mut context.memory)?),
        None => None,
    };
    let first_node = val.val.bit_range(first_node_field, &mut context.memory)?;
    let sizeof_node = unsafe {(*node_type).calculate_size()};

    let mut node_addr = first_node;
    let mut data: Vec<u8> = Vec::new();
    let mut is_truncated = false;
    for i in 0..size.unwrap_or(usize::MAX) {
        if node_addr == 0 && size.is_none() {
            break;
        }
        if i >= 300 {
            is_truncated = true;
            break;
        }
        let elem_addr = node_addr.saturating_add(sizeof_node).saturating_add(value_offset);
        data.extend_from_slice(&elem_addr.to_le_bytes());
        node_addr = AddrOrValueBlob::Addr(node_addr).bit_range(next_field.clone(), &mut context.memory)?;
    }
    make_array_of_references(val, data, value_type, is_truncated, state);
    Ok(())
}

fn recognize_rust_hash_table(substruct: &mut Substruct, val: &mut Cow<Value>, state: &mut EvalState, context: &mut EvalContext) -> Result<()> {
    let mut table = find_struct_field(&["table"], substruct)?;
    let bucket_type = find_nested_type("T", &table.nested_names)?;
    let bucket_mask_field = find_int_field(&["bucket_mask"], &mut table)?;
    let mut ctrl_type: *const TypeInfo = ptr::null();
    let ctrl_field = find_pointer_field(&["ctrl"], &mut table, &mut ctrl_type)?;
    if unsafe {(*ctrl_type).calculate_size()} != 1 {
        return err!(NoField, "");
    }

    // Hashbrown hash table works like this:
    //  * x.table.bucket_mask + 1 is the number of buckets
    //  * x.table::T is the bucket type
    //  * x.table.ctrl[i] is the control byte for bucket i; if it's not EMPTY or DELETED, this bucket contains a value
    //  * *(x.table.ctrl as *T - 1 - i) is the bucket value

    let bucket_size = unsafe {(*bucket_type).calculate_size()};
    let bucket_mask = val.val.bit_range(bucket_mask_field, &mut context.memory)?;
    let ctrl = val.val.bit_range(ctrl_field, &mut context.memory)?;
    let limit = 300usize;
    let mut is_truncated = false;
    let n = if bucket_mask + 1 <= limit {
        bucket_mask + 1
    } else {
        is_truncated = true;
        limit
    };
    let mut control_bytes = vec![0u8; n];
    context.memory.read(ctrl, &mut control_bytes)?;
    let mut data: Vec<u8> = Vec::new();
    for i in 0..n {
        let b = control_bytes[i];
        const EMPTY: u8 = 0b1111_1111;
        const DELETED: u8 = 0b1000_0000;
        if b == EMPTY || b == DELETED {
            continue;
        }
        data.extend_from_slice(&(ctrl - bucket_size * (i + 1)).to_le_bytes());
    }
    make_array_of_references(val, data, bucket_type, is_truncated, state);
    Ok(())
}

fn recognize_libstdcpp_deque(substruct: &mut Substruct, val: &mut Cow<Value>, state: &mut EvalState, context: &mut EvalContext) -> Result<()> {
    find_field(&["map"], substruct)?;
    let mut start = find_struct_field(&["start"], substruct)?;
    let mut finish = find_struct_field(&["finish"], substruct)?;
    let mut value_type = find_nested_type("value_type", &substruct.nested_names)?;
    let start_cur_field = find_pointer_field(&["cur"], &mut start, &mut value_type)?;
    let start_first_field = find_pointer_field(&["first"], &mut start, &mut value_type)?;
    let start_last_field = find_pointer_field(&["last"], &mut start, &mut value_type)?;
    let mut value_ptr_type: *const TypeInfo = ptr::null();
    let start_node_field = find_pointer_field(&["node"], &mut start, &mut value_ptr_type)?;
    start.check_all_fields_used()?;
    let finish_cur_field = find_pointer_field(&["cur"], &mut finish, &mut value_type)?;
    let finish_first_field = find_pointer_field(&["first"], &mut finish, &mut value_type)?;
    let finish_last_field = find_pointer_field(&["last"], &mut finish, &mut value_type)?;
    let finish_node_field = find_pointer_field(&["node"], &mut finish, &mut value_ptr_type)?;
    finish.check_all_fields_used()?;

    match unsafe {&(*value_ptr_type).t} {
        Type::Pointer(p) if p.type_ == value_type => (),
        _ => return err!(NoField, ""),
    }
    let value_size = unsafe {(*value_type).calculate_size()};
    if value_size == 0 {
        return err!(NotContainer, "");
    }

    let start_cur = val.val.bit_range(start_cur_field, &mut context.memory)?;
    let start_first = val.val.bit_range(start_first_field, &mut context.memory)?;
    let start_last = val.val.bit_range(start_last_field, &mut context.memory)?;
    let start_node = val.val.bit_range(start_node_field, &mut context.memory)?;
    let finish_cur = val.val.bit_range(finish_cur_field, &mut context.memory)?;
    let finish_first = val.val.bit_range(finish_first_field, &mut context.memory)?;
    let finish_last = val.val.bit_range(finish_last_field, &mut context.memory)?;
    let finish_node = val.val.bit_range(finish_node_field, &mut context.memory)?;

    if start_cur == finish_cur {
        // Empty.
        make_array_of_references(val, Vec::new(), value_type, /*is_truncated*/ false, state);
        return Ok(());
    }

    if start_last < start_first {
        return err!(NotContainer, "");
    }
    let block_bytes = start_last - start_first;
    if block_bytes % value_size != 0 || finish_last < finish_first || block_bytes != finish_last - finish_first || block_bytes == 0 {
        return err!(NotContainer, "");
    }
    if finish_node < start_node || (finish_node - start_node) % 8 != 0 || start_cur < start_first || start_cur > start_last || (start_cur - start_first) % value_size != 0 || finish_cur < finish_first || finish_cur > finish_last || (finish_cur - finish_first) % value_size != 0 {
        return err!(NotContainer, "");
    }

    let mut data: Vec<u8> = Vec::new();
    let (mut cur, mut block_end, mut block_ptr) = (start_cur, start_last, start_node);
    let mut is_truncated = false;
    loop {
        if data.len() / 8 >= 1000 {
            is_truncated = true;
            break;
        }
        if block_ptr == finish_node && cur == finish_cur {
            break;
        }
        if cur == block_end {
            block_ptr += 8;
            cur = context.memory.read_usize(block_ptr)?;
            block_end = cur + block_bytes;
        }
        if block_ptr == finish_node && cur == finish_cur {
            break;
        }
        data.extend_from_slice(&cur.to_le_bytes());
        cur += value_size;
    }

    make_array_of_references(val, data, value_type, is_truncated, state);

    Ok(())
}

fn recognize_libcpp_deque(substruct: &mut Substruct, val: &mut Cow<Value>, state: &mut EvalState, context: &mut EvalContext) -> Result<()> {
    let mut type_ = val.type_;
    // std::stack and std::queue are pointless trivial wrappers around std::deque. Unwrap.
    if let Some(t) = optional_field(find_nested_type("container_type", &substruct.nested_names))? {
        type_ = t;
    }

    let value_type = find_nested_type("value_type", unsafe {(*type_).nested_names})?;
    let mut map = find_struct_field(&["map"], substruct)?;
    let start_field = find_int_field(&["start"], substruct)?;
    let size_field = find_int_field(&["size"], substruct)?;
    substruct.check_all_fields_used()?;

    let mut value_ptr_type: *const TypeInfo = ptr::null();
    let begin_field = find_pointer_field(&["begin"], &mut map, &mut value_ptr_type)?;
    find_pointer_field(&["first", "front_cap"], &mut map, &mut value_ptr_type)?;
    find_pointer_field(&["end"], &mut map, &mut value_ptr_type)?;
    optional_field(find_pointer_field(&["end_cap", "back_cap", "cap"], &mut map, &mut value_ptr_type))?;
    map.check_all_fields_used()?;

    match unsafe {&(*value_ptr_type).t} {
        Type::Pointer(p) if p.type_ == value_type => (),
        _ => return err!(NoField, ""),
    }
    let value_size = unsafe {(*value_type).calculate_size()};

    let iterator_type = find_nested_type("iterator", unsafe {(*type_).nested_names})?;
    let mut block_size = find_nested_usize_constant("_BS", unsafe {(*iterator_type).nested_names})?;
    if block_size == 0 {
        // With _LIBCPP_ABI_INCOMPLETE_TYPES_IN_DEQUE, this template argument is always zero, and instead the static constant field __block_size is used.
        // But the value of this field doesn't seem to be present anywhere in the debug symbols. Neither are instantiations of the struct __deque_block_size.
        // So I'm falling back to calculating block size right here, using the formula from __deque_block_size from some version of libc++.
        // This may quietly break for other versions.
        if value_size > 0 {
            block_size = if value_size < 256 {4096 / value_size} else {16};
        } else {
            return err!(NotContainer, "");
        }
    }

    let start = val.val.bit_range(start_field, &mut context.memory)?;
    let size = val.val.bit_range(size_field, &mut context.memory)?;
    let begin = val.val.bit_range(begin_field, &mut context.memory)?;

    let mut data: Vec<u8> = Vec::new();
    let mut is_truncated = false;
    let mut block_start = 0usize;
    for i in start..start+size {
        if i - start > 1000 {
            is_truncated = true;
            break;
        }
        if i == start || i % block_size == 0 {
            block_start = context.memory.read_usize(begin + i / block_size * 8)?;
        }
        let ptr = block_start + i % block_size * value_size;
        data.extend_from_slice(&ptr.to_le_bytes());
    }

    make_array_of_references(val, data, value_type, is_truncated, state);

    Ok(())
}

fn recognize_cpp_map(substruct: &mut Substruct, val: &mut Cow<Value>, state: &mut EvalState, context: &mut EvalContext) -> Result<()> {
    let value_type = find_nested_type("value_type", &substruct.nested_names)?;
    let root_field;
    let mut node_type: *const TypeInfo = ptr::null();
    let mut custom_value_offset: Option<usize> = None;
    if optional_field(find_int_field(&["node_count"], substruct))?.is_some() {
        // libstdc++
        let mut header = find_struct_field(&["header"], substruct)?;
        root_field = find_pointer_field(&["parent"], &mut header, &mut node_type)?;
        find_pointer_field(&["left"], &mut header, &mut node_type)?;
        find_pointer_field(&["right"], &mut header, &mut node_type)?;
        find_field(&["color"], &mut header)?;
        header.check_all_fields_used()?;
    } else {
        // libc++
        find_int_field(&["pair3", "size"], substruct)?; // node count
        root_field = find_pointer_field(&["pair1", "end_node"], substruct, &mut node_type)?;
        find_field(&["begin_node"], substruct)?;

        // The base node struct is 3 pointers + 1 byte (color) + 7 bytes of padding = 32 bytes.
        // If the value type is small, it may be packed into that padding, so the actual offset is not always 32. Find it.
        // (This problem only came up in libc++ trees, not in libstdc++ trees (because it aligns value to 8 bytes for some reason), and not in linked lists (because the base node struct has no padding).)
        let tree = find_nested_type("__base", &substruct.nested_names)?;
        let np = find_nested_type("__node_pointer", unsafe {(*tree).nested_names})?;
        let n = match unsafe {&(*np).t} {
            Type::Pointer(p) => p.type_,
            _ => return err!(NoField, ""),
        };
        let mut ns = container_aux_struct(n)?;
        let value_field = find_field(&["value"], &mut ns)?;
        if value_field.bit_offset % 8 != 0 {
            return err!(NotContainer, "");
        }
        custom_value_offset = Some(value_field.bit_offset / 8);
    }
    substruct.check_all_fields_used()?;

    let mut node_struct = container_aux_struct(node_type)?;
    find_pointer_field(&["parent"], &mut node_struct, &mut ptr::null())?;
    let left_field = find_pointer_field(&["left"], &mut node_struct, &mut node_type)?;
    let right_field = find_pointer_field(&["right"], &mut node_struct, &mut node_type)?;
    find_field(&["color", "is_black"], &mut node_struct)?;
    node_struct.check_all_fields_used()?;

    let node_size = unsafe {(*node_type).calculate_size()};
    let value_offset = custom_value_offset.unwrap_or(node_size);

    let root = val.val.bit_range(root_field, &mut context.memory)?;

    // (The algorithm is chosen to minimize random reads from debuggee memory: each node is read once.)
    let mut stack: Vec<(usize, /*pass*/ u8)> = vec![(root, 0)];
    let mut data: Vec<u8> = Vec::new();
    for i in 0..1000 {
        match stack.pop() {
            None => break,
            Some((0, _)) => (),
            Some((node, 0)) => {
                let node_val = AddrOrValueBlob::Addr(node);
                let left = node_val.bit_range(left_field.clone(), &mut context.memory)?;
                let right = node_val.bit_range(right_field.clone(), &mut context.memory)?;
                stack.push((right, 0));
                stack.push((node, 1));
                stack.push((left, 0));
            }
            Some((node, 1)) => data.extend_from_slice(&(node + value_offset).to_le_bytes()),
            _ => panic!("huh"),
        }
    }

    make_array_of_references(val, data, value_type, /*is_truncated*/ !stack.is_empty(), state);

    Ok(())
}

// libc++: {union {__null_state_, __val_}, __engaged_}
// libstdc++: {_M_payload: {_M_empty: {}, _M_value}, _M_engaged}
fn recognize_cpp_optional(substruct: &mut Substruct, val: &mut Cow<Value>, state: &mut EvalState, context: &mut EvalContext, prettify_again: &mut bool) -> Result<()> {
    let engaged_field = find_int_field(&["engaged"], substruct)?;
    optional_field(find_field(&["null_state"], substruct))?;
    let payload_field = find_field(&["val", "payload"], substruct)?;
    substruct.check_all_fields_used()?;

    let engaged = val.val.bit_range(engaged_field.clone(), &mut context.memory)?;
    match engaged {
        0 => {
            let mut en = EnumType {enumerands: &[], type_: state.builtin_types.u8_};
            state.types.add_enumerand(&mut en, Enumerand {name: "nullopt", value: 0, flags: EnumerandFlags::empty()});
            let enum_type = state.types.add_enum(en);
            let new_val = Value {val: AddrOrValueBlob::Blob(ValueBlob::new(0)), type_: enum_type, flags: ValueFlags::empty()};
            *val = Cow::Owned(new_val);
        }
        1 => {
            let field_val = get_struct_field(&val.val, &payload_field, &mut context.memory)?;
            let new_val = Value {val: field_val, type_: payload_field.type_, flags: val.flags};
            *val = Cow::Owned(new_val);
            *prettify_again = true;
        }
        _ => return err!(NotContainer, "")
    }
    Ok(())
}
