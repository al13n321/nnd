use crate::{*, error::{*, Result, Error}, util::*, registers::*, types::*, procfs::*, symbols_registry::*, process_info::*, unwind::*, symbols::*, arena::*, pretty::*, settings::*};
use std::{fmt, fmt::Write, mem, collections::{HashMap, HashSet}, io::Write as ioWrite};
use tui::{style::{Style, Modifier, Color}};
use gimli::{Operation, EndianSlice, LittleEndian, Expression, Encoding, EvaluationResult, ValueType, DieReference, DW_AT_location, Location, DebugInfoOffset};
use bitflags::*;

type SliceType = EndianSlice<'static, LittleEndian>;

// Just a byte array that avoids heap allocation if length is <= 24 bytes.
// Doesn't store an exact length. The length is usually determined by data type, stored separately.
// Most of the time used for storing 8-byte values, e.g. copied from registers, so this case needs to be fast.
// TODO: Refactor to know its length and be 16 bytes.
#[derive(Debug, Clone)]
pub enum ValueBlob {
    Small([usize; 3]),
    Big(Vec<u8>),
}

impl ValueBlob {
    pub fn new(v: usize) -> Self { Self::Small([v, 0, 0]) }

    pub fn from_vec(v: Vec<u8>) -> Self {
        if v.len() <= 24 {
            Self::from_slice(&v)
        } else {
            Self::Big(v)
        }
    }

    pub fn with_capacity(bytes: usize) -> Self {
        if bytes <= 24 {
            Self::Small([0; 3])
        } else {
            Self::Big(vec![0; bytes])
        }
    }

    pub fn from_slice(s: &[u8]) -> Self {
        let mut r = Self::with_capacity(s.len());
        r.as_mut_slice()[..s.len()].copy_from_slice(s);
        r
    }

    pub fn as_slice(&self) -> &[u8] { match self { Self::Small(a) => unsafe{std::slice::from_raw_parts(mem::transmute(a.as_slice().as_ptr()), 24)}, Self::Big(v) => v.as_slice() } }
    pub fn as_mut_slice(&mut self) -> &mut [u8] { match self { Self::Small(a) => unsafe{std::slice::from_raw_parts_mut(mem::transmute(a.as_mut_slice().as_mut_ptr()), 24)}, Self::Big(v) => v.as_mut_slice() } }

    pub fn get_usize(&self) -> Result<usize> {
        match self {
            Self::Small(a) => Ok(a[0]),
            Self::Big(v) => return err!(Dwarf, "unexpectedly long value: {} bytes", v.len()),
        }
    }

    pub fn get_usize_prefix(&self) -> usize {
        match self {
            Self::Small(a) => a[0],
            Self::Big(v) => {
                let mut a: [u8; 8] = [0; 8];
                let n = v.len().min(8);
                a[..n].copy_from_slice(&v[..n]);
                usize::from_le_bytes(a)
            }
        }
    }

    pub fn resize(&mut self, bytes: usize) {
        match self {
            Self::Small(a) => {
                if bytes <= 24 {
                    return;
                }
                let a = *a;
                let mut v = Vec::from(self.as_slice());
                v.resize(bytes, 0);
                *self = Self::Big(v);
                
            }
            Self::Big(v) => {
                if bytes > 24 {
                    v.resize(bytes, 0);
                    return;
                }
                let mut b = Self::new(0);
                b.as_mut_slice()[..bytes].copy_from_slice(&v[..bytes]);
                *self = b;
            }
        }
    }

    pub fn capacity(&self) -> usize {
        match self {
            Self::Small(a) => 24,
            Self::Big(v) => v.len(),
        }
    }

    // Concatenate two bit strings. Used infrequently, implemented inefficiently.
    pub fn append_bits(&mut self, self_bits: usize, mut other: ValueBlob, size_in_bits: usize, bit_offset: usize) {
        other.zero_upper_bits(bit_offset + size_in_bits);
        let total_bytes = (self_bits + size_in_bits + 7) / 8;
        self.resize(total_bytes);
        let dest = self.as_mut_slice();

        if self_bits & 7 == 0 && bit_offset == 0 {
            // (Relatively) fast path.
            let src = &other.as_slice()[..(size_in_bits+7)/8];
            let self_bytes = self_bits / 8;
            dest[self_bytes..self_bytes + src.len()].copy_from_slice(src);
            return;
        }

        // We need bit other[i] to be ORed into bit self[i - bit_offset + self_bits].
        let shift = 16 - (bit_offset & 7) + (self_bits & 7);
        other.shl(shift); // (this number is added to the index of each bit)
        let self_whole_bytes = self_bits/8;
        // i - bit_offset + self_bits = i + shift - skip_bytes*8 + self_bits/8*8
        // skip_bytes*8 = bit_offset - self_bits&7 + shift
        let skip_bytes = 2 + bit_offset/8;
        self.bitwise_or(self_whole_bytes, &other, skip_bytes, total_bytes - self_whole_bytes);
    }
    pub fn shl(&mut self, bits: usize) { // bit from position i goes to position i+bits
        let bytes = self.capacity();
        self.resize(bytes + (bits+7)/8);
        let slice = self.as_mut_slice();
        if bits & 7 == 0 {
            slice.copy_within(0..bytes, bits/8);
        } else {
            for i in (0..bytes).rev() {
                let b = slice[i];
                slice[i + bits/8+1] |= b >> (8 - (bits & 7) as u32);
                slice[i + bits/8] = b << (bits & 7) as u32;
            }
        }
    }
    pub fn shr(&mut self, bits: usize) { // i -> i-bits
        let bytes = self.capacity();
        if bits > bytes*8 {
            panic!("tried to shift {}-byte value by {} bits", bytes, bits);
        }
        let slice = self.as_mut_slice();
        if bits & 7 == 0 {
            slice.copy_within(bits/8.., 0);
        } else {
            for i in 0..bytes-bits/8 {
                slice[i] = slice[i + bits/8] >> (bits & 7);
                if i + bits/8 + 1 < bytes {
                    slice[i] |= slice[i + bits/8 + 1] << (8 - (bits & 7));
                }
            }
        }
        self.resize(bytes - bits/8);
    }
    pub fn bitwise_or(&mut self, self_start: usize, other: &Self, other_start: usize, count: usize) {
        let slice = self.as_mut_slice();
        let other = other.as_slice();
        for i in 0..count {
            slice[self_start + i] |= other[other_start + i];
        }
    }
    pub fn zero_upper_bits(&mut self, bits_to_keep: usize) {
        let slice = self.as_mut_slice();
        slice[(bits_to_keep+7)/8..].fill(0);
        if bits_to_keep & 7 != 0 {
            slice[bits_to_keep/8] &= (1 << (bits_to_keep & 7) as u32) - 1;
        }
    }

    pub fn bit_range(&self, bit_offset: usize, bit_size: usize) -> Result<Self> {
        let byte_offset = bit_offset/8;
        let byte_end = (bit_offset + bit_size + 7)/8;
        let slice = self.as_slice();
        if byte_end > slice.len() {
            return err!(Dwarf, "bit range out of bounds");
        }
        let mut res = Self::from_slice(&slice[byte_offset..byte_end]);
        if bit_offset & 7 != 0 {
            res.shr(bit_offset & 7);
            res.resize((bit_size + 7)/8);
        }
        if bit_size & 7 != 0 {
            res.zero_upper_bits(8 - (bit_size & 7));
        }
        Ok(res)
    }
}

// For values whose address is known, we defer the dereferencing just in case a user expression takes address again ('&' operator).
#[derive(Debug, Clone)]
pub enum AddrOrValueBlob {
    Addr(usize),
    Blob(ValueBlob),
}
impl Default for AddrOrValueBlob { fn default() -> Self { AddrOrValueBlob::Blob(ValueBlob::new(0)) } }

impl AddrOrValueBlob {
    pub fn into_value(self, bytes: usize, memory: &MemReader) -> Result<ValueBlob> {
        Ok(match self {
            Self::Blob(b) => {
                if b.capacity() < bytes {
                    return err!(Dwarf, "value too short: ~{} < {}", b.capacity(), bytes);
                }
                b
            }
            Self::Addr(a) => {
                let mut b = ValueBlob::with_capacity(bytes);
                memory.read(a, &mut b.as_mut_slice()[..bytes])?;
                b
            }
        })
    }

    pub fn addr(&self) -> Option<usize> { match self { Self::Addr(a) => Some(*a), _ => None } }
    pub fn blob_ref(&self) -> Option<&ValueBlob> { match self { Self::Blob(b) => Some(b), _ => None } }
}

pub fn format_dwarf_expression<'a>(expr: Expression<EndianSlice<'a, LittleEndian>>, encoding: Encoding) -> Result<String> {
    let mut res = String::new();
    let mut op_iter = expr.operations(encoding);
    while let Some(op) = op_iter.next()? {
        if !res.is_empty() {
            res.push_str(" ");
        }
        match op {
            // These push to stack.
            Operation::Deref {base_type, size, space} => write!(res, "deref({})", size)?,
            Operation::Pick {index} => write!(res, "pick({})", index)?,
            Operation::PlusConstant {value} => write!(res, "+{}", value)?,
            Operation::UnsignedConstant {value} => write!(res, "{}u", value)?,
            Operation::SignedConstant {value} => write!(res, "{}s", value)?,
            Operation::RegisterOffset {register, offset, base_type} => {
                if let Some(r) = RegisterIdx::from_dwarf(register) { write!(res, "{}", r) } else { write!(res, "register({})", register.0) }?;
                if offset != 0 {
                    write!(res, "{:+}", offset)?;
                }
                if base_type.0 != 0 {
                    write!(res, "(type@u+{:x})", base_type.0)?;
                }
            }
            Operation::FrameOffset {offset} => {
                write!(res, "fb")?;
                if offset != 0 {
                    write!(res, "{:+}", offset)?;
                }
            }
            Operation::EntryValue {expression} => write!(res, "entry_value({})", format_dwarf_expression(Expression(expression), encoding)?)?,
            Operation::Address {address} => write!(res, "addr({:x})", address)?,
            Operation::AddressIndex {index} => write!(res, "debug_addr[{}]", index.0)?,
            Operation::ConstantIndex {index} => write!(res, "debug_addr(const)[{}]", index.0)?,
            Operation::TypedLiteral {base_type, value} => write!(res, "typed_literal(@u+{:x}, {:?})", base_type.0, value)?,
            Operation::Convert {base_type} => write!(res, "convert(@u+{:x})", base_type.0)?,
            Operation::Reinterpret {base_type} => write!(res, "reinterpret(@u+{:x})", base_type.0)?,
            Operation::PushObjectAddress => write!(res, "push_object_addr")?,
            Operation::TLS => write!(res, "tls")?,
            Operation::CallFrameCFA => write!(res, "cfa")?,

            // These specify where the result is.
            Operation::Register {register} => {
                write!(res, "reg(")?;
                if let Some(r) = RegisterIdx::from_dwarf(register) { write!(res, "{}", r) } else { write!(res, "register({})", register.0) }?;
                write!(res, ")")?;
            }
            Operation::Piece {size_in_bits, bit_offset} => write!(res, "piece({};{})", size_in_bits, bit_offset.unwrap_or(0))?,
            Operation::ImplicitValue {data} => write!(res, "implicit_value({:?})", data)?,
            Operation::ImplicitPointer {value, byte_offset} => write!(res, "implicit_pointer({:?}, {})", value, byte_offset)?,
            Operation::StackValue => write!(res, "stack")?,

            // Branch.
            Operation::Bra {target} => write!(res, "branch({})", target)?,
            Operation::Skip {target} => write!(res, "skip({})", target)?,

            // Call another expression.
            Operation::Call {offset} => write!(res, "call(@{:?})", offset)?,

            // Other.
            Operation::ParameterRef {offset} => write!(res, "parameter_ref(@u+{:x})", offset.0)?,
            Operation::WasmLocal {..} | Operation::WasmGlobal {..} | Operation::WasmStack {..} => write!(res, "wasm(?)")?,

            // Various operations on the stack.
            _ => write!(res, "{}", match op {
                Operation::Drop => "drop",
                Operation::Swap => "swap",
                Operation::Rot => "rot",
                Operation::Abs => "abs",
                Operation::And => "and",
                Operation::Div => "div",
                Operation::Minus => "minus",
                Operation::Mod => "mod",
                Operation::Mul => "mul",
                Operation::Neg => "neg",
                Operation::Not => "not",
                Operation::Or => "or",
                Operation::Plus => "plus",
                Operation::Shl => "shl",
                Operation::Shr => "shr",
                Operation::Shra => "shra",
                Operation::Xor => "xor",
                Operation::Eq => "eq",
                Operation::Ge => "ge",
                Operation::Gt => "gt",
                Operation::Le => "le",
                Operation::Lt => "lt",
                Operation::Ne => "ne",
                Operation::Nop => "nop",
                _ => "???",
            })?,
        }
    }
    Ok(res)
}

pub struct EvalState {
    binaries: Vec<BinaryInfo>,
    pub currently_evaluated_value_dubious: bool,
    pub types: Types,
    pub builtin_types: BuiltinTypes,
    pub variables: HashMap<String, Value>,
    // We may add things like name lookup cache (for types and global variables) here, though maybe we should avoid slow lookups here and expect the user to use search dialog to look up canonical names for things, maybe even automatically adding alias watches to shorten.
}

impl EvalState {
    pub fn new() -> Self {
        let mut types = Types::new();
        let builtin_types = types.add_builtins();
        Self { binaries: Vec::new(), currently_evaluated_value_dubious: false, types, builtin_types, variables: HashMap::new() } }

    pub fn clear(&mut self) {
        self.binaries.clear();
        self.types = Types::new();
        self.builtin_types = self.types.add_builtins();
        self.variables.clear();
    }

    pub fn update(&mut self, context: &EvalContext) {
        let mut seen_binaries: HashSet<BinaryId> = HashSet::new();
        for b in &self.binaries {
            seen_binaries.insert(b.id.clone());
        }
        for (id, info) in &context.process_info.binaries {
            if info.symbols.is_ok() && !seen_binaries.contains(id) {
                self.binaries.push(info.clone());
            }
        }
    }

    // Collect information needed to retrieve values of local variables.
    pub fn make_local_dwarf_eval_context<'a>(&'a self, context: &'a EvalContext<'a>, selected_subframe: usize) -> Result<(DwarfEvalContext<'a>, &'a FunctionInfo)> {
        let subframe = &context.stack.subframes[selected_subframe];
        let selected_frame = subframe.frame_idx;
        let frame = &context.stack.frames[selected_frame];
        let function = &context.stack.subframes[frame.subframes.end-1].function.as_ref_clone_error()?.0;
        let binary_id = match frame.binary_id.as_ref() {
            None => return err!(ProcessState, "no binary for address {:x}", frame.pseudo_addr),
            Some(b) => b,
        };
        if subframe.subfunction.is_none() {
            return err!(Dwarf, "function has no debug info");
        }
        let binary = context.process_info.binaries.get(binary_id).unwrap();
        let symbols = binary.symbols.as_ref_clone_error()?;
        let unit = match function.debug_info_offset() {
            None => return err!(ProcessState, "function has no debug info"),
            Some(off) => symbols.find_unit(off)? };
        let context = DwarfEvalContext {memory: context.memory, symbols: Some(symbols), addr_map: &binary.addr_map, encoding: unit.unit.header.encoding(), unit: Some(unit), regs: Some(&frame.regs), frame_base: &frame.frame_base};
        Ok((context, function))
    }

    pub fn get_variable(&mut self, context: &EvalContext, name: &str, maybe_register: bool, from_any_frame: bool, global: bool, only_type: bool) -> Result<Value> {
        if global {
            return err!(NotImplemented, "global variables not implemented");
        }
        if context.stack.frames.is_empty() {
            return err!(Internal, "no stack");
        }
        if maybe_register {
            if let Some(reg) = RegisterIdx::parse_ignore_case(name) {
                let type_ = self.builtin_types.u64_;
                if only_type {
                    return Ok(Value {val: Default::default(), type_, flags: ValueFlags::empty()});
                }
                let frame = &context.stack.frames[context.stack.subframes[context.selected_subframe].frame_idx];
                return match frame.regs.get_int(reg) {
                    Ok((v, dub)) => {
                        self.currently_evaluated_value_dubious |= dub;
                        Ok(Value {val: AddrOrValueBlob::Blob(ValueBlob::new(v as usize)), type_, flags: ValueFlags::empty()})
                    }
                    Err(_) => err!(Dwarf, "value of {} register is not known", reg),
                };
            }
        }
        for relative_subframe_idx in 0..context.stack.subframes.len().min(if from_any_frame {usize::MAX} else {1}) {
            let subframe_idx = (context.selected_subframe + relative_subframe_idx) % context.stack.subframes.len();
            match self.get_local_variable(context, name, subframe_idx, only_type) {
                Ok(v) => return Ok(v),
                Err(e) if !from_any_frame => return Err(e),
                Err(_) => (),
            }
        }
        err!(NoVariable, "local var {} not found in any frame", name)
    }

    pub fn get_type(&mut self, context: &EvalContext, name: &str) -> Result<*const TypeInfo> {
        for binary in &self.binaries {
            let symbols = match &binary.symbols {
                Ok(x) => x,
                Err(_) => continue };
            for shard in &symbols.shards {
                if let Some(t) = shard.types.find_by_name(name) {
                    return Ok(t);
                }
            }
        }
        err!(TypeMismatch, "no type '{}'", name)
    }

    fn get_local_variable(&mut self, context: &EvalContext, name: &str, subframe_idx: usize, only_type: bool) -> Result<Value> {
        let (dwarf_context, function) = self.make_local_dwarf_eval_context(context, subframe_idx)?;
        let symbols = dwarf_context.symbols.unwrap();
        let subframe = &context.stack.subframes[subframe_idx];
        let pseudo_addr = context.stack.frames[subframe.frame_idx].pseudo_addr;
        let static_pseudo_addr = dwarf_context.addr_map.dynamic_to_static(pseudo_addr);
        let subfunction = &subframe.subfunction.as_ref().unwrap().0;
        for v in symbols.local_variables_in_subfunction(subfunction, function.shard_idx()) {
            if !v.range().contains(&(static_pseudo_addr)) || unsafe {v.name()} != name {
                continue;
            }
            if only_type {
                return Ok(Value {val: Default::default(), type_: v.type_, flags: ValueFlags::empty()});
            }
            let (value, dubious) = eval_dwarf_expression(v.expr, &dwarf_context)?;
            let val = Value {val: value, type_: v.type_, flags: ValueFlags::empty()};
            self.currently_evaluated_value_dubious |= dubious;
            return Ok(val);
        }
        // TODO: Add " (use ^{} if global variable)" when we have global variables.
        err!(NoVariable, "local var {} not found", name)
    }
}

pub struct EvalContext<'a> {
    pub memory: &'a MemReader,
    pub process_info: &'a ProcessInfo,
    // We include the whole stack to allow watch expressions to use variables from other frames.
    pub stack: &'a StackTrace,
    pub selected_subframe: usize,
}

bitflags! { pub struct ValueFlags: u8 {
    // Ignore pretty printers. Affects formatting, field access, dereferencing (for smart pointers), indexing (for containers).
    const RAW = 0x1;
    const HEX = 0x2;
    const BIN = 0x4;

    // Similar to RAW, disables automatic unwrapping of single-field structs by prettifier. Doesn't do any of the other RAW things.
    // Can't be changed by the user. Used for structs produced by MetaType/MetaField.
    const NO_UNWRAPPING_INTERNAL = 0x8;
    // When formatting value, print struct name. Used after automatic downcasting. Not inherited by fields.
    const SHOW_TYPE_NAME = 0x10;
}}
impl ValueFlags {
    pub fn inherit(self) -> Self { self & !Self::SHOW_TYPE_NAME }
}

#[derive(Clone)]
pub struct Value {
    // We don't pre-check that val's blob capacity >= type_.size. It's up to the consumer of Value to check this when needed.
    pub val: AddrOrValueBlob,
    pub type_: *const TypeInfo,
    pub flags: ValueFlags,
}

// Appends to out.chars. Doesn't close the line, the caller should do it after the call.
// If expanded is true, the returned Vec is populated, and field names and array elements are not included in `out`.
pub fn format_value(v: &Value, expanded: bool, state: &mut EvalState, context: &EvalContext, arena: &mut Arena, out: &mut StyledText, palette: &Palette) -> (/*has_children*/ bool, /*children*/ Vec<(/*name*/ &'static str, /*child_id*/ usize, Result<Value>)>) {
    format_value_recurse(v, expanded, state, context, arena, out, palette, (out.lines.len(), out.chars.len()), false)
}

fn over_output_limit(out: &StyledText, text_start: (/*lines*/ usize, /*chars*/ usize)) -> bool {
    // (Currently we don't produce multiple lines, but have a line limit anyway in case we do it in future, e.g. for printing matrices.)
    out.chars.len() - text_start.1 > 100000 || out.lines.len() - text_start.0 > 1000 || (out.lines.len() == text_start.0 && out.chars.len() - text_start.1 > 1000)
}

pub fn format_value_recurse(v: &Value, expanded: bool, state: &mut EvalState, context: &EvalContext, arena: &mut Arena, out: &mut StyledText, palette: &Palette, text_start: (/*lines*/ usize, /*chars*/ usize), address_already_shown: bool) -> (/*has_children*/ bool, /*children*/ Vec<(/*name*/ &'static str, /*child_id*/ usize, Result<Value>)>) {
    // Output length limit. Also acts as recursion depth limit.
    if over_output_limit(out, text_start) {
        styled_write!(out, palette.value_warning, "…");
        return (false, Vec::new());
    }

    let write_address = |addr: usize, out: &mut StyledText| {
        styled_write!(out, palette.value_misc, "&0x{:x} ", addr);
    };
    let write_val_address_if_needed = |v: &AddrOrValueBlob, out: &mut StyledText| {
        if let AddrOrValueBlob::Addr(a) = v {
            if !address_already_shown {
                write_address(*a, out);
            }
        }
    };
    let list_struct_children = |value: &AddrOrValueBlob, s: &StructType, flags: ValueFlags, state: &mut EvalState, context: &EvalContext| -> Vec<(&'static str, usize, Result<Value>)> {
        let mut children: Vec<(&'static str, usize, Result<Value>)> = Vec::new();
        for (field_idx, field) in s.fields().iter().enumerate() {
            let name = if field.name.is_empty() {
                let mut w = state.types.misc_arena.write();
                write!(w, "{}", field_idx).unwrap();
                w.finish_str()
            } else {
                field.name
            };
            let field_val = match get_struct_field(value, field, context.memory) {
                Ok(val) => Ok(Value {val, type_: field.type_, flags: flags.inherit()}),
                Err(e) => Err(e),
            };
            children.push((name, hash(&(name, field_idx)), field_val));
        }
        children
    };

    let mut prettified_value: Option<Value> = None;
    if !v.flags.contains(ValueFlags::RAW) {
        prettified_value = match prettify_value(v, state, context) {
            Ok((x, warning)) => {
                if let Some(w) = warning {
                    styled_write!(out, palette.value_error, "<{}> ", w);
                }
                x
            }
            Err(e) => {
                write_val_address_if_needed(&v.val, out);
                styled_write!(out, palette.value_error, "<{}>", e);
                return (false, Vec::new());
            }
        };
    }
    let v = if let Some(vv) = &prettified_value {
        vv
    } else {
        v
    };

    let mut children: Vec<(&'static str, usize, Result<Value>)> = Vec::new();
    let t = unsafe {&*v.type_};
    let size = t.calculate_size();
    let value = match v.val.clone().into_value(size.min(1000000), context.memory) {
        Ok(v) => v,
        Err(e) => {
            write_val_address_if_needed(&v.val, out);
            styled_write!(out, palette.value_error, "<{}>", e);
            return (false, children);
        }
    };

    match &t.t {
        Type::Unknown => {
            write_val_address_if_needed(&v.val, out);
            styled_write!(out, palette.value_misc, "0x{:x} ", value.get_usize_prefix());
            styled_write!(out, palette.value_error, "<unknown type>");
        }
        Type::Primitive(p) => match value.get_usize() {
            Ok(_) if size == 0 => styled_write!(out, palette.value_misc, "()"), // covers things like void, decltype(nullptr), rust empty tuple, rust `!` type
            Ok(mut x) if size <= 8 => {
                let as_number = v.flags.intersects(ValueFlags::RAW | ValueFlags::HEX | ValueFlags::BIN);
                if p.contains(PrimitiveFlags::FLOAT) {
                    match size {
                        4 => styled_write!(out, palette.value, "{}", unsafe {mem::transmute::<u32, f32>(x as u32)}),
                        8 => styled_write!(out, palette.value, "{}", unsafe {mem::transmute::<usize, f64>(x)}),
                        _ => styled_write!(out, palette.value_error, "<bad size: {}>", size),
                    }
                } else if p.contains(PrimitiveFlags::UNSPECIFIED) {
                    write_val_address_if_needed(&v.val, out);
                    styled_write!(out, palette.value_misc, "<unspecified type> 0x{:x}", x);
                } else if p.contains(PrimitiveFlags::CHAR) && !as_number {
                    if size > 4 {
                        styled_write!(out, palette.value_error, "<bad char size: {}>", size);
                    } else if let Some(c) = char::from_u32(x as u32) {
                        styled_write!(out, palette.value, "{} '{}'", c as u32, c);
                    } else {
                        styled_write!(out, palette.value_error, "<bad char: {}>", x);
                    }
                } else if p.contains(PrimitiveFlags::BOOL) && !as_number {
                    match x {
                        0 => styled_write!(out, palette.value, "false"),
                        1 => styled_write!(out, palette.value, "true"),
                        _ => styled_write!(out, palette.value_warning, "{}", x),
                    }
                } else {
                    // Sign-extend.
                    let signed = p.contains(PrimitiveFlags::SIGNED);
                    if signed && size < 8 && x & 1 << (size*8-1) as u32 != 0 {
                        x |= !((1usize << size*8)-1);
                    }
                    format_integer(x, size, signed, v.flags, out, palette);
                }
            }
            Ok(_) => styled_write!(out, palette.value_error, "<bad size: {}>", size),
            Err(e) => styled_write!(out, palette.value_error, "<{}>", e),
        }
        Type::Pointer(p) => match value.get_usize() {
            Ok(x) => if p.flags.contains(PointerFlags::REFERENCE) {
                write_address(x, out);
                return format_value_recurse(&Value {val: AddrOrValueBlob::Addr(x), type_: p.type_, flags: v.flags.inherit()}, expanded, state, context, arena, out, palette, text_start, true);
            } else {
                styled_write!(out, palette.value, "*0x{:x} ", x);
                if x == 0 {
                    return (false, children);
                }
                if !expanded {
                    return (true, children);
                }
                if !try_format_as_string(Some(x), None, p.type_, None, false, v.flags, context.memory, "", out, palette) {
                    // If expanded, act like a reference, i.e. expand the pointee.
                    (_, children) = format_value_recurse(&Value {val: AddrOrValueBlob::Addr(x), type_: p.type_, flags: v.flags.inherit()}, true, state, context, arena, out, palette, text_start, true);
                }
                return (true, children);
            }
            Err(e) => styled_write!(out, palette.value_error, "<{}>", e),
        }
        Type::Array(a) => {
            // TODO: Print as string if element is char. Hexdump (0x"1a74673bc67f") if element is 1-byte and HEX value flag is set.
            let inner_type = unsafe {&*a.type_};
            let inner_size = inner_type.calculate_size();
            let stride = if a.stride != 0 { a.stride } else { inner_size };
            let value_ref = &value;
            let get_val = |i: usize| -> Result<Value> {
                let start = i * stride;
                let end = start + inner_size;
                if end > size {
                    return err!(Dwarf, "byte range out of bounds: {} > {}", end, size);
                }
                let elem = match value.bit_range(start * 8, inner_size * 8) {
                    Ok(v) => v,
                    Err(_) => return err!(TooLong, ""),
                };
                Ok(Value {val: AddrOrValueBlob::Blob(elem), type_: inner_type, flags: v.flags.inherit()})
            };
            let len = if a.flags.contains(ArrayFlags::LEN_KNOWN) { a.len } else { 1 };
            if expanded {
                for i in 0..len {
                    if i > 1000 {
                        children.push(("…", i, err!(TooLong, "{} more elements", len - i)));
                        break;
                    }
                    let v = get_val(i);
                    let err = v.is_err();
                    let mut w = arena.write();
                    write!(w, "[{}]", i).unwrap();
                    children.push((unsafe {mem::transmute(w.finish())}, i, v));
                    if err {
                        break;
                    }
                }
                if a.flags.contains(ArrayFlags::LEN_KNOWN) {
                    styled_write!(out, palette.value_misc_dim, "length ");
                    styled_write!(out, palette.value_misc, "{}", len);
                } else {
                    styled_write!(out, palette.value_misc, "length unknown");
                }
                try_format_as_string(v.val.addr(), Some(&value), a.type_, if a.flags.contains(ArrayFlags::LEN_KNOWN) {Some(len)} else {None}, a.flags.contains(ArrayFlags::UTF_STRING), v.flags, context.memory, ", ", out, palette);
            } else {
                if !try_format_as_string(v.val.addr(), Some(&value), a.type_, if a.flags.contains(ArrayFlags::LEN_KNOWN) {Some(len)} else {None}, a.flags.contains(ArrayFlags::UTF_STRING), v.flags, context.memory, "", out, palette) {
                    styled_write!(out, palette.value_misc_dim, "[");
                    for i in 0..len {
                        if i != 0 {
                            styled_write!(out, palette.value_misc_dim, ", ");
                        }
                        if over_output_limit(out, text_start) {
                            styled_write!(out, palette.value_warning, "…");
                            break;
                        }
                        match get_val(i) {
                            Ok(v) => {
                                format_value_recurse(&v, false, state, context, arena, out, palette, text_start, false);
                            }
                            Err(e) if e.is_too_long() => styled_write!(out, palette.value_warning, "…"),
                            Err(e) => {
                                styled_write!(out, palette.value_error, "<{}>", e);
                                break;
                            }
                        }
                    }
                    if !a.flags.contains(ArrayFlags::LEN_KNOWN) {
                        styled_write!(out, palette.value_misc_dim, ", <length unknown>");
                    }
                    styled_write!(out, palette.value_misc_dim, "]");
                }
                return (len != 0, children);
            }
        }
        Type::Struct(s) => {
            let value = if value.capacity() >= size {
                AddrOrValueBlob::Blob(value)
            } else {
                assert!(v.val.addr().is_some());
                v.val.clone()
            };
            children = list_struct_children(&value, s, v.flags, state, context);
            if v.flags.contains(ValueFlags::SHOW_TYPE_NAME) || (expanded && (!t.name.is_empty() || t.die.0 != 0)) {
                if t.name.is_empty() {
                    // TODO: Print file+line instead of DIE offset.
                    styled_write!(out, palette.type_name, "<{} @{:x}> ", t.t.kind_name(), t.die.0);
                } else {
                    styled_write!(out, palette.type_name, "{} ", t.name);
                }
            }
            if !expanded {
                styled_write!(out, palette.value_misc_dim, "{{");
                for (idx, (name, _, value)) in children.iter().enumerate() {
                    if idx != 0 {
                        styled_write!(out, palette.value_misc_dim, ", ");
                    }

                    let style = if name.starts_with('#') {palette.value_misc_dim} else {palette.value_field_name};
                    styled_write!(out, style, "{}", name);
                    styled_write!(out, palette.value_misc_dim, ": ");

                    match value {
                        Ok(v) => {
                            format_value_recurse(v, false, state, context, arena, out, palette, text_start, false);
                        }
                        Err(e) => styled_write!(out, palette.value_error, "<{}>", e),
                    }
                }
                if children.is_empty() && t.flags.contains(TypeFlags::DECLARATION) {
                    // This can happen e.g. if the file with definition was compiled without debug symbols.
                    styled_write!(out, palette.value_error, "<missing type definition>");
                }
                styled_write!(out, palette.value_misc_dim, "}}");
            }
        }
        Type::Enum(e) => match value.get_usize() {
            Ok(mut x) => {
                let et = unsafe {&*e.type_};
                let (mut size, signed) = match &et.t {
                    Type::Primitive(p) => (et.size, p.contains(PrimitiveFlags::SIGNED)),
                    _ => (8, false),
                };
                if size != 1 && size != 2 && size != 4 && size != 8 {
                    size = 8;
                }
                // Sign-extend (for matching with enumerand values below).
                if signed && size < 8 && x & 1 << (size*8-1) as u32 != 0 {
                    x |= !((1usize << size*8)-1);
                }
                format_integer(x, size, signed, v.flags, out, palette);
                if !v.flags.intersects(ValueFlags::RAW | ValueFlags::HEX | ValueFlags::BIN) {
                    styled_write!(out, palette.value_misc_dim, " (");
                    let mut found = false;
                    for enumerand in e.enumerands {
                        if enumerand.value == x && !enumerand.name.is_empty() {
                            styled_write!(out, palette.value_field_name, "{}", enumerand.name);
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        styled_write!(out, palette.value_error, "?");
                    }
                    styled_write!(out, palette.value_misc_dim, ")");
                }
            }
            Err(e) => styled_write!(out, palette.value_error, "<{}>", e),
        }
        Type::MetaType | Type::MetaField => {
            let val = reflect_meta_value(v, state, context, Some((out, palette)));
            children = list_struct_children(&val.val, unsafe {(*val.type_).t.as_struct().unwrap()}, val.flags, state, context);
        }
    }
    (!children.is_empty(), children)
}

// x0 must be already sign-extended to 8 bytes if signed.
fn format_integer(x0: usize, size: usize, signed: bool, flags: ValueFlags, out: &mut StyledText, palette: &Palette) {
    assert!(size > 0 && size <= 8);
    let mut x = x0;
    if size < 8 {
        x &= (1 << (size*8) as usize) - 1;
    }
    if flags.contains(ValueFlags::HEX) {
        styled_write!(out, palette.value, "0x{:x}", x);
    } else if flags.contains(ValueFlags::BIN) {
        styled_write!(out, palette.value, "0b{:b}", x);
    } else if !signed {
        styled_write!(out, palette.value, "{}", x);
    } else {
        let x: isize = unsafe {mem::transmute(x0)};
        styled_write!(out, palette.value, "{}", x);
    }
}

fn try_format_as_string(addr: Option<usize>, preread_blob: Option<&ValueBlob>, element_type: *const TypeInfo, len: Option<usize>, marked_as_string: bool, flags: ValueFlags, memory: &MemReader, prefix: &str, out: &mut StyledText, palette: &Palette) -> bool {
    if flags.contains(ValueFlags::RAW) {
        return false;
    }
    let element_type = unsafe {&*element_type};
    let p = match &element_type.t {
        Type::Primitive(p) => p,
        _ => return false,
    };
    if element_type.calculate_size() != 1 {
        // Support for utf16 or utf32 would go somewhere around here, if we were to add it.
        return false;
    }
    if len.is_none() && !p.contains(PrimitiveFlags::AMBIGUOUS_CHAR) {
        return false;
    }
    if !marked_as_string && !p.contains(PrimitiveFlags::CHAR) && !flags.contains(ValueFlags::HEX) {
        return false;
    }
    let limit = 1usize << 16;
    let mut temp_storage: Vec<u8>;
    let mut terminated = true;
    let (len, slice) = match len {
        Some(len) => match preread_blob {
            Some(b) => (len, b.as_slice()),
            None => {
                temp_storage = vec![0; len.min(limit)];
                match memory.read(addr.unwrap(), &mut temp_storage) {
                    Ok(()) => (),
                    Err(e) => {
                        styled_write!(out, palette.value_error, "<{}>", e);
                        return true;
                    }
                }
                (len, &temp_storage[..])
            }
        }
        None => {
            let mut addr = match addr {
                Some(x) => x,
                None => return false,
            };
            let page_size = 1usize << 12;
            let mut chunk_size = 1usize << 7;
            let mut res: Vec<u8> = Vec::new();
            terminated = false;
            while res.len() < limit {
                let n = (addr & !(chunk_size - 1)) + chunk_size - addr;
                let start = res.len();
                res.resize(start + n, 0);
                // We assume that each aligned 4 KiB range is either fully readable or fully unreadable.
                match memory.read(addr, &mut res[start..]) {
                    Ok(()) => (),
                    Err(e) => {
                        styled_write!(out, palette.value_misc_dim, "{}", prefix);
                        styled_write!(out, palette.value_error, "bad C string: <{}>", e);
                        return true;
                    }
                }
                if let Some(i) = res[start..].iter().position(|c| *c == 0) {
                    res.truncate(start + i);
                    terminated = true;
                    break;
                }
                addr += n;
                if n == chunk_size && chunk_size < page_size {
                    chunk_size <<= 1;
                }
            }
            temp_storage = res;
            (temp_storage.len(), &temp_storage[..])
        }
    };
    let slice = &slice[..slice.len().min(len).min(limit)];
    styled_write!(out, palette.value_misc_dim, "{}", prefix);
    if flags.contains(ValueFlags::HEX) {
        styled_write!(out, palette.value_misc_dim, "0x\"");
        for x in slice {
            write!(out.chars, "{:02x}", x).unwrap();
        }
        out.close_span(palette.value);
    } else {
        styled_write!(out, palette.value_misc_dim, "\"");
        if let Ok(s) = std::str::from_utf8(slice) {
            styled_write!(out, palette.value, "{}", s);
        } else {
            for &x in slice {
                if x >= 32 && x <= 126 {
                    write!(out.chars, "{}", x as char).unwrap();
                } else {
                    write!(out.chars, "\\x{:02x}", x).unwrap();
                }
            }
            out.close_span(palette.value);
        }
    }
    styled_write!(out, palette.value_misc_dim, "\"");
    if !terminated {
        styled_write!(out, palette.value_warning, "…");
    } else if slice.len() != len {
        styled_write!(out, palette.value_warning, "… {} more bytes", len - slice.len());
    }
    true
}

pub fn get_struct_field(val: &AddrOrValueBlob, field: &StructField, memory: &MemReader) -> Result<AddrOrValueBlob> {
    let mut type_bytes = unsafe {(*field.type_).calculate_size()};
    let field_bits = field.calculate_bit_size();
    if field_bits == 0 {
        return Ok(AddrOrValueBlob::Blob(ValueBlob::new(0)));
    }
    if type_bytes == 0 {
        type_bytes = (field_bits + 7)/8;
    }
    let mut blob = match val {
        AddrOrValueBlob::Addr(addr) => {
            if type_bytes * 8 == field_bits && field.bit_offset % 8 == 0 {
                return Ok(AddrOrValueBlob::Addr(addr + field.bit_offset/8));
            }
            if field_bits > 1 << 30 {
                return err!(Sanity, "field {} is suspiciously big: {} bits", field.name, field_bits);
            }
            let start_byte = field.bit_offset/8;
            let end = field.bit_offset + field_bits;
            let blob = AddrOrValueBlob::Addr(addr + start_byte).into_value((end - start_byte*8 + 7)/8, memory)?;
            blob.bit_range(field.bit_offset - start_byte*8, field_bits).unwrap()
        }
        AddrOrValueBlob::Blob(blob) => match blob.bit_range(field.bit_offset, field_bits) {
            Ok(x) => x,
            Err(_) => return err!(Dwarf, "field {} bit range out of bounds: {}+{} vs {}*8", field.name, field.bit_offset, field_bits, blob.capacity()),
        }
    };
    blob.resize(type_bytes);
    Ok(AddrOrValueBlob::Blob(blob))
}

// Information needed for evaluating DWARF expressions.
pub struct DwarfEvalContext<'a> {
    // Process.
    pub memory: &'a MemReader,

    // Binary.
    pub symbols: Option<&'a Symbols>,
    pub addr_map: &'a AddrMap,

    // Unit.
    pub encoding: Encoding,
    pub unit: Option<&'a CompilationUnit>,

    // Stack frame. Not required for global variables.
    pub regs: Option<&'a Registers>,
    pub frame_base: &'a Result<(usize, /*dubious*/ bool)>,
}

pub fn eval_dwarf_expression(expression: Expression<SliceType>, context: &DwarfEvalContext) -> Result<(AddrOrValueBlob, /*dubious*/ bool)> {
    let mut eval = expression.evaluation(context.encoding);
    let mut result = eval.evaluate()?;
    let mut dubious = false;
    loop {
        result = match &result {
            EvaluationResult::Complete => break,
            EvaluationResult::RequiresMemory {/* dynamic (?) */ address, size, space, base_type} => {
                if space.is_some() { return err!(Dwarf, "unexpected address space"); }
                if *size > 8 { return err!(Dwarf, "unexpectedly big memory read"); }
                let value_type = if base_type.0 == 0 {
                    ValueType::Generic
                } else if let (&Some(s), &Some(u)) = (&context.symbols, &context.unit) {
                    s.find_base_type(base_type.to_debug_info_offset(&u.unit.header).unwrap())?
                } else {
                    return err!(Dwarf, "can't look up base type (memory) without symbols");
                };
                let mut place = [0u8; 8];
                let slice = &mut place[..*size as usize];
                context.memory.read(*address as usize, slice)?;
                let val = match value_type {
                    ValueType::Generic => gimli::Value::Generic(u64::from_le_bytes(place)),
                    _ => gimli::Value::parse(value_type, EndianSlice::new(slice, LittleEndian::default()))? };
                eval.resume_with_memory(val)
            }
            EvaluationResult::RequiresRegister {register, base_type} => {
                let value_type = if base_type.0 == 0 {
                    ValueType::Generic
                } else if let (&Some(s), &Some(u)) = (&context.symbols, &context.unit) {
                    s.find_base_type(base_type.to_debug_info_offset(&u.unit.header).unwrap())?
                } else {
                    return err!(Dwarf, "can't look up base type (register) without symbols");
                };
                let reg = RegisterIdx::from_dwarf(*register).ok_or_else(|| error!(Dwarf, "unsupported register in expression: {:?}", register))?;
                let regs = match &context.regs { Some(r) => r, None => return err!(Dwarf, "register op unexpected") };
                let (reg_val, dub) = regs.get_int(reg)?;
                dubious |= dub;
                let val = match value_type {
                    ValueType::Generic => gimli::Value::Generic(reg_val),
                    _ => gimli::Value::parse(value_type, EndianSlice::new(&reg_val.to_le_bytes(), LittleEndian::default()))? };
                eval.resume_with_register(val)
            }
            EvaluationResult::RequiresFrameBase => {
                let (v, dub) = context.frame_base.clone()?;
                dubious |= dub;
                eval.resume_with_frame_base(v as u64)
            }
            EvaluationResult::RequiresCallFrameCfa => {
                let regs = match &context.regs { Some(r) => r, None => return err!(Dwarf, "cfa op unexpected") };
                let (cfa, dub) = regs.get_int(RegisterIdx::Cfa)?;
                dubious |= dub;
                eval.resume_with_call_frame_cfa(cfa)
            }
            EvaluationResult::RequiresAtLocation(reference) => {
                let symbols = match &context.symbols { None => return err!(Dwarf, "call op unexpected"), &Some(s) => s };
                let (unit, offset) = match reference {
                    DieReference::UnitRef(offset) =>
                        (match &context.unit {
                            None => return err!(Dwarf, "unit call op unexpected"),
                            Some(u) => &u.unit },
                         *offset),
                    DieReference::DebugInfoRef(offset) => {
                        let u = symbols.find_unit(*offset)?;
                        let unit_offset = match offset.to_unit_offset(&u.unit.header) { None => return err!(Dwarf, "DWARF call offset out of bounds"), Some(o) => o };
                        (&u.unit, unit_offset)
                    }
                };
                let die = unit.entry(offset)?;
                let attr = die.attr_value(DW_AT_location)?;
                let slice = match attr {
                    // It seems weird to ignore missing attribute, but it's what the DWARF spec says:
                    // "If there is no such attribute, then there is no effect."
                    None => EndianSlice::default(),
                    Some(a) => match a.exprloc_value() {
                        // I guess it's in principle allowed to be a location list, in which we'll have to
                        // look up the current instruction pointer, but I hope compilers don't output that.
                        None => return err!(Dwarf, "DW_OP_call target form unexpected: {:?}", a),
                        Some(Expression(s)) => s,
                    }
                };
                eval.resume_with_at_location(slice)
            }
            EvaluationResult::RequiresRelocatedAddress(static_addr) => {
                let addr = context.addr_map.static_to_dynamic(*static_addr as usize) as u64;
                eval.resume_with_relocated_address(addr)
            }
            EvaluationResult::RequiresIndexedAddress {index, relocate} => {
                let (symbols, unit) = match (&context.symbols, &context.unit) { (&Some(s), &Some(u)) => (s, u), _ => return err!(Dwarf, "indexed addr op unexpected") };
                let mut addr = symbols.dwarf.address(&unit.unit, *index)?;
                if *relocate {
                    addr = context.addr_map.static_to_dynamic(addr as usize) as u64;
                }
                eval.resume_with_indexed_address(addr)
            }
            EvaluationResult::RequiresBaseType(unit_offset) => {
                let (symbols, unit) = match (&context.symbols, &context.unit) { (&Some(s), &Some(u)) => (s, u), _ => return err!(Dwarf, "base type op unexpected") };
                let offset = unit_offset.to_debug_info_offset(&unit.unit.header).unwrap();
                let t = symbols.find_base_type(offset)?;
                eval.resume_with_base_type(t)
            }
            
            EvaluationResult::RequiresTls(_) => return err!(NotImplemented, "TLS is not supported"),

            // These are just alternative polite ways for the compiler to say "optimized out".
            EvaluationResult::RequiresEntryValue(_) => return err!(OptimizedAway, "requires entry value"),
            EvaluationResult::RequiresParameterRef(_) => return err!(OptimizedAway, "requires parameter ref"),
        }?;
    }
    let pieces = eval.result();
    let num_pieces = pieces.len();
    let mut res = ValueBlob::new(0);
    let mut res_bits = 0;
    let one_piece = pieces.len() == 1; // nya
    for piece in pieces {
        let mut blob_bytes = 8;
        let val = match piece.location {
            Location::Empty => return err!(OptimizedAway, "optimized away"),
            Location::Value{value: v} => AddrOrValueBlob::Blob(ValueBlob::new(match v {
                gimli::read::Value::F32(x) => unsafe {mem::transmute::<f32, u32>(x) as usize},
                gimli::read::Value::F64(x) => unsafe {mem::transmute(x)},
                _ => v.to_u64(!0)? as usize })),
            Location::Bytes{value: b} => {
                blob_bytes = b.len();
                AddrOrValueBlob::Blob(ValueBlob::from_slice(b.slice()))
            }
            Location::Register{register: reg} => {
                let reg = match RegisterIdx::from_dwarf(reg) {
                    None => return err!(NotImplemented, "unsupported register: {:?}", reg),
                    Some(r) => r,
                };
                let regs = match &context.regs { Some(r) => r, None => return err!(Dwarf, "register location unexpected") };
                match regs.get_int(reg) {
                    Err(_) => return err!(Dwarf, "register {} optimized away", reg),
                    Ok((v, dub)) => {
                        dubious |= dub;
                        AddrOrValueBlob::Blob(ValueBlob::new(v as usize))
                    }
                }
            }
            Location::Address{address: addr} => {
                blob_bytes = (piece.size_in_bits.unwrap_or(64) as usize + 7) / 8;
                AddrOrValueBlob::Addr(addr as usize)
            }
            Location::ImplicitPointer{..} => return err!(Dwarf, "implicit pointer"),
        };

        let bit_offset = piece.bit_offset.unwrap_or(0) as usize;
        let size_in_bits = piece.size_in_bits.unwrap_or((blob_bytes * 8).saturating_sub(bit_offset) as u64) as usize;
        if size_in_bits == 0 { return err!(Dwarf, "empty piece"); }
        if one_piece && bit_offset == 0 && size_in_bits == blob_bytes * 8 {
            // Most common case - one piece of normal size.
            return Ok((val, dubious));
        }

        let val = val.into_value((size_in_bits + bit_offset + 7) / 8, context.memory)?;
        res.append_bits(res_bits, val, size_in_bits, bit_offset);
        res_bits += size_in_bits;
    }
    Ok((AddrOrValueBlob::Blob(res), dubious))
}

// Utility for creating struct type+value at runtime. Used by pretty printers.
#[derive(Default)]
pub struct StructBuilder {
    pub value_blob: Vec<u8>,
    pub fields: Vec<StructField>,
}
impl StructBuilder {
    pub fn add_blob_field(&mut self, name: &'static str, value: &[u8], type_: *const TypeInfo) {
        let prev_len = self.value_blob.len();
        self.value_blob.extend_from_slice(value);
        self.fields.push(StructField {name, bit_offset: prev_len*8, bit_size: (self.value_blob.len() - prev_len)*8, flags: FieldFlags::empty(), type_});
    }
    pub fn add_field(&mut self, name: &'static str, value: Value) {
        let size = unsafe {(*value.type_).calculate_size()};
        let blob = value.val.blob_ref().unwrap().as_slice();
        assert!(size <= blob.len());
        self.add_blob_field(name, &blob[..size], value.type_);
    }

    pub fn add_usize_field(&mut self, name: &'static str, value: usize, type_: *const TypeInfo) {
        self.add_blob_field(name, &value.to_le_bytes(), type_);
    }
    pub fn add_str_field(&mut self, name: &'static str, value: &str, types: &mut Types, builtin_types: &BuiltinTypes) {
        let array_type = types.add_array(builtin_types.char8, value.len(), ArrayFlags::UTF_STRING);
        self.add_blob_field(name, value.as_bytes(), array_type);
    }

    pub fn finish(mut self, name: &'static str, flags: ValueFlags, types: &mut Types) -> Value {
        let fields_slice = types.fields_arena.add_slice(&self.fields);
        let struct_type = StructType {flags: StructFlags::empty(), fields_ptr: fields_slice.as_ptr(), fields_len: fields_slice.len()};
        let type_ = TypeInfo {name, size: self.value_blob.len(), die: DebugInfoOffset(0), flags: TypeFlags::SIZE_KNOWN, t: Type::Struct(struct_type)};
        let type_ = types.types_arena.add(type_);
        let val = AddrOrValueBlob::Blob(ValueBlob::from_vec(mem::take(&mut self.value_blob)));
        Value {val, type_, flags}
    }
}

#[cfg(test)]
mod tests {
    use crate::expr::*;

    // Slow but caught bugs.
    #[test]
    fn value_blob_nonsense_slow() {
        let lens = [0usize, 1, 3, 5, 7, 8, 9, 13, 15, 16, 17, 23, 24, 25, 25, 28, 31, 32, 33, 34, 35, 38, 39, 40, 41, 47];
        for &bits1 in &lens {
            for &bits2 in &lens {
                for pos1 in 0..bits1 {
                    for pos2 in 0..bits2 {
                        for off in 0..pos2+1 {
                            let mut a = ValueBlob::with_capacity((bits1+7)/8);
                            let mut b = ValueBlob::with_capacity((bits2+7)/8);
                            a.as_mut_slice()[pos1/8] |= 1 << (pos1 & 7) as u32;
                            b.as_mut_slice()[pos2/8] |= 1 << (pos2 & 7) as u32;
                            a.append_bits(bits1, b, bits2 - off, off);
                            let s = a.as_slice();
                            assert!(s.len() * 8 >= bits1 + bits2 - off);
                            for i in 0..s.len()*8 {
                                let bit = s[i/8] & (1 << (i&7) as u32) != 0;
                                assert_eq!(bit, i == pos1 || i == pos2 - off + bits1);
                            }
                        }
                    }
                }
            }
        }
    }
}
