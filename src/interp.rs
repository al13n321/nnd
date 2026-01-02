use crate::{*, types::*, expr::*, error::*, procfs::*, pretty::*, registers::*};
use std::{ops::Range, mem, borrow::Cow, fmt::Write as fmtWrite};

pub struct Expression {
    ast: Vec<ASTNode>,
    root: ASTIdx,
}
impl Expression {
    pub fn is_trivial_false(&self) -> bool {
        match &self.ast[self.root.0].a {
            AST::Literal(LiteralValue::Basic(BasicValue::U(0))) => true,
            _ => false,
        }
    }
}

pub fn parse_watch_expression(s: &str) -> Result<Expression> {
    let mut lex = Lexer {input: InputStream {input: s, pos: 0}, next_tokens: Vec::new(), previous_token_end: 0, previous_dot: false};
    let mut expr = Expression {ast: Vec::new(), root: ASTIdx(0)};
    let root = parse_expression(&mut lex, &mut expr, Precedence::Weakest)?;
    // TODO: Allow format specifiers at the end of expression, e.g. ", x", ", rx" - more conveinent than .#x because no need for parens. Syntax seems unambiguous even in full Rust?
    expr.root = root;
    let (r, t) = lex.peek(1)?;
    if !t.is_eof() {
        return err!(Syntax, "unexpected {:?} after expression at {}", t, r.start);
    }
    Ok(expr)
}

pub fn eval_watch_expression(expr_str: &str, state: &mut EvalState, context: &mut EvalContext) -> Result<(Value, /*dubious*/ bool)> {
    let expr = parse_watch_expression(expr_str)?;
    eval_parsed_expression(&expr, state, context)
}

pub fn eval_parsed_expression(expr: &Expression, state: &mut EvalState, context: &mut EvalContext) -> Result<(Value, /*dubious*/ bool)> {
    state.currently_evaluated_value_dubious = false;
    Ok((eval_expression(expr, expr.root, state, context, false)?, state.currently_evaluated_value_dubious))
}

// Make expression suitable for appending things like "[5]" or ".foo" to it. Used when adding a watch from a node in value tree.
// I.e. surround it with parentheses if needed, replace assignment with just the variable name.
pub fn adjust_expression_for_appending_child_path(expr_str: &str) -> Result<String> {
    let expr = parse_watch_expression(expr_str)?;
    let node = &expr.ast[expr.root.0];
    let parentheses = match &node.a {
        // These don't need parentheses.
        AST::Literal(_) | AST::Variable {..} | AST::Field {..} | AST::Array | AST::Tuple | AST::StructExpression(_) | AST::TupleIndexing(_) | AST::Call(_) | AST::Block | AST::TypeInfo => false,
        AST::BinaryOperator(BinaryOperator::Index) | AST::BinaryOperator(BinaryOperator::Slicify) => false,
        // These are unexpected at top level of a watch expression.
        AST::Type {..} | AST::PointerType | AST::ArrayType(_) | AST::Continue | AST::Break | AST::Return => false,

        // For variable assignment, just use the variable name.
        AST::BinaryOperator(BinaryOperator::Assign) => {
            if let AST::Variable {name, quoted, from_any_frame} = &expr.ast[node.children[0].0].a {
                if !quoted && !from_any_frame {
                    return Ok(name.clone());
                }
            }
            true
        }

        // These need parentheses.
        AST::UnaryOperator(_) | AST::BinaryOperator(_) | AST::TypeCast | AST::While | AST::For(_) | AST::If | AST::Let {..} | AST::FunctionDefinition {..} | AST::StructDefinition {..} => true,
    };
    if parentheses {
        Ok(format!("({})", expr_str))
    } else {
        Ok(expr_str.to_string())
    }
}

pub fn make_expression_for_variable(name: &str) -> String {
    if RegisterIdx::parse_ignore_case(name).is_some() || should_quote_identifier(name) {
        format!("`{}`", name)
    } else {
        name.to_string()
    }
}

pub fn does_expression_need_full_stack(expr: &Expression) -> bool {
    for node in &expr.ast {
        match &node.a {
            &AST::Variable {from_any_frame, ..} if from_any_frame => return true,
            _ => (),
        }
    }
    false
}

fn should_quote_identifier(name: &str) -> bool {
    if name.is_empty() {
        return true;
    }
    for (i, c) in name.char_indices() {
        match c {
            'a'..='z' | 'A'..='Z' | '_' | '#' | '$' | ':' => (),
            '0'..='9' if i != 0 => (),
            _ => return true,
        }
    }
    false
}

pub fn print_type_in_watch_language_syntax(t: *const TypeInfo, out: &mut String, recursion_depth: usize) -> Result<()> {
    if recursion_depth > 100 {
        return err!(Sanity, "cyclic or very deeply nested pointer");
    }
    let t = unsafe {&*t};
    match &t.t {
        Type::Pointer(p) => {
            // (The language doesn't have syntax for references, so ignore PointerFlags::REFERENCE and turn references into pointers.)
            out.push_str("*");
            print_type_in_watch_language_syntax(p.type_, out, recursion_depth + 1)
        }
        Type::Function => {
            out.push_str("fn");
            Ok(())
        }
        Type::Array(a) => {
            if a.stride != 0 && a.stride != unsafe {(*a.type_).calculate_size()} {
                return err!(NotImplemented, "array has nonstandard stride");
            }
            let len = if a.flags.contains(ArrayFlags::LEN_KNOWN) {a.len} else {1};
            out.push_str("[");
            print_type_in_watch_language_syntax(a.type_, out, recursion_depth + 1)?;
            write!(out, "; {}]", len).unwrap();
            Ok(())
        }
        _ if t.name.is_empty() => err!(Internal, "type has no name"),
        _ => {
            if should_quote_identifier(t.name) {
                write!(out, "`{}`", t.name).unwrap();
            } else {
                out.push_str(t.name);
            }
            Ok(())
        }
    }
}

// Slow dumb interpreter that walks the AST directly.
// Maybe at some point we should redesign the expression language more carefully, based on usage experience and on
// sketching custom pretty printers for lots of types in an imaginary expression language. It would probably be
// statically typed and compile to bytecode, maybe even to machine code that can be injected into the debuggee.
// Maybe the AddrOrValueBlob discriminator and the ValueFlags would become part of TypeInfo instead of being a weird external extension of the type system.
// `only_type` is for typeof(), to allow getting type of variables that aren't available; for many operations it falls back to calculating values and
// may fail unnecessarily, but that seems ok as long as the important case of getting types of unavailable variable is supported.
fn eval_expression(expr: &Expression, node_idx: ASTIdx, state: &mut EvalState, context: &mut EvalContext, only_type: bool) -> Result<Value> {
    let node = &expr.ast[node_idx.0];
    match &node.a {
        AST::Literal(v) => {
            let type_ = match v {
                LiteralValue::Basic(b) => match b {
                    BasicValue::U(x) => state.builtin_types.u64_,
                    BasicValue::I(x) => state.builtin_types.i64_,
                    BasicValue::F(x) => state.builtin_types.f64_,
                }
                LiteralValue::Char(c) if c.is_ascii() => state.builtin_types.char8,
                LiteralValue::Char(c) => state.builtin_types.char32,
                LiteralValue::String(s) => state.types.add_array(state.builtin_types.char8, Some(s.len()), ArrayFlags::empty()),
            };
            Ok(Value {val: AddrOrValueBlob::Blob(v.as_blob()), type_, flags: ValueFlags::empty()})
        }
        AST::Variable {name, quoted, from_any_frame} => {
            if !quoted && !from_any_frame {
                if let Some(v) = state.variables.get(name) {
                    return Ok(v.clone());
                }
            }
            state.get_variable(context, name, /*maybe_register*/ !*quoted, *from_any_frame, only_type, /*meta*/ false)
        }
        AST::Field {name, quoted} => {
            let mut val = eval_expression(expr, node.children[0], state, context, false)?; // disable only_type here so that pretty-printers don't have to support it
            if !quoted {
                let mut found = true;
                match name.as_str() {
                    "#r" => {
                        if val.flags.contains(ValueFlags::PRETTY) {
                            val.flags.remove(ValueFlags::PRETTY);
                        } else {
                            val.flags.insert(ValueFlags::RAW);
                        }
                    }
                    "#p" => {
                        if val.flags.contains(ValueFlags::RAW) {
                            val.flags.remove(ValueFlags::RAW);
                        } else {
                            val.flags.insert(ValueFlags::PRETTY);
                        }
                    }
                    "#x" => val.flags.insert(ValueFlags::HEX),
                    "#b" => val.flags.insert(ValueFlags::BIN),
                    "#be" => val.flags.insert(ValueFlags::BIG_ENDIAN),
                    "#le" => val.flags.remove(ValueFlags::BIG_ENDIAN),
                    _ => found = false,
                }
                if found {
                    return Ok(val);
                }
            }
            let mut values_to_check: Vec<Value> = Vec::new();
            follow_references_and_prettify(&mut val, Some(&mut values_to_check), /*pointers_too*/ true, state, context)?;
            // Look for the field in `val`, then in `additional_values` in reverse order (from inner to outer).
            values_to_check.push(val);
            let mut value_has_fields_at_all = false;
            for val in values_to_check.iter().rev() {
                let type_ = unsafe {&*val.type_};
                return match &type_.t {
                    Type::Struct(s) => {
                        value_has_fields_at_all = true;
                        let field_idx = match s.fields().iter().position(|f| f.name == name) {
                            Some(x) => x,
                            None => continue,
                        };
                        let field = &s.fields()[field_idx];
                        let v = get_struct_field(&val.val, field, &mut context.memory)?;
                        // Should the field inherit flags from the struct? E.g. should `foo.#r._M_begin` be printed as raw?
                        // Unclear, but this should be kept consistent between expression evaluation and value printing (format_value()).
                        // Currently we inherit.
                        Ok(Value {val: v, type_: field.type_, flags: val.flags.inherit()})
                    }
                    Type::Slice(s) if !quoted => {
                        value_has_fields_at_all = true;
                        match name.as_str() {
                            "#len" => {
                                let len = val.val.bit_range(64..128, &mut context.memory)?;
                                Ok(Value {val: AddrOrValueBlob::Blob(ValueBlob::new(len)), type_: state.builtin_types.u64_, flags: ValueFlags::empty()})
                            }
                            _ => continue,
                        }
                    }
                    Type::Array(a) if !quoted => {
                        value_has_fields_at_all = true;
                        match name.as_str() {
                            "#len" => {
                                if !a.flags.contains(ArrayFlags::LEN_KNOWN) {
                                    return err!(TypeMismatch, "can't take length of unsized array");
                                }
                                Ok(Value {val: AddrOrValueBlob::Blob(ValueBlob::new(a.len)), type_: state.builtin_types.u64_, flags: ValueFlags::empty()})
                            }
                            _ => continue,
                        }
                    }
                    _ => continue,
                }
            }
            return if value_has_fields_at_all {
                err!(TypeMismatch, "field {} not found", name)
            } else {
                err!(TypeMismatch, "trying to get field of {}", unsafe {&*values_to_check.last().unwrap().type_}.t.kind_name())
            }
        }
        &AST::TupleIndexing(field_idx) => {
            let mut val = eval_expression(expr, node.children[0], state, context, false)?;
            follow_references_and_prettify(&mut val, None, /*pointers_too*/ true, state, context)?;
            let type_ = unsafe {&*val.type_};
            match &type_.t {
                Type::Struct(s) => {
                    if field_idx >= s.fields().len() {
                        return err!(TypeMismatch, "field index our of range: {} >= {}", field_idx, s.fields().len());
                    }
                    let field = &s.fields()[field_idx];
                    let v = get_struct_field(&val.val, field, &mut context.memory)?;
                    Ok(Value {val: v, type_: field.type_, flags: val.flags.inherit()})
                }
                _ => return err!(TypeMismatch, "trying to get field of {}", type_.t.kind_name()),
            }
        }
        AST::UnaryOperator(UnaryOperator::Borrow) => {
            let mut val = eval_expression(expr, node.children[0], state, context, only_type)?;
            let type_ = unsafe {&*val.type_};
            match &type_.t {
                Type::Pointer(p) if p.flags.contains(PointerFlags::REFERENCE) => {
                    val.type_ = state.types.add_pointer(p.type_, p.flags.difference(PointerFlags::REFERENCE));
                }
                _ => {
                    val.type_ = state.types.add_pointer(val.type_, PointerFlags::empty());
                    if !only_type {
                        val.val = match val.val {
                            AddrOrValueBlob::Blob(_) => return err!(TypeMismatch, "can't take address of value"),
                            AddrOrValueBlob::Addr(a) => AddrOrValueBlob::Blob(ValueBlob::new(a)),
                        };
                    }
                }
            }
            Ok(val)
        }
        &AST::UnaryOperator(op) => {
            let mut val = eval_expression(expr, node.children[0], state, context, false)?;
            follow_references_and_prettify(&mut val, None, false, state, context)?;
            let type_ = unsafe {&*val.type_};
            match op {
                UnaryOperator::Dereference => match &type_.t {
                    Type::Pointer(p) => {
                        let addr = val.val.into_value(8, &mut context.memory)?.get_usize()?;
                        val.val = AddrOrValueBlob::Addr(addr);
                        val.type_ = p.type_;
                    }
                    _ => return err!(TypeMismatch, "can't dereference {}", type_.t.kind_name()),
                }
                UnaryOperator::Neg | UnaryOperator::Not => {
                    match &type_.t {
                        Type::Primitive(f) => {
                            if f.contains(PrimitiveFlags::UNSPECIFIED) { return err!(TypeMismatch, "can't negate void"); }
                            let size = type_.calculate_size();
                            if size > 8 || size == 0 {
                                return err!(TypeMismatch, "unexpected primitive value size: {} bytes", size);
                            }
                            let mut x = val.val.into_value(size, &mut context.memory)?.get_usize()?;
                            if f.contains(PrimitiveFlags::FLOAT) {
                                if op == UnaryOperator::Not { return err!(TypeMismatch, "can't bit-negate float"); }
                                match size {
                                    4 => x = f32::to_bits(-f32::from_bits(x as u32)) as usize,
                                    8 => x = f64::to_bits(-f64::from_bits(x as u64)) as usize,
                                    _ => return err!(Dwarf, "bad float size: {}", size),
                                }
                            } else if f.contains(PrimitiveFlags::BOOL) {
                                if op == UnaryOperator::Neg { return err!(TypeMismatch, "can't negate bool"); }
                                x ^= 1;
                            } else {
                                flip_endianness_if_needed(&mut x, size, val.flags);
                                // No need to sign-extend.
                                x = !x;
                                if op == UnaryOperator::Neg {
                                    x = x.wrapping_add(1);
                                    if !f.contains(PrimitiveFlags::SIGNED) {
                                        val.type_ = state.types.add_primitive("", size, f.union(PrimitiveFlags::SIGNED));
                                    }
                                }
                                x &= usize::MAX >> (64 - size as u32 * 8);
                            }
                            val.flags.remove(ValueFlags::BIG_ENDIAN);
                            val.val = AddrOrValueBlob::Blob(ValueBlob::new(x));
                        }
                        _ => return err!(TypeMismatch, "can't negate {}", type_.t.kind_name()),
                    }
                }
                UnaryOperator::Borrow => panic!("huh"),
            }
            Ok(val)
        }
        AST::TypeCast => {
            let mut val = eval_expression(expr, node.children[0], state, context, false)?;
            follow_references_and_prettify(&mut val, None, false, state, context)?;
            let type_ = eval_type(expr, node.children[1], state, context)?;
            let is_reinterpretable = |type_: *const TypeInfo, to: bool| -> bool {
                match unsafe {&(*type_).t} {
                    Type::Primitive(_) | Type::Pointer(_) | Type::PointerToMember(_) | Type::Struct(_) | Type::Enum(_) => true,
                    Type::Array(a) => a.flags.contains(ArrayFlags::LEN_KNOWN) || to,
                    Type::Slice(_) => !to,
                    _ => false,
                }
            };
            if !is_reinterpretable(val.type_, false) {
                return err!(TypeMismatch, "can't cast from {}", unsafe {(*val.type_).t.kind_name()});
            }
            if !is_reinterpretable(type_, true) {
                return err!(TypeMismatch, "can't cast to {}", unsafe {(*type_).t.kind_name()});
            }

            // Special casts for numeric types, e.g. int to float.
            match to_basic(&val, &mut context.memory, "cast") {
                Ok(b) => {
                    if let Some(v) = from_basic(b, type_)? {
                        val.val = v;
                        val.type_ = type_;
                        val.flags.remove(ValueFlags::BIG_ENDIAN); // to_basic converted it to little-endian
                        return Ok(val);
                    }
                }
                Err(e) if e.is_type_mismatch() => (),
                Err(e) => return Err(e),
            }

            // Reinterpret cast for everything else, e.g. array to struct (by value).
            // (Casting by value is useful when a value has no address, e.g. casting a simd register from [u64; 8] to [u32; 16].)
            // Currently we're extra permissive and allow casts even when sizes don't match, and even when the value is a reference (so could be cast through pointer instead);
            // if some of this turns out too error-prone in practice, we can add some constraints.
            let from_t = unsafe {&*val.type_};
            let (from_size, mut from_val) = match &from_t.t {
                Type::Slice(s) => {
                    // Cast slice as if it were an array. Useful for e.g. casting pretty-printed vectors to string (v as [char8]).
                    let slice_val = mem::take(&mut val.val).into_value(16, &mut context.memory)?;
                    let addr = slice_val.get_usize_at(0).unwrap();
                    let len = slice_val.get_usize_at(8).unwrap();
                    let inner_type = unsafe {&*s.type_};
                    let inner_size = inner_type.calculate_size();
                    (inner_size * len, AddrOrValueBlob::Addr(addr))
                }
                _ => {
                    (unsafe {(*val.type_).calculate_size()}, mem::take(&mut val.val))
                }
            };
            let t = unsafe {&*type_};
            match &t.t {
                Type::Array(a) if !a.flags.contains(ArrayFlags::LEN_KNOWN) => {
                    // Special cast to unsized array. Type of the result is a sized array of the ~same size as the left hand side.
                    // E.g. `ymm0 as [u8]` is the same as `ymm0 as [u8; 32]`.
                    let element_size = unsafe {(*a.type_).calculate_size()};
                    let n = from_size / element_size;
                    let sized_array = state.types.add_array(a.type_, Some(n), ArrayFlags::empty());
                    if let AddrOrValueBlob::Blob(blob) = &mut from_val {
                        blob.resize(n * element_size);
                    }
                    val.val = from_val;
                    val.type_ = sized_array;
                    return Ok(val);
                }
                _ => (),
            }
            let to_size = t.calculate_size();
            let v = match from_val {
                AddrOrValueBlob::Addr(addr) if to_size <= from_size => AddrOrValueBlob::Addr(addr),
                AddrOrValueBlob::Addr(addr) => AddrOrValueBlob::Blob(from_val.into_value(to_size, &mut context.memory)?),
                AddrOrValueBlob::Blob(mut blob) => {
                    blob.resize(to_size);
                    AddrOrValueBlob::Blob(blob)
                }
            };
            val.val = v;
            val.type_ = type_;
            Ok(val)
        }
        AST::TypeInfo => {
            let type_ = eval_type(expr, node.children[0], state, context)?;
            Ok(Value {val: AddrOrValueBlob::Blob(ValueBlob::new(type_ as usize)), type_: state.types.types_arena.add(TypeInfo {name: "type", size: 8, flags: TypeFlags::SIZE_KNOWN, t: Type::MetaType, ..Default::default()}), flags: ValueFlags::empty()})
        }
        &AST::BinaryOperator(op) if op == BinaryOperator::Assign => {
            match &expr.ast[node.children[0].0].a {
                AST::Variable {name, quoted, from_any_frame} if !quoted && !from_any_frame => {
                    if !state.variables.contains_key(&name[..]) {
                        // Check that there's no debuggee variable with this name.
                        match state.get_variable(context, name, /*maybe_register*/ !quoted, *from_any_frame, /*only_type*/ true, /*meta*/ false) {
                            Err(e) if e.is_no_variable() => (),
                            Err(e) => return Err(e),
                            Ok(_) => return err!(Runtime, "assigning to debuggee variables is not supported; to assign to a script variable use a different name (shadowing not allowed)"),
                        }
                    }
                    let mut val = eval_expression(expr, node.children[1], state, context, false)?;
                    if val.flags.contains(ValueFlags::PRETTY) {
                        follow_references_and_prettify(&mut val, None, /*pointers_too*/ false, state, context)?;
                    }
                    state.variables.insert(name.clone(), val.clone());
                    Ok(val)
                }
                AST::Variable {..} => return err!(NotImplemented, "assigning debuggee's variables is not supported"),
                AST::Field {..} => return err!(NotImplemented, "assigning to fields is not supported"),
                AST::TupleIndexing(_) => return err!(NotImplemented, "assigning to tuple elements is not supported"),
                _ => return err!(Syntax, "invalid assignment target"),
            }
        }
        &AST::BinaryOperator(op) => {
            let mut lhs = eval_expression(expr, node.children[0], state, context, false)?;
            follow_references_and_prettify(&mut lhs, None, false, state, context)?;
            match op { // short-circuiting
                BinaryOperator::LazyAnd | BinaryOperator::LazyOr => {
                    let mut x = to_basic(&lhs, &mut context.memory, "&&/||")?.cast_to_usize() != 0;
                    if x == (op == BinaryOperator::LazyAnd) {
                        // Not ideal that short-circuiting also skips typechecking.
                        let rhs = eval_expression(expr, node.children[1], state, context, false)?;
                        follow_references_and_prettify(&mut lhs, None, false, state, context)?;
                        x = to_basic(&rhs, &mut context.memory, "&&/||")?.cast_to_usize() != 0;
                    }
                    let type_ = state.builtin_types.bool_;
                    return Ok(Value {val: AddrOrValueBlob::Blob(ValueBlob::new(x as usize)), type_, flags: ValueFlags::empty()});
                }
                _ => (),
            }
            let mut rhs = eval_expression(expr, node.children[1], state, context, false)?;
            follow_references_and_prettify(&mut rhs, None, false, state, context)?;
            if op == BinaryOperator::Index || op == BinaryOperator::Slicify {
                let b = to_basic(&rhs, &mut context.memory, "index with")?;
                if b.is_f64() { return err!(TypeMismatch, "can't index with float"); }
                let idx = b.cast_to_usize();
                let t = unsafe {&*lhs.type_};
                return Ok(match &t.t {
                    Type::Pointer(p) => {
                        let idx = b.cast_to_isize();
                        let addr = lhs.val.into_value(8, &mut context.memory)?.get_usize()?;
                        let stride = unsafe {(*p.type_).calculate_size()} as isize;
                        if stride == 0 { return err!(TypeMismatch, "array element type has size 0"); }
                        let addr_offset = isize::checked_mul(idx, stride).flat_map(|res| isize::checked_add(addr as isize, res));
                        let addr_offset = match addr_offset {
                            Some(v) => v as usize,
                            None => return err!(Runtime, "array size or index is too big"),
                        };
                        if op == BinaryOperator::Index {
                            Value {val: AddrOrValueBlob::Addr(addr_offset), type_: p.type_, flags: lhs.flags.inherit()}
                        } else { // Slicify
                            if idx < 0 { return err!(Runtime, "negative slice length"); }
                            let array_type = state.types.add_array(p.type_, Some(idx as usize), ArrayFlags::empty());
                            Value {val: AddrOrValueBlob::Addr(addr), type_: array_type, flags: lhs.flags.inherit()}
                        }
                    }
                    Type::Array(a) if op == BinaryOperator::Index => {
                        if a.flags.contains(ArrayFlags::LEN_KNOWN) && idx >= a.len.max(1) { // allow accessing element 0 of 0-length arrays, just in case
                            return err!(Runtime, "array index out of range: {} >= {}", idx, a.len);
                        }
                        let stride = if a.stride == 0 {unsafe {(*a.type_).calculate_size()}} else {a.stride};
                        let val = match lhs.val {
                            AddrOrValueBlob::Addr(addr) => AddrOrValueBlob::Addr(addr + idx * stride),
                            AddrOrValueBlob::Blob(blob) => AddrOrValueBlob::Blob(blob.bit_range(idx * stride * 8, stride * 8)?),
                        };
                        Value {val, type_: a.type_, flags: lhs.flags.inherit()}
                    }
                    Type::Slice(s) if op == BinaryOperator::Index => {
                        let stride = unsafe {(*s.type_).calculate_size()};
                        let blob = lhs.val.into_value(16, &mut context.memory)?;
                        let addr = blob.get_usize_prefix();
                        let len = blob.get_usize_at(8)?;
                        if idx >= len.max(1) { // allow accessing element 0 of empty slice, as a way to get the data pointer
                            return err!(Runtime, "slice index out of range: {} >= {}", idx, len);
                        }
                        Value {val: AddrOrValueBlob::Addr(addr + idx * stride), type_: s.type_, flags: lhs.flags.inherit()}
                    }
                    _ => return err!(TypeMismatch, "can't {} {}", if op == BinaryOperator::Index {"index"} else {"slicify"}, t.t.kind_name()),
                });
            }
            if op == BinaryOperator::Range {
                let (t1, t2) = (unsafe {&*lhs.type_}, unsafe {&*rhs.type_});
                let (t1, t2) = match (t1.t.as_pointer(), t2.t.as_pointer()) {
                    (Some(t1), Some(t2)) => (t1.type_, t2.type_),
                    _ => return err!(NotImplemented, "range operator only supported for pointers"),
                };
                let (t1, t2) = (unsafe {&*t1}, unsafe {&*t2});
                let size = t1.calculate_size();
                if t2.calculate_size() != size {
                    return err!(TypeMismatch, "different types around '..'");
                }
                if size == 0 {
                    return err!(TypeMismatch, "range of size-0 types is not allowed");
                }
                let (addr1, addr2) = (lhs.val.into_value(8, &mut context.memory)?.get_usize()?, rhs.val.into_value(8, &mut context.memory)?.get_usize()?);
                if addr1 > addr2 {
                    return err!(Runtime, "range has negative length: 0x{:x} > 0x{:x}", addr1, addr2);
                }
                let len = addr2 - addr1;
                if len % size != 0 {
                    return err!(Runtime, "unaligned pointer difference");
                }
                let len = len / size;
                let array_type = state.types.add_array(t1, Some(len), ArrayFlags::empty());
                return Ok(Value {val: AddrOrValueBlob::Addr(addr1), type_: array_type, flags: ValueFlags::empty()});
            }

            // String comparison.
            match op {
                BinaryOperator::Eq | BinaryOperator::Ne | BinaryOperator::Gt | BinaryOperator::Lt | BinaryOperator::Ge | BinaryOperator::Le => {
                    let check = |t: *const TypeInfo| -> (/*is_byte_array*/ bool, /*is_c_string*/ bool) {
                        let (inner, len_known) = match unsafe {&(*t).t} {
                            Type::Pointer(p) => (p.type_, false),
                            Type::Array(a) => (a.type_, a.flags.contains(ArrayFlags::LEN_KNOWN)),
                            Type::Slice(s) => (s.type_, true),
                            _ => return (false, false),
                        };
                        let inner = unsafe {&*inner};
                        if inner.calculate_size() != 1 {
                            return (false, false);
                        }
                        if !len_known {
                            return match &inner.t {
                                Type::Primitive(p) if p.contains(PrimitiveFlags::AMBIGUOUS_CHAR) => (false, true),
                                _ => (false, false),
                            };
                        }
                        (true, false)
                    };
                    let (lhs_is_byte_array, lhs_is_c_string) = check(lhs.type_);
                    let (rhs_is_byte_array, rhs_is_c_string) = check(rhs.type_);
                    if lhs_is_byte_array || rhs_is_byte_array {
                        if !(lhs_is_byte_array || lhs_is_c_string) {
                            return err!(TypeMismatch, "can't compare {} to array", unsafe {(*lhs.type_).t.kind_name()});
                        }
                        if !(rhs_is_byte_array || rhs_is_c_string) {
                            return err!(TypeMismatch, "can't compare array to {}", unsafe {(*rhs.type_).t.kind_name()});
                        }

                        // Compare as byte arrays.
                        let as_blob = |mut val: Value, is_c_string: bool, memory: &mut CachedMemReader| -> Result<(ValueBlob, usize)> {
                            let t = unsafe {&*val.type_};
                            if is_c_string {
                                let addr = match &t.t {
                                    Type::Pointer(p) => val.val.bit_range(0..64, memory)?,
                                    Type::Array(a) => match val.val.addr() {
                                        Some(x) => x,
                                        None => return err!(TypeMismatch, "array length unknown"),
                                    }
                                    _ => panic!("huh"),
                                };
                                let (blob, terminated) = memory.read_null_terminated(addr, 1 << 20)?;
                                if !terminated {
                                    return err!(Sanity, "C string suspiciously long: more than {} bytes", blob.len());
                                }
                                let size = blob.len();
                                Ok((ValueBlob::from_vec(blob), size))
                            } else {
                                Ok(match &t.t {
                                    Type::Array(a) => (mem::take(&mut val.val).into_value(a.len, memory)?, a.len),
                                    Type::Slice(s) => {
                                        let addr = val.val.bit_range(0..64, memory)?;
                                        let size = val.val.bit_range(64..128, memory)?;
                                        if size > 100 << 20 {
                                            return err!(Sanity, "slice too long (over 100 MiB)");
                                        }
                                        let mut buf = vec![0u8; size];
                                        memory.read(addr, &mut buf)?;
                                        (ValueBlob::from_vec(buf), size)
                                    }
                                    _ => panic!("huh"),
                                })
                            }
                        };
                        let (lhs_blob, lhs_len) = as_blob(lhs, lhs_is_c_string, &mut context.memory)?;
                        let (rhs_blob, rhs_len) = as_blob(rhs, rhs_is_c_string, &mut context.memory)?;
                        let lhs_slice = &lhs_blob.as_slice()[..lhs_len];
                        let rhs_slice = &rhs_blob.as_slice()[..rhs_len];
                        let c = lhs_slice.cmp(rhs_slice);
                        let r = match op {
                            BinaryOperator::Eq => c.is_eq(),
                            BinaryOperator::Ne => c.is_ne(),
                            BinaryOperator::Gt => c.is_gt(),
                            BinaryOperator::Lt => c.is_lt(),
                            BinaryOperator::Ge => c.is_ge(),
                            BinaryOperator::Le => c.is_le(),
                            _ => panic!("huh"),
                        };
                        let type_ = state.builtin_types.bool_;
                        return Ok(Value {val: AddrOrValueBlob::Blob(ValueBlob::new(r as usize)), type_, flags: ValueFlags::empty()});
                    }
                }
                _ => (),
            }

            // All other binary operators require both args to be simple numbers or pointers.
            let mut a = to_basic(&lhs, &mut context.memory, "arithmetic")?;
            let mut b = to_basic(&rhs, &mut context.memory, "arithmetic")?;
            let r = match op {
                BinaryOperator::Add | BinaryOperator::Sub => {
                    let (mut ta, mut tb) = unsafe {(&*lhs.type_, &*rhs.type_)};
                    if let Some(pb) = tb.t.as_pointer() {
                        if let Some(pa) = ta.t.as_pointer() {
                            if op == BinaryOperator::Sub { // subtract pointers
                                let (stride_a, stride_b) = unsafe {((*pa.type_).calculate_size(), (*pb.type_).calculate_size())};
                                if stride_a != stride_b { return err!(TypeMismatch, "can't subtract pointers to different-sized types"); }
                                if stride_a == 0 { return err!(TypeMismatch, "can't subtract pointers to zero-size types"); }
                                let mut x = a.cast_to_usize().wrapping_sub(b.cast_to_usize());
                                if x % stride_a != 0 { return err!(TypeMismatch, "pointer difference not divisibly by type size"); }
                                x /= stride_a;
                                let type_ = state.builtin_types.i64_;
                                return Ok(Value {val: AddrOrValueBlob::Blob(ValueBlob::new(x)), type_, flags: ValueFlags::empty()});
                            }
                        } else if op == BinaryOperator::Add {
                            mem::swap(&mut a, &mut b);
                            mem::swap(&mut ta, &mut tb);
                        }
                    }
                    if let Some(pa) = ta.t.as_pointer() {
                        match &tb.t {
                            Type::PointerToMember(member) => if op == BinaryOperator::Add {
                                // pointer + field_offset: "dereference" the pointer-to-field
                                if pa.type_ != member.containing_type {
                                    return err!(TypeMismatch, "adding field offset to a pointer of different type");
                                }
                                let addr = a.cast_to_usize().wrapping_add(b.cast_to_usize());
                                let field_ptr_type = state.types.add_pointer(member.type_, PointerFlags::empty());
                                return Ok(Value {val: AddrOrValueBlob::Blob(ValueBlob::new(addr)), type_: field_ptr_type, flags: ValueFlags::empty()});
                            } else {
                                // pointer - field_offset: just subtract as numbers
                            }
                            Type::Pointer(_) => (), // pointer + pointer: add as numbers
                            _ if b.is_f64() => return err!(TypeMismatch, "can't add float to pointer"),
                            _ => {
                                // pointer + number: offset by number*sizeof(*pointer) bytes
                                let stride = unsafe {(*pa.type_).calculate_size()};
                                let x = a.cast_to_usize();
                                let y = b.cast_to_usize().wrapping_mul(stride);
                                let x = if op == BinaryOperator::Add {x.wrapping_add(y)} else {x.wrapping_sub(y)};
                                return Ok(Value {val: AddrOrValueBlob::Blob(ValueBlob::new(x)), type_: ta, flags: ValueFlags::empty()});
                            }
                        }
                    }

                    if a.is_f64() || b.is_f64() {
                        let (x, y) = (a.cast_to_f64(), b.cast_to_f64());
                        BasicValue::F(if op == BinaryOperator::Sub {x-y} else {x+y})
                    } else if op == BinaryOperator::Sub {
                        let (x, y) = (a.cast_to_usize(), b.cast_to_usize());
                        BasicValue::I(x.wrapping_sub(y) as isize) // unsigned - unsigned = signed
                    } else if a.is_isize() || b.is_isize() {
                        let (x, y) = (a.cast_to_isize(), b.cast_to_isize());
                        BasicValue::I(x.wrapping_add(y))
                    } else {
                        let (x, y) = (a.cast_to_usize(), b.cast_to_usize());
                        BasicValue::U(x.wrapping_add(y))
                    }
                }
                BinaryOperator::Mul | BinaryOperator::Div | BinaryOperator::Rem => {
                    if a.is_f64() || b.is_f64() {
                        let (x, y) = (a.cast_to_f64(), b.cast_to_f64());
                        BasicValue::F(match op {
                            BinaryOperator::Mul => x*y,
                            BinaryOperator::Div => x/y,
                            BinaryOperator::Rem => x.rem_euclid(y),
                            _ => panic!("huh"),
                        })
                    } else if b.cast_to_usize() == 0 && (op == BinaryOperator::Div || op == BinaryOperator::Rem) {
                        return err!(Runtime, "integer division by zero");
                    } else if a.is_isize() || b.is_isize() {
                        let (x, y) = (a.cast_to_isize(), b.cast_to_isize());
                        BasicValue::I(match op {
                            BinaryOperator::Mul => x.wrapping_mul(y),
                            BinaryOperator::Div => x.div_euclid(y),
                            BinaryOperator::Rem => x.rem_euclid(y),
                            _ => panic!("huh"),
                        })
                    } else {
                        let (x, y) = (a.cast_to_usize(), b.cast_to_usize());
                        BasicValue::U(match op {
                            BinaryOperator::Mul => x.wrapping_mul(y),
                            BinaryOperator::Div => x.div_euclid(y),
                            BinaryOperator::Rem => x.rem_euclid(y),
                            _ => panic!("huh"),
                        })
                    }
                }

                BinaryOperator::BitAnd | BinaryOperator::BitOr | BinaryOperator::BitXor => {
                    if a.is_f64() || b.is_f64() {
                        return err!(TypeMismatch, "can't do bitwise ops on floats");
                    }
                    let (x, y) = (a.cast_to_usize(), b.cast_to_usize());
                    let r = match op {
                        BinaryOperator::BitAnd => x&y,
                        BinaryOperator::BitOr => x|y,
                        BinaryOperator::BitXor => x^y,
                        _ => panic!("huh"),
                    };
                    if a.is_isize() || b.is_isize() {
                        BasicValue::I(r as isize)
                    } else {
                        BasicValue::U(r)
                    }
                }
                BinaryOperator::Shl | BinaryOperator::Shr => {
                    if a.is_f64() || b.is_f64() {
                        return err!(TypeMismatch, "can't shift floats");
                    }
                    let y = b.cast_to_usize();
                    if y >= 64 {
                        return err!(Runtime, "shift value too big: {}", y);
                    }
                    match a {
                        BasicValue::U(x) => BasicValue::U(if op == BinaryOperator::Shl {x << y} else {x >> y}),
                        BasicValue::I(x) => BasicValue::I(if op == BinaryOperator::Shl {x << y} else {x >> y}),
                        BasicValue::F(_) => panic!("huh"),
                    }
                }

                BinaryOperator::Eq | BinaryOperator::Ne | BinaryOperator::Gt | BinaryOperator::Lt | BinaryOperator::Ge | BinaryOperator::Le => {
                    // TODO: String comparison.
                    let c = if a.is_f64() || b.is_f64() {
                        a.cast_to_f64().partial_cmp(&b.cast_to_f64())
                    } else if a.is_isize() || b.is_isize() {
                        a.cast_to_isize().partial_cmp(&b.cast_to_isize())
                    } else {
                        a.cast_to_usize().partial_cmp(&b.cast_to_usize())
                    };
                    let r = match c {
                        None => false,
                        Some(c) => match op {
                            BinaryOperator::Eq => c.is_eq(),
                            BinaryOperator::Ne => c.is_ne(),
                            BinaryOperator::Gt => c.is_gt(),
                            BinaryOperator::Lt => c.is_lt(),
                            BinaryOperator::Ge => c.is_ge(),
                            BinaryOperator::Le => c.is_le(),
                            _ => panic!("huh"),
                        }
                    };
                    let type_ = state.builtin_types.bool_;
                    return Ok(Value {val: AddrOrValueBlob::Blob(ValueBlob::new(r as usize)), type_, flags: ValueFlags::empty()});
                }

                _ => return err!(NotImplemented, "{:?} not supported", op),
            };
            let type_ = match r {
                BasicValue::U(_) => state.builtin_types.u64_,
                BasicValue::I(_) => state.builtin_types.i64_,
                BasicValue::F(_) => state.builtin_types.f64_,
            };
            Ok(Value {val: AddrOrValueBlob::Blob(ValueBlob::new(r.transmute_to_usize())), type_, flags: ValueFlags::empty()})
        }
        AST::Call(name) => match &name[..] {
            "typeof" => {
                if node.children.len() != 1 {
                    return err!(TypeMismatch, "typeof() expects 1 argument, got {}", node.children.len());
                }
                let mut val = eval_expression(expr, node.children[0], state, context, true)?;
                if val.flags.contains(ValueFlags::PRETTY) {
                    follow_references_and_prettify(&mut val, None, /*pointers_too*/ true, state, context)?;
                }
                Ok(Value {val: AddrOrValueBlob::Blob(ValueBlob::new(val.type_ as usize)), type_: state.types.types_arena.add(TypeInfo {name: "type", size: 8, flags: TypeFlags::SIZE_KNOWN, t: Type::MetaType, ..Default::default()}), flags: ValueFlags::empty()})
            }
            "var" => {
                if node.children.len() != 1 {
                    return err!(TypeMismatch, "var() expects 1 argument, got {}", node.children.len());
                }
                match &expr.ast[node.children[0].0].a {
                    AST::Variable {name, quoted, from_any_frame} => {
                        Ok(state.get_variable(context, name, /*maybe_register*/ false, *from_any_frame, /*only_type*/ false, /*meta*/ true)?)
                    }
                    _ => return err!(Syntax, "var() argument must be a variable name"),
                }
            }
            "try" => {
                for &child in &node.children {
                    if let Ok(val) = eval_expression(expr, child, state, context, false) {
                        return Ok(val);
                    }
                }
                Ok(Value {val: AddrOrValueBlob::Blob(ValueBlob::new(0)), type_: state.builtin_types.u64_, flags: ValueFlags::empty()})
            }
            _ => return err!(NoFunction, "no builtin function '{}' (calling debuggee functions is not supported)", name),
        }
        AST::Type {..} | AST::PointerType | AST::ArrayType(_) => panic!("unexpected type AST"),
        _ => return err!(NotImplemented, "not implemented"),
    }
}

fn eval_type(expr: &Expression, node_idx: ASTIdx, state: &mut EvalState, context: &mut EvalContext) -> Result<*const TypeInfo> {
    let node = &expr.ast[node_idx.0];
    match &node.a {
        AST::Type {name, quoted} => state.get_type(context, name),
        AST::PointerType => {
            let inner = eval_type(expr, node.children[0], state, context)?;
            Ok(state.types.add_pointer(inner, PointerFlags::empty()))
        }
        AST::ArrayType(len) => {
            let inner = eval_type(expr, node.children[0], state, context)?;
            Ok(state.types.add_array(inner, len.clone(), ArrayFlags::empty()))
        }
        _ => panic!("unexpected non-type AST"),
    }
}

// `additional_values` are values before prettify_value() was applied. For field access, these are the structs whose fields the user may plausibly be trying to access.
// E.g. `unique_ptr<vector<int>>` is prettified into a slice, but we want to also allow things like `x._M_t` to access unique_ptr's fields and `x._M_begin` to access vector's fields.
fn follow_references_and_prettify(val: &mut Value, mut additional_values: Option<&mut Vec<Value>>, pointers_too: bool, state: &mut EvalState, context: &mut EvalContext) -> Result<()> {
    for step in 0..100 {
        if unsafe {(*val.type_).t.is_meta()} {
            *val = reflect_meta_value(val, state, context, None);
            return Ok(());
        }
        if !val.flags.contains(ValueFlags::RAW) {
            let mut cow = Cow::Borrowed(val);
            let mut _warning = None;
            prettify_value(&mut cow, &mut _warning, state, context)?;
            if let Cow::Owned(v) = cow {
                let prev_val = mem::replace(val, v);
                if let Some(ref mut additional) = additional_values {
                    additional.push(prev_val);
                }
            }
        }
        let type_ = unsafe {&*val.type_};
        match &type_.t {
            Type::Pointer(p) if p.flags.contains(PointerFlags::REFERENCE) || pointers_too => {
                let addr = val.val.clone().into_value(8, &mut context.memory)?.get_usize()?;
                val.val = AddrOrValueBlob::Addr(addr);
                val.type_ = p.type_;
            }
            _ => return Ok(()),
        }
    }
    err!(Sanity, "cyclic pointer")
}

// Simplified value behind primitive values, pointers, and enums.
#[derive(Clone, Copy, Debug)]
enum BasicValue {
    I(isize),
    U(usize),
    F(f64),
    // (Can add wide or simd types here.)
}
impl BasicValue {
    fn transmute_to_usize(&self) -> usize { match *self { Self::I(x) => x as usize, Self::U(x) => x, Self::F(x) => f64::to_bits(x) as usize } }
    fn cast_to_isize(&self) -> isize { match *self { Self::I(x) => x, Self::U(x) => x as isize, Self::F(x) => x as isize } }
    fn cast_to_usize(&self) -> usize { match *self { Self::I(x) => x as usize, Self::U(x) => x, Self::F(x) => x as usize } }
    fn cast_to_f64(&self) -> f64 { match *self { Self::I(x) => x as f64, Self::U(x) => x as f64, Self::F(x) => x } }
    fn kind_name(&self) -> &'static str { match *self { Self::I(x) => "int", Self::U(x) => "uint", Self::F(x) => "float" } }
    fn is_f64(&self) -> bool { match self { Self::F(_) => true, _ => false } }
    fn is_isize(&self) -> bool { match self { Self::I(_) => true, _ => false } }
}

fn to_basic(val: &Value, memory: &mut CachedMemReader, what: &str) -> Result<BasicValue> {
    let mut type_ = val.type_;
    while let Type::Enum(e) = unsafe {&(*type_).t} {
        type_ = e.type_;
    }
    let t = unsafe {&*type_};
    let size = t.calculate_size();
    if size > 8 || size == 0 {
        return err!(TypeMismatch, "unexpected primitive value size: {} bytes", size);
    }
    Ok(match &t.t {
        Type::Primitive(f) => {
            let mut x = val.val.clone().into_value(size, memory)?.get_usize()?;
            if f.contains(PrimitiveFlags::FLOAT) {
                BasicValue::F(match size {
                    4 => f32::from_bits(x as u32) as f64,
                    8 => f64::from_bits(x as u64),
                    _ => return err!(Dwarf, "unexpected float size: {}", size),
                })
            } else {
                flip_endianness_if_needed(&mut x, size, val.flags);
                if f.contains(PrimitiveFlags::SIGNED) {
                    // Sign-extend.
                    if size < 8 && x & 1 << (size*8-1) as u32 != 0 {
                        x |= !((1usize << size*8)-1);
                    }
                    BasicValue::I(x as isize)
                } else {
                    BasicValue::U(x)
                }
            }
        }
        Type::Pointer(_) | Type::PointerToMember(_) => BasicValue::U(val.val.clone().into_value(size, memory)?.get_usize()?),
        _ => return err!(TypeMismatch, "can't {} {}", what, t.t.kind_name()),
    })
}

fn from_basic(b: BasicValue, type_: *const TypeInfo) -> Result<Option<AddrOrValueBlob>> {
    let mut inner = type_;
    while let Type::Enum(e) = unsafe {&(*inner).t} {
        inner = e.type_;
    }
    let t = unsafe {&*inner};
    let size = t.calculate_size();
    let mut x = match &t.t {
        Type::Primitive(f) if f.contains(PrimitiveFlags::FLOAT) => {
            let x = b.cast_to_f64();
            match size {
                4 => f32::to_bits(x as f32) as usize,
                8 => f64::to_bits(x) as usize,
                _ => return err!(Dwarf, "unexpected float size: {}", size),
            }
        }
        Type::Primitive(f) if f.contains(PrimitiveFlags::SIGNED) => b.cast_to_isize() as usize, // covers negative float to signed int
        Type::Primitive(_) | Type::Pointer(_) | Type::PointerToMember(_) => b.cast_to_usize(),
        _ => return Ok(None),
    };
    if size < 8 {
        x &= (1usize << (size * 8)) - 1;
    }
    Ok(Some(AddrOrValueBlob::Blob(ValueBlob::new(x))))
}


#[derive(Clone, Debug)]
enum LiteralValue {
    Basic(BasicValue),
    Char(char),
    String(String),
}
impl LiteralValue {
    fn is_unsigned(&self) -> bool { self.as_unsigned().is_some() }
    fn as_unsigned(&self) -> Option<usize> { match self { Self::Basic(BasicValue::U(x)) => Some(*x), _ => None } }
    fn as_blob(&self) -> ValueBlob { match self { &Self::Basic(b) => ValueBlob::new(b.transmute_to_usize()), &Self::Char(c) => ValueBlob::new(c as u32 as usize), Self::String(s) => ValueBlob::from_slice(s.as_bytes()) } }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum UnaryOperator {
    Neg, // unary -
    Not, // unary !

    Borrow, // &
    Dereference, // *
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum BinaryOperator {
    Add, // +
    Sub, // -
    Mul, // *
    Div, // /
    Rem, // %
    BitAnd, // &
    BitOr, // |
    BitXor, // ^
    Shl, // <<
    Shr, // >>

    Eq, // ==
    Ne, // !=
    Gt, // >
    Lt, // <
    Ge, // >=
    Le, // <=

    LazyAnd, // &&
    LazyOr, // ||

    Assign, // =
    AddAssign, // +=
    SubAssign, // -=
    MulAssign, // *=
    DivAssign, // /=
    RemAssign, // %=
    AndAssign, // &=
    OrAssign, // |=
    XorAssign, // ^=
    ShlAssign, // <<=
    ShrAssign, // >>=

    Range, // ..

    Index, // [n]
    Slicify, // .[n]
}

#[derive(Clone, Copy, Eq, PartialEq, Debug)]
struct ASTIdx(usize);

// Syntax and names are partially stolen from https://doc.rust-lang.org/reference/expressions.html
enum AST {
    Literal(LiteralValue), // 42.69, "foo"
    Variable {name: String, quoted: bool, from_any_frame: bool}, // foo::bar::v, or `v`, or ^v
    UnaryOperator(UnaryOperator), // -x, !f
    BinaryOperator(BinaryOperator), // a + b, x %= 2
    Field {name: String, quoted: bool}, // a.b, a.`b`
    TypeCast, // a as i64
    Type {name: String, quoted: bool}, // Foo
    PointerType, // *Foo
    ArrayType(/*len*/ Option<usize>), // [Foo; 10] or [Foo]

    Array, // [a, 42, b]
    Tuple, // (a, 42, "foo", b)
    TupleIndexing(usize), // t.0
    StructExpression(Vec<String>), // struct { x: 42, y: 69 }
    Call(String), // f(1, "foo")
    Continue, // continue
    Break, // break
    Return, // return

    Block, // {a += 1; f(x); 42}

    While, // while i < 10 { i += 1; }
    For(String), // for i in 10..20 { i += 1 }
    If, // if a < b { a = b; } else { b = a; }

    Let { // let v = 42
        name: String,
        has_type: bool,
    },

    TypeInfo, // type(i64)  TODO: For sizeof and offsetof implement .#size and .#offset on types and fields. Maybe add sizeof()/offsetof() syntax too.

    FunctionDefinition { // children: arg types, return type (if has), body Block
        name: String,
        arg_names: Vec<String>,
        has_return_type: bool,
    },
    StructDefinition { // children: field types
        name: String,
        field_names: Vec<String>,
    },
}

struct ASTNode {
    range: Range<usize>,
    a: AST,
    children: Vec<ASTIdx>,
}

struct InputStream<'a> {
    input: &'a str,
    pos: usize,
}
impl<'a> InputStream<'a> {
    fn peek(&self) -> Option<char> {
        self.input[self.pos..].chars().next()
    }
    fn eat(&mut self) -> Option<char> {
        let mut it = self.input[self.pos..].chars();
        let r = it.next();
        self.pos = unsafe {it.as_str().as_ptr().offset_from(self.input.as_ptr())} as usize;
        r
    }
    fn uneat(&mut self) {
        loop {
            assert!(self.pos > 0);
            self.pos -= 1;
            if self.input.is_char_boundary(self.pos) {
                break;
            }
        }
    }
    fn eat_if_eq(&mut self, c: char) -> bool {
        match self.peek() {
            Some(x) if x == c => {
                self.eat();
                return true;
            }
            _ => false,
        }
    }
    fn eat_digits(&mut self, radix: u32) -> &'a str {
        let start = self.pos;
        let mut it = self.input[self.pos..].chars();
        loop {
            self.pos = unsafe {it.as_str().as_ptr().offset_from(self.input.as_ptr())} as usize;
            match it.next() {
                Some(c) if c.is_digit(radix) => (),
                _ => break,
            }
        }
        &self.input[start..self.pos]
    }
}

struct Lexer<'a> {
    input: InputStream<'a>,
    next_tokens: Vec<(Range<usize>, Token)>,
    previous_token_end: usize,
    // For parsing s.1.1 as [identifier, dot, 1, dot, 1] instead of [identifier, dot, 1.1f].
    previous_dot: bool,
}
impl<'a> Lexer<'a> {
    // peek(1) to get next token without consuming it, peek(2) for second-next, etc
    fn peek(&mut self, n: usize) -> Result<(Range<usize>, &Token)> {
        assert!(n > 0);
        loop {
            if self.next_tokens.len() >= n {
                let (r, t) = &self.next_tokens[n-1];
                return Ok((r.clone(), t));
            }

            let c = match self.input.eat() {
                None => return Ok((self.input.pos..self.input.pos, &Token::Eof)),
                Some(c) => c };
            let start = self.input.pos;
            let previous_dot = mem::take(&mut self.previous_dot);
            let token = match c {
                ' ' | '\t' | '\n' | '\r' => continue,
                '+' => Token::BinaryOperator(if self.input.eat_if_eq('=') { BinaryOperator::AddAssign } else { BinaryOperator::Add }),
                '-' => if self.input.eat_if_eq('>') { Token::Arrow } else { Token::BinaryOperator(if self.input.eat_if_eq('=') { BinaryOperator::SubAssign } else { BinaryOperator::Sub }) },
                '*' => Token::BinaryOperator(if self.input.eat_if_eq('=') { BinaryOperator::MulAssign } else { BinaryOperator::Mul }),
                '/' => Token::BinaryOperator(if self.input.eat_if_eq('=') { BinaryOperator::DivAssign } else { BinaryOperator::Div }),
                '%' => Token::BinaryOperator(if self.input.eat_if_eq('=') { BinaryOperator::RemAssign } else { BinaryOperator::Rem }),
                '&' => Token::BinaryOperator(if self.input.eat_if_eq('=') { BinaryOperator::AndAssign } else if self.input.eat_if_eq('&') { BinaryOperator::LazyAnd } else { BinaryOperator::BitAnd }),
                '|' => Token::BinaryOperator(if self.input.eat_if_eq('=') { BinaryOperator::OrAssign } else if self.input.eat_if_eq('|') { BinaryOperator::LazyOr } else { BinaryOperator::BitOr }),
                '^' => Token::BinaryOperator(if self.input.eat_if_eq('=') { BinaryOperator::XorAssign } else { BinaryOperator::BitXor }),
                '<' => Token::BinaryOperator(if self.input.eat_if_eq('=') { BinaryOperator::Le } else if self.input.eat_if_eq('<') { if self.input.eat_if_eq('=') { BinaryOperator::ShlAssign } else { BinaryOperator::Shl } } else { BinaryOperator::Lt }),
                '>' => Token::BinaryOperator(if self.input.eat_if_eq('=') { BinaryOperator::Ge } else if self.input.eat_if_eq('>') { if self.input.eat_if_eq('=') { BinaryOperator::ShrAssign } else { BinaryOperator::Shr } } else { BinaryOperator::Gt }),
                '=' => Token::BinaryOperator(if self.input.eat_if_eq('=') { BinaryOperator::Eq } else { BinaryOperator::Assign }),
                '.' => if self.input.eat_if_eq('.') { Token::BinaryOperator(BinaryOperator::Range) } else { self.previous_dot = true; Token::Char('.') },
                '!' => if self.input.eat_if_eq('=') { Token::BinaryOperator(BinaryOperator::Ne) } else { Token::UnaryOperator(UnaryOperator::Not) },
                ',' | '(' | ')' | '[' | ']' | '{' | '}' | ';' | '@' => Token::Char(c),
                ':' if self.input.peek() != Some(':') => Token::Char(':'),
                '"' => {
                    let mut s = String::new();
                    loop {
                        match self.input.eat() {
                            None => return err!(Syntax, "unterminated string literal at {}", start),
                            Some('"') => break,
                            Some('\\') => s.push(self.parse_char_escape_sequence("string", start)?),
                            Some(c) => s.push(c),
                        }
                    }
                    Token::Literal(LiteralValue::String(s))
                }
                '\'' => {
                    let c = match self.input.eat() {
                        None => return err!(Syntax, "unterminated char literal at {}", start),
                        Some('\'') => return err!(Syntax, "empty char literal at {}", start),
                        Some('\\') => self.parse_char_escape_sequence("char", start)?,
                        Some(c) => c,
                    };
                    match self.input.eat() {
                        None => return err!(Syntax, "unterminated char literal at {}", start),
                        Some('\'') => (),
                        Some(c) => return err!(Syntax, "char literal is too long at {}", start),
                    }
                    Token::Literal(LiteralValue::Char(c))
                }
                '0'..='9' => {
                    self.input.uneat();
                    let mut int_s = self.input.eat_digits(10);
                    let mut radix = 10u32;
                    if int_s == "0" {
                        if self.input.eat_if_eq('x') {
                            radix = 16;
                            int_s = self.input.eat_digits(radix);
                        } else if self.input.eat_if_eq('b') {
                            radix = 2;
                            int_s = self.input.eat_digits(radix);
                        }
                    }
                    let (has_dot, frac_s) = if !previous_dot && self.input.eat_if_eq('.') {
                        (true, self.input.eat_digits(radix))
                    } else {
                        (false, "")
                    };
                    let exp_radix = if !previous_dot && self.input.eat_if_eq('e') {
                        10u32
                    } else if self.input.eat_if_eq('p') {
                        2
                    } else {
                        0
                    };
                    let exp_negative = exp_radix != 0 && self.input.eat_if_eq('-');
                    let exp_s = if exp_radix == 0 { "" } else { self.input.eat_digits(radix) };
                    if let Some(c) = self.input.peek() {
                        match c {
                            '0'..='9' | 'a'..='z' | 'A'..='Z' | '_' => return err!(Syntax, "unexpected suffix after number at {}", self.input.pos),
                            '.' if !previous_dot => return err!(Syntax, "unexpected '.' after number at {}", self.input.pos),
                            _ => (),
                        }
                    }
                    if has_dot || exp_radix != 0 {
                        let mut val = 0.0f64;
                        for c in int_s.chars() {
                            val = val * radix as f64 + c.to_digit(radix).unwrap() as f64;
                        }
                        let mut frac = 0.0f64;
                        for c in frac_s.chars().rev() {
                            // This accumulates error, there's probably a better way.
                            frac = (frac + c.to_digit(radix).unwrap() as f64) / radix as f64;
                        }
                        val += frac;
                        if exp_radix != 0 {
                            let mut exp = 0i32;
                            for c in exp_s.chars() {
                                exp = exp.saturating_mul(radix as i32).saturating_add(c.to_digit(radix).unwrap() as i32);
                            }
                            if exp_negative {
                                exp = -exp;
                            }
                            val *= (exp_radix as f64).powi(exp);
                        }
                        Token::Literal(LiteralValue::Basic(BasicValue::F(val)))
                    } else {
                        let mut val = 0usize;
                        for c in int_s.chars() {
                            val = match val.checked_mul(radix as usize).map_or(None, |x| x.checked_add(c.to_digit(radix).unwrap() as usize)) {
                                None => return err!(Syntax, "integer literal is too big at {}", start),
                                Some(v) => v,
                            };
                        }
                        Token::Literal(LiteralValue::Basic(BasicValue::U(val)))
                    }
                }
                '`' => {
                    let mut s = String::new();
                    loop {
                        match self.input.eat() {
                            None => return err!(Syntax, "unterminated quoted identifier at {}", start),
                            Some('`') => break,
                            Some('\\') => s.push(self.parse_char_escape_sequence("quoted identifier", start)?),
                            Some(c) => s.push(c),
                        }
                    }
                    Token::Identifier {quoted: true, s}
                }
                'a'..='z' | 'A'..='Z' | '_' | '#' | '$' | ':' => {
                    self.input.uneat();
                    let mut s = String::new();
                    loop {
                        let c = match self.input.peek() {
                            None => break,
                            Some(c) => c };
                        match c {
                            'a'..='z' | 'A'..='Z' | '_' | '#' | '$' | '0'..='9' => (),
                            ':' => {
                                self.input.eat();
                                if self.input.peek() == Some(':') { // "::" as in `foo::bar`
                                    s.push(c);
                                } else {
                                    self.input.uneat(); // ":" as in `let foo: u8`
                                    break;
                                }
                            }
                            _ => break,
                        }
                        s.push(c);
                        self.input.eat();
                    }
                    Token::Identifier {quoted: false, s}
                }
                x => return err!(Syntax, "unexpected character at {}: '{}'", start, x),
            };
            self.next_tokens.push((start..self.input.pos, token));
        }
    }

    fn parse_char_escape_sequence(&mut self, literal_type: &str, literal_start: usize) -> Result<char> {
        Ok(
            match self.input.eat() {
                None => return err!(Syntax, "unterminated {} literal at {}", literal_type, literal_start),
                Some('0') => '\0',
                Some('n') => '\n',
                Some('r') => '\r',
                Some('t') => '\t',
                Some('x') => {
                    let (a, b) = (self.input.eat(), self.input.eat());
                    if b.is_none() { return err!(Syntax, "unterminated {} literal at {}", literal_type, literal_start); }
                    let (a, b) = (a.unwrap(), b.unwrap());
                    match (a.to_digit(16), b.to_digit(16)) {
                        (Some(a), Some(b)) => (a*16 + b) as u8 as char,
                        _ => return err!(Syntax, "invalid escape sequence in {} literal: \"\\x{}{}\" at {}", literal_type, a, b, self.input.pos - 4),
                    }
                }
                Some(c) => c,
            }
        )
    }

    fn eat(&mut self, n: usize) -> Result<(Range<usize>, Token)> {
        assert!(n > 0);
        self.previous_token_end = self.peek(n)?.0.end;
        Ok(self.next_tokens.drain(..n.min(self.next_tokens.len())).last().unwrap_or_else(|| (self.input.pos..self.input.pos, Token::Eof)))
    }

    fn eat_if<F: FnOnce(&Token) -> bool>(&mut self, f: F) -> Result<Option<(Range<usize>, Token)>> {
        Ok(if f(self.peek(1)?.1) {
            let (r, t) = self.next_tokens.remove(0);
            self.previous_token_end = r.end;
            Some((r, t))
        } else {
            None
        })
    }

    fn peek_expect<F: FnOnce(&Token) -> bool>(&mut self, what: &str, f: F) -> Result<(Range<usize>, &Token)> {
        let (r, t) = self.peek(1)?;
        if !f(t) {
            return err!(Syntax, "expected {}, found {:?} at {}", what, t, r.start);
        }
        Ok((r, t))
    }

    fn expect<F: FnOnce(&Token) -> bool>(&mut self, what: &str, f: F) -> Result<(Range<usize>, Token)> {
        self.peek_expect(what, f)?;
        Ok(self.eat(1)?)
    }
}

#[derive(Debug, Clone)]
enum Token {
    BinaryOperator(BinaryOperator), // abusing the struct to mean specific characters (e.g. '*') rather than their semantics (e.g. multiplication or dereference)
    UnaryOperator(UnaryOperator),
    Arrow, // ->
    Char(char), // , [ ] ( ) { } etc
    Literal(LiteralValue), // 42 "foo" etc
    Identifier {
        s: String,
        quoted: bool,
    },
    Eof,
}
impl Token {
    fn is_identifier(&self) -> bool { match self { Self::Identifier {..} => true, _ => false } }
    fn into_identifier(self) -> String { match self { Self::Identifier {s, ..} => s, _ => panic!("identifier expected") } }
    fn is_keyword(&self, word: &str) -> bool { match self { Self::Identifier {s, quoted} if !quoted && s == word => true, _ => false } }
    fn is_char(&self, c: char) -> bool { match self { Self::Char(x) if x == &c => true, _ => false } }
    fn is_arrow(&self) -> bool { match self { Self::Arrow => true, _ => false } }
    fn is_binary_operator(&self, op: BinaryOperator) -> bool { match self { Self::BinaryOperator(x) if x == &op => true, _ => false } }
    fn is_eof(&self) -> bool { match self { Self::Eof => true, _ => false } }
}

fn parse_block(lex: &mut Lexer, expr: &mut Expression) -> Result<ASTIdx> {
    let (range, _) = lex.expect("'{'", |t| t.is_char('{'))?;
    let mut node = ASTNode {range, children: Vec::new(), a: AST::Block};
    loop {
        if let Some((range, _)) = lex.eat_if(|t| t.is_char('}'))? {
            // Either "{}" or ";}". The block returns an empty tuple.
            expr.ast.push(ASTNode {range, children: Vec::new(), a: AST::Tuple});
            node.children.push(ASTIdx(expr.ast.len()-1));
            break;
        }
        node.children.push(parse_expression(lex, expr, Precedence::Weakest)?);
        let (r, t) = lex.eat(1)?;
        match t {
            Token::Char(';') => continue,
            Token::Char('}') => break,
            _ => return err!(Syntax, "expected ';' or '}}', got {:?} at {}", t, r.start),
        }
    }
    assert!(!node.children.is_empty());
    node.range.end = lex.previous_token_end;
    expr.ast.push(node);
    Ok(ASTIdx(expr.ast.len()-1))
}

fn parse_type(lex: &mut Lexer, expr: &mut Expression) -> Result<ASTIdx> {
    let (range, token) = lex.eat(1)?;
    let mut node = ASTNode {range, children: Vec::new(), a: AST::Tuple};
    node.a = match token {
        Token::BinaryOperator(op) if op == BinaryOperator::Mul => {
            node.children.push(parse_type(lex, expr)?);
            AST::PointerType
        }
        Token::BinaryOperator(op) if op == BinaryOperator::BitAnd => return err!(Syntax, "references not supported, use pointers"),
        Token::Identifier {s, quoted} => AST::Type {name: s, quoted},
        Token::Char('[') => {
            // Array.
            node.children.push(parse_type(lex, expr)?);
            let (range, token) = lex.eat(1)?;
            if let Token::Char(';') = token {
                // Sized array.
                let (r, t) = lex.eat(1)?;
                let len = match t {
                    Token::Literal(LiteralValue::Basic(BasicValue::U(len))) => len,
                    _ => return err!(Syntax, "expected nonnegative number, got {:?} at {}", t, r.start),
                };
                lex.expect("']'", |t| t.is_char(']'))?;
                AST::ArrayType(Some(len))
            } else if let Token::Char(']') = token {
                // Array with unknown size.
                AST::ArrayType(None)
            } else {
                return err!(Syntax, "expected ';' or ']', got {:?} at {}", token, range.start);
            }
        }
        _ => return err!(Syntax, "expected type, got {:?} at {}", token, node.range.start),
    };
    node.range.end = lex.previous_token_end;
    expr.ast.push(node);
    Ok(ASTIdx(expr.ast.len() - 1))
}

fn parse_expression(lex: &mut Lexer, expr: &mut Expression, outer_precedence: Precedence) -> Result<ASTIdx> {
    let (range, token) = lex.eat(1)?;
    let mut node = ASTNode {range, children: Vec::new(), a: AST::Tuple};
    let mut replace: Option<ASTIdx> = None; // ignore `node` and use this node as the initial expression
    node.a = match token {
        Token::Literal(value) => AST::Literal(value),
        Token::Identifier {s, quoted} => {
            let mut ast = AST::Variable {name: s.clone(), quoted, from_any_frame: false};
            if !quoted {
                match &s as &str {
                    "struct" => {
                        let (range, token) = lex.eat(1)?;
                        match token {
                            Token::Char('{') => {
                                let mut field_names: Vec<String> = Vec::new();
                                loop {
                                    let (r, t) = lex.eat(1)?;
                                    let name = match t {
                                        Token::Identifier {s, ..} => s.clone(),
                                        Token::Char('}') => break,
                                        _ => return err!(Syntax, "expected field name, got {:?} at {}", t, r.start),
                                    };
                                    lex.expect("':'", |t| t.is_char(':'))?;
                                    let ex = parse_expression(lex, expr, Precedence::Weakest)?;
                                    field_names.push(name);
                                    node.children.push(ex);

                                    if lex.eat_if(|t| t.is_char(','))?.is_none() {
                                        lex.peek_expect("'}'", |t| t.is_char('}'))?;
                                    }
                                }
                                ast = AST::StructExpression(field_names)
                            }
                            Token::Identifier {quoted: _, s: name} => {
                                lex.expect("struct definition body", |t| t.is_char('{'))?;
                                let mut field_names: Vec<String> = Vec::new();
                                loop {
                                    let (r, t) = lex.eat(1)?;
                                    let name = match t {
                                        Token::Identifier {s, ..} => s.clone(),
                                        Token::Char('}') => break,
                                        _ => return err!(Syntax, "expected field name, got {:?} at {}", t, r.start),
                                    };
                                    field_names.push(name);
                                    lex.expect("':'", |t| t.is_char(':'))?;
                                    node.children.push(parse_type(lex, expr)?);

                                    if lex.eat_if(|t| t.is_char(','))?.is_none() {
                                        lex.peek_expect("'}'", |t| t.is_char('}'))?;
                                    }
                                }
                                ast = AST::StructDefinition {name: name.clone(), field_names};
                            }
                            _ => return err!(Syntax, "expected struct name or body, got {:?} at {}", token, range.start),
                        }
                    }
                    "continue" => ast = AST::Continue,
                    "break" => ast = AST::Break,
                    "return" => {
                        match lex.peek(1)?.1 {
                            Token::Eof | Token::Char(';') | Token::Char(',') | Token::Char('}') | Token::Char(')') => (),
                            _ => node.children.push(parse_expression(lex, expr, Precedence::Return)?),
                        }
                        ast = AST::Return;
                    }
                    "while" => {
                        node.children.push(parse_expression(lex, expr, Precedence::Weakest)?);
                        node.children.push(parse_block(lex, expr)?);
                        ast = AST::While;
                    }
                    "for" => {
                        let name = lex.expect("loop variable name", |t| t.is_identifier())?.1.into_identifier();
                        lex.expect("'in'", |t| t.is_keyword("in"))?;
                        node.children.push(parse_expression(lex, expr, Precedence::Weakest)?);
                        node.children.push(parse_block(lex, expr)?);
                        ast = AST::For(name);
                    }
                    "loop" => {
                        node.children.push(parse_block(lex, expr)?);
                        ast = AST::While;
                    }
                    "if" => {
                        node.children.push(parse_expression(lex, expr, Precedence::Weakest)?);
                        node.children.push(parse_block(lex, expr)?);

                        if lex.eat_if(|t| t.is_keyword("else"))?.is_some() {
                            if lex.peek(1)?.1.is_keyword("if") {
                                node.children.push(parse_expression(lex, expr, Precedence::Strongest)?);
                            } else {
                                node.children.push(parse_block(lex, expr)?);
                            }
                        }

                        ast = AST::If;
                    }
                    "let" => {
                        let name = lex.expect("variable name", |t| t.is_identifier())?.1.into_identifier();
                        let has_type = lex.eat_if(|t| t.is_char(':'))?.is_some();
                        if has_type {
                            node.children.push(parse_type(lex, expr)?);
                        }
                        if lex.eat_if(|t| t.is_binary_operator(BinaryOperator::Assign))?.is_some() {
                            node.children.push(parse_expression(lex, expr, Precedence::Weakest)?);
                        }
                        ast = AST::Let {name, has_type};
                    }
                    "fn" => {
                        let name = lex.expect("function name", |t| t.is_identifier())?.1.into_identifier();
                        let mut arg_names: Vec<String> = Vec::new();
                        lex.expect("'('", |t| t.is_char('('))?;
                        while lex.eat_if(|t| t.is_char(')'))?.is_none() {
                            let arg_name = lex.expect("arg name", |t| t.is_identifier())?.1.into_identifier();
                            lex.expect("':'", |t| t.is_char(':'))?;
                            node.children.push(parse_type(lex, expr)?);
                            arg_names.push(arg_name);
                        }
                        let has_return_type = lex.eat_if(|t| t.is_arrow())?.is_some();
                        if has_return_type {
                            node.children.push(parse_type(lex, expr)?);
                        }
                        node.children.push(parse_block(lex, expr)?);
                        ast = AST::FunctionDefinition {name, arg_names, has_return_type};
                    }
                    _ => (),
                }
            }
            ast
        }
        Token::BinaryOperator(op) => {
            if op == BinaryOperator::BitXor {
                let e = parse_expression(lex, expr, Precedence::Strongest)?;
                match &mut expr.ast[e.0].a {
                    AST::Variable {from_any_frame, ..} => match op {
                        BinaryOperator::BitXor => *from_any_frame = true,
                        _ => panic!("huh"),
                    }
                    _ => return err!(Syntax, "expected variable name after unary {:?} at {}", op, node.range.start),
                }
                expr.ast[e.0].range.start = node.range.start;
                replace = Some(e);
                AST::Tuple // ignored
            } else {
                let unary_op = match op {
                    BinaryOperator::Sub => UnaryOperator::Neg, // we could easily fuse sign into numeric literal here, but there's no need
                    BinaryOperator::Mul => UnaryOperator::Dereference,
                    BinaryOperator::BitAnd => UnaryOperator::Borrow,
                    op => return err!(Syntax, "expected expression, got {:?} at {}", op, node.range.start),
                };
                let precedence = unary_operator_precedence(unary_op);
                let e = parse_expression(lex, expr, precedence)?;
                node.children.push(e);
                AST::UnaryOperator(unary_op)
            }
        }
        Token::UnaryOperator(unary_op) => match unary_op {
            UnaryOperator::Not => {
                let precedence = unary_operator_precedence(unary_op);
                let e = parse_expression(lex, expr, precedence)?;
                node.children.push(e);
                AST::UnaryOperator(unary_op)
            }
            x => panic!("unexpected lexer output: {:?}", x),
        }
        Token::Char('{') => {
            let i = parse_block(lex, expr)?;
            replace = Some(i);
            AST::Tuple // ignored
        }
        Token::Char('(') => {
            let e = parse_expression(lex, expr, Precedence::Weakest)?;
            let (r, t) = lex.eat(1)?;
            match t {
                Token::Char(')') => { // expression in parens
                    replace = Some(e);
                    AST::Tuple // ignored
                }
                Token::Char(',') => { // tuple
                    lex.eat(1)?;
                    node.children.push(e);
                    while lex.eat_if(|t| t.is_char(')'))?.is_none() {
                        node.children.push(parse_expression(lex, expr, Precedence::Weakest)?);
                        if lex.eat_if(|t| t.is_char(','))?.is_none() {
                            lex.expect("')'", |t| t.is_char(')'))?;
                            break;
                        }
                    }
                    AST::Tuple
                }
                _ => return err!(Syntax, "expected ',' or ')', got {:?} at {}", t, r.start),
            }
        }
        Token::Char('[') => {
            while lex.eat_if(|t| t.is_char(']'))?.is_none() {
                node.children.push(parse_expression(lex, expr, Precedence::Weakest)?);
                if lex.eat_if(|t| t.is_char(','))?.is_none() {
                    lex.peek_expect("']'", |t| t.is_char(']'))?;
                }
            }
            AST::Array
        }
        t => return err!(Syntax, "expected expression, got {:?} at {}", t, node.range.start),
    };
    let mut node_idx = if let Some(idx) = replace {
        idx
    } else {
        node.range.end = lex.previous_token_end;
        expr.ast.push(node);
        ASTIdx(expr.ast.len()-1)
    };

    loop {
        let (range, token) = lex.peek(1)?;
        match token {
            &Token::BinaryOperator(op) => {
                let precedence = binary_operator_precedence(op);
                if outer_precedence >= precedence { // left to right associativity (for right-to-left use '>'; for requiring parens, keep track of previous precedences in the loop)
                    break;
                }
                lex.eat(1)?;
                let rhs = parse_expression(lex, expr, precedence)?;
                let node = ASTNode {range: expr.ast[node_idx.0].range.start..expr.ast[rhs.0].range.end, children: vec![node_idx, rhs], a: AST::BinaryOperator(op)};
                expr.ast.push(node);
                node_idx = ASTIdx(expr.ast.len()-1);
            }
            Token::Char('(') => {
                if outer_precedence >= Precedence::CallOrIndex {
                    break;
                }
                lex.eat(1)?;
                match &expr.ast[node_idx.0].a {
                    AST::Variable {name, quoted, from_any_frame} if !quoted && !from_any_frame => {
                        let name = name.clone();
                        if name == "type" {
                            let t = parse_type(lex, expr)?;
                            expr.ast[node_idx.0].children.push(t);
                            expr.ast[node_idx.0].a = AST::TypeInfo;
                        } else {
                            while !lex.peek(1)?.1.is_char(')') {
                                let ex = parse_expression(lex, expr, Precedence::Weakest)?;
                                expr.ast[node_idx.0].children.push(ex);
                                if lex.eat_if(|t| t.is_char(','))?.is_none() {
                                    lex.peek_expect("')'", |t| t.is_char(')'))?;
                                }
                            }
                            expr.ast[node_idx.0].a = AST::Call(name);
                        }
                        let (r, _) = lex.expect("')'", |t| t.is_char(')'))?;
                        expr.ast[node_idx.0].range.end = r.end;
                    }
                    _ => return err!(Syntax, "expression can't be called at {}", range.start),
                }
            }
            Token::Char('[') => {
                if outer_precedence >= Precedence::CallOrIndex {
                    break;
                }
                lex.eat(1)?;
                let rhs = parse_expression(lex, expr, Precedence::Weakest)?;
                lex.expect("']'", |t| t.is_char(']'))?;
                let node = ASTNode {range: expr.ast[node_idx.0].range.start..expr.ast[rhs.0].range.end, children: vec![node_idx, rhs], a: AST::BinaryOperator(BinaryOperator::Index)};
                expr.ast.push(node);
                node_idx = ASTIdx(expr.ast.len()-1);
            }
            Token::Char('.') => {
                if outer_precedence >= Precedence::Field {
                    break;
                }
                lex.eat(1)?;
                let (r, t) = lex.eat(1)?;
                let mut node = ASTNode {range: expr.ast[node_idx.0].range.start..r.end, children: vec![node_idx], a: AST::Tuple};
                let a = match t {
                    Token::Identifier {s, quoted} => {
                        AST::Field {name: s, quoted}
                    }
                    Token::Literal(value) if value.is_unsigned() => {
                        AST::TupleIndexing(value.as_unsigned().unwrap())
                    }
                    Token::Char('[') => {
                        node.children.push(parse_expression(lex, expr, Precedence::Weakest)?);
                        lex.expect("']'", |t| t.is_char(']'))?;
                        AST::BinaryOperator(BinaryOperator::Slicify)
                    }
                    _ => return err!(Syntax, "expected field name, got {:?} at {}", t, r.start),
                };
                node.a = a;
                expr.ast.push(node);
                node_idx = ASTIdx(expr.ast.len()-1);
            }
            Token::Identifier{s, quoted} if !quoted && s == "as" => {
                if outer_precedence >= Precedence::TypeCast {
                    break;
                }
                lex.eat(1)?;
                let type_idx = parse_type(lex, expr)?;
                let node = ASTNode {range: expr.ast[node_idx.0].range.start..expr.ast[type_idx.0].range.end, children: vec![node_idx, type_idx], a: AST::TypeCast};
                expr.ast.push(node);
                node_idx = ASTIdx(expr.ast.len()-1);
            }
            _ => break,
        }
    }

    Ok(node_idx)
}

// Operator precedence.
#[derive(Eq, PartialEq, Ord, PartialOrd, Debug)]
enum Precedence {
    Weakest,

    Return, // return
    Assign, // = += -= *= /= %= &= |= ^= <<= >>=
    Range, // .. ..=
    LazyOr, // ||
    LazyAnd, // &&
    Cmp, // == != < > <= >=
    Or, // |
    Xor, // ^
    And, // &
    Shift, // << >>
    Add, // + -
    Mul, // * / %
    TypeCast, // x as i64
    Unary, // -x, !b, &v, *p
    CallOrIndex, // f(x), a[i]
    Field, // a.b

    Strongest,
}

fn binary_operator_precedence(op: BinaryOperator) -> Precedence {
    match op {
        BinaryOperator::Add | BinaryOperator::Sub => Precedence::Add,
        BinaryOperator::Mul | BinaryOperator::Div | BinaryOperator::Rem => Precedence::Mul,
        BinaryOperator::BitAnd => Precedence::And,
        BinaryOperator::BitOr => Precedence::Or,
        BinaryOperator::BitXor => Precedence::Xor,
        BinaryOperator::Shl | BinaryOperator::Shr => Precedence::Shift,
        BinaryOperator::Eq | BinaryOperator::Ne | BinaryOperator::Gt | BinaryOperator::Lt | BinaryOperator::Ge | BinaryOperator::Le => Precedence::Cmp,
        BinaryOperator::LazyAnd => Precedence::LazyAnd,
        BinaryOperator::LazyOr => Precedence::LazyOr,
        BinaryOperator::Assign | BinaryOperator::AddAssign | BinaryOperator::SubAssign | BinaryOperator::MulAssign | BinaryOperator::DivAssign | BinaryOperator::RemAssign
            | BinaryOperator::AndAssign | BinaryOperator::OrAssign | BinaryOperator::XorAssign | BinaryOperator::ShlAssign | BinaryOperator::ShrAssign => Precedence::Assign,
        BinaryOperator::Range => Precedence::Range,
        BinaryOperator::Index => Precedence::CallOrIndex,
        BinaryOperator::Slicify => Precedence::Field,
    }
}

fn unary_operator_precedence(_op: UnaryOperator) -> Precedence {
    Precedence::Unary
}
