use crate::{*, error::{*, Result, Error}, util::*, registers::*, types::*, procfs::*, symbols_registry::*, process_info::*, unwind::*, symbols::*, arena::*, pretty::*, settings::*, common_ui::*, dwarf::*};
use std::{fmt, fmt::Write, mem, collections::{HashMap, HashSet}, io::Write as ioWrite, borrow::Cow, ops::Range, path::Path};
use gimli::{Operation, Expression, Encoding, EvaluationResult, ValueType, DieReference, DW_AT_location, Location, DebugInfoOffset, Reader};
use bitflags::*;
use rand::random;

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

    pub fn from_two_usizes(s: [usize; 2]) -> Self {
        Self::Small([s[0], s[1], 0])
    }

    pub fn from_u64_slice(val: &[u64]) -> Self {
        let mut vec: Vec<u8> = Vec::with_capacity(val.len() * 8);
        for &x in val {
            vec.extend_from_slice(&x.to_le_bytes());
        }
        Self::from_vec(vec)
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
    pub fn get_usize_at(&self, offset: usize) -> Result<usize> {
        let s = self.as_slice();
        if offset + 8 > s.len() {
            return err!(Internal, "blob offset out of bounds: {}+8 > {}", offset, s.len());
        }
        let mut a = [0u8; 8];
        a.copy_from_slice(&s[offset..offset+8]);
        Ok(usize::from_le_bytes(a))
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
        other.add_low_bits(shift); // (this number is added to the index of each bit)
        let self_whole_bytes = self_bits/8;
        // i - bit_offset + self_bits = i + shift - skip_bytes*8 + self_bits/8*8
        // skip_bytes*8 = bit_offset - self_bits&7 + shift
        let skip_bytes = 2 + bit_offset/8;
        self.bitwise_or(self_whole_bytes, &other, skip_bytes, total_bytes - self_whole_bytes);
    }
    pub fn add_low_bits(&mut self, bits: usize) { // bit from position i goes to position i+bits
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
    pub fn remove_low_bits(&mut self, bits: usize) {
        let bytes = self.capacity();
        if bits > bytes*8 {
            panic!("tried to remove {} bits from {}-byte value", bits, bytes);
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
            res.remove_low_bits(bit_offset & 7);
            res.resize((bit_size + 7)/8);
        }
        if bit_size & 7 != 0 {
            res.zero_upper_bits(bit_size);
        }
        Ok(res)
    }

    pub fn byte_range(&self, r: Range<usize>) -> Result<Self> {
        let slice = self.as_slice();
        if r.end > slice.len() {
            return err!(Runtime, "blob slice out of bounds: [{}, {}) > {}", r.start, r.end, slice.len());
        }
        Ok(Self::from_slice(&slice[r]))
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
    pub fn into_value(self, bytes: usize, memory: &mut CachedMemReader) -> Result<ValueBlob> {
        Ok(match self {
            Self::Blob(b) => {
                if b.capacity() < bytes {
                    return err!(Dwarf, "value too short: ~{} < {}", b.capacity(), bytes);
                }
                b
            }
            Self::Addr(a) => {
                if bytes > (100 << 20) {
                    return err!(Sanity, "value too long (over 100 MiB)");
                }
                let mut b = ValueBlob::with_capacity(bytes);
                memory.read(a, &mut b.as_mut_slice()[..bytes])?;
                b
            }
        })
    }

    pub fn addr(&self) -> Option<usize> { match self { Self::Addr(a) => Some(*a), _ => None } }
    pub fn blob_ref(&self) -> Option<&ValueBlob> { match self { Self::Blob(b) => Some(b), _ => None } }

    pub fn byte_range(&self, offset: Range<usize>, memory: &mut CachedMemReader) -> Result<Self> {
        match self {
            &Self::Addr(addr) if addr > usize::MAX - offset.start => err!(ProcessState, "address overflow: 0x{} + {}", addr, offset.start),
            &Self::Addr(addr) => Ok(Self::Addr(addr + offset.start)),
            Self::Blob(blob) => Ok(Self::Blob(blob.byte_range(offset)?)),
        }
    }

    pub fn bit_range(&self, bit_offset: Range<usize>, memory: &mut CachedMemReader) -> Result<usize> {
        assert!(bit_offset.len() <= 64);
        let mut a = [0u8; 9];
        let byte_offset = bit_offset.start/8..(bit_offset.end+7)/8;
        match self {
            Self::Blob(b) => {
                if bit_offset.end > b.capacity() * 64 {
                    return err!(Dwarf, "value too short: ~{} < {}", b.capacity(), (bit_offset.end + 63) / 64);
                }
                a[..byte_offset.len()].copy_from_slice(&b.as_slice()[byte_offset.clone()]);
            }
            Self::Addr(addr) => memory.read(addr.saturating_add(byte_offset.start), &mut a[..byte_offset.len()])?,
        }

        // Why, Rust?
        let mut b = [0u8; 8];
        b.copy_from_slice(&a[..8]);
        let mut r = usize::from_le_bytes(b);

        if bit_offset.start%8 != 0 {
            r >>= (bit_offset.start%8) as u32;
        }
        if bit_offset.end%8 != 0 {
            let e = a[byte_offset.len() - 1];
            let e = e & ((1u8 << (bit_offset.end%8) as u32) - 1);
            r &= !(0xffusize << (bit_offset.len() - bit_offset.end%8) as u32);
            r |= (e as usize) << (bit_offset.len() - bit_offset.end%8) as u32;
        }

        Ok(r)
    }

    pub fn get_usize(&self, memory: &mut CachedMemReader) -> Result<usize> {
        match self {
            &Self::Addr(addr) => memory.read_usize(addr),
            Self::Blob(blob) => blob.get_usize(),
        }
    }
    pub fn get_usize_prefix(&self, memory: &mut CachedMemReader) -> Result<usize> {
        match self {
            &Self::Addr(addr) => memory.read_usize(addr),
            Self::Blob(blob) => Ok(blob.get_usize_prefix()),
        }
    }
    pub fn get_usize_at(&self, offset: usize, memory: &mut CachedMemReader) -> Result<usize> {
        match self {
            &Self::Addr(addr) => memory.read_usize(addr + offset),
            Self::Blob(blob) => blob.get_usize_at(offset),
        }
    }
}

pub fn format_dwarf_expression<'a>(expr: Expression<DwarfSlice>, encoding: Encoding) -> Result<String> {
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
                if let Some(r) = RegisterIdx::from_dwarf(register) {
                    write!(res, "{}", r)
                } else if let Some(r) = ExtraRegisterIdx::from_dwarf(register) {
                    write!(res, "{}", r)
                } else {
                    write!(res, "register({})", register.0)
                }?;
                if offset != 0 {
                    write!(res, "{}0x{:x}", if offset < 0 {"-"} else {"+"}, offset.abs())?;
                }
                if base_type.0 != 0 {
                    write!(res, "(type@u+0x{:x})", base_type.0)?;
                }
            }
            Operation::FrameOffset {offset} => {
                write!(res, "fb")?;
                if offset != 0 {
                    write!(res, "{}0x{:x}", if offset < 0 {"-"} else {"+"}, offset.abs())?;
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
                if let Some(r) = RegisterIdx::from_dwarf(register) {
                    write!(res, "{}", r)
                } else if let Some(r) = ExtraRegisterIdx::from_dwarf(register) {
                    write!(res, "{}", r)
                } else {
                    write!(res, "register({})", register.0)
                }?;
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
        Self { currently_evaluated_value_dubious: false, types, builtin_types, variables: HashMap::new() } }

    pub fn clear(&mut self) {
        self.types = Types::new();
        self.builtin_types = self.types.add_builtins();
        self.variables.clear();
    }

    pub fn get_variable(&mut self, context: &mut EvalContext, name: &str, maybe_register: bool, from_any_frame: bool, only_type: bool, meta: bool) -> Result<Value> {
        assert!(!meta || (!maybe_register && !only_type));
        let global_alt_name = if name.starts_with("::") {Some(&name[2..])} else {None};
        if !context.stack.frames.is_empty() && (global_alt_name.is_none() || from_any_frame) {
            // Try register.
            if maybe_register {
                if let Some(reg) = RegisterIdx::parse_ignore_case(name) {
                    let type_ = self.builtin_types.u64_;
                    if only_type {
                        return Ok(Value {val: Default::default(), type_, flags: ValueFlags::empty()});
                    }
                    let frame = &context.stack.frames[context.stack.subframes[context.selected_subframe].frame_idx];
                    return match frame.regs.get(reg) {
                        Ok((v, dub)) => {
                            self.currently_evaluated_value_dubious |= dub;
                            Ok(Value {val: AddrOrValueBlob::Blob(ValueBlob::new(v as usize)), type_, flags: ValueFlags::empty()})
                        }
                        Err(_) => err!(Dwarf, "value of {} register is not known", reg),
                    };
                } else if let Some(reg) = ExtraRegisterIdx::parse_ignore_case(name) {
                    if only_type {
                        let buf = [0u64; 8];
                        assert!(reg.len <= buf.len());
                        let val = &buf[..reg.len];
                        return Ok(self.make_extra_register_value(val));
                    }
                    if let &Some(regs) = &context.extra_regs {
                        let regs = regs.get();
                        let (val, dub) = regs.get(reg)?;
                        self.currently_evaluated_value_dubious |= dub;
                        return Ok(self.make_extra_register_value(val));
                    }
                }
            }

            // Try local variable.
            for relative_subframe_idx in 0..context.stack.subframes.len().min(if from_any_frame {usize::MAX} else {1}) {
                let subframe_idx = (context.selected_subframe + relative_subframe_idx) % context.stack.subframes.len();
                let mut found = false;
                match self.get_local_variable(context, name, subframe_idx, only_type, meta, &mut found) {
                    Ok(v) => return Ok(v),
                    Err(e) if found => return Err(e),
                    Err(_) => (),
                }
            }
        }

        // Try global variable.
        for binary in context.symbols_registry.iter() {
            let symbols = match &binary.symbols {
                Ok(x) => x,
                Err(_) => continue };
            let mut v = symbols.find_global_variable_by_name(name);
            if v.is_none() {
                if let &Some(alt) = &global_alt_name {
                    v = symbols.find_global_variable_by_name(alt);
                }
            }
            let v = match v {
                Some(x) => x,
                None => continue,
            };
            if meta {
                let type_ = symbols.builtin_types.meta_variable;
                let blob = ValueBlob::from_two_usizes([binary.id, v as *const Variable as usize]);
                return Ok(Value {val: AddrOrValueBlob::Blob(blob), type_, flags: ValueFlags::empty()});
            }
            if only_type {
                return Ok(Value {val: Default::default(), type_: v.type_, flags: ValueFlags::empty()});
            }
            return Self::get_global_variable(&mut self.currently_evaluated_value_dubious, context, v, binary, only_type);
        }

        if context.stack.frames.is_empty() && global_alt_name.is_none() {
            // If the process is running or absent, show error like "<running>" instead of "<variable foo not found>".
            context.check_has_stack()?;
        }

        err!(NoVariable, "variable {} not found", name)
    }

    pub fn get_type(&mut self, context: &mut EvalContext, name: &str) -> Result<*const TypeInfo> {
        for binary in context.symbols_registry.iter() {
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

    // TODO: Check that the value size is not too small, in both get_*_variable(). Often debug info has invalid (?) expressions that return 8 bytes instead of sizeof(struct). E.g. I saw that for `fde` in list_lsdas().
    
    fn get_local_variable(&mut self, context: &mut EvalContext, name: &str, subframe_idx: usize, only_type: bool, meta: bool, found: &mut bool) -> Result<Value> {
        context.check_has_stack()?;
        let subframe = &context.stack.subframes[subframe_idx];
        let frame = &context.stack.frames[subframe.frame_idx];
        let pseudo_addr = frame.pseudo_addr;
        let (mut dwarf_context, _) = context.make_local_dwarf_eval_context(subframe_idx)?;
        let static_pseudo_addr = dwarf_context.addr_map.dynamic_to_static(pseudo_addr);
        for v in dwarf_context.local_variables {
            if !v.range().contains(&(static_pseudo_addr)) || unsafe {v.name()} != name {
                continue;
            }
            *found = true;
            if meta {
                let type_ = dwarf_context.symbols.clone().unwrap().builtin_types.meta_variable;
                let blob = ValueBlob::from_two_usizes([frame.binary_id.clone()?, v as *const Variable as usize]);
                return Ok(Value {val: AddrOrValueBlob::Blob(blob), type_, flags: ValueFlags::empty()});
            }
            if only_type {
                return Ok(Value {val: Default::default(), type_: v.type_, flags: ValueFlags::empty()});
            }
            let (val, dubious) = eval_variable(&v.location, &mut dwarf_context)?;
            self.currently_evaluated_value_dubious |= dubious;
            return Ok(Value {val, type_: v.type_, flags: ValueFlags::empty()});
        }
        err!(NoVariable, "")
    }

    pub fn get_global_variable(currently_evaluated_value_dubious: &mut bool, context: &mut EvalContext, var: &Variable, binary: &Binary, only_type: bool) -> Result<Value> {
        let (val, dubious) = if only_type {
            (Default::default(), false)
        } else {
            match var.location.unpack() {
                VariableLocation::Const(s) => (AddrOrValueBlob::Blob(ValueBlob::from_slice(s)), false),
                VariableLocation::Expr(e) => {
                    let mut dwarf_context = context.make_global_dwarf_eval_context(binary, var.debug_info_offset().unwrap())?;
                    eval_dwarf_expression(e, &mut dwarf_context)?
                }
                VariableLocation::Unknown => return err!(Dwarf, "location unknown"),
            }
        };
        *currently_evaluated_value_dubious |= dubious;
        Ok(Value {val, type_: var.type_, flags: ValueFlags::empty()})
    }

    pub fn make_extra_register_value(&mut self, val: &[u64]) -> Value {
        assert!(!val.is_empty());
        if val.len() == 1 {
            return Value {val: AddrOrValueBlob::Blob(ValueBlob::new(val[0] as usize)), type_: self.builtin_types.u64_, flags: ValueFlags::HEX};
        }
        let array_type = self.types.add_array(self.builtin_types.u64_, Some(val.len()), ArrayFlags::empty());
        let blob = ValueBlob::from_u64_slice(val);
        Value {val: AddrOrValueBlob::Blob(blob), type_: array_type, flags: ValueFlags::HEX}
    }
}

pub struct EvalContext<'a> {
    pub symbols_registry: &'a SymbolsRegistry,

    // If there's no process, reads will return "no process" error.
    pub memory: CachedMemReader,
    pub process_info: &'a ProcessInfo,

    // We include the whole stack to allow watch expressions to use variables from other frames.
    // Empty if the thread is running.
    pub stack: &'a StackTrace,
    pub selected_subframe: usize,

    pub extra_regs: Option<&'a LazyExtraRegisters>,
    pub fs_base: Option<u64>, // same as FsBase register in `stack`, but present even if `stack` is empty (when program is running)
}
impl EvalContext<'_> {
    pub fn check_has_stack(&self) -> Result<()> {
        self.memory.mem.check_valid()?;
        if self.stack.frames.is_empty() {
            return err!(ProcessState, "running");
        }
        Ok(())
    }
    
    // Collect information needed to retrieve values of local variables.
    pub fn make_local_dwarf_eval_context<'a>(&'a mut self, selected_subframe: usize) -> Result<(DwarfEvalContext<'a>, &'a FunctionInfo)> {
        self.check_has_stack()?;
        let subframe = &self.stack.subframes[selected_subframe];
        let selected_frame = subframe.frame_idx;
        let frame = &self.stack.frames[selected_frame];
        let function_idx = self.stack.subframes[frame.subframes.end-1].function_idx.clone()?;
        let binary_id = frame.binary_id.clone()?;
        let subfunction_idx = match &subframe.subfunction_idx {
            None => return err!(Dwarf, "function has no debug info"),
            Some(x) => *x,
        };
        let binary = match self.symbols_registry.get(binary_id) {
            None => return err!(Internal, "binary was unloaded after generating backtrace"),
            Some(x) => x,
        };
        let symbols = binary.symbols.as_ref_clone_error()?;
        let function = &symbols.functions[function_idx];
        let unit = match function.debug_info_offset() {
            None => return err!(ProcessState, "function has no debug info"),
            Some(off) => symbols.find_unit(off)? };
        let shard_idx = function.shard_idx();
        let subfunction = &symbols.shards[shard_idx].subfunctions[subfunction_idx];
        let local_variables = symbols.local_variables_in_subfunction(subfunction, shard_idx);

        let context = DwarfEvalContext {memory: &mut self.memory, symbols: Some(symbols), addr_map: &binary.addr_map, tls_offset: &binary.tls_offset, encoding: unit.unit.header.encoding(), unit: Some(unit), regs: Some(&frame.regs), extra_regs: self.extra_regs.clone(), frame_base: Some(&frame.frame_base), local_variables, fs_base: self.fs_base.clone()};
        Ok((context, function))
    }

    pub fn make_global_dwarf_eval_context<'a>(&'a mut self, binary: &'a Binary, die_offset: DebugInfoOffset) -> Result<DwarfEvalContext<'a>> {
        let symbols = binary.symbols.as_ref_clone_error()?;
        let unit = symbols.find_unit(die_offset)?;
        Ok(DwarfEvalContext {memory: &mut self.memory, symbols: Some(symbols), addr_map: &binary.addr_map, tls_offset: &binary.tls_offset, encoding: unit.unit.header.encoding(), unit: Some(unit), regs: None, extra_regs: None, frame_base: None, local_variables: &[], fs_base: self.fs_base.clone()})
    }
}

bitflags! { pub struct ValueFlags: u16 {
    // Ignore pretty printers. Affects formatting, field access, dereferencing (for smart pointers), indexing (for containers).
    const RAW = 0x1;

    const HEX = 0x2;
    const BIN = 0x4;

    // Similar to RAW, disables automatic unwrapping of single-field structs by prettifier. Doesn't do any of the other RAW things.
    // Can't be changed by the user. Used for structs produced by MetaType/MetaField/etc.
    const NO_UNWRAPPING_INTERNAL = 0x8;
    // When formatting value, print struct name. Used after automatic downcasting. Not inherited by fields.
    const SHOW_TYPE_NAME = 0x10;

    // Force prettified value where normally raw value would be used (e.g. typeof(x.#p)). Mutually exclusive with RAW.
    const PRETTY = 0x20;

    // Interpret integers as big-endian.
    // (The implementation of this is pretty error-prone, it's easy to miss a code site that needs to check this flag and flip endianness. Idk what to do about it.)
    const BIG_ENDIAN = 0x40;
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

pub enum ValueChildKind {
    ArrayElement(usize),
    ArrayTail(usize),
    StructField, // field name is child name in ValueChildInfo
    Other,
}

#[derive(Clone)]
pub enum ValueClickAction {
    None,
    // This value represents code location, jump to it on click.
    CodeLocation(FileLineInfo),
    Function {binary_id: usize, function_idx: usize, static_addr: usize},
}
impl ValueClickAction {
    pub fn is_none(&self) -> bool { match self { Self::None => true, _ => false } }
}

pub struct ValueChildInfo {
    pub identity: usize,
    pub name_line: usize, // line in `names_out` given to format_value()
    pub kind: ValueChildKind,
    pub deref: usize, // how many layers of pointers (but not references) we dereferenced between the parent and this child; kind of an extension of `kind`
    pub value: Result<Value>,
}

// Prints the value human-readably to the unclosed line of `out`.
// If `expanded`, also lists the "children" of the value, e.g. struct fields or array elements. Their names are formatted into `names_out`.
// `has_children` is returned even if expanded = false; it tells whether the value "logically" has children, even if there are 0 of them (e.g. empty array).
// The format can depend on `expanded`, e.g. array and struct contents are omitted (because they should be visible as children instead).
// Doesn't close the line in `out`, the caller should do it.
pub fn format_value(v: &Value, expanded: bool, state: &mut EvalState, context: &mut EvalContext, out: &mut StyledText, names_out: &mut StyledText, palette: &Palette) -> (/*has_children*/ bool, /*children*/ Vec<ValueChildInfo>, ValueClickAction) {
    let (text_start_lines, text_start_chars) = (out.lines.len(), out.chars.len());
    format_value_recurse(v, false, &mut FormatValueState {expanded, state, context, out, names_out, palette, text_start_lines, text_start_chars})
}

struct FormatValueState<'a, 'b> {
    expanded: bool,
    state: &'a mut EvalState,
    context: &'a mut EvalContext<'b>,
    out: &'a mut StyledText,
    names_out: &'a mut StyledText,
    palette: &'a Palette,
    text_start_lines: usize,
    text_start_chars: usize,
}
impl<'a, 'b> FormatValueState<'a, 'b> {
    fn over_output_limit(&self) -> bool {
        // (Currently we don't produce multiple lines, but have a line limit anyway in case we do it in future, e.g. for printing matrices.)
        self.out.chars.len() - self.text_start_chars > 10000 || self.out.lines.len() - self.text_start_lines > 100 || (self.out.lines.len() == self.text_start_lines && self.out.chars.len() - self.text_start_chars > 1000)
    }
}

fn format_value_recurse(v: &Value, address_already_shown: bool, state: &mut FormatValueState) -> (/*has_children*/ bool, /*children*/ Vec<ValueChildInfo>, ValueClickAction) {
    let mut click_action = ValueClickAction::None;

    // Output length limit. Also acts as recursion depth limit.
    if state.over_output_limit() {
        styled_write!(state.out, state.palette.truncation_indicator.2, "{}", state.palette.truncation_indicator.1);
        return (false, Vec::new(), click_action);
    }

    let write_address = |addr: usize, state: &mut FormatValueState| {
        styled_write!(state.out, state.palette.value_misc, "&0x{:x} ", addr);
    };
    let write_val_address_if_needed = |v: &AddrOrValueBlob, state: &mut FormatValueState| {
        if let AddrOrValueBlob::Addr(a) = v {
            if !address_already_shown {
                write_address(*a, state);
            }
        }
    };
    let list_struct_children = |value: &AddrOrValueBlob, s: &StructType, flags: ValueFlags, state: &mut FormatValueState| -> Vec<ValueChildInfo> {
        s.fields().iter().enumerate().map(|(field_idx, field)| {
            let name_line = if field.name.is_empty() {
                styled_writeln!(state.names_out, state.palette.value_misc, "{}", field_idx)
            } else {
                styled_writeln!(state.names_out, state.palette.field_name, "{}", field.name)
            };
            let value = match get_struct_field(value, field, &mut state.context.memory) {
                Ok(val) => Ok(Value {val, type_: field.type_, flags: flags.inherit()}),
                Err(e) => Err(e),
            };
            ValueChildInfo {identity: hash(&(field_idx, field.name)), name_line, kind: ValueChildKind::StructField, deref: 0, value}
        }).collect()
    };

    let mut v = Cow::Borrowed(v);
    if !v.flags.contains(ValueFlags::RAW) {
        let mut warning = None;
        match prettify_value(&mut v, &mut warning, state.state, state.context) {
            Ok(()) => if let Some(w) = warning {
                styled_write!(state.out, state.palette.error, "<{}> ", w);
            }
            Err(e) => {
                write_val_address_if_needed(&v.val, state);
                styled_write!(state.out, state.palette.error, "<{}>", e);
                return (false, Vec::new(), click_action);
            }
        }
    }

    let mut children: Vec<ValueChildInfo> = Vec::new();
    let t = unsafe {&*v.type_};
    let size = t.calculate_size();
    let usize_prefix = if size == 0 {
        0
    } else {
        match v.val.get_usize_prefix(&mut state.context.memory) {
            Ok(mut x) => {
                if size < 8 {
                    x &= usize::MAX >> (64 - size as u32 * 8);
                }
                x
            }
            Err(e) => {
                write_val_address_if_needed(&v.val, state);
                styled_write!(state.out, state.palette.error, "<{}>", e);
                return (false, children, click_action);
            }
        }
    };

    match &t.t {
        Type::Unknown => {
            write_val_address_if_needed(&v.val, state);
            styled_write!(state.out, state.palette.value_misc, "0x{:x} ", usize_prefix);
            styled_write!(state.out, state.palette.error, "<unknown type>");
        }
        // `value` can be longer than the type's `size` e.g. if a 4-byte value is stored in an 8-byte register.
        // It can even be longer than 8 bytes if it's stored in a wider register, e.g. float stored in zmm0 (aka xmm0 or ymm0).
        Type::Primitive(p) => match usize_prefix {
            _ if size == 0 => styled_write!(state.out, state.palette.value_misc, "()"), // covers things like void, decltype(nullptr), rust empty tuple, rust `!` type
            mut x if size <= 8 => {
                let as_number = v.flags.intersects(ValueFlags::RAW | ValueFlags::HEX | ValueFlags::BIN);
                if p.contains(PrimitiveFlags::FLOAT) {
                    match size {
                        4 => styled_write!(state.out, state.palette.value, "{:?}", f32::from_bits(x as u32)),
                        8 => styled_write!(state.out, state.palette.value, "{:?}", f64::from_bits(x as u64)),
                        _ => styled_write!(state.out, state.palette.error, "<bad size: {}>", size),
                    }
                } else if p.contains(PrimitiveFlags::UNSPECIFIED) {
                    write_val_address_if_needed(&v.val, state);
                    flip_endianness_if_needed(&mut x, size, v.flags);
                    styled_write!(state.out, state.palette.value_misc, "<unspecified type> 0x{:x}", x);
                } else if p.contains(PrimitiveFlags::CHAR) && !as_number {
                    if size > 4 {
                        styled_write!(state.out, state.palette.error, "<bad char size: {}>", size);
                    } else if let Some(c) = char::from_u32(x as u32) {
                        styled_write!(state.out, state.palette.value, "{} '{}'", c as u32, c);
                    } else {
                        styled_write!(state.out, state.palette.value, "{}", x);
                    }
                } else if p.contains(PrimitiveFlags::BOOL) && !as_number {
                    match x {
                        0 => styled_write!(state.out, state.palette.value, "false"),
                        1 => styled_write!(state.out, state.palette.value, "true"),
                        _ => styled_write!(state.out, state.palette.warning, "{}", x),
                    }
                } else {
                    flip_endianness_if_needed(&mut x, size, v.flags);
                    // Sign-extend.
                    let signed = p.contains(PrimitiveFlags::SIGNED);
                    if signed && size < 8 && x & 1 << (size*8-1) as u32 != 0 {
                        x |= !((1usize << size*8)-1);
                    }
                    format_integer(x, size, signed, v.flags, state.out, state.palette);
                }
            }
            _ => styled_write!(state.out, state.palette.error, "<bad size: {}>", size),
        }
        Type::Pointer(p) => if p.flags.contains(PointerFlags::REFERENCE) {
            //write_address(x, state);
            return format_value_recurse(&Value {val: AddrOrValueBlob::Addr(usize_prefix), type_: p.type_, flags: v.flags.inherit()}, true, state);
        } else if unsafe {(*p.type_).t.is_function()} {
            format_function_pointer(usize_prefix, state, &mut click_action);
        } else {
            styled_write!(state.out, if state.expanded {state.palette.value_misc} else {state.palette.value}, "*0x{:x} ", usize_prefix);
            let t = unsafe {&*p.type_};
            if usize_prefix == 0 || (t.flags.contains(TypeFlags::SIZE_KNOWN) && t.size == 0) { // don't expand nullptr and void*
                return (false, children, click_action);
            }
            if !state.expanded {
                return (true, children, click_action);
            }
            if !try_format_as_string(&AddrOrValueBlob::Addr(usize_prefix), p.type_, None, false, v.flags, &mut state.context.memory, "", state.out, state.palette) {
                // If expanded, act like a reference, i.e. expand the pointee.
                (_, children, _) = format_value_recurse(&Value {val: AddrOrValueBlob::Addr(usize_prefix), type_: p.type_, flags: v.flags.inherit()}, true, state);
                for c in &mut children {
                    c.deref += 1;
                }
            }
            return (true, children, click_action);
        }
        Type::PointerToMember(p) => {
            styled_write!(state.out, state.palette.value, "0x{:x}", usize_prefix);
            styled_write!(state.out, state.palette.value_misc, " (");
            let mut found = false;
            if let Type::Struct(s) = unsafe {&(*p.containing_type).t} {
                for field in s.fields() {
                    if field.bit_offset == usize_prefix * 8 {
                        styled_write!(state.out, state.palette.field_name, "{}", field.name);
                        found = true;
                        break;
                    }
                }
            }
            if !found {
                styled_write!(state.out, state.palette.error, "?");
            }
            styled_write!(state.out, state.palette.value_misc, ")");
        }
        Type::Function => {
            match &v.val {
                &AddrOrValueBlob::Addr(addr) => {
                    format_function_pointer(addr, state, &mut click_action);
                }
                AddrOrValueBlob::Blob(_) => {
                    styled_write!(state.out, state.palette.error, "<function with unknown address>");
                }
            }
        }
        Type::Array(a) => {
            format_array(a.type_, if a.flags.contains(ArrayFlags::LEN_KNOWN) {Some(a.len)} else {None}, a.stride, &v.val, a.flags.contains(ArrayFlags::UTF_STRING), a.flags.contains(ArrayFlags::TRUNCATED), v.flags, state, &mut children);
            return (true, children, click_action);
        }
        Type::Slice(s) => {
            let blob = match &v.val {
                AddrOrValueBlob::Blob(x) => x,
                AddrOrValueBlob::Addr(_) => panic!("unexpected slice ref") };
            let addr = blob.get_usize_at(0).unwrap();
            let len = blob.get_usize_at(8).unwrap();
            format_array(s.type_, Some(len), 0, &AddrOrValueBlob::Addr(addr), s.flags.contains(SliceFlags::UTF_STRING), /*is_truncated*/ false, v.flags, state, &mut children);
            return (true, children, click_action);
        }
        Type::Struct(s) => {
            children = list_struct_children(&v.val, s, v.flags, state);
            if v.flags.contains(ValueFlags::SHOW_TYPE_NAME) || (state.expanded && (!t.name.is_empty() || t.die.0 != 0)) {
                if t.name.is_empty() {
                    // TODO: Print file+line instead of DIE offset.
                    styled_write!(state.out, state.palette.value_misc, "<{} @{:x}> ", t.t.kind_name(), t.die.0);
                } else {
                    let limit = 100;
                    if v.flags.contains(ValueFlags::SHOW_TYPE_NAME) || t.name.len() <= limit {
                        styled_write!(state.out, state.palette.type_name, "{} ", t.name);
                    } else {
                        // Truncate long type names to avoid filling up half the window with nonsense C++ template names.
                        // Instead of truncating here, it would be better to tell the caller to reduce height limit for this row (to e.g. 2 lines).
                        let mut i = limit;
                        while !t.name.is_char_boundary(i) {
                            i -= 1;
                        }
                        styled_write!(state.out, state.palette.type_name, "{} ", t.name);
                        styled_write!(state.out, state.palette.truncation_indicator.2, "{} ", state.palette.truncation_indicator.1);
                    }
                }
            }
            if !state.expanded {
                styled_write!(state.out, state.palette.value_misc, "{{");
                for (idx, child) in children.iter().enumerate() {
                    if idx != 0 {
                        styled_write!(state.out, state.palette.value_misc, ", ");
                    }

                    state.out.import_spans(state.names_out, state.names_out.get_line(child.name_line));
                    styled_write!(state.out, state.palette.value_misc, ": ");

                    match &child.value {
                        Ok(v) => {
                            format_value_recurse(v, false, state);
                        }
                        Err(e) => styled_write!(state.out, state.palette.error, "<{}>", e),
                    }
                }
                if children.is_empty() && t.flags.contains(TypeFlags::DECLARATION) {
                    // This can happen e.g. if the file with definition was compiled without debug symbols.
                    styled_write!(state.out, state.palette.error, "<missing type definition>");
                }
                styled_write!(state.out, state.palette.value_misc, "}}");
            }
        }
        Type::Enum(e) => {
            let mut x = usize_prefix;
            let et = unsafe {&*e.type_};
            let (mut size, signed) = match &et.t {
                Type::Primitive(p) => (et.size, p.contains(PrimitiveFlags::SIGNED)),
                _ => (8, false),
            };
            if size != 1 && size != 2 && size != 4 && size != 8 {
                size = 8;
            }
            flip_endianness_if_needed(&mut x, size, v.flags);
            // Sign-extend (for matching with enumerand values below).
            if signed && size < 8 && x & 1 << (size*8-1) as u32 != 0 {
                x |= !((1usize << size*8)-1);
            }
            format_integer(x, size, signed, v.flags, state.out, state.palette);
            if !v.flags.intersects(ValueFlags::RAW | ValueFlags::HEX | ValueFlags::BIN) {
                styled_write!(state.out, state.palette.value_misc, " (");

                // Represent the value as a bitwise OR of some enumerands, with no bits in common, preferring bigger ones.
                // This works for both bitflags and regular enums:
                //  * for regular enums we'll find an exact match and print just one enumerand,
                //  * for bitflags we'll potentially print multiple enumerands ORed together,
                //  * if bitflags enum has some multibit enumerands (e.g. representing meaningful combinations of flags),
                //    we'll prefer to use them instead of their constituent single-bit enumerands,
                //  * if value is 0, and bitflags enum doesn't have a 0 enumerand, we'll print a red '?'; a little confusing, but I don't have better ideas.
                let mut candidates: Vec<(usize, &'static str)> = Vec::new();
                for enumerand in e.enumerands {
                    // Take enumerands whose bits are a subset of the value.
                    if x & enumerand.value == enumerand.value && (enumerand.value != 0 || x == 0) && !enumerand.name.is_empty() {
                        candidates.push((enumerand.value, enumerand.name));
                    }
                }
                // Sort by descending value. If multiple enumerands have the same value, take the first one in order of declaration (hence the stable sort).
                candidates.sort_by_key(|(v, _)| !v);
                candidates.dedup_by_key(|(v, _)| *v);
                // Greedily pick disjoint enumerands.
                let mut found = 0usize;
                candidates.retain(|(v, n)| {
                    if found & v == 0 {
                        found |= v;
                        true
                    } else {
                        false
                    }
                });
                if found == x && !candidates.is_empty() {
                    // Covered all bits.
                    let mut first = true;
                    for (_, name) in candidates.iter().rev() {
                        if !first {
                            styled_write!(state.out, state.palette.value_misc, " | ");
                        }
                        first = false;
                        styled_write!(state.out, state.palette.field_name, "{}", name);
                    }
                } else {
                    assert!(found & x == found);
                    styled_write!(state.out, state.palette.error, "?");
                }
                styled_write!(state.out, state.palette.value_misc, ")");
            }
        }
        Type::MetaType | Type::MetaField | Type::MetaVariable => {
            let val = reflect_meta_value(&v, state.state, state.context, Some((state.out, state.palette)));
            children = list_struct_children(&val.val, unsafe {(*val.type_).t.as_struct().unwrap()}, val.flags, state);
        }
        Type::MetaCodeLocation => {
            let blob = match &v.val {
                AddrOrValueBlob::Blob(x) => x,
                AddrOrValueBlob::Addr(_) => panic!("unexpected slice ref") };
            let binary_id = blob.get_usize_at(0).unwrap();
            let line = LineInfo::deserialize([blob.get_usize_at(8).unwrap(), blob.get_usize_at(16).unwrap()]);
            match state.context.symbols_registry.get(binary_id) {
                None => styled_write!(state.out, state.palette.error, "binary unloaded"),
                Some(binary) => {
                    let symbols = binary.symbols.as_ref().unwrap();
                    let file = &symbols.files[line.file_idx().unwrap()];
                    let name = file.filename.file_name().unwrap_or(std::ffi::OsStr::new("")).to_string_lossy();
                    styled_write!(state.out, state.palette.filename, "{}", name);
                    if line.line() != 0 {
                        styled_write!(state.out, state.palette.line_number, ":{}", line.line());
                        if line.column() != 0 {
                            styled_write!(state.out, state.palette.column_number, ":{}", line.column());
                        }
                    }
                    let info = FileLineInfo {line, filename: file.filename.to_owned(), path: file.path.to_owned(), version: file.version.clone()};
                    click_action = ValueClickAction::CodeLocation(info);
                }
            }
        }
    }
    (!children.is_empty(), children, click_action)
}

// x0 must be already sign-extended to 8 bytes if signed, and converted to little-endian if big-endian.
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
    } else if signed {
        styled_write!(out, palette.value, "{}", x0 as isize);
    } else {
        styled_write!(out, palette.value, "{}", x);
    }
}

fn format_function_pointer(addr: usize, state: &mut FormatValueState, click_action: &mut ValueClickAction) {
    styled_write!(state.out, state.palette.value_misc, "0x{:x}", addr);

    if addr != 0 {
        for binary in state.context.symbols_registry.iter() {
            let Ok(symbols) = &binary.symbols else {continue};
            let static_addr = binary.addr_map.dynamic_to_static(addr);
            let Ok((function, function_idx)) = symbols.addr_to_function(static_addr) else {continue};
            *click_action = ValueClickAction::Function {binary_id: binary.id, function_idx, static_addr};
            styled_write!(state.out, state.palette.function_name, " {}", function.demangle_name());
            return;
        }

        styled_write!(state.out, state.palette.default_dim, " <unknown function>");
    }
}

fn format_array(inner_type: *const TypeInfo, len: Option<usize>, stride: usize, value: &AddrOrValueBlob, is_string: bool, is_truncated: bool, flags: ValueFlags,
                state: &mut FormatValueState, children: &mut Vec<ValueChildInfo>) {
    let inner_type = unsafe {&*inner_type};
    let inner_size = inner_type.calculate_size();
    let stride = if stride != 0 { stride } else { inner_size };
    let get_val = |i: usize, state: &mut FormatValueState| -> Result<Value> {
        let start = i * stride;
        let end = start + inner_size;
        let val = value.byte_range(start..end, &mut state.context.memory)?;
        Ok(Value {val, type_: inner_type, flags: flags.inherit()})
    };
    if state.expanded {
        let mut indicated_truncation = false;
        for i in 0..len.unwrap_or(1) {
            if i > 1000 {
                let name_line = styled_writeln!(state.names_out, state.palette.value_misc, "…");
                children.push(ValueChildInfo {identity: i, name_line, kind: ValueChildKind::ArrayTail(i), deref: 0, value: err!(TooLong, "{} more elements", len.unwrap() - i)});
                indicated_truncation = true;
                break;
            }
            let value = get_val(i, state);
            let err = value.is_err();
            styled_write!(state.names_out, state.palette.value_misc, "[");
            styled_write!(state.names_out, state.palette.value, "{}", i);
            let name_line = styled_writeln!(state.names_out, state.palette.value_misc, "]");
            children.push(ValueChildInfo {identity: i, name_line, kind: ValueChildKind::ArrayElement(i), deref: 0, value});
            if err {
                break;
            }
        }
        if is_truncated && len.is_some() {
            if !indicated_truncation {
                let name_line = styled_writeln!(state.names_out, state.palette.value_misc, "…");
                children.push(ValueChildInfo {identity: len.unwrap(), name_line, kind: ValueChildKind::Other, deref: 0, value: err!(TooLong, "truncated")});
            }
            styled_write!(state.out, state.palette.value_misc, "length >= ");
            styled_write!(state.out, state.palette.value, "{}", len.clone().unwrap());
        } else if let Some(len) = len {
            styled_write!(state.out, state.palette.value_misc, "length ");
            styled_write!(state.out, state.palette.value, "{}", len);
        } else {
            styled_write!(state.out, state.palette.value_misc, "length unknown");
        }
        try_format_as_string(value, inner_type, len.clone(), is_string, flags, &mut state.context.memory, ", ", state.out, state.palette);
    } else {
        if !try_format_as_string(value, inner_type, len.clone(), is_string, flags, &mut state.context.memory, "", state.out, state.palette) {
            styled_write!(state.out, state.palette.value_misc, "[");
            for i in 0..len.unwrap_or(1) {
                if i != 0 {
                    styled_write!(state.out, state.palette.value_misc, ", ");
                }
                if state.over_output_limit() {
                    styled_write!(state.out, state.palette.truncation_indicator.2, "{}", state.palette.truncation_indicator.1);
                    break;
                }
                match get_val(i, state) {
                    Ok(v) => {
                        format_value_recurse(&v, false, state);
                    }
                    Err(e) if e.is_too_long() => styled_write!(state.out, state.palette.truncation_indicator.2, "{}", state.palette.truncation_indicator.1),
                    Err(e) => {
                        styled_write!(state.out, state.palette.error, "<{}>", e);
                        break;
                    }
                }
            }
            if len.is_none() {
                styled_write!(state.out, state.palette.value_misc, ", <length unknown>");
            } else if is_truncated {
                styled_write!(state.out, state.palette.value_misc, ", ");
                styled_write!(state.out, state.palette.truncation_indicator.2, "{}", state.palette.truncation_indicator.1);
            }
            styled_write!(state.out, state.palette.value_misc, "]");
        }
    }
}

// If an array seems like a string, format it as string.
fn try_format_as_string(value: &AddrOrValueBlob, element_type: *const TypeInfo, len: Option<usize>, marked_as_string: bool, flags: ValueFlags, memory: &mut CachedMemReader, prefix: &str, out: &mut StyledText, palette: &Palette) -> bool {
    if flags.contains(ValueFlags::RAW) {
        return false;
    }
    let element_type = unsafe {&*element_type};
    let p = match &element_type.t {
        Type::Primitive(p) => p,
        _ => return false,
    };
    if element_type.calculate_size() != 1 {
        // Support for utf16 and utf32 would go somewhere around here, if we were to add it.
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
        Some(len) => match value {
            &AddrOrValueBlob::Addr(addr) => {
                temp_storage = vec![0; len.min(limit)];
                match memory.read(addr, &mut temp_storage) {
                    Ok(()) => (),
                    Err(e) => {
                        styled_write!(out, palette.error, "<{}>", e);
                        return true;
                    }
                }
                (len, &temp_storage[..])
            }
            AddrOrValueBlob::Blob(b) => (len, b.as_slice()),
        }
        None => {
            let addr = match value {
                &AddrOrValueBlob::Addr(x) => x,
                AddrOrValueBlob::Blob(_) => return false,
            };
            temp_storage = match memory.read_null_terminated(addr, limit) {
                Ok((r, t)) => {
                    terminated |= t;
                    r
                }
                Err(e) => {
                    styled_write!(out, palette.value_misc, "{}", prefix);
                    styled_write!(out, palette.error, "bad C string: <{}>", e);
                    return true;
                }
            };
            (temp_storage.len(), &temp_storage[..])
        }
    };
    let slice = &slice[..slice.len().min(len).min(limit)];
    styled_write!(out, palette.value_misc, "{}", prefix);
    if flags.contains(ValueFlags::HEX) {
        styled_write!(out, palette.value_misc, "0x\"");
        for x in slice {
            write!(out.chars, "{:02x}", x).unwrap();
        }
        out.close_span(palette.value);
    } else {
        styled_write!(out, palette.value_misc, "\"");
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
    styled_write!(out, palette.value_misc, "\"");
    if !terminated {
        styled_write!(out, palette.warning, "…");
    } else if slice.len() != len {
        styled_write!(out, palette.warning, "… {} more bytes", len - slice.len());
    }
    true
}

pub fn get_struct_field(val: &AddrOrValueBlob, field: &StructField, memory: &mut CachedMemReader) -> Result<AddrOrValueBlob> {
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
    pub memory: &'a mut CachedMemReader,

    // Binary.
    pub symbols: Option<&'a Symbols>,
    pub addr_map: &'a AddrMap,
    pub tls_offset: &'a Result<usize>,

    // Unit.
    pub encoding: Encoding,
    pub unit: Option<&'a DwarfUnit>,

    // Stack frame. Not required for global variables.
    pub regs: Option<&'a Registers>,
    pub frame_base: Option<&'a Result<(usize, /*dubious*/ bool)>>,

    // Thread info.
    pub extra_regs: Option<&'a LazyExtraRegisters>,
    pub fs_base: Option<u64>,

    pub local_variables: &'a [Variable],
}

pub fn eval_dwarf_expression(mut expression: Expression<DwarfSlice>, context: &mut DwarfEvalContext) -> Result<(AddrOrValueBlob, /*dubious*/ bool)> {
    // Ignore [DW_OP_deref, DW_OP_stack_value] at the end of expression.
    // This is a workaround for what may be a quirk in LLVM: sometimes [DW_OP_deref, DW_OP_stack_value] is used for
    // variables whose type is a struct bigger than 8 bytes. Taken literally, these instructions say to read 8 bytes
    // at the address and report the result as the value of the variable, which makes no sense. Usually such address
    // points to the whole struct, not just its first 8 bytes, so we can report the address without dereferencing it.
    // (Maybe this will end up in gimli instead: https://github.com/gimli-rs/gimli/pull/738 )
    if expression.0.slice().len() >= 2 && expression.0.slice().ends_with(&[gimli::constants::DW_OP_deref.0, gimli::constants::DW_OP_stack_value.0]) {
        expression = Expression(DwarfSlice::new(&expression.0.slice()[..expression.0.slice().len() - 2]));
    }

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
                    _ => gimli::Value::parse(value_type, gimli::EndianSlice::new(slice, gimli::LittleEndian::default()))? };
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
                let (reg_val, dub) = if let Some(reg) = RegisterIdx::from_dwarf(*register) {
                    let regs = match &context.regs { Some(r) => r, None => return err!(Dwarf, "register op unexpected") };
                    regs.get(reg)?
                } else if let Some(reg) = ExtraRegisterIdx::from_dwarf(*register) {
                    let &Some(regs) = &context.extra_regs else {return err!(ProcessState, "no simd registers")};
                    let regs = regs.get();
                    let (vec, dub) = regs.get(reg)?;
                    (vec[0], dub)
                } else {
                    return err!(Dwarf, "unsupported register in expression: {:?}", register);
                };
                dubious |= dub;
                let val = match value_type {
                    ValueType::Generic => gimli::Value::Generic(reg_val),
                    _ => gimli::Value::parse(value_type, gimli::EndianSlice::new(&reg_val.to_le_bytes(), gimli::LittleEndian::default()))? };
                eval.resume_with_register(val)
            }
            EvaluationResult::RequiresFrameBase => {
                let (v, dub) = match &context.frame_base {
                    None => return err!(Dwarf, "no frame base"),
                    &Some(x) => x.clone()?,
                };
                dubious |= dub;
                eval.resume_with_frame_base(v as u64)
            }
            EvaluationResult::RequiresCallFrameCfa => {
                let regs = match &context.regs { Some(r) => r, None => return err!(Dwarf, "cfa op unexpected") };
                let (cfa, dub) = regs.get(RegisterIdx::Cfa)?;
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
                    None => DwarfSlice::default(),
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

            EvaluationResult::RequiresTls(offset) => {
                if let &Some(fs_base) = &context.fs_base {
                    let tls_offset = context.tls_offset.clone()?;
                    eval.resume_with_tls(fs_base.wrapping_sub(tls_offset as u64).wrapping_add(*offset))
                } else {
                    return err!(ProcessState, "no current thread");
                }
            }

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
                gimli::read::Value::F32(x) => f32::to_bits(x) as usize,
                gimli::read::Value::F64(x) => f64::to_bits(x) as usize,
                _ => v.to_u64(!0)? as usize })),
            Location::Bytes{value: b} => {
                blob_bytes = b.len();
                AddrOrValueBlob::Blob(ValueBlob::from_slice(b.slice()))
            }
            Location::Register{register: reg} => {
                if let Some(reg) = RegisterIdx::from_dwarf(reg) {
                    let &Some(regs) = &context.regs else {return err!(Dwarf, "register location unexpected")};
                    match regs.get(reg) {
                        Err(_) => return err!(Dwarf, "register {} optimized away", reg),
                        Ok((v, dub)) => {
                            dubious |= dub;
                            AddrOrValueBlob::Blob(ValueBlob::new(v as usize))
                        }
                    }
                } else if let Some(reg) = ExtraRegisterIdx::from_dwarf(reg) {
                    let &Some(regs) = &context.extra_regs else {return err!(Dwarf, "no simd registers")};
                    let regs = regs.get();
                    let (v, dub) = regs.get(reg)?;
                    dubious |= dub;
                    let blob = ValueBlob::from_u64_slice(v);
                    AddrOrValueBlob::Blob(blob)
                } else {
                    return err!(NotImplemented, "unsupported register: {:?}", reg);
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

        let val = val.into_value((size_in_bits + bit_offset + 7) / 8, &mut context.memory)?;
        res.append_bits(res_bits, val, size_in_bits, bit_offset);
        res_bits += size_in_bits;
    }
    Ok((AddrOrValueBlob::Blob(res), dubious))
}

pub fn eval_variable(location: &PackedVariableLocation, context: &mut DwarfEvalContext) -> Result<(AddrOrValueBlob, /*dubious*/ bool)> {
    match location.unpack() {
        VariableLocation::Const(s) => Ok((AddrOrValueBlob::Blob(ValueBlob::from_slice(s)), false)),
        VariableLocation::Expr(e) => eval_dwarf_expression(e, context),
        VariableLocation::Unknown => err!(Dwarf, "location unknown"),
    }
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
        self.fields.push(StructField {name, bit_offset: prev_len*8, bit_size: (self.value_blob.len() - prev_len)*8, flags: FieldFlags::empty(), type_, discr_value: 0});
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
    pub fn add_usize_blob_field(&mut self, name: &'static str, value: &[usize], type_: *const TypeInfo) {
        unsafe {self.add_blob_field(name, std::slice::from_raw_parts(value.as_ptr() as *const u8, value.len() * 8), type_)};
    }
    pub fn add_str_field(&mut self, name: &'static str, value: &str, types: &mut Types, builtin_types: &BuiltinTypes) {
        let array_type = types.add_array(builtin_types.char8, Some(value.len()), ArrayFlags::UTF_STRING);
        self.add_blob_field(name, value.as_bytes(), array_type);
    }
    pub fn add_slice_field(&mut self, name: &'static str, ptr: usize, len: usize, type_: *const TypeInfo, flags: SliceFlags, types: &mut Types) {
        let slice_type = types.add_slice(type_, flags);
        let mut a = [0u8; 16];
        a[..8].copy_from_slice(&ptr.to_le_bytes());
        a[8..].copy_from_slice(&len.to_le_bytes());
        self.add_blob_field(name, &a, slice_type);
    }
    pub fn add_enum_field(&mut self, name: &'static str, val: usize, enumerands: &[&'static str], types: &mut Types, builtin_types: &BuiltinTypes) {
        assert!(val < enumerands.len());
        let mut en = EnumType {enumerands: &[], type_: builtin_types.u64_};
        for (value, name) in enumerands.iter().enumerate() {
            types.add_enumerand(&mut en, Enumerand {name, value, flags: EnumerandFlags::empty()});
        }
        let enum_type = types.add_enum(en);
        self.add_usize_field(name, val, enum_type);
    }

    pub fn finish(mut self, name: &'static str, flags: ValueFlags, types: &mut Types) -> Value {
        let fields_slice = types.fields_arena.add_slice(&self.fields);
        let struct_type = StructType {flags: StructFlags::empty(), fields_ptr: fields_slice.as_ptr(), fields_len: fields_slice.len()};
        let type_ = TypeInfo {name, size: self.value_blob.len(), die: DebugInfoOffset(0), binary_id: usize::MAX, line: LineInfo::invalid(), language: LanguageFamily::Internal, nested_names: &[], flags: TypeFlags::SIZE_KNOWN, t: Type::Struct(struct_type)};
        let type_ = types.types_arena.add(type_);
        let val = AddrOrValueBlob::Blob(ValueBlob::from_vec(mem::take(&mut self.value_blob)));
        Value {val, type_, flags}
    }
}

pub fn is_value_truthy(val: &Value, memory: &mut CachedMemReader) -> Result<bool> {
    let t = unsafe {&*val.type_};
    let size = t.calculate_size();
    match &t.t {
        Type::Primitive(f) if f.contains(PrimitiveFlags::UNSPECIFIED) || size == 0 => err!(TypeMismatch, "got void value instead of a boolean"),
        Type::Primitive(_) => {
            let v = val.val.clone().into_value(size, memory)?;
            Ok(v.as_slice()[..size].iter().copied().any(|x| x != 0))
        }
        _ => err!(TypeMismatch, "got value of {} type instead of a boolean", t.t.kind_name()),
    }
}

pub fn flip_endianness_if_needed(x: &mut usize, size: usize, flags: ValueFlags) {
    let size = size.min(8).max(1);
    if flags.contains(ValueFlags::BIG_ENDIAN) {
        *x = x.swap_bytes() >> (64 - size*8);
    }
}

#[cfg(test)]
mod tests {
    use crate::expr::*;

    #[test]
    fn value_blob_nonsense() {
        let lens = [1, 3, 5, 7, 8, 9, 13, 15, 16, 17, 23, 24, 25, 25, 28, 31, 32, 33, 34, 35, 38, 39, 40, 41, 47];
        for _ in 0..3000 {
            let bits1 = lens[random::<usize>()%lens.len()];
            let bits2 = lens[random::<usize>()%lens.len()];
            let pos1: usize = random::<usize>()%bits1;
            let pos2: usize = random::<usize>()%bits2;
            let off: usize = random::<usize>()%(pos2+1);

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
