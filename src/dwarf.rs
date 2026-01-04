use crate::{*, error::{*, Result, Error}, log::*, util::*, types::LanguageFamily};
use gimli::{*, constants::DwForm};
use std::{str, borrow::Cow, fmt, sync::{Mutex, Arc}, collections::{HashSet, HashMap, hash_map::Entry}, mem, ptr, ops::Range, arch::x86_64::*};
use rand::random;
use bitflags::bitflags;

// DWARF parsing.
// Currently we use some things from gimli, while most hot paths are reimplemented in a different way for speed (and incidentally some convenience). We should probably get rid of gimli altogether, for simplicity, compilation speed, and executable size.
//
// Approach to parsing attributes: we declare a struct for each tag we're interested in, pre-register information about layouts of these structs,
// then pre-process abbreviations to produce a compact plan for parsing attributes and storing results in the struct. This should be faster than gimli's approach because:
//  * attribute forms are checked only once for each abbreviation instead of once for each DIE,
//  * there's no two-step data transformation where we first do a big `match` to parse the attribute into an enum, then do another `match` on that enum.
//
// Use macro dwarf_struct!() to declare the struct and describe which attributes and forms to expect.
//
// (This looks aggressively microoptimized in some ways, but actually it turned out only a little faster than gimli. I'm probably doing something wrong.)

// We currently don't support .debug_types section. If we were to support it, we would pack section id and offset into one 8-byte value and use that as DieOffset (just like UnitSectionOffset, but 8 bytes instead of 16).
pub type DieOffset = DebugInfoOffset<usize>;

// Set of unsupported DWARF features that we've encountered in a file, so that we can show a warning about it.
bitflags! { pub struct DwarfUnsupportedFeatures: usize {
    const TYPE_SIGNATURES = 0x1;
    const SUPPLEMENTARY_OBJECT_FILES = 0x2;
    const SKELETON_UNITS = 0x4;
}}
impl fmt::Display for DwarfUnsupportedFeatures {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut first = true;
        for (val, name) in [(Self::TYPE_SIGNATURES, "type signatures"), (Self::SUPPLEMENTARY_OBJECT_FILES, "supplementary object files"), (Self::SKELETON_UNITS, "skeleton units (spooky)")] {
            if self.contains(val) {
                if !first {
                    write!(f, ", ")?;
                }
                first = false;
                write!(f, "{}", name)?;
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy)]
pub struct DwarfSlice {
    // The data is guaranteed to be padded on the right by at least one extra page of readable memory (see Mmap::new()), even if the slice is empty.
    p: *const u8,
    n: usize,
}
unsafe impl Send for DwarfSlice {}
unsafe impl Sync for DwarfSlice {}
impl Default for DwarfSlice { fn default() -> Self { Self {p: [0u8; 4096].as_ptr(), n: 0} } }
impl fmt::Debug for DwarfSlice { fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> std::result::Result<(), fmt::Error> { write!(fmt, "DwarfSlice of length {}", self.n) } }
impl DwarfSlice {
    pub fn new(slice: &'static [u8]) -> DwarfSlice { DwarfSlice {p: slice.as_ptr(), n: slice.len()} }
    pub fn slice(&self) -> &'static [u8] {unsafe {std::slice::from_raw_parts(self.p, self.n)}}
    pub fn as_ptr(&self) -> *const u8 {self.p}

    #[inline]
    pub fn read_bytes(&mut self, len: usize) -> gimli::Result<&'static [u8]> {
        if len > self.n {
            Err(gimli::Error::UnexpectedEof(self.offset_id()))
        } else {
            let r = unsafe {std::slice::from_raw_parts(self.p, len)};
            self.p = unsafe {self.p.add(len)};
            self.n -= len;
            Ok(r)
        }
    }

    pub fn read_u24(&mut self) -> gimli::Result<u32> {
        let mut a = [0u8; 4];
        a[..3].copy_from_slice(self.read_bytes(3)?);
        Ok(u32::from_le_bytes(a))
    }

    pub fn get_null_terminated_slice(self, offset: usize) -> Result<&'static [u8]> {
        unsafe {
            if offset >= self.n {
                return err!(Dwarf, "string ref starts out of bounds");
            }
            let len = strlen_padded(self.p.add(offset), self.n - offset);
            if len >= self.n - offset {
                return err!(Dwarf, "string ref unterminated");
            }
            Ok(std::slice::from_raw_parts(self.p.add(offset), len))
        }
    }
}

#[derive(Clone)]
pub struct SliceReader {
    p: *const u8,
    n: usize,
    unexpected_eof: bool,
}
impl SliceReader {
    pub fn new(slice: &'static [u8]) -> Self { Self {p: slice.as_ptr(), n: slice.len(), unexpected_eof: false} }
    pub fn check(&self) -> Result<()> { if self.unexpected_eof {err!(Dwarf, "unexpected end of section")} else {Ok(())} }

    pub fn is_empty(&self) -> bool {
        self.n == 0
    }

    pub fn offset_from(&self, base: &'static [u8]) -> usize {
        let base_ptr = base.as_ptr() as usize;
        let ptr = self.p as usize;
        debug_assert!(ptr >= base_ptr && ptr <= base_ptr + base.len());
        ptr - base_ptr
    }

    pub fn as_slice(&self) -> &'static [u8] { unsafe {std::slice::from_raw_parts(self.p, self.n)} }

    #[inline]
    unsafe fn read_bytes_unchecked(&mut self, len: usize) -> &'static [u8] { let r = std::slice::from_raw_parts(self.p, len); self.p = self.p.add(len); self.n -= len; r }
    #[inline]
    unsafe fn advance_unchecked(&mut self, len: usize) -> *const u8 { let p = self.p; self.p = self.p.add(len); self.n -= len; p }

    // Byte reading functions that try to be faster by avoiding Result<>. Instead, you may parse a bunch of values, then call check() to check that there was no unexpected end of data.
    // Also call check() if any other parsing error occurred, because that error may've been caused by reaching eof and getting unexpected zeroes from these functions.
    pub fn read_u8_or_zero(&mut self) -> u8 { unsafe { if self.n == 0 {self.unexpected_eof = true; 0} else {*self.advance_unchecked(1)} } }
    pub fn read_u16_or_zero(&mut self) -> u16 { unsafe { if self.n < 2 {self.unexpected_eof = true; self.n = 0; 0} else {ptr::read_unaligned(self.advance_unchecked(2) as *const u16)} } }
    pub fn read_u24_or_zero(&mut self) -> u32 { unsafe { if self.n < 3 {self.unexpected_eof = true; self.n = 0; 0} else {ptr::read_unaligned(self.advance_unchecked(3) as *const u32) & 0xffffff} } } // relying on padding
    pub fn read_u32_or_zero(&mut self) -> u32 { unsafe { if self.n < 4 {self.unexpected_eof = true; self.n = 0; 0} else {ptr::read_unaligned(self.advance_unchecked(4) as *const u32)} } }
    pub fn read_u64_or_zero(&mut self) -> usize { unsafe { if self.n < 8 {self.unexpected_eof = true; self.n = 0; 0} else {ptr::read_unaligned(self.advance_unchecked(8) as *const usize)} } }
    pub fn read_bytes_or_empty(&mut self, len: usize) -> &'static [u8] { unsafe { if self.n < len {self.unexpected_eof = true; self.n = 0; &[]} else {std::slice::from_raw_parts(self.advance_unchecked(len), len)} } }

    pub fn skip(&mut self, len: usize) { if self.n < len {self.unexpected_eof = true; self.n = 0;} else {self.p = unsafe {self.p.add(len)}; self.n -= len;} }

    #[inline]
    pub fn read_leb128_or_zero<const SIGNED: bool>(&mut self) -> usize {
        // (This implementation tries to be a little more clever than a simple loop, but it probably mostly doesn't matter, see other_things/varint_benchmark.c)
        let chunk = unsafe {ptr::read_unaligned(self.p as *const usize)};
        let mut bytes: usize;
        let mut res: usize;
        if (chunk & 0x80) == 0 { // 1 byte
            bytes = 1;
            res = chunk & 0x7f;
        } else if (chunk & 0x0000008080808080) != 0x0000008080808080 { // 2..5 bytes
            res = (chunk & 0x7f) | ((chunk & 0x7f00) >> 1);
            bytes = 2;
            if (chunk & 0x8000) != 0 {
                res |= (chunk & 0x7f0000) >> 2;
                bytes += 1;
            }
            if (chunk & 0x808000) == 0x808000 {
                res |= (chunk & 0x7f000000) >> 3;
                bytes += 1;
            }
            if (chunk & 0x80808000) == 0x80808000 {
                res |= (chunk & 0x7f00000000) >> 4;
                bytes += 1;
            }
        } else {
            let mut x = chunk;
            // Move the 8 groups of 7 bits from their scattered positions to the low 56 bits.
            x = ((x & 0x7f007f007f007f00) >> 1) | (x & 0x007f007f007f007f);
            x = ((x & 0xffff000000000000) >> 6) | ((x & 0x0000ffff00000000) >> 4) | ((x & 0x00000000ffff0000) >> 2) | (x & 0x000000000000ffff);
            res = x;
            if (chunk & 0x8080808080808080) != 0x8080808080808080 { // 6..8 bytes
                bytes = ((((!chunk) & 0x8080808080808080).trailing_zeros() >> 3) + 1) as usize;
                res &= usize::MAX >> (64 - bytes*7);
            } else { // 9..10 bytes
                let high = unsafe {ptr::read_unaligned(self.p.add(8) as *const u16) as usize};
                res |= high << 56;
                res &= (high << 55) | 0x7fffffffffffffff; // in case it's a weirdly encoded number with length 10 bytes but the upper bit unset
                bytes = 9 + ((high >> 7) & 1);

                if high & 0x80 != 0 && high & if SIGNED {0x8000} else {0xfe00} != 0 {
                    bytes = usize::MAX; // pretend it's unexpected eof; not quite the correct error name, but meh
                }
            }
        }

        if bytes > self.n {
            self.unexpected_eof = true;
            self.n = 0;
            0
        } else {
            if SIGNED && bytes < 10 { // sign-extend
                let bits = bytes * 7;
                res = ((res as isize) << (64 - bits) >> (64 - bits)) as usize;
            }

            self.p = unsafe {self.p.add(bytes)};
            self.n -= bytes;
            res
        }
    }

    pub fn read_uleb128_or_zero(&mut self) -> usize {
        self.read_leb128_or_zero::<false>()
    }
    pub fn read_sleb128_or_zero(&mut self) -> isize {
        self.read_leb128_or_zero::<true>() as isize
    }

    pub fn read_uleb128_u16_or_zero(&mut self) -> u16 {
        let chunk = unsafe {ptr::read_unaligned(self.p as *const u32)};
        let mut res = chunk & 0x7f;
        let mut bytes = 1;
        if chunk & 0x80 != 0 {
            res |= (chunk & 0x7f00) >> 1;
            bytes += 1;
        }
        if (chunk & 0x8080) == 0x8080 {
            res |= (chunk & 0x7f0000) >> 2;
            bytes += 1;

            if chunk & 0xfc0000 != 0 {
                bytes = usize::MAX;
            }
        }
        if bytes > self.n {
            self.unexpected_eof = true;
            self.n = 0;
            0
        } else {
            self.p = unsafe {self.p.add(bytes)};
            self.n -= bytes;
            res as u16
        }
    }

    pub fn skip_leb128(&mut self) {
        let chunk = unsafe {ptr::read_unaligned(self.p as *const usize)};
        let mut bytes = ((((!chunk) & 0x8080808080808080).trailing_zeros() >> 3) + 1) as usize;
        if bytes == 8 {
            let high: u8 = unsafe {*self.p.add(8)};
            bytes += (high >> 7) as usize;
        }
        if bytes > self.n {
            self.unexpected_eof = true;
            self.n = 0;
        } else {
            self.p = unsafe {self.p.add(bytes)};
            self.n -= bytes;
        }
    }

    pub fn read_null_terminated_slice_or_empty(&mut self) -> &'static [u8] {
        unsafe {
            let len = strlen_padded(self.p, self.n);
            if len >= self.n {
                self.unexpected_eof = true;
                self.n = 0;
                &[]
            } else {
                let r = std::slice::from_raw_parts(self.p, len);
                self.p = self.p.add(len + 1);
                self.n -= len + 1;
                r
            }
        }
    }

    pub fn read_abbreviation<'ab>(&mut self, context: &AttributeContext<'ab>) -> Result<Option<&'ab Abbreviation>> {
        let code = self.read_uleb128_or_zero();
        if code == 0 {
            self.check()?;
            return Ok(None);
        }
        Ok(Some(context.unit.abbreviation_set.get(code, &context.shared)?))
    }

    pub fn skip_attributes(&mut self, abbreviation: &Abbreviation, context: &AttributeContext) -> Result<()> {
        unsafe {self.read_attributes(abbreviation, /*which_layout*/ 2, context, ptr::null_mut())}
    }

    pub unsafe fn read_attributes(&mut self, abbreviation: &Abbreviation, which_layout: usize, context: &AttributeContext, out: *mut u8) -> Result<()> {
        let r = self.read_attributes_impl(abbreviation, which_layout, context, out);
        if self.unexpected_eof {
            err!(Dwarf, "unexpected end of section when parsing attributes")
        } else {
            r
        }
    }

    #[inline]
    pub unsafe fn read_attributes_impl(&mut self, abbreviation: &Abbreviation, which_layout: usize, context: &AttributeContext, out: *mut u8) -> Result<()> {
        let actions = &abbreviation.actions[which_layout];
        let mut flags = actions.flags_value;
        for action_idx in actions.actions.clone() {
            let mut action = context.shared.actions_pool[action_idx as usize];
            if action.form == DW_FORM_indirect {
                let mut form = action.form;
                while form == constants::DW_FORM_indirect {
                    form = constants::DwForm(self.read_uleb128_u16_or_zero());
                }
                let implicit_const_value = if form == DW_FORM_implicit_const {
                    self.read_sleb128_or_zero() as usize
                } else {
                    0
                };
                // Do the checks+dispatch that we normally do when preprocessing abbreviations.
                let layout_idx = action.param >> 16;
                let name = DwAt((action.param & 0xffff) as u16);
                let layout = &context.shared.layouts.layouts[layout_idx].1;
                let mut ignore_unsupported_features = DwarfUnsupportedFeatures::empty(); // hopefully there aren't executables where some features are used only behind DW_FORM_indirect
                action = prepare_attribute_action(AttributeSpecification {name, form, implicit_const_value}, layout, context.unit.unit.header.encoding(), &context.shared.warnings, &mut ignore_unsupported_features, &mut flags)?;
            }

            let out_field = out.add(action.field_offset as usize);
            // I guess this is not UB? I just want to emit a `mov` instruction, is it too much to ask.
            let set_usize = |x: usize| ptr::copy_nonoverlapping(&x as *const usize as *const u8, out_field, 8);
            let set_slice = |x: &'static [u8], check_utf8: bool| {
                if check_utf8 && unsafe {!is_ascii_padded(x.as_ptr(), x.len())} && std::str::from_utf8(x).is_err() {
                    if context.shared.warnings.warn(DW_AT_null, DW_FORM_string) {
                        eprintln!("warning: invalid UTF8 in string attribute: {:?}", &x[..x.len().min(500)]);
                    }
                    return;
                }
                ptr::copy_nonoverlapping(&x as *const &'static [u8] as *const u8, out_field, 16);
            };

            let set_strx = |index: usize, context: &AttributeContext| -> Result<()> {
                let offset = context.dwarf.string_offset(&context.unit.unit, DebugStrOffsetsIndex(index))?;
                let s = context.dwarf.debug_str.reader().get_null_terminated_slice(offset.0)?;
                set_slice(s, action.param != 0);
                Ok(())
            };
            let set_addrx = |index: usize, context: &AttributeContext| -> Result<()> {
                let addr = context.dwarf.address(&context.unit.unit, DebugAddrIndex(index))? as usize;
                set_usize(addr);
                Ok(())
            };
            let set_unit_offset = |mut offset: usize, context: &AttributeContext| {
                if action.param != 0 {
                    // Convert to global offset.
                    offset = UnitOffset(offset).to_debug_info_offset(&context.unit.unit.header).unwrap().0; // (panics if `unit` is a type unit instead of compile unit)
                }
                set_usize(offset);
            };

            match action.form {
                DW_FORM_addr => set_usize(if context.unit.unit.header.encoding().address_size == 8 {self.read_u64_or_zero() as usize} else {self.read_u32_or_zero() as usize}),

                DW_FORM_block1 => {
                    let len = self.read_u8_or_zero() as usize;
                    set_slice(self.read_bytes_or_empty(len), false);
                }
                DW_FORM_block2 => {
                    let len = self.read_u16_or_zero() as usize;
                    set_slice(self.read_bytes_or_empty(len), false);
                }
                DW_FORM_block4 => {
                    let len = self.read_u32_or_zero() as usize;
                    set_slice(self.read_bytes_or_empty(len), false);
                }
                DW_FORM_block | DW_FORM_exprloc => {
                    let len = self.read_uleb128_or_zero();
                    set_slice(self.read_bytes_or_empty(len), false);
                }
                DW_FORM_data16 => set_slice(self.read_bytes_or_empty(16), false),

                DW_FORM_data1 => set_usize(self.read_u8_or_zero() as usize),
                DW_FORM_data2 => set_usize(self.read_u16_or_zero() as usize),
                DW_FORM_data4 => set_usize(self.read_u32_or_zero() as usize),
                DW_FORM_data8 => set_usize(self.read_u64_or_zero() as usize),
                DW_FORM_sdata => set_usize(self.read_sleb128_or_zero() as usize),
                DW_FORM_udata => set_usize(self.read_uleb128_or_zero()),

                DW_FORM_string => set_slice(self.read_null_terminated_slice_or_empty(), action.param != 0),
                DW_EXTRA_FORM_strp4 => {
                    let offset = self.read_u32_or_zero() as usize;
                    let s = context.dwarf.debug_str.reader().get_null_terminated_slice(offset)?;
                    set_slice(s, action.param != 0);
                }
                DW_EXTRA_FORM_strp8 => {
                    let offset = self.read_u64_or_zero();
                    let s = context.dwarf.debug_str.reader().get_null_terminated_slice(offset)?;
                    set_slice(s, action.param != 0);
                }
                DW_EXTRA_FORM_line_strp4 => {
                    let offset = self.read_u32_or_zero() as usize;
                    let s = context.dwarf.debug_line_str.reader().get_null_terminated_slice(offset)?;
                    set_slice(s, action.param != 0);
                }
                DW_EXTRA_FORM_line_strp8 => {
                    let offset = self.read_u64_or_zero();
                    let s = context.dwarf.debug_line_str.reader().get_null_terminated_slice(offset)?;
                    set_slice(s, action.param != 0);
                }
                DW_FORM_strx => set_strx(self.read_uleb128_or_zero(), context)?,
                DW_FORM_strx1 => set_strx(self.read_u8_or_zero() as usize, context)?,
                DW_FORM_strx2 => set_strx(self.read_u16_or_zero() as usize, context)?,
                DW_FORM_strx3 => set_strx(self.read_u24_or_zero() as usize, context)?,
                DW_FORM_strx4 => set_strx(self.read_u32_or_zero() as usize, context)?,

                DW_FORM_flag => {
                    let v = self.read_u8_or_zero();
                    if v > 1 {
                        return err!(Dwarf, "invalid flag value: {}", v);
                    }
                    *(out_field as *mut bool) = v != 0;
                }
                DW_FORM_flag_present => *(out_field as *mut bool) = true,

                DW_FORM_ref1 => set_unit_offset(self.read_u8_or_zero() as usize, context),
                DW_FORM_ref2 => set_unit_offset(self.read_u16_or_zero() as usize, context),
                DW_FORM_ref4 => set_unit_offset(self.read_u32_or_zero() as usize, context),
                DW_FORM_ref8 => set_unit_offset(self.read_u64_or_zero() as usize, context),
                DW_FORM_ref_udata => set_unit_offset(self.read_uleb128_or_zero(), context),

                DW_FORM_addrx => set_addrx(self.read_uleb128_or_zero(), context)?,
                DW_FORM_addrx1 => set_addrx(self.read_u8_or_zero() as usize, context)?,
                DW_FORM_addrx2 => set_addrx(self.read_u16_or_zero() as usize, context)?,
                DW_FORM_addrx3 => set_addrx(self.read_u24_or_zero() as usize, context)?,
                DW_FORM_addrx4 => set_addrx(self.read_u32_or_zero() as usize, context)?,

                DW_FORM_implicit_const => set_usize(action.param),

                DW_FORM_loclistx => {
                    let index = self.read_uleb128_or_zero();
                    let offset = context.dwarf.locations_offset(&context.unit.unit, DebugLocListsIndex(index))?.0;
                    set_usize(offset);
                }
                DW_FORM_rnglistx => {
                    let index = self.read_uleb128_or_zero();
                    let offset = context.dwarf.ranges_offset(&context.unit.unit, DebugRngListsIndex(index))?.0;
                    set_usize(offset);
                }

                DW_EXTRA_FORM_skip_bytes => self.skip(action.param),
                DW_EXTRA_FORM_skip_leb128 => self.skip_leb128(),
                DW_EXTRA_FORM_skip_block => {
                    let len = self.read_uleb128_or_zero();
                    self.skip(len);
                }
                DW_EXTRA_FORM_skip_block1 => {
                    let len = self.read_u8_or_zero() as usize;
                    self.skip(len);
                }
                DW_EXTRA_FORM_skip_block2 => {
                    let len = self.read_u16_or_zero() as usize;
                    self.skip(len);
                }
                DW_EXTRA_FORM_skip_block4 => {
                    let len = self.read_u32_or_zero() as usize;
                    self.skip(len);
                }
                DW_EXTRA_FORM_skip_string => {self.read_null_terminated_slice_or_empty();}

                // These are unexpected here because prepare_attribute_action() converts them to other forms.
                // DW_FORM_ref_addr | DW_FORM_sec_offset => ,

                // These are not supported, prepare_attribute_action() converts them into DW_EXTRA_FORM_skip_* forms.
                // DW_FORM_ref_sig8 => ,
                // DW_FORM_ref_sup4 => ,
                // DW_FORM_ref_sup8 => ,
                // DW_FORM_GNU_ref_alt => ,
                // DW_EXTRA_FORM_strp_sup4 => ,
                // DW_EXTRA_FORM_strp_sup8 => ,

                _ => panic!("unexpected attribute form in prepared action: {}", action.form), // (we already validated action.form in prepare_attribute_action())
            }
        }

        if flags != 0 {
            let flags_ptr = out.add(actions.flags_offset as usize) as *mut u32;
            *flags_ptr = flags;
        } else {
            // (If it's a skip-all layout, `out` is a null pointer, don't dereference it.)
        }

        Ok(())
    }
}

#[derive(Clone, Copy)]
pub struct AttributeSpecification {
    pub name: DwAt,
    pub form: DwForm,
    pub implicit_const_value: usize,
}

#[derive(Clone)]
pub struct Abbreviation {
    pub tag: DwTag,
    pub has_children: bool,

    // 0 - normal tag-specific struct layout.
    // 1 - common struct layout for chasing abstract_origin/specification pointers without looking at the tag.
    // 2 - skip
    actions: [AbbreviationActions; 3],
}

#[derive(Clone)]
pub struct AbbreviationSet {
    pub code_to_idx: Range<usize>, // in AttributesSharedData.code_to_idx_pool
    pub consecutive: bool,
}
impl AbbreviationSet {
    fn new() -> Self { Self {code_to_idx: 0..0, consecutive: true} }

    fn get<'a>(&self, code: usize, shared: &'a AbbreviationsSharedData) -> Result<&'a Abbreviation> {
        let slice = &shared.code_to_idx_pool[self.code_to_idx.clone()];
        let idx = if self.consecutive {
            if code < slice.len() {
                slice[code].1
            } else {
                return err!(Dwarf, "abbvreviation code out of bounds: {} >= {}", code, slice.len());
            }
        } else {
            let i = slice.partition_point(|a| a.0 < code);
            if i == slice.len() || slice[i].0 > code {
                return err!(Dwarf, "abbreviation code not found: {}", code);
            } else {
                slice[i].1
            }
        };
        Ok(&shared.abbreviations_pool[idx])
    }
}

#[derive(Clone, Copy)]
struct AttributeAction {
    form: DwForm,
    field_offset: u32,
    // For string forms: 1 to check utf8 validity, 0 to leave a &[u8].
    // For DW_FORM_ref*: 1 to convert to DebugInfoOffset, 0 to keep UnitOffset.
    // For DW_FORM_implicit_const: the constant value.
    // For DW_EXTRA_FORM_skip_bytes: how many bytes to skip.
    // For DW_FORM_indirect: packed layout_idx and DwAt.
    param: usize,
}

#[derive(Default, Clone)]
struct AbbreviationActions {
    flags_offset: u32,
    flags_value: u32,
    actions: Range<u32>, // in AbbreviationsSharedData.actions_pool
}

#[derive(Default, Clone)]
pub struct AttributeStructLayout {
    pub flags_offset: u32,
    pub fields: Vec<(/*offset*/ u32, DwAt, AttributeType)>,

    pub num_fields_included_in_flags: u32,
}
impl AttributeStructLayout {
    // Expand special attribute groups into individual attributes.
    fn preprocess(&mut self) {
        assert!(self.fields.len() <= 24);
        self.num_fields_included_in_flags = self.fields.len() as u32;
        let (mut saw_ranges, mut saw_location, mut saw_specification) = (false, false, false);
        for i in 0..self.num_fields_included_in_flags as usize {
            let &(offset, attr_name, attr_type) = &self.fields[i];
            match attr_type {
                AttributeType::Ranges => {
                    assert!(!mem::replace(&mut saw_ranges, true));
                    self.fields[i] = (offset + mem::offset_of!(DwarfRanges, ranges) as u32, DW_AT_ranges, AttributeType::Ranges);
                    self.fields.push((offset + mem::offset_of!(DwarfRanges, low_pc) as u32, DW_AT_low_pc, AttributeType::Ranges));
                    self.fields.push((offset + mem::offset_of!(DwarfRanges, high_pc) as u32, DW_AT_high_pc, AttributeType::Ranges));
                    self.fields.push((offset + mem::offset_of!(DwarfRanges, entry_pc) as u32, DW_AT_entry_pc, AttributeType::Ranges));
                }
                AttributeType::CodeLocation => {
                    assert!(!mem::replace(&mut saw_location, true));
                    let attrs = match attr_name {
                        DW_AT_decl_file => [DW_AT_decl_file, DW_AT_decl_line, DW_AT_decl_column],
                        DW_AT_call_file => [DW_AT_call_file, DW_AT_call_line, DW_AT_call_column],
                        _ => panic!("unexpected attribute name for CodeLocation field: {}", attr_name),
                    };
                    self.fields[i] = (offset + mem::offset_of!(DwarfCodeLocation, file) as u32, attrs[0], AttributeType::Unsigned);
                    self.fields.push((offset + mem::offset_of!(DwarfCodeLocation, line) as u32, attrs[1], AttributeType::Unsigned));
                    self.fields.push((offset + mem::offset_of!(DwarfCodeLocation, column) as u32, attrs[2], AttributeType::Unsigned));
                }
                AttributeType::SpecificationOrAbstractOrigin => {
                    assert!(!mem::replace(&mut saw_specification, true));
                    let other_attr = match attr_name {
                        DW_AT_specification => DW_AT_abstract_origin,
                        DW_AT_abstract_origin => DW_AT_specification,
                        _ => panic!("unexpected attribute for SpecificationOrAbstractOrigin field: {}", attr_name),
                    };
                    self.fields.push((offset, other_attr, AttributeType::SpecificationOrAbstractOrigin));
                }
                _ => (),
            }
        }
    }
}

#[derive(Default)]
pub struct AllAttributeStructLayouts {
    layouts: Vec<(DwTag, AttributeStructLayout)>,
    num_primary_layouts: usize, // layouts[0..num_primary_layouts] correspond to tags and are sorted by tag
    secondary_layout_idx: usize, // layouts[secondary_layout_idx] is the alternative layout to use for all tags in secondary_tags
    unit_layout_idx: usize, // layouts[unit_layout_idx] is the alternative layout to use for DW_TAG_compile_unit
    empty_layout_idx: usize, // layout[empty_layout_idx] is a skip-all-attributes layout that can be used with null pointer as target struct
    secondary_tags: Vec<DwTag>,
}
impl AllAttributeStructLayouts {
    pub fn new(layout_groups: Vec<(Vec<DwTag>, AttributeStructLayout)>, secondary_layout: AttributeStructLayout, mut secondary_tags: Vec<DwTag>) -> Self {
        let mut layouts: Vec<(DwTag, AttributeStructLayout)> = Vec::new();
        for (tags, layout) in layout_groups {
            for tag in tags {
                layouts.push((tag, layout.clone()));
            }
        }
        for tag in [DW_TAG_compile_unit, DW_TAG_partial_unit, DW_TAG_type_unit] {
            layouts.push((tag, UnitLateAttributes::layout()));
        }

        layouts.sort_unstable_by_key(|(t, _)| *t);
        for i in 0..layouts.len()-1 {
            if layouts[i].0 == layouts[i+1].0 {
                panic!("multiple struct layouts for tag {}", layouts[i].0);
            }
        }

        let num_primary_layouts = layouts.len();
        let secondary_layout_idx = layouts.len();
        layouts.push((DW_TAG_null, secondary_layout));
        let unit_layout_idx = layouts.len();
        layouts.push((DW_TAG_null, UnitEarlyAttributes::layout()));
        let empty_layout_idx = layouts.len();
        layouts.push((DW_TAG_null, AttributeStructLayout::default()));
        for (_, l) in &mut layouts {
            l.preprocess();
        }
        secondary_tags.sort_unstable();
        Self {layouts, num_primary_layouts, secondary_layout_idx, unit_layout_idx, empty_layout_idx, secondary_tags}
    }

    fn find(&self, tag: DwTag) -> Option<usize> {
        let i = self.layouts[..self.num_primary_layouts].partition_point(|(t, _)| *t < tag);
        if i < self.num_primary_layouts && self.layouts[i].0 == tag {
            Some(i)
        } else {
            None
        }
    }

    fn find_secondary(&self, tag: DwTag) -> Option<usize> {
        if tag == DW_TAG_compile_unit || tag == DW_TAG_partial_unit || tag == DW_TAG_type_unit {
            Some(self.unit_layout_idx)
        } else if self.secondary_tags.contains(&tag) {
            Some(self.secondary_layout_idx)
        } else {
            None
        }
    }
}

#[derive(Default)]
struct FormWarningLimiter {
    warnings_printed: Mutex<HashSet<(DwAt, DwForm)>>,
}
impl FormWarningLimiter {
    fn warn(&self, name: DwAt, form: DwForm) -> bool {
        // If this turns out to be slow, can use RW mutex with double-checked locking, since the set should be very small.
        let mut set = self.warnings_printed.lock().unwrap();
        set.insert((name, form))
    }
}

pub struct AbbreviationsSharedData {
    layouts: AllAttributeStructLayouts,
    warnings: FormWarningLimiter,
    pub unsupported_features: DwarfUnsupportedFeatures,

    actions_pool: Vec<AttributeAction>,
    abbreviations_pool: Vec<Abbreviation>,
    code_to_idx_pool: Vec<(/*code*/ usize, /*idx_in_abbreviations_pool*/ usize)>,
}

#[derive(Clone)]
pub struct AttributeContext<'a> {
    // TODO: Try inlining frequently accessed fields of these structs here for speed.
    pub unit: &'a DwarfUnit,
    pub dwarf: &'a Dwarf<DwarfSlice>,
    pub shared: &'a AbbreviationsSharedData,
}
impl<'a> AttributeContext<'a> {
    pub fn switch_unit(&mut self, unit: &'a DwarfUnit) {
        self.unit = unit;
    }
}

// What to do with an attribute: which forms to expect, what output type to produce, what conversions to apply.
// Approximately maps to DWARF's "attribute class" (as in DWARF 5 spec).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AttributeType {
    // Type: &'static str.
    // Class: string.
    // Forms: DW_FORM_string, DW_FORM_strp, DW_FORM_line_strp, DW_FORM_strp_sup, DW_FORM_strx{,1,2,3,4}.
    String,
    // Type: &'static [u8].
    // Class: string, block; also, DW_FORM_data16.
    // Forms: DW_FORM_block{,1,2,4}, DW_FORM_data16, and all String forms.
    Slice,
    // Type: usize.
    // Class: constant, excluding data16, sdata, and implicit_const.
    // Forms: DW_FORM_data{1,2,4,8}, DW_FORM_udata.
    Unsigned,
    // Type: isize.
    // Class: constant, only sdata or implicit_const.
    // Forms: DW_FORM_sdata, DW_FORM_implicit_const.
    Signed, // isize
    // Type: usize. Signed value is bit-cast to unsigned.
    // Class: constant: excluding data16.
    // Forms: Unsigned + Signed.
    MaybeSigned,
    // Type: usize (UnitOffset).
    // Class: reference, only within-unit (i.e. not DW_FORM_ref_addr).
    // Forms: DW_FORM_ref{1,2,4,8,_udata}.
    UnitOffset,
    // Type: usize (DebugInfoOffset).
    // Class: reference.
    // Forms: DW_FORM_ref{1,2,4,8,_udata}, DW_FORM_ref_addr.
    // Unit offset is converted to .debug_info offset.
    DebugInfoOffset,
    // Type: usize.
    // Class: address.
    // Forms: DW_FORM_addr, DW_FORM_addrx{,1,2,3,4}, DW_FORM_GNU_addr_index.
    Address,
    // Type: Expression, aka &'static [u8].
    // Class: exprloc.
    // Forms: DW_FORM_exprloc.
    Expression,
    // Type: LocationListsOffset, aka usize.
    // Class: loclist.
    // Forms: DW_FORM_loclistx, DW_FORM_sec_offset.
    LocationListsOffset,
    // Type: bool.
    // Class: flag.
    // Forms: DW_FORM_flag, DW_FORM_flag_present.
    Flag,
    // Type: usize.
    // Class: lineptr, loclistsptr, etc.
    // Forms: DW_FORM_sec_offset.
    SectionOffset,

    // Groups of attributes that are special-cased and grouped into sub-structs for convenience.

    // Type: DwarfRanges.
    // Attributes: DW_AT_ranges (rnglist), DW_AT_low_pc (address), DW_AT_high_pc (address or constant), DW_AT_entry_pc (address or constant).
    // DW_AT_ranges forms: DW_FORM_rnglistx, DW_FORM_sec_offset.
    // Upper bits of the `fields` bitmask will indicate which fields of DwarfRanges were set. See constants in DwarfRanges.
    Ranges,
    // Type: DwarfCodeLocation.
    // If declared with attribute name DW_AT_decl_file, matches attributes DW_AT_decl_file, DW_AT_decl_line, DW_AT_decl_column.
    // If declared with attribute name DW_AT_call_file, matches attributes DW_AT_call_file, DW_AT_call_line, DW_AT_call_column.
    // The `fields` bit is set iff DW_AT_decl_file/DW_AT_call_file is present.
    CodeLocation,
    // Type: DwarfReference, aka usize.
    // Attributes: DW_AT_specification, DW_AT_abstract_origin.
    // Class: reference.
    // Forms: DW_FORM_ref{1,2,4,8,_udata}, DW_FORM_ref_addr.
    // Normally at most one of these two attributes is present, so we merge them into one field.
    // If either of the attributes is present, bit DwarfReference::HAS_SPECIFICATION_OR_ABSTRACT_ORIGIN is set in `fields`.
    // The attribute may have offset relative to the current unit or relative to the whole .debug_info section. In the latter case, bit DwarfReference::GLOBAL is set in `fields`.
    SpecificationOrAbstractOrigin,
}

#[macro_export]
macro_rules! dwarf_field_mask_constants {
    (($counter:expr, {})) => {}; // base case

    (($counter:expr, { $field:ident, $($rest:ident,)* })) => { // recursive case
        pub const $field: u32 = 1 << ($counter);
        dwarf_field_mask_constants!(($counter + 1, { $($rest,)* }));
    };
}

// Example usage:
//
// dwarf_struct!{ MyStruct {
//     range_lists: RangeListsOffset, DW_AT_ranges, RangeLists;
//     low_pc: usize, DW_AT_low_pc, Address;
//     high_pc_addr: usize, DW_AT_high_pc, Address;
//     high_pc_num: usize, DW_AT_high_pc, Unsigned;
// }}
//
//
// Expands into approximately:
//
// struct MyStruct {
//     range_lists: RangeListsOffset,
//     low_pc: usize,
//     high_pc_addr: usize,
//     high_pc_num: usize,
//
//     fields: u32, // bitmask saying which fields were assigned
// }
// impl MyStruct {
//     // Bits in the `fields` mask.
//     const range_lists: u32 = 1 << 0;
//     const low_pc: u32 = 1 << 1;
//     const high_pc_addr: u32 = 1 << 2;
//     const high_pc_num: u32 = 1 << 3;
//
//     fn layout() -> AttributeStructLayout {
//         AttributeStructLayout {fields: vec![
//             (offsetof!(Self, range_lists) as u32, DW_AT_ranges, AttributeType::RangeLists),
//             (offsetof!(Self, low_pc) as u32, DW_AT_low_pc, AttributeType::Address),
//             (offsetof!(Self, high_pc_addr) as u32, DW_AT_high_pc, AttributeType::Address),
//             (offsetof!(Self, high_pc_num) as u32, DW_AT_high_pc, AttributeType::Unsigned),
//         ]}
//     }
// }
//
//
// If multiple fields have the same attribute name, the first one that matches the form will be assigned.
// E.g. in the example above high_pc_addr will be assigned if the attribute has form DW_FORM_addr*, high_pc_num will be assigned if DW_FORM_data*/DW_FORM_udata.

#[macro_export]
macro_rules! dwarf_struct {
    ($name:ident {
        $($field:ident: $type:ty, $dw_at:ident, $attribute_type:ident;)*
    }) => {
        #[derive(Default)]
        pub struct $name {
            pub $($field: $type,)*

            pub fields: u32,
        }

        impl $name {
            dwarf_field_mask_constants!((0, {$($field,)*}));

            pub fn layout() -> AttributeStructLayout {
                AttributeStructLayout {
                    flags_offset: std::mem::offset_of!(Self, fields) as u32,
                    fields: vec![$(
                        (
                            std::mem::offset_of!(Self, $field) as u32,
                            gimli::constants::$dw_at,
                            dwarf::AttributeType::$attribute_type,
                        ),
                    )*],

                    num_fields_included_in_flags: 0,
                }
            }
        }
    };
}

// Special type that can be used in dwarf_struct!():
//   ranges: DwarfRanges, DW_AT_ranges, AttributeType::Ranges;
// Covers 4 attributes (even though only one is explicitly given to dwarf_struct!()): DW_AT_ranges, DW_AT_low_pc, DW_AT_high_pc, DW_AT_entry_pc.
#[derive(Default)]
pub struct DwarfRanges {
    pub ranges: usize, // offset in .debug_ranges or .debug_rnglists
    pub low_pc: usize,
    pub high_pc: usize,
    pub entry_pc: usize,
}
impl DwarfRanges {
    // These bits would be set in the parent struct's `fields` bitmask.
    // (Make sure to not clash with the bit in DwarfReference. Also keep it in sync with the assert in AttributeStructLayout.preprocess())
    pub const RANGES: u32 = 1 << 24;
    pub const LOW_PC: u32 = 1 << 25;
    pub const HIGH_PC: u32 = 1 << 26;
    // Set if the DW_AT_high_pc had data form (i.e. it needs to be added to low_pc), unset if address form.
    pub const HIGH_PC_IS_RELATIVE: u32 = 1 << 27;
    pub const ENTRY_PC: u32 = 1 << 28;
    pub const ENTRY_PC_IS_RELATIVE: u32 = 1 << 29;
}

#[derive(Default, Clone, Copy)]
pub struct DwarfReference {
    pub offset: usize,
}
impl DwarfReference {
    // (Keep these from clashing with bits in DwarfRanges and in sync with assert in preprocess().)
    pub const HAS_SPECIFICATION_OR_ABSTRACT_ORIGIN: u32 = 1 << 30;
    pub const GLOBAL: u32 = 1 << 31;
}

#[derive(Default, Clone, Copy)]
pub struct DwarfCodeLocation {
    pub file: usize,
    pub line: usize,
    pub column: usize,
}

pub struct DwarfUnit {
    pub offset: DieOffset,
    pub unit: Unit<DwarfSlice>,
    pub abbreviation_set: AbbreviationSet,

    pub name: &'static str,
    pub comp_dir: &'static str,
    pub language: LanguageFamily,

    pub ranges: DwarfRanges,
    pub fields: u32, // for `ranges`

    // These are used by Symbols.
    pub shard_idx: usize,
    pub file_idx_remap: Vec<usize>, // DWARF file index -> index in Symbols.files
}

dwarf_struct!{ UnitEarlyAttributes {
    // Be careful to not include any attributes that may require knowing unit's section offsets. E.g. name, comp_dir, low_pc can't be here.
    str_offsets_base: usize, DW_AT_str_offsets_base, SectionOffset;
    addr_base: usize, DW_AT_addr_base, SectionOffset;
    loclists_base: usize, DW_AT_loclists_base, SectionOffset;
    rnglists_base: usize, DW_AT_rnglists_base, SectionOffset;
}}

dwarf_struct!{ UnitLateAttributes {
    name: &'static str, DW_AT_name, String;
    comp_dir: &'static str, DW_AT_comp_dir, String;
    ranges: DwarfRanges, DW_AT_ranges, Ranges;
    language: usize, DW_AT_language, Unsigned;
    stmt_list: usize, DW_AT_stmt_list, SectionOffset; // (this could be in UnitEarlyAttributes, but more convenient here)
}}

pub fn list_units(dwarf: &mut Dwarf<DwarfSlice>, binary_name: &str, layouts: AllAttributeStructLayouts) -> Result<(Vec<DwarfUnit>, AbbreviationsSharedData)> {
    let mut shared = AbbreviationsSharedData {layouts, warnings: FormWarningLimiter::default(), unsupported_features: DwarfUnsupportedFeatures::empty(), actions_pool: Vec::new(), abbreviations_pool: Vec::new(), code_to_idx_pool: Vec::new()};

    let mut unit_headers: Vec<(UnitHeader<DwarfSlice>, AbbreviationSet)> = Vec::new();
    let mut abbrev_offsets: Vec<((/*offset*/ usize, Encoding), /*unit_idx*/ usize)> = Vec::new();
    {
        let _prof = ProfileScope::with_threshold(0.01, format!("listing units ({})", binary_name));
        let mut iter = dwarf.debug_info.units();
        while let Some(header) = iter.next()? {
            abbrev_offsets.push(((header.debug_abbrev_offset().0, header.encoding()), unit_headers.len()));
            unit_headers.push((header, AbbreviationSet::new()));
        }
    }
    {
        let _prof = ProfileScope::with_threshold(0.01, format!("loading abbreviations ({})", binary_name));
        abbrev_offsets.sort_unstable_by_key(|((offset, encoding), _)| (*offset, encoding.address_size, encoding.format == Format::Dwarf64, encoding.version));
        let mut off_start = 0usize;
        let mut all_consecutive = true;
        // serialized abbreviation -> index in abbreviations_pool
        let mut abbrev_dedup: HashMap<&'static [u8], usize> = HashMap::new();
        let mut attributes: Vec<AttributeSpecification> = Vec::new();
        while off_start < abbrev_offsets.len() {
            let &(offset, encoding) = &abbrev_offsets[off_start].0;
            let mut off_end = off_start + 1;
            while off_end < abbrev_offsets.len() && abbrev_offsets[off_end].0 == (offset, encoding) {
                off_end += 1;
            }

            let code_to_idx_start = shared.code_to_idx_pool.len();
            shared.code_to_idx_pool.push((0, 0));
            let (mut consecutive, mut sorted) = (true, true);
            let mut prev_code = 0;

            let mut reader = SliceReader::new(dwarf.debug_abbrev.reader().slice());
            reader.skip(offset);
            loop {
                let code = reader.read_uleb128_or_zero();
                if code == 0 {
                    reader.check()?;
                    break;
                }

                let abbrev_slice = reader.as_slice();

                let tag = reader.read_uleb128_u16_or_zero();
                if tag == 0 {
                    reader.check()?;
                    return err!(Dwarf, "abbreviation has tag 0");
                }
                let tag = DwTag(tag);
                let has_children = reader.read_u8_or_zero();
                if has_children > 1 {
                    reader.check()?;
                    return err!(Dwarf, "invalid has_children value in abbreviation");
                }

                attributes.clear();
                loop {
                    let name = reader.read_uleb128_u16_or_zero();
                    let form = reader.read_uleb128_u16_or_zero();
                    if name == 0 || form == 0 {
                        reader.check()?;
                        if name != 0 || form != 0 {
                            return err!(Dwarf, "invalid name/form pair in attribute specification");
                        }
                        break;
                    }
                    let implicit_const_value = if form == DW_FORM_implicit_const.0 {
                        reader.read_sleb128_or_zero() as usize
                    } else {
                        0
                    };
                    attributes.push(AttributeSpecification {name: DwAt(name), form: DwForm(form), implicit_const_value});
                }

                let abbrev_slice = &abbrev_slice[..reader.offset_from(abbrev_slice)];
                let abbrev_idx = match abbrev_dedup.entry(abbrev_slice) {
                    Entry::Occupied(o) => *o.get(),
                    Entry::Vacant(v) => {
                        let mut actions = [AbbreviationActions::default(), AbbreviationActions::default(), AbbreviationActions::default()];
                        if let Some(layout_idx) = shared.layouts.find(tag) {
                            actions[0] = prepare_abbreviation_actions(&attributes, layout_idx, encoding, &mut shared)?;
                        }
                        if let Some(layout_idx) = shared.layouts.find_secondary(tag) {
                            actions[1] = prepare_abbreviation_actions(&attributes, layout_idx, encoding, &mut shared)?;
                        }
                        actions[2] = prepare_abbreviation_actions(&attributes, shared.layouts.empty_layout_idx, encoding, &mut shared)?;

                        let idx = shared.abbreviations_pool.len();
                        shared.abbreviations_pool.push(Abbreviation {tag, has_children: has_children != 0, actions});
                        v.insert(idx);
                        idx
                    }
                };

                shared.code_to_idx_pool.push((code, abbrev_idx));

                if code != prev_code + 1 {
                    consecutive = false;
                    if code <= prev_code {
                        sorted = false;
                    }
                }
                prev_code = code;
            }
            reader.check()?;

            let code_to_idx = code_to_idx_start..shared.code_to_idx_pool.len();

            if !sorted {
                let slice = &mut shared.code_to_idx_pool[code_to_idx.clone()];
                slice.sort_unstable_by_key(|a| a.0);
                for i in 0..slice.len()-1 {
                    if slice[i].0 == slice[i+1].0 {
                        return err!(Dwarf, "duplicate abbreviation code: {}", slice[i].0);
                    }
                }
            }
            all_consecutive &= consecutive;

            let set = AbbreviationSet {code_to_idx, consecutive};
            for i in off_start+1..off_end {
                unit_headers[abbrev_offsets[i].1].1 = set.clone();
            }
            unit_headers[abbrev_offsets[off_start].1].1 = set;

            off_start = off_end;
        }

        if !all_consecutive {
            eprintln!("info: not all abbreviation codes are consecutive ({})", binary_name)
        }
    }
    let mut units: Vec<DwarfUnit> = Vec::with_capacity(unit_headers.len());
    {
        let _prof = ProfileScope::with_threshold(0.01, format!("preparing units ({})", binary_name));
        for (header, abbreviation_set) in unit_headers {
            let offset = match header.offset() {
                UnitSectionOffset::DebugInfoOffset(o) => o,
                _ => return err!(Internal, "unit offset has unexpected type"),
            };
            let mut unit = DwarfUnit {
                offset,
                unit: Unit {
                    header,
                    // We don't use these, have our own implementation.
                    abbreviations: Arc::new(Abbreviations::default()), name: None, comp_dir: None,
                    // We'll assign these below.
                    low_pc: 0, str_offsets_base: DebugStrOffsetsBase(0), addr_base: DebugAddrBase(0), loclists_base: DebugLocListsBase(0),
                    rnglists_base: DebugRngListsBase(0), line_program: None,
                    dwo_id: None, // not supported
                },
                abbreviation_set,
                name: "", comp_dir: "", ranges: DwarfRanges::default(), fields: 0, language: LanguageFamily::Unknown, shard_idx: 0, file_idx_remap: Vec::new(),
            };
            let attribute_context = AttributeContext {unit: &unit, dwarf, shared: &shared};

            let initial_cursor = SliceReader::new(header.range_from(UnitOffset(unit.unit.header.header_size())..)?.slice());

            // Have to read attributes twice: first to get base section offsets, then other attributes (which may need section offsets to interpret).
            // (We could be slightly more efficient and remember uninterpreted attributes instead of re-parsing them from bytes,
            //  but it probably doesn't matter because there are only tens of thousands of units.)

            let mut cursor = initial_cursor.clone();
            let Some(abbrev) = cursor.read_abbreviation(&attribute_context)? else { return err!(Dwarf, "unit missing root DIE") };
            let mut attrs = UnitEarlyAttributes::default();
            unsafe {cursor.read_attributes(&abbrev, /*which_layout*/ 1, &attribute_context, &raw mut attrs as *mut u8)?};

            unit.unit.str_offsets_base = DebugStrOffsetsBase(attrs.str_offsets_base);
            unit.unit.addr_base = DebugAddrBase(attrs.addr_base);
            unit.unit.loclists_base = DebugLocListsBase(attrs.loclists_base);
            unit.unit.rnglists_base = DebugRngListsBase(attrs.rnglists_base);

            let attribute_context = AttributeContext {unit: &unit, dwarf, shared: &shared};
            let mut cursor = initial_cursor.clone();
            let Some(abbrev) = cursor.read_abbreviation(&attribute_context)? else { return err!(Sanity, "file changed") }; // re-lookup because of borrow checker
            let mut attrs = UnitLateAttributes::default();
            unsafe {cursor.read_attributes(&abbrev, /*which_layout*/ 0, &attribute_context, &raw mut attrs as *mut u8)?};

            if attrs.fields & UnitLateAttributes::stmt_list != 0 {
                unit.unit.line_program = Some(dwarf.debug_line.program(DebugLineOffset(attrs.stmt_list), unit.unit.header.address_size(), Some(DwarfSlice::new(attrs.comp_dir.as_bytes())), Some(DwarfSlice::new(attrs.name.as_bytes())))?);
            }
            unit.unit.low_pc = attrs.ranges.low_pc as u64;

            unit.name = attrs.name;
            unit.comp_dir = attrs.comp_dir;
            unit.ranges = attrs.ranges;
            unit.fields = attrs.fields;
            unit.language = match DwLang(attrs.language as u16) {
                // Unfortunately the C_plus_plus_* constants don't follow any predictable pattern, so we'll have to update this list every few years as new C++ versions are added to DWARF.
                DW_LANG_C | DW_LANG_C11 | DW_LANG_C17 | DW_LANG_C89 | DW_LANG_C99 | DW_LANG_C_plus_plus | DW_LANG_C_plus_plus_03 | DW_LANG_C_plus_plus_11 | DW_LANG_C_plus_plus_14 | DW_LANG_C_plus_plus_17 | DW_LANG_C_plus_plus_20 => LanguageFamily::Cpp,
                DW_LANG_Rust => LanguageFamily::Rust,
                _ => LanguageFamily::Other,
            };

            units.push(unit);
        }
    }

    Ok((units, shared))
}

// Boilerplate adapter so that we can use gimli parsing code for some things.
impl gimli::Reader for DwarfSlice {
    type Endian = LittleEndian;
    type Offset = usize;
    fn endian(&self) -> Self::Endian {LittleEndian::default()}

    // Boring adapters.
    fn len(&self) -> usize {self.n}
    fn empty(&mut self) {self.n = 0;}
    fn truncate(&mut self, len: usize) -> gimli::Result<()> {if len > self.n {Err(gimli::Error::UnexpectedEof(self.offset_id()))} else {self.n = len; Ok(())}}
    fn offset_id(&self) -> ReaderOffsetId {ReaderOffsetId(self.p as u64)}
    fn lookup_offset_id(&self, id: ReaderOffsetId) -> Option<usize> {let ptr = self.p as u64; if id.0 >= ptr && id.0 <= ptr + self.n as u64 {Some((id.0 - ptr) as usize)} else {None}}
    fn skip(&mut self, len: usize) -> gimli::Result<()> {self.read_bytes(len)?; Ok(())}
    fn split(&mut self, len: usize) -> gimli::Result<Self> {Ok(Self::new(self.read_bytes(len)?))}
    fn to_slice(&self) -> gimli::Result<Cow<'_, [u8]>> {Ok(self.slice().into())}
    fn to_string_lossy(&self) -> gimli::Result<Cow<'_, str>> {Ok(String::from_utf8_lossy(self.slice()))}
    fn to_string(&self) -> gimli::Result<Cow<'_, str>> {match str::from_utf8(self.slice()) {Ok(s) => Ok(s.into()), _ => Err(gimli::Error::BadUtf8)}} // unused, no need to optimize
    fn read_slice(&mut self, buf: &mut [u8]) -> gimli::Result<()> {buf.copy_from_slice(self.read_bytes(buf.len())?); Ok(())}
    fn offset_from(&self, base: &Self) -> usize {
        let base_ptr = base.p as usize;
        let ptr = self.p as usize;
        debug_assert!(ptr >= base_ptr && ptr <= base_ptr + base.n);
        ptr - base_ptr
    }

    // Functions that have slow default implementations in gimli and need to be optimized.

    #[inline]
    fn find(&self, byte: u8) -> gimli::Result<usize> {
        if byte == 0 {
            let len = unsafe {strlen_padded(self.p, self.n)};
            if len >= self.n {
                Err(gimli::Error::UnexpectedEof(self.offset_id()))
            } else {
                Ok(len)
            }
        } else {
            for i in 0..self.n {
                if unsafe {*self.p.add(i)} == byte {
                    return Ok(i);
                }
            }
            Err(gimli::Error::UnexpectedEof(self.offset_id()))
        }
    }

    fn read_u8(&mut self) -> gimli::Result<u8> {Ok(self.read_bytes(1)?[0])}
    fn read_u16(&mut self) -> gimli::Result<u16> {Ok(u16::from_le_bytes(self.read_bytes(2)?.try_into().unwrap()))}
    fn read_u32(&mut self) -> gimli::Result<u32> {Ok(u32::from_le_bytes(self.read_bytes(4)?.try_into().unwrap()))}
    fn read_u64(&mut self) -> gimli::Result<u64> {Ok(u64::from_le_bytes(self.read_bytes(8)?.try_into().unwrap()))}

    fn read_i8(&mut self) -> gimli::Result<i8> {Ok(self.read_u8()? as i8)}
    fn read_i16(&mut self) -> gimli::Result<i16> {Ok(self.read_u16()? as i16)}
    fn read_i32(&mut self) -> gimli::Result<i32> {Ok(self.read_u32()? as i32)}
    fn read_i64(&mut self) -> gimli::Result<i64> {Ok(self.read_u64()? as i64)}
    fn read_f32(&mut self) -> gimli::Result<f32> {Ok(f32::from_bits(self.read_u32()?))}
    fn read_f64(&mut self) -> gimli::Result<f64> {Ok(f64::from_bits(self.read_u64()?))}

    fn skip_leb128(&mut self) -> gimli::Result<()> {
        // TODO: Optimize.
        while self.read_u8()? >= 128 {}
        Ok(())
    }

    fn read_uleb128(&mut self) -> gimli::Result<u64> {
        // TODO: Make it fast using simd and/or bit tricks. The input is padded, so it's safe to e.g. start by reading 8 bytes into a usize instead of checking for eof after every byte.
        let mut r = 0u64;
        let mut shift = 0u32;
        loop {
            if self.n == 0 {
                return Err(gimli::Error::UnexpectedEof(self.offset_id()));
            }
            let b = unsafe {*self.p};
            self.p = unsafe {self.p.add(1)};
            self.n -= 1;
            if shift == 63 && b > 1 {
                return Err(gimli::Error::BadUnsignedLeb128);
            }
            r |= ((b & 0x7f) as u64) << shift;
            if b < 128 {
                return Ok(r);
            }
            shift += 7;
        }
    }

    fn read_uleb128_u32(&mut self) -> gimli::Result<u32> {
        let r = self.read_uleb128()?;
        if r > u32::MAX as u64 {
            Err(gimli::Error::BadUnsignedLeb128)
        } else {
            Ok(r as u32)
        }
    }
}


const DW_FORM_addr: DwForm = DwForm(0x01);
const DW_FORM_block2: DwForm = DwForm(0x03);
const DW_FORM_block4: DwForm = DwForm(0x04);
const DW_FORM_data2: DwForm = DwForm(0x05);
const DW_FORM_data4: DwForm = DwForm(0x06);
const DW_FORM_data8: DwForm = DwForm(0x07);
const DW_FORM_string: DwForm = DwForm(0x08);
const DW_FORM_block: DwForm = DwForm(0x09);
const DW_FORM_block1: DwForm = DwForm(0x0a);
const DW_FORM_data1: DwForm = DwForm(0x0b);
const DW_FORM_flag: DwForm = DwForm(0x0c);
const DW_FORM_sdata: DwForm = DwForm(0x0d);
const DW_FORM_strp: DwForm = DwForm(0x0e);
const DW_FORM_udata: DwForm = DwForm(0x0f);
const DW_FORM_ref_addr: DwForm = DwForm(0x10);
const DW_FORM_ref1: DwForm = DwForm(0x11);
const DW_FORM_ref2: DwForm = DwForm(0x12);
const DW_FORM_ref4: DwForm = DwForm(0x13);
const DW_FORM_ref8: DwForm = DwForm(0x14);
const DW_FORM_ref_udata: DwForm = DwForm(0x15);
const DW_FORM_indirect: DwForm = DwForm(0x16);
const DW_FORM_sec_offset: DwForm = DwForm(0x17);
const DW_FORM_exprloc: DwForm = DwForm(0x18);
const DW_FORM_flag_present: DwForm = DwForm(0x19);
const DW_FORM_ref_sig8: DwForm = DwForm(0x20);
const DW_FORM_strx: DwForm = DwForm(0x1a);
const DW_FORM_addrx: DwForm = DwForm(0x1b);
const DW_FORM_ref_sup4: DwForm = DwForm(0x1c);
const DW_FORM_strp_sup: DwForm = DwForm(0x1d);
const DW_FORM_data16: DwForm = DwForm(0x1e);
const DW_FORM_line_strp: DwForm = DwForm(0x1f);
const DW_FORM_implicit_const: DwForm = DwForm(0x21);
const DW_FORM_loclistx: DwForm = DwForm(0x22);
const DW_FORM_rnglistx: DwForm = DwForm(0x23);
const DW_FORM_ref_sup8: DwForm = DwForm(0x24);
const DW_FORM_strx1: DwForm = DwForm(0x25);
const DW_FORM_strx2: DwForm = DwForm(0x26);
const DW_FORM_strx3: DwForm = DwForm(0x27);
const DW_FORM_strx4: DwForm = DwForm(0x28);
const DW_FORM_addrx1: DwForm = DwForm(0x29);
const DW_FORM_addrx2: DwForm = DwForm(0x2a);
const DW_FORM_addrx3: DwForm = DwForm(0x2b);
const DW_FORM_addrx4: DwForm = DwForm(0x2c);
const DW_FORM_GNU_addr_index: DwForm = DwForm(0x1f01);
const DW_FORM_GNU_str_index: DwForm = DwForm(0x1f02);
const DW_FORM_GNU_ref_alt: DwForm = DwForm(0x1f20);
const DW_FORM_GNU_strp_alt: DwForm = DwForm(0x1f21);

// These are not actual DWARF forms, I made these numbers up. If future versions of the standard clash with these values, change them. (Or change the type to u32 and use values >= 2^16.)
const DW_EXTRA_FORM_skip_bytes: DwForm = DwForm(0xfe00);
const DW_EXTRA_FORM_skip_leb128: DwForm = DwForm(0xfe01);
const DW_EXTRA_FORM_skip_block: DwForm = DwForm(0xfe02);
const DW_EXTRA_FORM_skip_block1: DwForm = DwForm(0xfe03);
const DW_EXTRA_FORM_skip_block2: DwForm = DwForm(0xfe04);
const DW_EXTRA_FORM_skip_block4: DwForm = DwForm(0xfe05);
const DW_EXTRA_FORM_skip_string: DwForm = DwForm(0xfe06);
const DW_EXTRA_FORM_strp4: DwForm = DwForm(0xfe07);
const DW_EXTRA_FORM_strp8: DwForm = DwForm(0xfe08);
const DW_EXTRA_FORM_line_strp4: DwForm = DwForm(0xfe09);
const DW_EXTRA_FORM_line_strp8: DwForm = DwForm(0xfe0a);
const DW_EXTRA_FORM_strp_sup4: DwForm = DwForm(0xfe0b);
const DW_EXTRA_FORM_strp_sup8: DwForm = DwForm(0xfe0c);


fn prepare_attribute_action(attr: AttributeSpecification, layout: &AttributeStructLayout, encoding: Encoding, warnings: &FormWarningLimiter, unsupported_features: &mut DwarfUnsupportedFeatures, flags: &mut u32) -> Result<AttributeAction> {
    assert!(attr.form != DW_FORM_indirect);

    let unsupported_form = match attr.form {
        DW_FORM_ref_sig8 => {
            unsupported_features.insert(DwarfUnsupportedFeatures::TYPE_SIGNATURES);
            true
        }
        DW_FORM_ref_sup4 | DW_FORM_ref_sup8 | DW_FORM_GNU_ref_alt | DW_FORM_strp_sup | DW_EXTRA_FORM_strp_sup4 | DW_EXTRA_FORM_strp_sup8 | DW_FORM_GNU_strp_alt =>
        {
            unsupported_features.insert(DwarfUnsupportedFeatures::SUPPLEMENTARY_OBJECT_FILES);
            true
        }
        _ => false,
    };

    let mut found_name = false;
    for i in 0..layout.fields.len() {
        let &(field_offset, attr_name, attr_type) = &layout.fields[i];
        if attr_name != attr.name{
            continue;
        }
        found_name = true;

        if unsupported_form {
            break;
        }
        
        let mut found_match = true;
        let mut form = attr.form;
        let mut param = 0usize;
        match attr_type {
            AttributeType::String => match attr.form {
                DW_FORM_string | DW_FORM_strp | DW_FORM_line_strp | DW_FORM_strp_sup | DW_FORM_strx | DW_FORM_strx1 | DW_FORM_strx2 | DW_FORM_strx3 | DW_FORM_strx4 | DW_FORM_GNU_str_index | DW_FORM_GNU_strp_alt => param = 1,
                _ => found_match = false,
            }
            AttributeType::Slice => match attr.form {
                DW_FORM_block | DW_FORM_block1 | DW_FORM_block2 | DW_FORM_block4 | DW_FORM_string | DW_FORM_strp | DW_FORM_line_strp | DW_FORM_strp_sup | DW_FORM_strx | DW_FORM_strx1 | DW_FORM_strx2 | DW_FORM_strx3 | DW_FORM_strx4 | DW_FORM_data16 | DW_FORM_GNU_str_index | DW_FORM_GNU_strp_alt => (),
                _ => found_match = false,
            }
            AttributeType::Unsigned => match attr.form {
                DW_FORM_data1 | DW_FORM_data2 | DW_FORM_data4 | DW_FORM_data8 | DW_FORM_udata => (),
                DW_FORM_implicit_const => param = attr.implicit_const_value, // or maybe we should check that it's <= i64::MAX, since implicit_const is, in theory, signed
                _ => found_match = false,
            }
            AttributeType::Signed => match attr.form {
                DW_FORM_sdata => (),
                DW_FORM_implicit_const => param = attr.implicit_const_value,
                _ => found_match = false,
            }
            AttributeType::MaybeSigned => match attr.form {
                DW_FORM_data1 | DW_FORM_data2 | DW_FORM_data4 | DW_FORM_data8 | DW_FORM_udata | DW_FORM_sdata => (),
                DW_FORM_implicit_const => param = attr.implicit_const_value,
                _ => found_match = false,
            }
            AttributeType::UnitOffset => match attr.form {
                DW_FORM_ref1 | DW_FORM_ref2 | DW_FORM_ref4 | DW_FORM_ref8 | DW_FORM_ref_udata => (),
                _ => found_match = false,
            }
            AttributeType::DebugInfoOffset => match attr.form {
                DW_FORM_ref1 | DW_FORM_ref2 | DW_FORM_ref4 | DW_FORM_ref8 | DW_FORM_ref_udata | DW_FORM_ref_addr => param = 1,
                _ => found_match = false,
            }
            AttributeType::Address => match attr.form {
                DW_FORM_addr | DW_FORM_addrx | DW_FORM_addrx1 | DW_FORM_addrx2 | DW_FORM_addrx3 | DW_FORM_addrx4 | DW_FORM_GNU_addr_index => (),
                _ => found_match = false,
            }
            AttributeType::Expression => match attr.form {
                DW_FORM_exprloc => (),
                _ => found_match = false,
            }
            AttributeType::LocationListsOffset => match attr.form {
                DW_FORM_loclistx | DW_FORM_sec_offset | DW_FORM_data4 | DW_FORM_data8 => (),
                _ => found_match = false,
            }
            AttributeType::Flag => match attr.form {
                DW_FORM_flag | DW_FORM_flag_present => (),
                _ => found_match = false,
            }
            AttributeType::SectionOffset => match attr.form {
                // Allow data4 and data8 to partially support DWARF 3.
                DW_FORM_sec_offset | DW_FORM_data4 | DW_FORM_data8 => (),
                _ => found_match = false,
            }

            AttributeType::Ranges => match attr.name {
                DW_AT_ranges => match attr.form {
                    // Compatibility: the sec_offset case would need additional logic to support split dwarf (dwo).
                    DW_FORM_rnglistx | DW_FORM_sec_offset | DW_FORM_data4 | DW_FORM_data8 => *flags |= DwarfRanges::RANGES,
                    _ => found_match = false,
                }
                DW_AT_low_pc => match attr.form {
                    DW_FORM_addr | DW_FORM_addrx | DW_FORM_addrx1 | DW_FORM_addrx2 | DW_FORM_addrx3 | DW_FORM_addrx4 => *flags |= DwarfRanges::LOW_PC,
                    _ => found_match = false,
                }
                DW_AT_high_pc => match attr.form {
                    DW_FORM_addr | DW_FORM_addrx | DW_FORM_addrx1 | DW_FORM_addrx2 | DW_FORM_addrx3 | DW_FORM_addrx4 => *flags |= DwarfRanges::HIGH_PC,
                    DW_FORM_data1 | DW_FORM_data2 | DW_FORM_data4 | DW_FORM_data8 | DW_FORM_udata => *flags |= DwarfRanges::HIGH_PC | DwarfRanges::HIGH_PC_IS_RELATIVE,
                    _ => found_match = false,
                }
                DW_AT_entry_pc => match attr.form {
                    DW_FORM_addr | DW_FORM_addrx | DW_FORM_addrx1 | DW_FORM_addrx2 | DW_FORM_addrx3 | DW_FORM_addrx4 => *flags |= DwarfRanges::ENTRY_PC,
                    DW_FORM_data1 | DW_FORM_data2 | DW_FORM_data4 | DW_FORM_data8 | DW_FORM_udata => *flags |= DwarfRanges::ENTRY_PC | DwarfRanges::ENTRY_PC_IS_RELATIVE,
                    _ => found_match = false,
                }
                _ => panic!("unexpected Ranges attribute name"),
            }
            AttributeType::SpecificationOrAbstractOrigin => {
                if *flags & DwarfReference::HAS_SPECIFICATION_OR_ABSTRACT_ORIGIN != 0 {
                    if warnings.warn(attr.name, attr.form) {
                        eprintln!("warning: an entry has both DW_AT_specification and DW_AT_abstract_origin");
                    }
                    // If both attributes are present, make sure we don't end up with the value from one of them but flag DwarfReference::GLOBAL from the other.
                    found_match = false;
                    found_name = false; // don't warn about unexpected form
                } else {
                    *flags |= DwarfReference::HAS_SPECIFICATION_OR_ABSTRACT_ORIGIN;
                    match attr.form {
                        DW_FORM_ref1 | DW_FORM_ref2 | DW_FORM_ref4 | DW_FORM_ref8 | DW_FORM_ref_udata => (),
                        DW_FORM_ref_addr => *flags |= DwarfReference::GLOBAL,
                        _ => found_match = false,
                    }
                }
            }
            AttributeType::CodeLocation => panic!("this was supposed to be preprocessed away"),
        }

        if found_match {
            // Some more form conversions to make life easier (and faster) for parser.
            match form {
                DW_FORM_GNU_str_index => form = DW_FORM_strx,
                DW_FORM_GNU_addr_index => form = DW_FORM_addrx,
                DW_FORM_ref_addr | DW_FORM_sec_offset => form = if encoding.format.word_size() == 4 {DW_FORM_data4} else {DW_FORM_data8},
                DW_FORM_strp => form = if encoding.format.word_size() == 4 {DW_EXTRA_FORM_strp4} else {DW_EXTRA_FORM_strp8},
                DW_FORM_line_strp => form = if encoding.format.word_size() == 4 {DW_EXTRA_FORM_line_strp4} else {DW_EXTRA_FORM_line_strp8},
                DW_FORM_strp_sup | DW_FORM_GNU_strp_alt => form = if encoding.format.word_size() == 4 {DW_EXTRA_FORM_strp_sup4} else {DW_EXTRA_FORM_strp_sup8},
                _ => (),
            }

            if i < layout.num_fields_included_in_flags as usize {
                *flags |= 1 << i;
            }
            return Ok(AttributeAction {form, field_offset, param});
        }
    }

    if found_name && warnings.warn(attr.name, attr.form) {
        eprintln!("warning: attribute {} form {} is not supported", attr.name, attr.form);
    }
    let (form, param): (DwForm, usize) = match attr.form {
        DW_FORM_addr => (DW_EXTRA_FORM_skip_bytes, encoding.address_size as usize),
        DW_FORM_strp | DW_FORM_ref_addr | DW_FORM_sec_offset | DW_FORM_strp_sup | DW_FORM_line_strp | DW_FORM_GNU_ref_alt | DW_FORM_GNU_strp_alt => (DW_EXTRA_FORM_skip_bytes, encoding.format.word_size() as usize),

        DW_FORM_data1 | DW_FORM_flag | DW_FORM_ref1 | DW_FORM_strx1 | DW_FORM_addrx1 => (DW_EXTRA_FORM_skip_bytes, 1),
        DW_FORM_data2 | DW_FORM_ref2 | DW_FORM_strx2 | DW_FORM_addrx2 => (DW_EXTRA_FORM_skip_bytes, 2),
        DW_FORM_strx3 | DW_FORM_addrx3 => (DW_EXTRA_FORM_skip_bytes, 3),
        DW_FORM_data4 | DW_FORM_ref4 | DW_FORM_ref_sup4 | DW_FORM_strx4 | DW_FORM_addrx4 => (DW_EXTRA_FORM_skip_bytes, 4),
        DW_FORM_data8 | DW_FORM_ref8 | DW_FORM_ref_sig8 | DW_FORM_ref_sup8 => (DW_EXTRA_FORM_skip_bytes, 8),
        DW_FORM_data16 => (DW_EXTRA_FORM_skip_bytes, 16),

        DW_FORM_string => (DW_EXTRA_FORM_skip_string, 0),

        DW_FORM_block | DW_FORM_exprloc => (DW_EXTRA_FORM_skip_block, 0),
        DW_FORM_block1 => (DW_EXTRA_FORM_skip_block1, 0),
        DW_FORM_block2 => (DW_EXTRA_FORM_skip_block2, 0),
        DW_FORM_block4 => (DW_EXTRA_FORM_skip_block4, 0),

        DW_FORM_sdata | DW_FORM_udata | DW_FORM_ref_udata | DW_FORM_strx | DW_FORM_addrx | DW_FORM_loclistx | DW_FORM_rnglistx | DW_FORM_GNU_addr_index | DW_FORM_GNU_str_index => (DW_EXTRA_FORM_skip_leb128, 0),

        DW_FORM_flag_present | DW_FORM_implicit_const => (DW_EXTRA_FORM_skip_bytes, 0),

        _ => return err!(Dwarf, "unknown form: {}", attr.form),
    };

    Ok(AttributeAction {form, param, field_offset: u32::MAX})
}

fn prepare_abbreviation_actions(attributes: &[AttributeSpecification], layout_idx: usize, encoding: Encoding, shared: &mut AbbreviationsSharedData) -> Result<AbbreviationActions> {
    let mut flags_value = 0u32;
    let actions_start = shared.actions_pool.len();
    let layout = &shared.layouts.layouts[layout_idx].1;

    for attr in attributes {
        if attr.form == DW_FORM_indirect {
            // DW_FORM_indirect is annoying and almost never used, so we don't have to support it. But we support it.
            // Defer the prepare_attribute_action() call till parsing time.
            shared.actions_pool.push(AttributeAction {form: DW_FORM_indirect, field_offset: u32::MAX, param: layout_idx << 16 | attr.name.0 as usize});
            continue;
        }

        let action = prepare_attribute_action(*attr, layout, encoding, &shared.warnings, &mut shared.unsupported_features, &mut flags_value)?;
        if action.form == DW_EXTRA_FORM_skip_bytes {
            if action.param == 0 {
                continue;
            }
            if shared.actions_pool.len() > actions_start && shared.actions_pool.last().unwrap().form == DW_EXTRA_FORM_skip_bytes {
                shared.actions_pool.last_mut().unwrap().param += action.param;
                continue;
            }
        }
        shared.actions_pool.push(action);
    }

    let actions_end = shared.actions_pool.len();
    if actions_end > u32::MAX as usize {
        return err!(Sanity, "more than 2^32 total attributes in abbreviations");
    }

    Ok(AbbreviationActions {flags_offset: layout.flags_offset, flags_value, actions: actions_start as u32 .. actions_end as u32})
}

// The input must have at least 15 readable bytes after the end of the string (we're reading in blocks of 16 bytes).
unsafe fn strlen_padded(s: *const u8, n: usize) -> usize {
    let mut ptr = s;
    let end = s.add(n);
    let zero = _mm_setzero_si128();
    while ptr < end {
        let v = _mm_loadu_si128(ptr as *const __m128i);
        let eq = _mm_cmpeq_epi8(v, zero);
        let mask = _mm_movemask_epi8(eq);
        if mask != 0 {
            let mut res = ptr as usize - s as usize;
            res += mask.trailing_zeros() as usize;
            return res
        }
        ptr = ptr.add(16);
    }
    n
}

// (We could merge this with strlen_padded() for more speed, but it doesn't seem likely to help much.)
unsafe fn is_ascii_padded(s: *const u8, n: usize) -> bool {
    let mut ptr = s;
    let end = s.add(n);
    while ptr < end {
        let v = _mm_loadu_si128(ptr as *const __m128i);
        let mask = _mm_movemask_epi8(v);
        if mask != 0 {
            let fail_pos = mask.trailing_zeros() as usize;
            return ptr.add(fail_pos) >= end;
        }
        ptr = ptr.add(16);
    }
    true
}

#[cfg(test)]
pub mod tests {
    use crate::dwarf::*;

    #[test]
    pub fn lebowski128() {
        let mut data = [0u8; 16];
        for it in 0..10000 {
            let signed = random::<bool>();
            let bits = (random::<u8>() % 64 + 1) as usize;
            let mut num = random::<usize>();
            if signed && bits < 64 && random::<bool>() {
                num |= (usize::MAX) << bits;
            } else {
                num &= usize::MAX >> (64 - bits);
            }
            for b in &mut data {
                *b = random::<u8>();
            }
            let len = if signed {
                gimli::leb128::write::signed(&mut &mut data[..], num as i64).unwrap()
            } else {
                gimli::leb128::write::unsigned(&mut &mut data[..], num as u64).unwrap()
            };

            let slice_ptr = data.as_ptr();
            let slice_len = random::<u8>() as usize % (data.len() + 1);
            let mut reader = SliceReader {p: slice_ptr, n: slice_len, unexpected_eof: false};

            let res = if signed {
                reader.read_sleb128_or_zero() as usize
            } else if bits <= 16 && random::<bool>() {
                assert!(len <= 3 && num <= u16::MAX as usize);
                reader.read_uleb128_u16_or_zero() as usize
            } else {
                reader.read_uleb128_or_zero()
            };
            if slice_len < len {
                assert!(reader.unexpected_eof);
                assert_eq!(reader.n, 0);
                assert_eq!(res, 0);
            } else {
                assert!(!reader.unexpected_eof);
                let read_bytes = reader.p as usize - slice_ptr as usize;
                assert_eq!(read_bytes, len);
                assert_eq!(reader.n, slice_len - read_bytes);
                assert_eq!(res, num);
            }
        }
    }

    #[test]
    pub fn strlen() {
        let mut data = [0u8; 1200];
        for it in 0..100 {
            let n = random::<usize>() % 1000;
            let start = random::<usize>() % 50;
            for i in 0..data.len() {
                data[i] = random::<u8>();
                while i >= start && i < start + n && data[i] == 0 {
                    data[i] = random::<u8>();
                }
            }
            data[start + n] = 0;
            let lim = random::<usize>() % 1000;
            let res = unsafe {strlen_padded(data[start..].as_ptr(), lim)};

            if lim <= n {
                assert!(res >= lim);
            } else {
                assert_eq!(res, n);
            }
        }
    }
}
