use crate::{*, error::{*, Result, Error}, util::*, elf::*, procfs::*, range_index::*, registers::*, log::*, arena::*, types::*, expr::{*, Value}, dwarf::*, os::*};
use std::{cmp, str, mem, rc::Rc, fs::File, path::{Path, PathBuf}, sync::atomic::{AtomicUsize, Ordering, AtomicBool}, sync::{Arc, Mutex}, collections::{HashMap, hash_map::{Entry, DefaultHasher}}, hash::{Hash, Hasher}, ffi::OsStr, os::unix::ffi::OsStrExt, io, io::{Read, Write as ioWrite}, fmt::Write, time::{Instant, Duration}, ptr, slice, fmt, borrow::Cow, thread, io::BufRead, hint};
use gimli::*;
use bitflags::*;
use std::ops::Range;

// Data structures for the program information: functions, variables, struct fields, etc.
//
// The main goal of this debugger is to work well with the bloated modern binaries with 3 GB of debug symbols.
// So it's important to make these data structures reasonably efficient and compact.
//
// (Note: this long comment at the top of this file is one of the first things written in this project. It's probably quite outdated and wrong and needs to be updated.)
//
// Some rough stats about a typical binary (clickhouse, DWARF4, written in C++, statically linked with lots of libraries, some in rust):
//  * Binary size: 2.4 GB
//  * Size of the .text section (i.e. the actual program): 303 MB
//  * Debug info section sizes:
//     .debug_line       132 MB
//     .debug_abbrev     14 MB
//     .debug_info       853 MB
//     .debug_aranges    6 MB
//     .debug_ranges     128 MB
//     .debug_str        332 MB
//     .debug_pubnames   6 MB
//     .debug_pubtypes   5 MB
//     .debug_loc        449 MB
//     .gdb_index        7 MB
//  * Other noteworthy sections:
//     .eh_frame         27 MB
//     .eh_frame_hdr     4 MB
//     .rodata section   59 MB
//     .symtab           21 MB
//     .strtab           99 MB
//  * Compilation units:                              33 K
//  * DWARF DIEs:                                     83 M
//  * DWARF attributes:                               275 M
//  * Functions:                                      600 K
//  * Functions with address range:                   12 M
//  * Structs/classes/unions/enums:                   2.3 M
//  * Fields of structs/classes/unions:               3 M
//  * Variables and function parameters:              38 M
//  * Variable loc ranges:                            21 M
//  * Inlined function calls:                         9 M
//  * Inline function ranges:                         12 M
//  * Total length of mangled function names:         926 MB
//  * Total length of fully-qualified function names: 1800 MB
//  * Total length of unqualified function names:     165 MB
//  * Total length of variable/arg/field names:       40 MB
//  * Total length of fully-qualified type names:     273 MB
//  * 73% of functions and 57% of types are template instantiations. This sounds suspiciously low, maybe I didn't count right.
//  * In .eh_frame:
//     - CIEs: 4
//     - FDEs: 533 K
//     - rows: 4.6 M
//     - register rules: 17 M
//     - max rows per FDE: 2.5 K
//
// (There are many weird things going on that I don't understand, e.g.:
//   * Most of the 33 K compilation units are duplicates, and in other builds the number is more like 6 K.
//     But 6 K seems too small - surely (?) ClickHouse and its 100+ dependencies have much more files than that.
//   * Template instantiations are probably duplicated a lot - once for each compilation unit that instantiated it. AFAIU, the actual machine code gets deduplicated by
//     the linker, but debug symbols don't. So we should probably try to deduplicate that somehow.
//   * Vast majority of functions have no address range. Are they all inlined? The fraction seems suspiciously high. Maybe they're some useless duplicates that need to be
//     coalesced with the primary instance that does have an address range? Idk.
//   * Lots of variables have no locations. Are they some weird duplicates like in previous item? Or are they optimized out so completely that their value never actually
//     exists anywhere? Or does the compiler fail to emit debug information about their location? Is this why gdb and lldb constantly say "optimized out" about variables
//     that are obviously not optimized out if you look at the disassembly?)
//
// Some more stats, from bin/load_symbols.rs, debug build of clickhouse:
// 8.720 K units, 27.170 K files (34.24x dedup, 1.884 MiB of paths, 7.097 MiB of remap), 2.654 M functions (2.00x dedup, 101.224 MiB, 450.984 MiB of names, 1.111 MiB extra names), 43.018 M lines (1.282 GiB), 13.450 M local variables (718.309 MiB), 11.366 M global variables, 1.556 M types (8.27x dedup, 1.54x offsets, 1.744 M names (435.198 MiB), 118.750 MiB infos, 49.791 MiB fields (1.89% growth waste), 0 B misc, temp 1.312 GiB offset maps, temp 191.406 MiB dedup maps) (128.317 K base types)


// All 'static lifetimes actually point into the mmapped region inside ElfFile. (I believe it's not undefined behavior if we don't actually dereference dangling references, specifically for immutable 'static references.)

// We mostly don't worry about portability and abstraction layers, but here we try to keep DWARF stuff contained in this file, in case we want to support Mac OS in future or something, and also because it's ugly.
// But one could imagine getting rid of all on-the-fly parsing of DWARF, and instead pre-convert everything into our own data structures, and then having multiple converters for different source formats. (Ok, no, dwarf expressions make this too complex.)
// (Or using something like a vtable to parse different formats on the fly, but hopefully our data structures can be made compact enough and conversion can be made fast enough that this won't be needed.)

pub struct SymbolsShard {
    // Address to line number. Each entry applies to addresses [this_entry.addr(), next_entry.addr()), where next_entry is the next higher entry across all shards, as if they were merged into one sorted array.
    // If file_idx() == None, this range of addresses has no line information.
    // Doesn't include inlined function call sites.
    // Expect tens of millions of these.
    // This takes ~60% more memory than the corresponding .debug_line section, but the conversion is pretty fast (compared to .debug_info).
    pub addr_to_line: Vec<LineInfo>,

    // Line number to addresses, for adding breakpoints.
    // Includes both regular line numbers and inlined function call sites. For inlined call sites, includes subfunction_level, for regular line numbers it's u16::MAX.
    // For .debug_line, includes only entries marked as "statement", i.e. recommended breakpoint addresses.
    // Sorted by (file_idx, line, column).
    pub line_to_addr: Vec<(LineInfo, /*subfunction_level*/ u16)>,

    pub types: Types,

    // Functions and inlined function calls.
    pub subfunctions: Vec<Subfunction>,
    // Indices in `subfunctions` of boundaries between sorted runs of ranges corresponding to one function+level.
    // Normally accessed through FunctionInfo.subfunction_levels, which points to a slice of this array.
    // With that slice in hand, subfunctions[slice[i]..slice[i+1]] are the sorted ranges at level i within the function.
    // Length of the slice is number of levels + 1.
    pub subfunction_levels: Vec<usize>,

    // (Used only for restoring tabs in disassembly window after restart. They're matched by name in case the executabe was recompiled, and addresses and DIE offsets changed.
    //  Unfortunate that we have to spend time and memory on building this whole map just for that minor feature, but I don't have better ideas. This adds ~3s/num_cores to load time.)
    pub mangled_name_to_function: Vec<(&'static [u8], FunctionAddr, /*idx in Symbols.functions*/ usize)>,

    pub misc_arena: Arena,

    // "Local" variables, by which we mean variables that should show up in the local variables window when the instruction pointer is in the correct range.
    // Includes static variables inside functions, but with address range clamped to the function's address range - we want
    // the variable to automatically show up in the UI only if we're in that function, not all the time.
    pub local_variables: Vec<Variable>,

    pub global_variables: Arena, // array of Variable-s (need stable pointers)
    // Id is *const Variable, can be in different shard.
    pub sorted_global_variable_names: StringTable,
}

// Some location in machine code that we may want to put special breakpoints on. E.g. start of main(), or __cxa_throw().
#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub enum PointOfInterest {
    MainFunction,
    LibraryLoad, // _dl_debug_state
    Panic,
    Exception,
}
impl PointOfInterest {
    pub fn save_state(self, out: &mut Vec<u8>) -> Result<()> {
        match self { Self::MainFunction => out.write_u8(0)?, Self::LibraryLoad => out.write_u8(1)?, Self::Panic => out.write_u8(2)?, Self::Exception => out.write_u8(3)?, } Ok(())
    }
    pub fn load_state(inp: &mut &[u8]) -> Result<Self> {
        Ok(match inp.read_u8()? { 0 => Self::MainFunction, 1 => Self::LibraryLoad, 2 => Self::Panic, 3 => Self::Exception, x => return err!(Environment, "unexpected PointOfInterest in save file: {}", x) })
    }

    pub fn name_for_ui(self) -> &'static str {
        match self {
            Self::MainFunction => "main function",
            Self::LibraryLoad => "library load",
            Self::Panic => "panic (Rust)",
            Self::Exception => "exception (C++)",
        }
    }
}

pub struct Symbols {
    // Executable and possibly additional binaries with debug info (e.g. from debuglink or --module).
    // elves[0] is the actual executable, e.g. it should have .text section.
    pub elves: Vec<Arc<ElfFile>>,

    // .debug_info, .debug_line, etc - sections describing things in the source code (functions, line numbers, structs and their fields, etc) and how they map to address ranges.
    // If some or all sections are missing, we treat them as empty, and no special handling is needed because empty sections parse as valid DWARF debug info with 0 units.
    pub dwarf: Dwarf<DwarfSlice>,

    // Units in .debug_info, sorted by DieOffset (not to be confused with address).
    // Expect tens of thousands of these.
    pub units: Vec<DwarfUnit>,

    // Indexes to map addresses (in debuggee's virtual address space) to stuff.
    // Keep in mind that these assume segment addresses as defined in ELF file, which are different from addresses at runtime.
    // We call these "static" and "dynamic" addresses.

    // Deduplicated source code files. Expect tens of thousands of these.
    pub files: Vec<FileInfo>,
    pub file_paths: StringTable,
    pub path_to_used_file: HashMap<&'static Path, usize>, // files with used_lines != 0

    // All functions that either have machine code or are inlined at least once. Taken from .debug_info and .symtab. Sorted by address. Expect millions of these.
    // We assume that functions' address ranges cover the whole .text section and don't overlap, so we only store start address for each range
    // and assume that each range ends where the next one begins. This assumption is also useful for .symtab, which seems to lack reliable range length information
    // (the information is there, but it's often incorrect).
    pub functions: Vec<FunctionInfo>,

    pub shards: Vec<SymbolsShard>,

    pub builtin_types: BuiltinTypes,

    // Annoyingly, DWARF expressions refer to primitive data types by their DIE offset within the unit, and each unit has its own copy of all the primitive type descriptions.
    // So we have this map from offset to the primitive type description. (Maybe we should remove it and parse the DIE on demand. And maybe parse more DIEs on demand in general.)
    pub base_types: Vec<u64>, // packed: bits 8-63 are DIE offset, bits 0-7 are gimli::read::ValueType enum.

    // Static addresses corresponding to .text section.
    pub code_addr_range: Range<usize>,

    // C++ vtables addresses, sorted. Comes from .symtab. Used for automatically downcasting to concrete types.
    pub vtables: Vec<VTableInfo>,

    // Addresses of things like main() and __cxa_throw().
    pub points_of_interest: HashMap<PointOfInterest, Vec<usize>>,

    // How long it took to load the symbols and how much memory it used.
    pub loading_duration_ns: usize,
    pub loading_memory_usage: Option<usize>,
}

// Data structures for functions and inlined function calls.
//
// FunctionInfo is a function. It may or may not have address ranges.
// Because of peculiarities of debug information encountered in practice,
// the exact ranges we attribute to functions are not known until we merge and deduplicate functions from .debug_info and .symtab.
// That's why FunctionInfo doesn't contain the end of the range, and subfunctions (see below) may have
// address ranges not fully consistent with their function's ranges (i.e. stick out or have gaps).
//
// Subfunction is an address range inside a function, corresponding either to the whole function (level-0 subfunction)
// or to an inlined function call (or a part of an inlined function call, if the call consists of multiple ranges).
// Subfunctions of each function form a tree, organized into "levels" by nesting depth. Subfunctions of each level live in their own sorted array slice.
// Level i has subfunctions s.subfunctions[s.subfunction_levels[f.subfunction_levels.start + i]], where s is SymbolsShard, and f is FunctionInfo.
// Subfunction ranges are always properly nested, ranges on each level don't overlap,
// and the nesting of ranges matches the child-parent relationships in the subfunction tree:
//
// |------------------------------------------------|   <--  level 0 - whole function
//      |----------------------|     |---------|        <--  level 1 - inlined function calls directly from the function
//         |----|    |-------|            |--|          <--  level 2 - inlined function calls from level 1, etc
//
// The range tree is well-formed within each function (we do a pass to validate and fix up the ranges after parsing each function),
// but nothing is guaranteed across functions.

#[derive(Clone)]
pub struct Subfunction {
    // Index in Symbols.functions. MAX if level == 0 or if DWARF had invalid reference.
    // (During symbols loading, this is a FunctionAddr instead.)
    pub callee_idx: usize,
    local_variables: usize, // packed range of indices in `local_variables`
    // Location of the function definition (if level-0) or call site (if level > 0). Invalid if unknown.
    pub call_line: LineInfo,
    pub addr_range: Range<usize>,
    // Uniquely identifies the inlined function call within the function.
    // If an inlined function call consists of multiple address ranges, each range gets its own Subfunction, but their `identity`s are equal.
    // This is important when stepping: if a step-over starts from inside one address range of an inlined function call and ends in another,
    // the stack_digest logic must notice that these two Subfunction-s are logically the same; otherwise the parent stack frame gets selected, and the user becomes frustrated.
    pub identity: u32,
}
impl Subfunction {
    // Note: multiple Subfunction-s may point to the same variables (if they represent different address ranges of the same inlined function call).
    pub fn local_variables_range(&self) -> Range<usize> { let start = self.local_variables >> 24; Range {start, end: start + (self.local_variables & 0xffffff)} }

    pub fn pack_range(r: Range<usize>) -> usize { r.start << 24 | r.len() }
}

bitflags! { pub struct FunctionFlags: u8 {
    // This is not a function but a marker telling where the previous function ends.
    const SENTINEL = 0x1;
    // Not a real function but address range of a misc code section, e.g. .plt
    const SECTION = 0x2;
    // The information is taken from .symtab
    const SYMTAB = 0x4;
    // The function is inlined at least once.
    const INLINED = 0x8;
}}

// For functions that have machine code: address of the first instruction.
// For inline-only functions: FUNCTION_ADDR_MAX + DIE offset.
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct FunctionAddr(pub usize);
pub const FUNCTION_ADDR_MAX: usize = 1 << 60; // reserve at least two high bits for function_sorting_key
impl FunctionAddr {
    pub fn new(mut addr: usize, warn: &mut Limiter) -> Self {
        if addr >= FUNCTION_ADDR_MAX {
            if warn.check(line!()) {
                eprintln!("warning: function address too high: 0x{:x}", addr);
            }
            addr = FUNCTION_ADDR_MAX - 1;
        }
        Self(addr)
    }
    pub fn inline(die: DieOffset) -> Self { assert!(die.0 < FUNCTION_ADDR_MAX); Self(FUNCTION_ADDR_MAX + die.0) }

    pub fn addr(&self) -> Option<usize> { if self.0 < FUNCTION_ADDR_MAX { Some(self.0) } else { None } }
    pub fn is_addr(&self) -> bool { self.0 < FUNCTION_ADDR_MAX }
}

#[derive(Clone)]
pub struct FunctionInfo {
    // If the function has machine code then addr.is_addr(), and one of the address ranges of this function is:
    // [functions[i].addr, functions[i+1].addr).
    pub addr: FunctionAddr,
    die: DieOffset,
    // Entry point of the function. 0 if this is not a real function. May be outside this FunctionInfo's address range (e.g. if the function has multiple ranges).
    entry_addr: usize,

    // If a function has multiple address ranges, we create a FunctionInfo for each range and link them together into a circular linked list, sorted by addr.
    // Only the FunctionInfo with lowest addr has all the fields populated, so lookup walks to it.
    // Usually there's just one range, i.e. prev_addr == addr.
    // This linked list may be malformed in theory, if DWARF has bad ranges, but I've never seen that in practice. So expect it to be good but make sure to not crash if it's bad,
    pub prev_addr: FunctionAddr,

    // Points either into the binary's mmap or into misc_arena, or to a string literal.
    // Usually mangled. It would be better to demangle all the names when loading symbols, so that we can do fast search for demangled name substring.
    // But cpp_demangle library is too slow for that: it takes ~1 minute to demangle 1-2 GB of names. Maybe eventually we'll try to make a faster demangler, but for now it seems like too much work.
    mangled_name: *const u8,
    mangled_name_len: u32,
    pub shard_idx: u16,
    pub flags: FunctionFlags,
    pub language: LanguageFamily,
    // Range in SymbolsShard.subfunction_levels, which points to a series of slices in subfunctions,
    // where i-th slice is the sorted sequence of subfunctions at level i.
    // Empty if the function has no machine code or comes from .symtab
    pub subfunction_levels: Range<usize>,
}
unsafe impl Send for FunctionInfo {}
unsafe impl Sync for FunctionInfo {}
impl FunctionInfo {
    pub fn mangled_name(&self) -> &'static [u8] { unsafe {slice::from_raw_parts(self.mangled_name, self.mangled_name_len as usize)} }
    pub fn debug_info_offset(&self) -> Option<DieOffset> { if self.die.0 == usize::MAX { None } else { Some(self.die) } }
    // 0 means this function has no machine code or comes from .symtab, 1 means it has no inline functions.
    pub fn num_levels(&self) -> usize { self.subfunction_levels.len().saturating_sub(1) }
    pub fn shard_idx(&self) -> usize { self.shard_idx as usize }

    pub fn demangle_name(&self) -> String {
        let name = self.mangled_name();
        match self.language {
            LanguageFamily::Rust => if let Ok(s) = str::from_utf8(name) {
                return rustc_demangle::demangle(s).to_string();
            }
            _ => if name.starts_with(b"_Z") {
                if let Ok(symbol) = cpp_demangle::BorrowedSymbol::new_with_options(name, &cpp_demangle::ParseOptions::default().recursion_limit(1000)) {
                    let options = cpp_demangle::DemangleOptions::new().recursion_limit(1000).no_return_type().no_params().hide_expression_literal_types();
                    if let Ok(r) = symbol.demangle(&options) {
                        return r;
                    }
                }
            }
        }
        String::from_utf8_lossy(name).into_owned()
    }
}

// Identifying information about a function, suitable for writing to the save file.
// We want both more specific and less specific information here.
// Specific (e.g. address) to be able to find the exactly correct function if the binary hasn't changed.
// Less specific (e.g. name) to be likely to find the correct function if the binary changed a little.
#[derive(Debug, Clone)]
pub struct FunctionLocator {
    pub binary_locator: BinaryLocator,
    pub mangled_name: Vec<u8>,
    pub demangled_name: String,
    pub addr: FunctionAddr,
}
impl FunctionLocator {
    pub fn save_state(&self, out: &mut Vec<u8>) -> Result<()> {
        self.binary_locator.save_state_incomplete(out)?;
        out.write_slice(&self.mangled_name)?;
        out.write_str(&self.demangled_name)?; // can't just demangle on load because we don't know the language (alernatively we could save the language here)
        out.write_usize(self.addr.0)?;
        Ok(())
    }
    pub fn load_state(inp: &mut &[u8]) -> Result<Self> {
        Ok(Self {binary_locator: BinaryLocator::load_state_incomplete(inp)?, mangled_name: inp.read_slice()?, demangled_name: inp.read_str()?, addr: FunctionAddr(inp.read_usize()?)})
    }

    pub fn matches_incomplete(&self, other: &Self) -> bool {
        self.binary_locator.matches_incomplete(&other.binary_locator) && self.mangled_name == other.mangled_name && (!self.mangled_name.is_empty() || self.addr == other.addr)
    }
}


pub enum VariableLocation<'a> {
    Const(&'a [u8]),
    Expr(Expression<DwarfSlice>),
    Unknown,
}
#[derive(Clone, Copy)]
pub enum PackedVariableLocation {
    ShortConst([u8; 12]),
    LongConst {ptr: *const u8, len: u32}, // in the binary mmap; not necessarily longer than ShortConst limit
    Expr {ptr: *const u8, len: u32},
    Unknown,
}
impl Default for PackedVariableLocation { fn default() -> Self { Self::Unknown } }
impl PackedVariableLocation {
    pub fn expr(e: Expression<DwarfSlice>) -> Self { Self::Expr {ptr: e.0.as_ptr(), len: e.0.len().min(u32::MAX as usize) as u32} }
    pub fn const_slice(x: &'static [u8]) -> Self { Self::LongConst {ptr: x.as_ptr(), len: x.len().min(u32::MAX as usize) as u32} }
    pub fn const_usize(x: usize) -> Self { let mut a = [0u8; 12]; a[..8].copy_from_slice(&x.to_le_bytes()); Self::ShortConst(a) }

    pub fn unpack(&self) -> VariableLocation<'_> {
        match self {
            Self::ShortConst(a) => VariableLocation::Const(a),
            &Self::LongConst {ptr, len} => VariableLocation::Const(unsafe {slice::from_raw_parts(ptr, len as usize)}),
            &Self::Expr {ptr, len} => VariableLocation::Expr(Expression(DwarfSlice::new(unsafe {slice::from_raw_parts(ptr, len as usize)}))),
            Self::Unknown => VariableLocation::Unknown,
        }
    }
}

bitflags! { pub struct VariableFlags: u8 {
    // It's an argument of the containing function.
    const PARAMETER = 0x1;
    // It's a pseudovariable holding the expression from DW_AT_frame_base.
    const FRAME_BASE = 0x2;
    const TEMPLATE_PARAMETER = 0x4;
    const GLOBAL = 0x8;
}}

#[derive(Clone)]
pub struct Variable {
    // If local variable: unqualified name, in binary's mmap.
    // If global variable: fully qualified name (possibly with artificial suffix to make it unique), in sorted_global_variable_names (likely of a different shard).
    // (During symbols loading if global variable: non-disambiguated fully qualified name in temp_global_var_arena.)
    pub name_ptr: *const u8,
    pub name_len: u32,
    pub type_: *const TypeInfo,
    pub location: PackedVariableLocation,
    // Pc range in which this variable exists.
    pub start: usize,
    pub len: u32,
    pub line: LineInfo,
    offset_and_flags: u64, // DieOffset and VariableFlags
}
unsafe impl Send for Variable {}
unsafe impl Sync for Variable {}
impl Variable {
    fn new(name: &'static str, type_: *const TypeInfo, offset: DieOffset, line: LineInfo, flags: VariableFlags) -> Self {
        Self {name_ptr: name.as_ptr(), name_len: name.len().min(u32::MAX as usize) as u32, type_, line, offset_and_flags: Variable::pack_offset_and_flags(offset, flags),
              location: PackedVariableLocation::Unknown, start: 0, len: 0}
    }
    
    pub unsafe fn name(&self) -> &'static str { if self.name_len == 0 { "" } else { str::from_utf8_unchecked(std::slice::from_raw_parts(self.name_ptr, self.name_len as usize)) } }
    pub fn set_name(&mut self, n: &'static str) { self.name_ptr = n.as_ptr(); self.name_len = n.len().min(u32::MAX as usize) as u32; }
    pub fn range(&self) -> core::ops::Range<usize> { self.start..self.start + self.len as usize }
    pub fn pack_offset_and_flags(off: DieOffset, flags: VariableFlags) -> u64 { (off.0 as u64) << 8 | flags.bits() as u64 }
    pub fn debug_info_offset(&self) -> Option<DieOffset> {
        let off = (self.offset_and_flags as usize) >> 8;
        if off == usize::MAX >> 8 {
            None
        } else {
            Some(DebugInfoOffset(off))
        }
    }
    pub fn flags(&self) -> VariableFlags { unsafe{mem::transmute((self.offset_and_flags & 0xff) as u8)} }
    pub fn add_flags(&mut self, f: VariableFlags) { self.offset_and_flags |= f.bits() as u64; }

    fn with_range(&self, range: gimli::Range) -> Self {
        let mut r = self.clone();
        r.start = range.begin as usize;
        r.len = (range.end - range.begin).min(u32::MAX as u64) as u32;
        r
    }

    pub fn readable_flags(&self) -> String {
        let mut s = String::new();
        let flags = self.flags();
        if flags.contains(VariableFlags::PARAMETER) {s.push_str("parameter | ");}
        if flags.contains(VariableFlags::FRAME_BASE) {s.push_str("frame_base | ");}
        if flags.contains(VariableFlags::TEMPLATE_PARAMETER) {s.push_str("template_parameter | ");}
        if flags.contains(VariableFlags::GLOBAL) {s.push_str("global | ");}
        if !s.is_empty() {
            s.replace_range(s.len()-3.., "");
        }
        s
    }
}

// Source code file. Can be referenced from line number information, functions (to say where the function was defined), etc.
#[derive(Clone)]
pub struct FileInfo {
    pub unit_comp_dir: &'static Path, // not actually static, points into the binary's mmap (either main binary or debuglink binary)
    pub directory: &'static Path, // same
    pub filename: &'static Path, // same
    // Joined path unit_comp_dir / directory / filename. If directory is absolute (starts with '/'), unit_comp_dir is omitted.
    // Lives in file_paths arena.
    pub path: &'static Path,
    pub version: FileVersionInfo,
    // How many LineInfo-s with nonzero line() in line_to_addr point to this file.
    // (What's the deal with zero line()? I've seen a binary that has most source files listed twice in the file table: once with path "./src/<...>", once with "./build/./src/<...>".
    //  The former is only referenced by a few inlined function call sites, and only with line() == 0. Idk what's up with that. Let's ignore these files so that they don't show up
    //  in file search dialog. They'll still show up in source code window if we actually hit that inlined function and select it in the stack trace; idk what to do about that, there's
    //  no good way for the debugger to know that these different paths refer to the same file.)
    pub used_lines: usize,
}
impl FileInfo {
    fn concat_path(&self, out: &mut PathBuf) {
        out.clear();
        out.push(self.unit_comp_dir);
        out.push(self.directory);
        out.push(self.filename);
    }
}

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct FileVersionInfo {
    pub timestamp: u64, // 0 if unknown
    pub size: u64, // 0 if unknown
    pub md5: Option<[u8; 16]>,
}
impl Default for FileVersionInfo { fn default() -> Self { Self {timestamp: 0, size: 0, md5: None} } }
impl fmt::Debug for FileVersionInfo { fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::result::Result<(), fmt::Error> { write!(f, "({}, {}, {:?})", self.timestamp, self.size, self.md5.as_ref().map(|a| a[0])) } }
impl FileVersionInfo {
    pub fn save_state(&self, out: &mut Vec<u8>) -> io::Result<()> {
        out.write_u64(self.timestamp)?;
        out.write_u64(self.size)?;
        match &self.md5 {
            None => out.write_u8(0)?,
            Some(x) => {
                out.write_u8(1)?;
                out.write(x)?;
            }
        }
        Ok(())
    }

    pub fn load_state(inp: &mut &[u8]) -> Result<Self> {
        Ok(FileVersionInfo {timestamp: inp.read_u64()?, size: inp.read_u64()?, md5: match inp.read_u8()? {
                             0 => None,
                             1 => {let mut x = [0u8; 16]; inp.read(&mut x)?; Some(x)}
                             x => return err!(Environment, "unexpected bool in save file (md5): {}", x) }})
    }
}

bitflags! { pub struct LineFlags: usize {
    // In addr_to_line: end of inlined function.
    // In line_to_addr: start of inlined function.
    const INLINED_FUNCTION = 0x1;
    // Whether this is the main address corresponding to this line+column.
    // Suitable for setting a breakpoint or stepping to.
    // If a LineInfo covers a range of instructions, this flag applies only to the first of them (at addr()).
    // LineInfo-s without this flag often contain garbage, presumably because compilers try to reduce debug info size that way.
    // (I didn't find a way to reliably tell whether a non-statement line info is garbage or not, but I didn't look very thoroughly.)
    const STATEMENT = 0x2;
}}
const LINE_FLAGS_BITS: u32 = 2;

// A machine code location + source code location: address, file, line number, column number.
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct LineInfo {
    // There are tens of millions of instances of this struct, so it's important to make it compact.
    // Currently we bit-pack things into 128 bits like this:
    //   48 bits - address
    //   16 bits - column number
    //   31 bits - file idx; MAX means this is an end-of-sequence marker, not a real line info
    //   1 bit   - LineFlags
    //   32 bits - line number
    // (If some of these get exceeded in practice, or if it takes too much memory, feel free to redistribute the bits or rethink the whole thing. E.g.:
    //  * code could be split into 64 KB pages, with each page having its own addr -> everything indexes, making all addresses 16-bit,
    //  * we could do a pre-pass to get max line number for each file, then use a common numbering for all lines of all files, as if the files were all concatenated into one;
    //    or just redistribute the bits here dynamically based on how many files there are etc,
    //  * instead of copying all line number information out of DWARF, we could store sparse checkpoints into DWARF's line number programs; note that the state of
    //    line number "program" execution is just the gimli::read::LineRow struct, and the whole thing is pretty simple if you read the gimli code around it,
    //    so this seems very doable if needed; (I'm guessing what people usually do is have an index of "sequences" (DWARF term), but those can be >100k rows, so we should split them up, which is easy;)
    //    I went with the copy-everything-out approach to make it easier to support other platforms or split-DWARF in future if needed.)
    pub data: [usize; 2],
}

static PRINTED_LINE_INFO_OVERFLOW_WARNING: AtomicUsize = AtomicUsize::new(0);

const LINE_FILE_IDX_MAX: usize = u32::MAX as usize >> LINE_FLAGS_BITS;

impl LineInfo {
    pub fn new(addr: usize, file_idx: Option<usize>, mut line: usize, mut column: usize, flags: LineFlags) -> Result<LineInfo> {
        let file_idx = match file_idx {
            None => LINE_FILE_IDX_MAX,
            Some(i) if i >= LINE_FILE_IDX_MAX => return err!(NotImplemented, "unsupportedly many files: {}", i),
            Some(i) => i };
        if addr >= 1 << 48 { return err!(NotImplemented, "unsupportedly high address: {}", addr); }
        if line >= 1usize << 32 || column >= 1usize << 16 {
            if PRINTED_LINE_INFO_OVERFLOW_WARNING.fetch_add(1, Ordering::SeqCst) < 5 {
                eprintln!("warning: line number ({}) or column number ({}) is too high and will be clamped (to 32 and 16 bits respectively)", line, column);
                line = line.min((1usize << 32) - 1);
                column = column.min((1usize << 16) - 1);
            }
        }
        Ok(LineInfo {data: [(addr << 16) | column, file_idx << (32 + LINE_FLAGS_BITS) | flags.bits() << 32 | line]})
    }
    pub fn invalid() -> Self { Self {data: [usize::MAX, usize::MAX]} }

    pub fn addr(&self) -> usize { self.data[0] >> 16 }
    pub fn line(&self) -> usize { self.data[1] & 0xffffffff }
    pub fn column(&self) -> usize { self.data[0] & 0xffff }
    pub fn flags(&self) -> LineFlags { LineFlags::from_bits_truncate(self.data[1] >> 32) }
    pub fn set_flag(&mut self, f: LineFlags) { self.data[1] |= f.bits() << 32; }
    pub fn unset_flag(&mut self, f: LineFlags) { self.data[1] &= !(f.bits() << 32); }
    pub fn set_line_and_column_from(&mut self, from: LineInfo) { self.data[0] = (self.data[0] & !0xffff) | (from.data[0] & 0xffff); self.data[1] = (self.data[1] & !0xffffffff) | (from.data[1] & 0xffffffff); }

    pub fn file_idx(&self) -> Option<usize> {
        let r = self.data[1] >> (32 + LINE_FLAGS_BITS);
        if r == LINE_FILE_IDX_MAX as usize {
            None
        } else {
            Some(r)
        }
    }

    pub fn equals(self, other: Self, use_line_number_with_column: bool) -> bool {
        self.file_idx() == other.file_idx() && self.line() == other.line() && (!use_line_number_with_column || self.column() == other.column())
    }

    pub fn with_addr(mut self, addr: usize) -> Self {
        self.data[0] = (self.data[0] & 0xffff) | (addr << 16);
        self
    }
    pub fn with_addr_and_flags(mut self, addr: usize, flags: LineFlags) -> Self {
        self.data[0] = (self.data[0] & 0xffff) | (addr << 16);
        self.data[1] = self.data[1] & !(LineFlags::all().bits() << 32) | (flags.bits() << 32);
        self
    }

    // Sorting key equivalent to (file, line, column, addr)
    pub fn file_line_column_addr(&self) -> [usize; 2] {
        [self.data[1] & !(LineFlags::all().bits() << 32), self.data[0] << 48 | self.data[0] >> 16]
    }
    // Sorting key equivalent to (addr(), file_idx().is_none(), line() == 0, flags().contains(INLINED_FUNCTION)).
    // Used when sorting addr_to_line. addr() is for sorting, everything else is deduplication priority.
    // In particular:
    //  * An address range may start where another one ends (file_idx().is_none()) - keep the start, discard the end marker.
    //  * An inlined function end (from .debug_info) may clash with an explicit line number information row (from .debug_line) - keep the explicit one.
    //  * ... except the case when the row in .debug_line is missing the line number, which does happen, ugh.
    pub fn addr_filenone_linebad_inlined(&self) -> (usize, bool, bool, bool) {
        (self.data[0] & 0xffffffffffff0000, self.data[1] == LINE_FILE_IDX_MAX as usize, self.line() == 0, (self.data[1] >> 32) & LineFlags::INLINED_FUNCTION.bits() != 0)
    }
}
impl fmt::Debug for LineInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> std::result::Result<(), fmt::Error> {
        write!(f, "(f{:?},l{},c{},a{},f{:?})", self.file_idx(), self.line(), self.column(), self.addr(), self.flags())
    }
}

#[derive(Clone)]
pub struct VTableInfo {
    // We don't expect the [start, end) ranges to overlap between vtables.
    pub start: usize,
    pub end: usize,
    pub name: &'static str, // in misc_arena
    pub type_: Option<*const TypeInfo>,
}
unsafe impl Send for VTableInfo {}
unsafe impl Sync for VTableInfo {}

impl Symbols {
    pub fn find_unit(&self, offset: DieOffset) -> Result<&DwarfUnit> {
        let idx = self.units.partition_point(|u| u.offset <= offset);
        if idx == 0 { return err!(Internal, "entry offset out of bounds"); }
        Ok(&self.units[idx - 1])
    }

    pub fn addr_to_function(&self, addr: usize) -> Result<(&FunctionInfo, /*function_idx*/ usize)> {
        let mut idx = self.functions.partition_point(|f| f.addr.0 <= addr);
        if idx == 0 { return err!(ProcessState, "address below min function address"); }
        if idx == self.functions.len() || !self.functions[idx].addr.is_addr() { return err!(ProcessState, "address above max function address"); }
        idx -= 1;
        if self.functions[idx].flags.contains(FunctionFlags::SENTINEL) { return err!(ProcessState, "no function at address"); }

        // Follow the linked list to the first address range of this function.
        loop {
            let prev_addr = self.functions[idx].prev_addr;
            if prev_addr >= self.functions[idx].addr {
                break;
            }
            let new_idx = self.functions.partition_point(|f| f.addr < prev_addr);
            if new_idx + 1 >= self.functions.len() || self.functions[new_idx].addr != prev_addr || self.functions[new_idx].die != self.functions[idx].die {
                break;
            }
            idx = new_idx;
        }
        
        Ok((&self.functions[idx], idx))
    }

    pub fn function_addr_ranges(&self, mut function_idx: usize) -> Vec<Range<usize>> {
        let mut ranges: Vec<Range<usize>> = Vec::new();
        if self.functions[function_idx].addr.addr().is_none() {
            return ranges;
        }
        loop {
            let f = &self.functions[function_idx];
            assert!(!f.flags.contains(FunctionFlags::SENTINEL));
            ranges.push(f.addr.addr().unwrap()..self.functions[function_idx + 1].addr.addr().unwrap());

            let new_idx = self.functions.partition_point(|ff| ff.addr < f.prev_addr);
            if new_idx + 1 >= self.functions.len() {
                break;
            }
            let g = &self.functions[new_idx];
            if g.addr != f.prev_addr || g.die != f.die || g.prev_addr >= g.addr {
                break;
            }

            function_idx = new_idx;
        }
        ranges.reverse();
        ranges
    }

    pub fn find_nearest_function(&self, mangled_name: &[u8], addr: FunctionAddr) -> Option<usize> {
        // If there are multiple functions with the same name (e.g. anonymous), pick the one with the nearest address or DIE offset.
        let mut res: (usize, Option<usize>) = (usize::MAX, None);
        for shard in &self.shards {
            let a = &shard.mangled_name_to_function;
            let idx = a.partition_point(|t| t < &(mangled_name, addr, 0));
            if idx < a.len() && a[idx].0 == mangled_name {
                res = res.min((a[idx].1.0 - addr.0, Some(a[idx].2)));
            }
            if idx > 0 && a[idx-1].0 == mangled_name {
                res = res.min((addr.0 - a[idx-1].1.0, Some(a[idx-1].2)));
            }
        }
        res.1
    }

    pub fn subfunction_idxs_at_level(&self, level: usize, function: &FunctionInfo) -> Range<usize> {
        let shard = &self.shards[function.shard_idx()];
        let levels = &shard.subfunction_levels[function.subfunction_levels.clone()];
        assert!(levels.len() > level + 1);
        levels[level]..levels[level+1]
    }
    
    pub fn subfunctions_at_level<'a>(&'a self, level: usize, function: &FunctionInfo) -> &'a [Subfunction] {
        &self.shards[function.shard_idx()].subfunctions[self.subfunction_idxs_at_level(level, function)]
    }

    pub fn root_subfunction<'a>(&'a self, function: &FunctionInfo) -> Option<(&'a Subfunction, /*subfunction_idx*/ usize)> {
        if function.subfunction_levels.is_empty() {
            None
        } else {
            let idxs = self.subfunction_idxs_at_level(0, function);
            assert!(!idxs.is_empty());
            let idx = idxs.start;
            Some((&self.shards[function.shard_idx()].subfunctions[idx], idx))
        }
    }

    pub fn local_variables_in_subfunction<'a>(&'a self, subfunction: &Subfunction, shard_idx: usize) -> &'a [Variable] {
        &self.shards[shard_idx].local_variables[subfunction.local_variables_range()]
    }

    pub fn containing_subfunction_at_level(&self, addr: usize, level: u16, function: &FunctionInfo) -> Option<(/*subfunction_idx*/ usize, /*level*/u16)> {
        let shard = &self.shards[function.shard_idx()];
        let levels = &shard.subfunction_levels[function.subfunction_levels.clone()];
        let range = if level == u16::MAX {
            0..function.num_levels()
        } else {
            assert!(levels.len() > level as usize + 1);
            level as usize..level as usize + 1
        };
        let mut res = None;
        for level in range {
            let idxs = levels[level]..levels[level+1];
            let ranges = &shard.subfunctions[idxs.clone()];
            let i = ranges.partition_point(|r| r.addr_range.end <= addr);
            if i == ranges.len() || ranges[i].addr_range.start > addr  {
                break;
            }
            res = Some((idxs.start + i, level as u16));
        }
        res
    }

    pub fn subfunction_ancestor_at_level(&self, sf_idx: usize, from_level: u16, to_level: u16, function: &FunctionInfo) -> (/*subfunction_idx*/ usize, /*level*/ u16) {
        if from_level <= to_level {
            return (sf_idx, from_level);
        }
        let shard = &self.shards[function.shard_idx()];
        let addr = shard.subfunctions[sf_idx].addr_range.start;
        (self.containing_subfunction_at_level(addr, to_level, function).unwrap().0, to_level)
    }

    pub fn find_global_variable_by_name<'a>(&'a self, name: &str) -> Option<&'a Variable> {
        for s in &self.shards {
            if let Some(id) = s.sorted_global_variable_names.binary_search(name.as_bytes()) {
                let v = id as *const Variable;
                return Some(unsafe {&*v});
            }
        }
        None
    }

    // Iterator that merges and deduplicates sorted addr_to_line arrays from all shards on the fly.
    // The first element (if any) either covers `addr` or is above `addr`; its file_idx() may be None.
    pub fn addr_to_line_iter<'a>(&'a self, addr: usize) -> impl Iterator<Item = LineInfo> + 'a {
        let mut sources: Vec<&'a [LineInfo]> = Vec::new();
        let mut first_below = 0;
        for s in &self.shards {
            let mut i = s.addr_to_line.partition_point(|line| line.addr() <= addr);
            if i > 0 {
                i -= 1;
                first_below = first_below.max(s.addr_to_line[i].addr());
            }
            if i < s.addr_to_line.len() {
                sources.push(&s.addr_to_line[i..]);
            }
        }
        for s in &mut sources {
            if s[0].addr() < first_below {
                *s = &s[1..];
            }
        }
        AddrToLineIter {prev_addr: usize::MAX, iter: MergeIterator::new(sources, |line| /*it's a max-heap*/ cmp::Reverse(line.addr_filenone_linebad_inlined()))}
    }

    // The file_idx() in the returned LineInfo is never None (instead, the whole LineInfo is None).
    pub fn find_line(&self, addr: usize) -> Option<LineInfo> {
        match self.addr_to_line_iter(addr).next() {
            None => None,
            Some(line) if line.addr() > addr || line.file_idx().is_none() => None,
            Some(line) => Some(line.clone()),
        }
    }

    // If the given line has no addresses, returns the next line that has.
    pub fn line_to_addrs(&self, file_idx: usize, line_number: usize, only_statements: bool) -> std::result::Result<Vec<(LineInfo, /*subfunction_level*/ u16)>, Option<usize>> {
        let mut res: Vec<(LineInfo, u16)> = Vec::new();
        let mut min_line = usize::MAX;
        for s in &self.shards {
            let mut idx = s.line_to_addr.partition_point(|l| (l.0.file_idx().unwrap(), l.0.line()) < (file_idx, line_number));
            while idx < s.line_to_addr.len() && only_statements && !s.line_to_addr[idx].0.flags().contains(LineFlags::STATEMENT) {
                idx += 1;
            }
            if idx < s.line_to_addr.len() && s.line_to_addr[idx].0.file_idx() == Some(file_idx) {
                min_line = min_line.min(s.line_to_addr[idx].0.line());
            }
            while idx < s.line_to_addr.len() && s.line_to_addr[idx].0.file_idx() == Some(file_idx) && s.line_to_addr[idx].0.line() == line_number {
                if !only_statements || s.line_to_addr[idx].0.flags().contains(LineFlags::STATEMENT) {
                    res.push(s.line_to_addr[idx].clone());
                }
                
                idx += 1;
            }
        }
        if !res.is_empty() {
            Ok(res)
        } else if min_line == usize::MAX {
            Err(None)
        } else {
            Err(Some(min_line))
        }
    }

    pub fn list_lines_for_file(&self, path: &Path) -> Vec<LineInfo> {
        let mut res: Vec<LineInfo> = Vec::new();
        let file_idx = match self.path_to_used_file.get(path) {
            Some(i) => *i,
            None => return res };
        for s in &self.shards {
            let mut i = s.line_to_addr.partition_point(|l| l.0.file_idx().unwrap() < file_idx);
            while i < s.line_to_addr.len() && s.line_to_addr[i].0.file_idx().unwrap() == file_idx {
                res.push(s.line_to_addr[i].0.clone());
                i += 1;
            }
        }
        res
    }

    pub fn find_base_type(&self, offset: DieOffset) -> Result<ValueType> {
        let idx = self.base_types.partition_point(|x| ((x >> 8) as usize) < offset.0);
        if idx < self.base_types.len() && (self.base_types[idx] >> 8) as usize == offset.0 {
            Ok(unsafe{mem::transmute((self.base_types[idx] & 0xff) as u8)})
        } else {
            err!(Dwarf, "no base type @0x{:x}", offset.0)
        }
    }

    pub fn find_vtable(&self, static_addr: usize) -> Result<VTableInfo> {
        let idx = self.vtables.partition_point(|v| v.end <= static_addr);
        if idx > 0 && self.vtables[idx].start <= static_addr {
            Ok(self.vtables[idx].clone())
        } else {
            err!(Dwarf, "no known vtable at address")
        }
    }
}

struct AddrToLineIter<'a, K: Ord, F: FnMut(&LineInfo) -> K> {
    prev_addr: usize,
    iter: MergeIterator<'a, LineInfo, K, F>,
}
impl<K: Ord, F: FnMut(&LineInfo) -> K> Iterator for AddrToLineIter<'_, K, F> {
    type Item = LineInfo;
    
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(line) = self.iter.next() {
            // This deduplication logic is less sophisticated than what we do in parse_debug_line() and sort_addr_to_line().
            // But this should be more than enough because usually all debug info for each function's address range is within one unit,
            // so all jank fixup happens during loading, before we get here.
            if line.addr() != self.prev_addr {
                self.prev_addr = line.addr();
                return Some(line.clone());
            }
        }
        None
    }
}

// ============================================== symbols loading code below ===============================================

pub struct SymbolsLoader {
    pub num_shards: usize,

    sym: Symbols,
    shards: Vec<SyncUnsafeCell<CachePadded<SymbolsLoaderShard>>>,
    die_to_function_shards: Vec<SyncUnsafeCell<CachePadded<Vec<(DieOffset, usize)>>>>,
    types: TypesLoader,
    abbreviations_shared: AbbreviationsSharedData,
    binary_id: usize,

    // Shuffling global variable names across threads for deduplication.
    // [sender][receiver] -> messages
    send_global_variable_names: Vec<CachePadded<SyncUnsafeCell<Vec<CachePadded<SyncUnsafeCell<Vec<GlobalVariableNameMessage>>>>>>>,

    // [.strtab, .symtab], [.dynsym, .dynstr]
    strtab_symtab: Vec<[&'static [u8]; 2]>,

    // Things for management and bookkeeping.
    status: Arc<SymbolsLoadingStatus>,
    progress_per_stage: Vec<[(f64, &'static str); /* prepare, run */ 2]>, // what the progress indicator should show at the start of [prepare_stage(), run()] for each stage; stage 0 is new()
    prepare_time_per_stage_ns: Vec<usize>, // stage -> time
    run_time_per_stage_ns: Vec<Vec<AtomicUsize>>, // stage -> shard -> time
    shard_progress_ppm: Vec<CachePadded<AtomicUsize>>, // shard -> progress
    stage: usize,

    // Stats, just for information.
    types_before_dedup: usize,
    type_offsets: usize,
    type_offset_maps_bytes: usize,
    type_dedup_maps_bytes: usize,
}

pub struct SymbolsLoadingStatus {
    pub cancel: AtomicBool,
    pub progress_ppm: AtomicUsize,
    pub stage: Mutex<String>,
}
impl SymbolsLoadingStatus { pub fn new() -> Self { Self {cancel: false.into(), progress_ppm: 0.into(), stage: String::new().into()} } }

struct SymbolsLoaderShard {
    sym: SymbolsShard,
    addr_to_line_len_after_debug_line: usize,

    units: Vec<usize>,
    symtab_ranges: Vec<Vec<Range<usize>>>,

    // Each DWARF unit has its own table of file paths. We merge them into one table and deduplicate. This decreases their number from millions to tens of thousands.
    file_dedup: Vec<FileDedup>,

    file_used_lines: Vec<(/*file_idx*/ usize, /*used_lines*/ usize)>,

    // Side note: types in DWARF are usually organized in one of 3 ways:
    //  (a) Each unit has its own types. All DW_AT_type are offsets within current unit (UnitRef). There are lots of duplicate types because each unit gets
    //      a copy of all types from the headers in includes. Some types are declared in one unit and defined in another, and we have to match them up using names.
    //  (b) DW_AT_type point to any units in .debug_info (DebugInfoRef). I've seen this with ThinLTO. Presumably it deduplicates types across units.
    //  (c) DW_AT_type point to type units in .debug_types using type signatures. For us, this is probably no different from (b) - types are already deduped.
    // Currently we're not taking advantage of this. We could skip deduplication in cases (b) and (c) (although hold on, my latest test shows lots of dedup on
    // ThinLTO-d binary, idk which info is right, would need to check more carefully), and do processing/deduplication incrementally one unit at a time in case (a).
    types: TypesLoadingShard,

    base_types: Vec<u64>,

    functions: Vec<FunctionInfo>,
    max_function_end: usize,
    subfunctions_need_fixup: Vec<usize>,

    vtables: Vec<VTableInfo>,
    points_of_interest: HashMap<PointOfInterest, Vec<usize>>,

    temp_global_var_arena: Arena,

    // Stats, just for information.
    functions_before_dedup: usize,

    warn: Limiter,
}

struct FileDedup {
    file: FileInfo,
    path_hash: usize,
    unit_idx: usize,
    idx_in_unit: usize,
}

#[derive(Clone, Copy, Ord, PartialOrd, Eq, PartialEq)]
struct GlobalVariableNameMessage {
    name: &'static str,
    ptr: *mut Variable,
}
unsafe impl Send for GlobalVariableNameMessage {}
unsafe impl Sync for GlobalVariableNameMessage {}

// Usage: call new(), then alternate between single-threaded calls to prepare_stage(i) and multi-threaded calls to run(i, shard_idx) (for all shard_idx in parallel); when prepare_stage() returns Ok(false), call into_result().
impl SymbolsLoader {
    pub fn new(elves: Vec<Arc<ElfFile>>, binary_id: usize, max_shards: usize, status: Arc<SymbolsLoadingStatus>) -> Result<Self> {
        assert!(!elves.is_empty());
        let start_time = Instant::now();

        let find_section = |name: &str| -> Result<Option<(&[u8], /*addr*/ usize)>> {
            for elf in &elves {
                if let Some(&idx) = elf.section_by_name.get(name) {
                    let data = elf.section_data(idx)?;
                    if !data.is_empty() {
                        return Ok(Some((data, elf.sections[idx].address)));
                    }
                }
            }
            Ok(None)
        };
        let load_section = |id: SectionId| -> Result<DwarfSlice> {
            match find_section(id.name())? {
                Some((data, _)) => Ok(DwarfSlice::new(unsafe {mem::transmute(data)})),
                None => Ok(DwarfSlice::new(&[0u8;0][..])),
            }
        };

        let mut dwarf = Dwarf::load(load_section)?;
        *status.stage.lock().unwrap() = "listing units".to_string();

        if !dwarf.debug_types.reader().is_empty() {
            // This was removed in DWARF 5, so probably not worth supporting.
            return err!(Dwarf, ".debug_types not supported");
        }

        let code_addr_range = match find_section(".text")? {
            Some((data, addr)) => addr..addr+data.len(),
            None => 0..0,
        };

        let mut strtab_symtab: Vec<[&'static [u8]; 2]> = Vec::new();
        for [strtab_name, symtab_name] in [[".strtab", ".symtab"], [".dynstr", ".dynsym"]] {
            match (find_section(strtab_name)?, find_section(symtab_name)?) {
                (Some((strtab, _)), Some((symtab, _))) => strtab_symtab.push(unsafe {[mem::transmute(strtab), mem::transmute(symtab)]}),
                _ => (),
            }
        }

        let binary_size: usize = elves.iter().map(|e| e.decompressed_size()).sum();
        let num_shards = max_shards.min(binary_size >> 20).max(1);
        // How should we assign units to shards?
        // For maximum balance, we'd want to shuffle the units and assign them round-robin. But that's bad for locality of file reads.
        // For maximum locality, we'd want to just split the file into num_shards subranges. But that's bad for balance
        // if there's some bias in how expensive units are per byte (e.g. maybe rust units come before C++ units,
        // and maybe they have smaller DIEs, making them slower to process for the same size.)
        // So we do something hybrid: take ranges of 4 MB consecutive units and assign them to shards round-robin.
        // I haven't tested if this actually helps or not.
        let unit_distribution_granularity = (1usize << 22).min(dwarf.debug_info.reader().len() / num_shards).max(1);

        // Estimates of how long different stages take relative to each other, for progress indication.
        let progress_fraction = [
            [(1.746, "listing units"), (0.000, ""), ],
            [(0.000, ""), (0.039, "parsing file tables"), ],
            [(0.131, "deduping file tables"), (6.766, "parsing DWARF"), ],
            [(0.153, "deduping functions"), (0.198, "resolving type decls and sorting funcs"), ],
            [(0.000, ""), (2.084, "traversing type graph"), ],
            [(0.000, ""), (0.404, "processing name -> type"), ],
            [(0.000, ""), (0.031, "processing type -> name"), ],
            [(0.000, ""), (0.244, "fixing up type and func refs"), ],
            [(0.605, "finishing up"), (0.000, ""), ],
            [(0.000, ""), (0.000, ""), ],
            [(0.000, ""), (0.000, ""), ],];
        let mut progress_per_stage: Vec<[(f64, &'static str); 2]> = Vec::new();
        {
            let s: f64 = progress_fraction.iter().map(|a| a[0].0 + a[1].0).sum();
            let mut p = 0.0f64;
            for a in progress_fraction {
                progress_per_stage.push([(p, a[0].1), (p + a[0].0/s, a[1].1)]);
                p += (a[0].0 + a[1].0)/s;
            }
            assert!((p - 1.0).abs() < 1e-6);
            progress_per_stage.push([(p, ""), (p, "")]);
        }
        let mut prepare_time_per_stage_ns: Vec<usize> = vec![0; progress_per_stage.len()];
        let run_time_per_stage_ns: Vec<Vec<AtomicUsize>> = (0..progress_per_stage.len()).map(|_| (0..num_shards).map(|_| AtomicUsize::new(0)).collect()).collect();

        let (types_loader, types_shards) = TypesLoader::create(num_shards);
        let mut shards: Vec<SymbolsLoaderShard> = types_shards.into_iter().map(|types| SymbolsLoaderShard {
            sym: SymbolsShard {addr_to_line: Vec::new(), line_to_addr: Vec::new(), types: Types::new(), misc_arena: Arena::new(), local_variables: Vec::new(), global_variables: Arena::new(), sorted_global_variable_names: StringTable::new(), subfunctions: Vec::new(), subfunction_levels: Vec::new(), mangled_name_to_function: Vec::new()},
            addr_to_line_len_after_debug_line: 0,
            units: Vec::new(), symtab_ranges: Vec::new(), file_dedup: Vec::new(), file_used_lines: Vec::new(), types, base_types: Vec::new(), functions: Vec::new(), subfunctions_need_fixup: Vec::new(), vtables: Vec::new(), points_of_interest: HashMap::new(),
            temp_global_var_arena: Arena::new(), max_function_end: 0, functions_before_dedup: 0, warn: Limiter::new()}).collect();

        let mut round_robin_shard = 0usize;
        let mut round_robin_offset = 0usize;

        let debug_info_section = dwarf.debug_info.reader().slice();
        let mut reported_progress_offset = 0usize;

        let layouts = AllAttributeStructLayouts::new(
            vec![
                (vec![DW_TAG_namespace], NamespaceAttributes::layout()),
                (vec![DW_TAG_variable, DW_TAG_formal_parameter], VariableAttributes::layout()),
                (vec![DW_TAG_subprogram], SubprogramAttributes::layout()),
                (vec![DW_TAG_base_type, DW_TAG_unspecified_type, DW_TAG_structure_type, DW_TAG_class_type, DW_TAG_union_type, DW_TAG_enumeration_type, DW_TAG_pointer_type, DW_TAG_reference_type, DW_TAG_rvalue_reference_type, DW_TAG_array_type, DW_TAG_const_type, DW_TAG_restrict_type, DW_TAG_volatile_type, DW_TAG_atomic_type, DW_TAG_typedef, DW_TAG_subroutine_type, DW_TAG_ptr_to_member_type], TypeAttributes::layout()),
                (vec![DW_TAG_inheritance, DW_TAG_member, DW_TAG_enumerator], FieldAttributes::layout()),
                (vec![DW_TAG_variant_part], VariantPartAttributes::layout()),
                (vec![DW_TAG_variant], VariantAttributes::layout()),
                (vec![DW_TAG_subrange_type], SubrangeTypeAttributes::layout()),
                (vec![DW_TAG_lexical_block], LexicalBlockAttributes::layout()),
                (vec![DW_TAG_inlined_subroutine], InlinedSubroutineAttributes::layout()),
                (vec![DW_TAG_template_type_parameter], TemplateTypeParameterAttributes::layout()),
                (vec![DW_TAG_template_value_parameter], TemplateValueParameterAttributes::layout()),
            ],
            CommonAttributes::layout(),
            vec![DW_TAG_label, DW_TAG_variable, DW_TAG_formal_parameter, DW_TAG_subprogram, DW_TAG_inlined_subroutine]);

        let (mut units, abbreviations_shared) = list_units(&mut dwarf, &elves[0].name, layouts)?;
        for (i, unit) in units.iter_mut().enumerate() {
            if unit.offset.0 > round_robin_offset + unit_distribution_granularity {
                round_robin_offset = unit.offset.0;
                round_robin_shard = (round_robin_shard + 1) % shards.len();
            }
            unit.shard_idx = round_robin_shard;
            shards[unit.shard_idx].units.push(i);

            if unit.offset.0 > reported_progress_offset + 10000000 {
                reported_progress_offset = unit.offset.0;
                status.progress_ppm.store((unit.offset.0 as f64 / debug_info_section.len() as f64 * progress_per_stage[0][1].0 * 1e6) as usize, Ordering::Relaxed);
            }
        }

        for [_, symtab] in &strtab_symtab {
            let entry_size = mem::size_of::<libc::Elf64_Sym>();
            if symtab.len() % entry_size != 0 {
                return err!(Dwarf, ".symtab or .dynsym length is not divisible by {}: {}", entry_size, symtab.len());
            }
            let count = symtab.len() / entry_size;
            for i in 0..num_shards {
                shards[i].symtab_ranges.push(vec![count*i/num_shards*entry_size .. count*(i+1)/num_shards*entry_size]);
            }
        }

        // I am a good programmer.
        let send_global_variable_names: Vec<CachePadded<SyncUnsafeCell<Vec<CachePadded<SyncUnsafeCell<Vec<GlobalVariableNameMessage>>>>>>> =
            (0..shards.len()).map(|_| CachePadded::new(SyncUnsafeCell::new((0..shards.len()).map(|_| CachePadded::new(SyncUnsafeCell::new(Vec::new()))).collect()))).collect();

        prepare_time_per_stage_ns[0] = start_time.elapsed().as_nanos() as usize;
        Ok(SymbolsLoader {
            num_shards: shards.len(), binary_id, sym: Symbols {elves, dwarf, units, files: Vec::new(), file_paths: StringTable::new(), path_to_used_file: HashMap::new(), functions: Vec::new(), shards: Vec::new(), builtin_types: BuiltinTypes::invalid(), base_types: Vec::new(), vtables: Vec::new(), points_of_interest: HashMap::new(), loading_duration_ns: 0, loading_memory_usage: None, code_addr_range},
            shards: shards.into_iter().map(|s| SyncUnsafeCell::new(CachePadded::new(s))).collect(), die_to_function_shards: (0..num_shards).map(|_| SyncUnsafeCell::new(CachePadded::new(Vec::new()))).collect(), types: types_loader, send_global_variable_names, strtab_symtab, status, progress_per_stage,
            abbreviations_shared, prepare_time_per_stage_ns, run_time_per_stage_ns, shard_progress_ppm: (0..num_shards).map(|_| CachePadded::new(AtomicUsize::new(0))).collect(), stage: 0, types_before_dedup: 0, type_offsets: 0, type_offset_maps_bytes: 0, type_dedup_maps_bytes: 0})
    }

    // The loading procedure alternates between single-threaded and multithreaded (sharded) parts. This is the single-threaded part, while run() is the multithreaded part.
    // Returns Ok(false) if there are no more stages; into_result() should be called in that case.
    pub fn prepare_stage(&mut self, stage: usize) -> Result<bool> {
        self.check_cancellation()?;
        let start_time = Instant::now();
        assert_eq!(TypesLoader::num_stages(), 4); // update the matches here and in run() when this changes
        self.stage = stage;
        *self.status.stage.lock().unwrap() = self.progress_per_stage[stage][0].1.to_string();
        self.report_prepare_progress(0.0);
        for p in &self.shard_progress_ppm { p.store(0, Ordering::Relaxed); }
        match stage {
            1 => (), // then parse file tables
            2 => {
                self.dedup_files();
                self.parse_misc_sections(0, unsafe {&mut *self.shards[0].get()});
            } // then parse dwarf and symtab
            3 => {
                self.types_before_dedup = self.shards.iter().map(|s| unsafe {(*s.get()).types.types_before_dedup}).sum();
                self.type_offsets = self.shards.iter().map(|s| unsafe {(*s.get()).types.num_offsets()}).sum();
                self.type_offset_maps_bytes = self.shards.iter().map(|s| unsafe {(*s.get()).types.offset_map_bytes()}).sum();

                self.types.shards_ready(self.shards.iter().map(|s| unsafe {mem::replace(&mut (*s.get()).types, TypesLoadingShard::invalid())}).collect());
                self.collect_used_lines_per_file();
                self.dedup_functions();
            }// then work on types (match declarations to definitions) and on functions (sort die -> idx arrays)
            4 => (), // types (traverse the graph)
            5 => (), // types (process name -> type mapping, detect name collisions)
            6 => (), // types (process type -> name mapping, pick main name for each type)
            7 => (), // then fixup type and function refs
            8 => {
                self.type_dedup_maps_bytes = self.types.dedup_maps_bytes();

                self.finish_types();
                self.merge_base_types();
                self.collect_vtables_and_points_of_interest(); // must be after build_name_to_function_map()

                self.prepare_time_per_stage_ns[self.stage] = start_time.elapsed().as_nanos() as usize;
                self.log_timing_and_stats();
                return Ok(false);
            }
            _ => panic!("unexpected stage to prepare"),
        }
        self.report_prepare_progress(1.0);
        *self.status.stage.lock().unwrap() = self.progress_per_stage[stage][1].1.to_string();
        self.prepare_time_per_stage_ns[self.stage] = start_time.elapsed().as_nanos() as usize;
        Ok(true)
    }
    pub fn run(&self, stage: usize, shard_idx: usize) -> Result<()> {
        self.check_cancellation()?;
        let start_time = Instant::now();
        let progress_callback = |prog: f64| self.report_run_progress(shard_idx, prog);
        match stage {
            1 => self.parse_file_tables(shard_idx, unsafe {&mut *self.shards[shard_idx].get()})?,
            2 => {
                let shard = unsafe {&mut *self.shards[shard_idx].get()};
                self.parse_debug_line(shard)?;
                // We sort addr_to_line twice: before and after parsing .debug_info, because fixup_subfunction_line() needs to do lookup in the information from .debug_line.
                self.sort_addr_to_line(shard, /*finalize*/ false);
                self.parse_dwarf(shard_idx, shard)?;
                self.parse_symtab(shard_idx, shard)?;
                self.sort_functions(shard);
                self.sort_addr_to_line(shard, /*finalize*/ true);
                self.sort_line_to_addr(shard);
            }
            3 => {
                let shard = unsafe {&mut *self.shards[shard_idx].get()};
                self.sort_global_variable_names(shard_idx, shard);
                self.build_name_to_function_map(shard_idx, shard);
                self.sort_die_to_function(unsafe {&mut *self.die_to_function_shards[shard_idx].get()});
                self.types.run(0, shard_idx, &progress_callback);
            }
            4 => self.types.run(1, shard_idx, &progress_callback),
            5 => self.types.run(2, shard_idx, &progress_callback),
            6 => self.types.run(3, shard_idx, &progress_callback),
            7 => {
                let shard = unsafe {&mut *self.shards[shard_idx].get()};
                self.fixup_type_refs(shard_idx, shard);
                self.fixup_function_refs(shard);
            }
            _ => panic!("unexpected stage to run"),
        }
        self.run_time_per_stage_ns[stage][shard_idx].store(start_time.elapsed().as_nanos() as usize, Ordering::Relaxed);
        Ok(())
    }

    pub fn into_result(mut self) -> Symbols {
        self.sym.shards = self.shards.into_iter().map(|s| s.into_inner().into_inner().sym).collect();
        self.sym
    }

    fn check_cancellation(&self) -> Result<()> {
        if self.status.cancel.load(Ordering::Relaxed) { err!(Cancelled, "") } else { Ok(()) }
    }

    fn report_prepare_progress(&mut self, prog: f64) {
        let prog = self.progress_per_stage[self.stage][0].0 * (1.0-prog) + self.progress_per_stage[self.stage][1].0 * prog;
        self.status.progress_ppm.store((prog * 1e6) as usize, Ordering::Relaxed);
    }

    fn report_run_progress(&self, shard_idx: usize, new_prog: f64) {
        self.shard_progress_ppm[shard_idx].store((new_prog * 1e6) as usize, Ordering::Relaxed);
        let prog: usize = self.shard_progress_ppm.iter().map(|s| s.load(Ordering::Relaxed)).sum();
        let prog = prog as f64 / 1e6 / self.shard_progress_ppm.len() as f64;
        let prog = self.progress_per_stage[self.stage][1].0 * (1.0-prog) + self.progress_per_stage[self.stage+1][0].0 * prog;
        self.status.progress_ppm.store((prog * 1e6) as usize, Ordering::Relaxed);
    }

    fn parse_file_tables(&self, shard_idx: usize, shard: &mut SymbolsLoaderShard) -> Result<()> {
        let mut temp_path = PathBuf::new();
        for &unit_idx in &shard.units {
            if let Some(program) = &self.sym.units[unit_idx].unit.line_program {
                let header = program.header();
                // DWARF filename table indexing is 1-based in DWARF <= 4, 0-based in DWARF 5+.
                let idx_base = (header.encoding().version <= 4) as usize;
                let entries = header.file_names();
                if idx_base == 1 {
                    shard.file_dedup.push(FileDedup {file: FileInfo {unit_comp_dir: Path::new(""), directory: Path::new(""), filename: Path::new(""), path: Path::new(""), version: FileVersionInfo {timestamp: 0, size: 0, md5: None}, used_lines: 0}, path_hash: 0, unit_idx, idx_in_unit: 0});
                }
                let comp_unit = &self.sym.units[unit_idx];
                let unit = &comp_unit.unit;
                for (idx, file) in entries.iter().enumerate() {
                    let directory = Path::new(OsStr::from_bytes(match file.directory(header) {
                        None => &[],
                        Some(d) => self.sym.dwarf.attr_string(unit, d)?.slice(),
                    }));
                    let filename = Path::new(OsStr::from_bytes(self.sym.dwarf.attr_string(unit, file.path_name())?.slice()));
                    let f = FileInfo {unit_comp_dir: Path::new(comp_unit.comp_dir), directory, filename, path: /*assigned after dedup*/ Path::new(""), used_lines: 0,
                                          version: FileVersionInfo {timestamp: file.timestamp(), size: file.size(), md5: if program.header().file_has_md5() { Some(file.md5().clone()) } else { None } }};
                    f.concat_path(&mut temp_path);
                    let mut hasher = DefaultHasher::new();
                    temp_path.hash(&mut hasher);
                    shard.file_dedup.push(FileDedup {file: f, path_hash: hasher.finish() as usize, unit_idx, idx_in_unit: idx_base + idx});
                }
            }
        }
        Ok(())
    }

    fn dedup_files(&mut self) {
        let mut files: Vec<FileDedup> = Vec::new();
        for shard in &mut self.shards {
            files.append(&mut mem::take(&mut shard.get_mut().file_dedup));
        }
        files.sort_unstable_by_key(|f| f.path_hash);
        let mut file_idx = 0;
        let mut temp_path = PathBuf::new();
        for (i, file) in files.iter().enumerate() {
            if i == 0 || file.path_hash != files[i-1].path_hash {
                let mut f = file.file.clone();
                file_idx = self.sym.files.len();
                f.concat_path(&mut temp_path);
                f.path = self.sym.file_paths.add_path(&temp_path, file_idx);
                self.sym.files.push(f);
            }
            let remap = &mut self.sym.units[file.unit_idx].file_idx_remap;
            if remap.len() <= file.idx_in_unit {
                remap.resize(file.idx_in_unit + 1, 0);
            }
            remap[file.idx_in_unit] = file_idx;
        }
    }

    fn parse_dwarf(&self, shard_idx: usize, shard: &mut SymbolsLoaderShard) -> Result<()> {
        let bytes_total: usize = shard.units.iter().map(|i| self.sym.units[*i].unit.header.unit_length()).sum();
        let mut bytes_reported = 0usize;
        let mut bytes_processed = 0usize;

        let units_copy = shard.units.clone();
        for unit_idx in units_copy {
            {
                let mut loader = DwarfLoader::new(self, shard, unit_idx)?;
                loader.load()?;
            }

            bytes_processed += self.sym.units[unit_idx].unit.header.unit_length();
            if bytes_processed > bytes_reported + 10000000 {
                self.check_cancellation()?;
                bytes_reported = bytes_processed;
                self.report_run_progress(shard_idx, bytes_processed as f64 / bytes_total as f64);
            }
        }

        shard.types.finalize();

        shard.sym.local_variables.shrink_to_fit();
        shard.sym.subfunctions.shrink_to_fit();
        shard.sym.subfunction_levels.shrink_to_fit();

        Ok(())
    }

    fn parse_debug_line(&self, shard: &mut SymbolsLoaderShard) -> Result<()> {
        for &unit_idx in &shard.units {
            let unit = &self.sym.units[unit_idx];
            let program = match &unit.unit.line_program {
                None => continue,
                Some(x) => x };

            let mut rows_iter = program.clone().rows();
            let mut skip_current_sequence = false;
            while let Some((header, row)) = rows_iter.next_row()? {
                if row.address() == 0 {
                    // Binaries often have lots (like 70%) of sequences that start at zero address, presumably because a relocation was lost at some point during compilation.
                    // Maybe that's what happens when code gets optimized out at linking time (by ThinLTO?), or maybe it's a compiler bug, idk.
                    // Skip such sequences because they take up memory and overlap each other a lot.
                    // Apart from that, line number programs seem to be well-formed in practice, so for non-skipped sequences we expect that address ranges don't overlap,
                    // addresses don't decrease within a sequence, each sequence ends with a row with end_sequence() = true, etc.
                    skip_current_sequence = true;
                }

                if !skip_current_sequence {
                    let info = if row.end_sequence() {
                        LineInfo::new(row.address() as usize, None, 0, 0, LineFlags::empty())?
                    } else {
                        let file = unit.file_idx_remap.get(row.file_index() as usize).copied(); // if out of bounds (unexpected in practice), just treat it as an end-of-sequence
                        let line = row.line().map_or(0, |x| u64::from(x) as usize);
                        let column = match row.column() {
                            ColumnType::LeftEdge => 0,
                            ColumnType::Column(c) => u64::from(c) as usize,
                        };
                        let is_stmt = row.is_stmt() && file.is_some();
                        LineInfo::new(row.address() as usize, file, line, column, if is_stmt {LineFlags::STATEMENT} else {LineFlags::empty()})?
                    };

                    let mut skip = false;
                    if let Some(prev) = shard.sym.addr_to_line.last() {
                        if info.line() == 0 && info.file_idx().is_some() && prev.file_idx() == info.file_idx() && prev.line() != 0 {
                            // Often there's a zero line number out of nowhere, surrounded by good line numbers with same file.
                            // Idk what this means or whether it's intended. Let's pretend it's not there.
                            // We also do a similar thing in sort_addr_to_line() and fixup_subfunction_call_line().
                            // (Why do it here? To avoid needing stable sort in sort_addr_to_line().)
                            skip = true;
                        } else if prev.addr() == row.address() as usize {
                            // Two consecutive rows have the same address. We have to be very careful here, otherwise breakpoints get super janky.
                            // This took a few attempts to get right (the the reasoning was forgotten and I broke it again, so I'm documenting it better now).
                            //
                            // Consider this typical sequence of rows, all having the same address:
                            //
                            // Address            Line   Column File   ISA Discriminator OpIndex Flags
                            // ------------------ ------ ------ ------ --- ------------- ------- -------------
                            // 0x00000000000017b7    175      9      1   0             0       0  is_stmt
                            // 0x00000000000017b7    176      9      1   0             0       0  is_stmt
                            // 0x00000000000017b7     25     24      1   0             0       0  is_stmt
                            // 0x00000000000017b7     26      5      1   0             0       0  is_stmt
                            // 0x00000000000017b7     26     14      1   0             0       0
                            //
                            // Line 176 is call site of an inlined function. Line 25 is inside the inlined function.
                            // Additionally, there's a DW_TAG_inlined_subroutine that starts at the same address.
                            // Notice that:
                            //  * We must not add rows 1-2 (lines 175-176) to line_to_addr with STATEMENT flag.
                            //    Otherwise setting a breakpoint on line 176 would be broken: the breakpoint will have subfunction_level = u16::MAX,
                            //    so when it's hit we'll select the inner subframe of the stack trace, which is inside the inlined function on line 26 instead of 176.
                            //    (The breakpoint instead should be set using the LineInfo produced by DW_TAG_inlined_subroutine, which has subfunction_level = 0.)
                            //  * We must add at most one of the rows 3-4 (lines 25-26) to line_to_addr. If we add both, they'll be highlighted in the source code, as if there are two places control can stop;
                            //    then the user may do a step and expect to get from one highlighted line/column to the other, and be confused when it skips way ahead instead.
                            //    This is particularly bad when one of the columns is a function call and another is a parameter of the function call; if stopped on the parameter, typically
                            //    you'd do a step-over-column to get to the function call, then do step-into to step into the call; but here the step-over-column would step over the whole call - very annoying.
                            //  * We must put at least one row with line 26 into line_to_addr with STATEMENT flag, so that breakpoint can be set on it.
                            //
                            // The logic we ended up with is: keep only one of the consecutive rows with the same address; if any rows have is_stmt == true, keep the last of them, otherwise keep the last.

                            if prev.file_idx().is_none() {
                                // End of sequence... sike, a new sequence starts at the same address. Drop the end-of-sequence marker. (This happens in practice.)
                                shard.sym.addr_to_line.pop();
                            } else {
                                skip = true;
                                assert!(shard.sym.line_to_addr.last().is_some_and(|(p, _)| p.addr() == row.address() as usize));
                                if info.file_idx().is_none() {
                                    // `prev` covers an address range of length 0. We're not interested in that.
                                    shard.sym.line_to_addr.pop();
                                    *shard.sym.addr_to_line.last_mut().unwrap() = info;
                                } else if info.flags().contains(LineFlags::STATEMENT) >= prev.flags().contains(LineFlags::STATEMENT) {
                                    *shard.sym.line_to_addr.last_mut().unwrap() = (info, u16::MAX);
                                    *shard.sym.addr_to_line.last_mut().unwrap() = info;
                                } else {
                                    // `prev` is a statement, and `info` is not. Keep `prev`.
                                }
                            }
                        }
                    }
                    if !skip {
                        if info.file_idx().is_some() {
                            shard.sym.line_to_addr.push((info.clone(), u16::MAX));
                        }
                        shard.sym.addr_to_line.push(info);
                    }
                }

                if row.end_sequence() {
                    skip_current_sequence = false;
                }
            }
        }

        Ok(())
    }

    fn function_sorting_key(f: &FunctionInfo) -> usize {
        assert!(FUNCTION_ADDR_MAX << 2 != 0 && (FUNCTION_ADDR_MAX - 1) & FUNCTION_ADDR_MAX == 0);
        // If a function starts at the same address as another function ends, the real function should come first (to discard the end marker).
        // If a function is present both in .symtab and .debug_info, the .debug_info function should come first (to discard the other one).
        (f.addr.0 << 2) | ((f.flags.contains(FunctionFlags::SENTINEL) as usize) << 1) | f.flags.contains(FunctionFlags::SYMTAB) as usize
    }
    
    fn sort_functions(&self, shard: &mut SymbolsLoaderShard) {
        shard.functions_before_dedup = shard.functions.len();
        shard.functions.sort_unstable_by_key(Self::function_sorting_key);
        shard.functions.dedup_by_key(|f| f.addr);
    }

    fn sort_global_variable_names(&self, shard_idx: usize, shard: &mut SymbolsLoaderShard) {
        let mut names: Vec<GlobalVariableNameMessage> = Vec::new();
        for other_shard in &self.send_global_variable_names {
            unsafe {names.append(&mut *(*other_shard.get())[shard_idx].get())};
        }
        names.sort_unstable();

        let mut start = 0usize;
        while start < names.len() {
            let mut end = start + 1;
            while end < names.len() && names[end].name == names[start].name {
                end += 1;
            }
            let suffix_helper = DisambiguatingSuffixes::new(end - start);
            for i in start..end {
                let n = &names[i];
                let (final_name, _) = suffix_helper.disambiguate(n.name, i - start, n.ptr as usize, &mut shard.sym.sorted_global_variable_names);
                unsafe {(*n.ptr).set_name(final_name)};
            }
            start = end;
        }
    }

    fn sort_addr_to_line(&self, shard: &mut SymbolsLoaderShard, finalize: bool) {
        shard.sym.addr_to_line.sort_unstable_by_key(|x| x.addr_filenone_linebad_inlined());

        let mut prev = LineInfo::new(0, None, 0, 0, LineFlags::empty()).unwrap();
        shard.sym.addr_to_line.retain(|l| {
            // Deduplicate. E.g. if a sequence starts at the same address another sequence ends, keep the start and discard the end.
            if l.addr() == prev.addr() {
                return false;
            }

            // I've seen line number info like this:
            //                       src/Functions/sleep.h:122:29
            //   000022265edb <+4fb> call DB::IDataType::createColumnConst
            //   000022265ee0 <+500> jmp _+505h
            //                       src/Functions/sleep.h     <----------------------------------------- ???
            // ⮕ 000022265ee5 <+505> lea rdi,[rbp-130h]
            //                       src/Functions/sleep.h:122:16
            //   000022265eec <+50c> call boost::intrusive_ptr<DB::IColumn const>::operator->
            //
            // What's that line table entry in the middle without a line number? Idk. Let's just remove it.
            if l.line() == 0 && l.file_idx().is_some() && l.file_idx() == prev.file_idx() && prev.line() != 0 {
                return false;
            }

            prev = l.clone();
            true
        });

        if finalize {
            shard.sym.addr_to_line.shrink_to_fit();
        } else {
            shard.addr_to_line_len_after_debug_line = shard.sym.addr_to_line.len();
        }
    }

    fn sort_line_to_addr(&self, shard: &mut SymbolsLoaderShard) {
        shard.sym.line_to_addr.sort_unstable_by_key(|x| x.0.file_line_column_addr());

        for (l, _) in &shard.sym.line_to_addr {
            if l.line() == 0 || !l.flags().contains(LineFlags::STATEMENT) { // see comment on LineInfo::used_lines
                continue;
            }
            let idx = l.file_idx().unwrap();
            match shard.file_used_lines.last_mut() {
                Some(x) if x.0 == idx => x.1 += 1,
                _ => shard.file_used_lines.push((idx, 1)),
            }
        }
    }

    fn parse_symtab(&self, shard_idx: usize, shard: &mut SymbolsLoaderShard) -> Result<()> {
        for (section_idx, ranges) in shard.symtab_ranges.iter().enumerate() {
            let [strtab, symtab] = &self.strtab_symtab[section_idx];
            let entry_size = mem::size_of::<libc::Elf64_Sym>();
            for range in ranges {
                for offset in range.clone().step_by(entry_size) {
                    let mut sym: libc::Elf64_Sym;
                    unsafe {
                        sym = mem::zeroed();
                        ptr::copy_nonoverlapping::<u8>(symtab[offset..offset+entry_size].as_ptr(), mem::transmute(&mut sym), entry_size);
                    }
                    if sym.st_value == 0 || sym.st_shndx == SHN_UNDEF {
                        continue;
                    }
                    let addr = sym.st_value as usize;

                    // Function.
                    if sym.st_info & 0xf == STT_FUNC {
                        let name_ref = if sym.st_name == 0 {
                            let mut out = shard.sym.misc_arena.write();
                            write!(out, "[function at {:x} (.symtab)]", addr)?;
                            out.finish()
                        } else {
                            let suf = &strtab[sym.st_name as usize..];
                            let end = suf.iter().position(|c| *c == b'\0').unwrap_or(suf.len());
                            &suf[..end]
                        };
                        let name_ref: &'static str = unsafe {mem::transmute(name_ref)};

                        let f_addr = FunctionAddr::new(addr, &mut shard.warn);
                        shard.functions.push(FunctionInfo {addr: f_addr, die: DebugInfoOffset(usize::MAX), entry_addr: addr, prev_addr: f_addr, mangled_name: name_ref.as_ptr(), mangled_name_len: name_ref.len() as u32, shard_idx: shard_idx as u16, flags: FunctionFlags::SYMTAB, language: LanguageFamily::Unknown, subfunction_levels: 0..0});

                        // Dummy function that the dynamic linker calls to notify the debugger after each library load.
                        if name_ref == "_dl_debug_state" {
                            shard.points_of_interest.entry(PointOfInterest::LibraryLoad).or_default().push(addr);
                        }
                        if name_ref == "__cxa_throw" {
                            shard.points_of_interest.entry(PointOfInterest::Exception).or_default().push(addr);
                        }

                        // For some reason functions' [st_value, st_value + st_size) ranges overlap a lot. Maybe st_size is just not reliable.
                        // So we ignore st_size and assume that each function ends where the next function starts.
                        continue;
                    }

                    // Vtable.
                    if sym.st_info & 0xf == STT_OBJECT && sym.st_size != 0 && sym.st_name != 0 && strtab[sym.st_name as usize..].starts_with(b"_ZTV") {
                        let mangled = &strtab[sym.st_name as usize..];
                        let end = mangled.iter().position(|c| *c == b'\0').unwrap_or(mangled.len());
                        let mangled = &mangled[..end];
                        // Unfortunately, there's no pointer from vtable info to the type DIE. There's only the mangled name. And the type DIE doesn't even contain the mangled name, or even the fully-qualified name!
                        // We have to reconstruct the fully-qualified name while parsing DWARF, from the DIEs and attributes describing namespaces, template arguments, etc.
                        // Then match that reconstructed name against the name from symtab. We currently don't do it well at all. Doing it fully correctly is probably crazy complicated,
                        // but there's probably plenty of low-hanging improvement in the name reconstruction logic.
                        // Probably it would be better to do structural comparison on the demangling AST instead of demangled strings, to not be sensitive to the arbitrary details of how different manglers/demanglers
                        // print things like lambdas and anonymous namespaces; but that sounds too complicated.
                        match cpp_demangle::BorrowedSymbol::new_with_options(mangled, &cpp_demangle::ParseOptions::default().recursion_limit(1000)) {
                            Err(e) => if shard.warn.check(line!()) { eprintln!("warning: failed to demangle (1) vtable symtab entry '{}': {}", String::from_utf8_lossy(mangled), e); }
                            Ok(symbol) => match symbol.demangle(&cpp_demangle::DemangleOptions::default().recursion_limit(1000)) {
                                Err(e) => if shard.warn.check(line!()) { eprintln!("warning: failed to demangle (2) vtable symtab entry '{}': {}", String::from_utf8_lossy(mangled), e); }
                                Ok(name) if name.starts_with("{vtable(") => {
                                    // It's either "{vtable(Foo)}" or "{vtable(Foo)} [.clone .3e570ba5df68adedf72ec05448f83d40]". AFAIU, the latter means it's a synthetic type that's not quite Foo; I guess we should still treat it as Foo.
                                    let name = &name["{vtable(".len()..];
                                    if let Some(end) = name.rfind(")}") {
                                        let name = &name[..end];
                                        let name = shard.sym.misc_arena.add_str(name);
                                        shard.vtables.push(VTableInfo {start: addr, end: addr + sym.st_size as usize, name, type_: None});
                                    } else {
                                        if shard.warn.check(line!()) { eprintln!("error: unexpected demangled vtable name format, this is a bug: '{}' -> {}", String::from_utf8_lossy(mangled), name); }
                                    }
                                }
                                Ok(name) => if shard.warn.check(line!()) { eprintln!("error: unexpected demangled vtable name format, this is a bug: '{}' -> {}", String::from_utf8_lossy(mangled), name); }
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn parse_misc_sections(&self, shard_idx: usize, shard: &mut SymbolsLoaderShard) {
        // Sections that contain executable code but are not usually covered by debug symbols. We pretend that each of them is a function, to make them show up in disassembly window at all.
        for name in [".init", ".fini", ".plt", ".plt.got", ".plt.sec"] {
            if let Some(&idx) = self.sym.elves[0].section_by_name.get(name) {
                let s = &self.sym.elves[0].sections[idx];
                if s.size != 0 && s.address != 0 {
                    let name_ref = shard.sym.misc_arena.add_slice(name.as_bytes());
                    let start_addr = FunctionAddr::new(s.address, &mut shard.warn);
                    let end_addr = FunctionAddr::new(s.address.saturating_add(s.size), &mut shard.warn);
                    shard.functions.push(FunctionInfo {
                        addr: start_addr, prev_addr: start_addr, entry_addr: s.address,
                        die: DebugInfoOffset(usize::MAX), mangled_name: name_ref.as_ptr(), mangled_name_len: name_ref.len() as u32,
                        shard_idx: shard_idx as u16, flags: FunctionFlags::SECTION, language: LanguageFamily::Unknown, subfunction_levels: 0..0});
                    shard.functions.push(FunctionInfo {
                        addr: end_addr, prev_addr: end_addr, entry_addr: 0,
                        die: DebugInfoOffset(usize::MAX), mangled_name: "".as_ptr(), mangled_name_len: 0,
                        shard_idx: shard_idx as u16, flags: FunctionFlags::SECTION | FunctionFlags::SENTINEL, language: LanguageFamily::Unknown, subfunction_levels: 0..0});
                }
            }
        }
    }

    fn fixup_type_refs(&self, shard_idx: usize, shard: &mut SymbolsLoaderShard) {
        for v in &mut shard.sym.local_variables {
            v.type_ = self.types.find_final_type(DebugInfoOffset(v.type_ as usize));
        }
        for v in unsafe {shard.sym.global_variables.iter_mut::<Variable>()} {
            v.type_ = self.types.find_final_type(DebugInfoOffset(v.type_ as usize));
        }
    }

    fn finish_types(&mut self) {
        let (types, builtin_types) = mem::replace(&mut self.types, TypesLoader::invalid()).into_results();
        self.sym.builtin_types = builtin_types;
        for (i, t) in types.into_iter().enumerate() {
            self.shards[i].get_mut().sym.types = t;
        }
    }

    fn merge_base_types(&mut self) {
        for shard in &mut self.shards {
            self.sym.base_types.append(&mut mem::take(&mut shard.get_mut().base_types));
        }
        self.sym.base_types.shrink_to_fit();
        self.sym.base_types.sort_unstable();
    }

    // Some glue code to compensate for style differences between cpp_demangle output and our synthesized type names.
    // Replace "(anonymous namespace)" with "_".
    // This is far from sufficient to cover all cases. That would probably require a crazy amount of code that understands the whole C++ type system
    // and actually parses type names and compares them structurally. (E.g. C++ template argument may be an expression, or a type of a labmda, etc.)
    fn adjust_vtable_type_name<'a>(name: &'a str, out: &'a mut String) -> &'a str {
        out.clear();
        const NEEDLE: &str = "(anonymous namespace)::";
        const REPLACEMENT: &str = "_::";

        let mut last_end = 0;
        while let Some(pos) = name[last_end..].find(NEEDLE) {
            let absolute_pos = last_end + pos;
            out.push_str(&name[last_end..absolute_pos]);
            out.push_str(REPLACEMENT);
            last_end = absolute_pos + NEEDLE.len();
        }

        if last_end == 0 {
            name
        } else {
            out.push_str(&name[last_end..]);
            &out[..]
        }
    }

    fn collect_vtables_and_points_of_interest(&mut self) {
        // There are usually only tens of thousands of vtables, so it's ok to process them in one thread.
        for shard in &mut self.shards {
            self.sym.vtables.append(&mut mem::take(&mut shard.get_mut().vtables));
            for (p, addrs) in &shard.get_mut().points_of_interest {
                self.sym.points_of_interest.entry(*p).or_default().extend(addrs.iter().copied());
            }
        }
        // TODO: __cxa_throw, _ZN3std9panicking20rust_panic_with_hook17.{17}E, test that it works with regular panics and overflow checks, with and without handler, with and without catch, and for uncaught C++ exceptions
        /*
        for shard in &mut self.shards {
            let mut find_function = |name: &[u8], p: PointOfInterest, sym: &mut Symbols| {
                let v = &shard.get_mut().sym.mangled_name_to_function;
                let i = v.partition_point(|(n, _, _)| *n < name);
                if i < v.len() && v[i].0 == name {
                    let f = &sym.functions[v[i].2];
                    if f.entry_addr != 0 {
                        sym.points_of_interest.entry(p).or_default().push(f.entry_addr);
                    }
                }
            };
            find_function(b"__cxa_throw", PointOfInterest::..., &mut self.sym);
        }*/
        self.sym.vtables.sort_unstable_by_key(|v| v.start);

        for (_, addrs) in &mut self.sym.points_of_interest {
            addrs.sort_unstable();
            addrs.dedup();
        }

        let mut adjusted_name = String::new();
        for v in &mut self.sym.vtables {
            for shard in &mut self.shards {
                let adjusted_name = Self::adjust_vtable_type_name(v.name, &mut adjusted_name);
                if let Some(t) = shard.get_mut().sym.types.find_by_name(adjusted_name) {
                    v.type_ = Some(t);
                    break;
                }
            }
        }
    }

    fn collect_used_lines_per_file(&mut self) {
        for shard in &mut self.shards {
            for &(idx, count) in &shard.get_mut().file_used_lines {
                self.sym.files[idx].used_lines += count;
            }
        }
        for i in 0..self.sym.files.len() {
            if self.sym.files[i].used_lines == 0 {
                continue;
            }
            self.sym.path_to_used_file.insert(self.sym.files[i].path, i);
        }
    }

    fn dedup_functions(&mut self) {
        let max_function_end = self.shards.iter_mut().map(|s| s.get_mut().max_function_end).max().unwrap_or(0);
        let end_addr = FunctionAddr::new(max_function_end, &mut self.shards[0].get_mut().warn);
        let additional_functions = [FunctionInfo {addr: end_addr, prev_addr: end_addr, entry_addr: 0, mangled_name: "".as_ptr(), mangled_name_len: 0, shard_idx: 0, flags: FunctionFlags::SENTINEL, language: LanguageFamily::Unknown, subfunction_levels: 0..0, die: DebugInfoOffset(usize::MAX)}];
        let mut sources: Vec<&[FunctionInfo]> = self.shards.iter().map(|s| unsafe {&(*s.get()).functions[..]}).collect();
        sources.push(&additional_functions);
        let mut iter = MergeIterator::new(sources, |f| !Self::function_sorting_key(f));
        let mut functions: Vec<FunctionInfo> = Vec::new();
        let mut prev_addr = FunctionAddr(usize::MAX);
        while let Some(f) = iter.next() {
            if f.addr != prev_addr {
                prev_addr = f.addr;
                functions.push(f.clone());
            }
        }
        for (i, f) in functions.iter().enumerate() {
            if f.flags.contains(FunctionFlags::INLINED) {
                let shard_idx = f.die.0 % self.die_to_function_shards.len();
                self.die_to_function_shards[shard_idx].get_mut().push((f.die, i));
            }
        }
        functions.shrink_to_fit();
        self.sym.functions = functions;
    }

    fn build_name_to_function_map(&self, shard_idx: usize, shard: &mut SymbolsLoaderShard) {
        let start_idx = self.sym.functions.len() * shard_idx / self.shards.len();
        let end_idx = self.sym.functions.len() * (shard_idx + 1) / self.shards.len();
        for idx in start_idx..end_idx {
            let f = &self.sym.functions[idx];
            shard.sym.mangled_name_to_function.push((f.mangled_name(), f.addr, idx));
        }
        shard.sym.mangled_name_to_function.sort_unstable();
    }
    
    fn sort_die_to_function(&self, die_to_function: &mut Vec<(DieOffset, usize)>) {
        die_to_function.sort_unstable_by_key(|t| t.0);
    }

    fn fixup_function_refs(&self, shard: &mut SymbolsLoaderShard) {
        for sf in &mut shard.sym.subfunctions {
            if sf.identity == 0 {
                continue;
            }
            let die = sf.callee_idx;
            let shard_idx = die % self.die_to_function_shards.len();
            let die_to_function = unsafe {&*self.die_to_function_shards[shard_idx].get()};
            let i = die_to_function.partition_point(|t| t.0.0 < die);
            if i == die_to_function.len() || die_to_function[i].0.0 != die {
                sf.callee_idx = usize::MAX;
            } else {
                sf.callee_idx = die_to_function[i].1;
            }
        }
    }

    fn log_timing_and_stats(&mut self) {
        let prepare_ns: usize = self.prepare_time_per_stage_ns.iter().copied().sum();
        let total_cpu_ns  = prepare_ns + self.run_time_per_stage_ns.iter().map(|v| v.iter().map(|t| t.load(Ordering::Relaxed)).sum::<usize>()).sum::<usize>();
        let total_wall_ns = prepare_ns + self.run_time_per_stage_ns.iter().map(|v| v.iter().map(|t| t.load(Ordering::Relaxed)).max().unwrap()).sum::<usize>();
        self.sym.loading_duration_ns = total_wall_ns;
        if total_wall_ns > 500_000_000 {
            let funcs_before_dedup: usize = self.shards.iter().map(|s| unsafe {(*s.get()).functions_before_dedup}).sum();
            let subfunctions_needed_fixup: usize = self.shards.iter().map(|s| unsafe {(*s.get()).subfunctions_need_fixup.len()}).sum();
            let misc_arena_size: usize = self.shards.iter().map(|s| unsafe {(*s.get()).sym.misc_arena.capacity()}).sum();
            let addr_to_lines: usize = self.shards.iter().map(|s| unsafe {(*s.get()).sym.line_to_addr.len()}).sum();
            let line_to_addrs: usize = self.shards.iter().map(|s| unsafe {(*s.get()).sym.addr_to_line.len()}).sum();
            let lines_in_debug_line: usize = self.shards.iter().map(|s| unsafe {(*s.get()).addr_to_line_len_after_debug_line}).sum();
            let local_variables: usize = self.shards.iter().map(|s| unsafe {(*s.get()).sym.local_variables.len()}).sum();
            let global_variables: usize = self.shards.iter().map(|s| unsafe {(*s.get()).sym.global_variables.used() / mem::size_of::<Variable>()}).sum();
            let global_variable_name_bytes: usize = self.shards.iter().map(|s| unsafe {(*s.get()).sym.sorted_global_variable_names.arena.capacity()}).sum();
            let files_before_dedup: usize = self.sym.units.iter().map(|u| u.file_idx_remap.len()).sum();

            let mut function_names_len = 0usize;
            let mut max_subfunction_level = 0usize;
            for f in &self.sym.functions {
                if f.prev_addr >= f.addr {
                    function_names_len += f.mangled_name().len();
                }
                max_subfunction_level = max_subfunction_level.max(f.subfunction_levels.len().saturating_sub(1));
            }

            let final_types: usize = self.shards.iter().map(|s| unsafe {(*s.get()).sym.types.num_types()}).sum();
            let type_names = self.shards.iter().map(|s| unsafe {(*s.get()).sym.types.sorted_type_names.strings.len()}).sum();
            let type_names_len = self.shards.iter().map(|s| unsafe {(*s.get()).sym.types.sorted_type_names.arena.used()}).sum();
            let type_infos_bytes = self.shards.iter().map(|s| unsafe {(*s.get()).sym.types.types_arena.used()}).sum();
            let fields_bytes = self.shards.iter().map(|s| unsafe {(*s.get()).sym.types.fields_arena.used()}).sum();
            let types_misc_bytes = self.shards.iter().map(|s| unsafe {(*s.get()).sym.types.misc_arena.used()}).sum();
            let subfunctions: usize = self.shards.iter().map(|s| unsafe {(*s.get()).sym.subfunctions.len()}).sum();
            let subfunction_levels: usize = self.shards.iter().map(|s| unsafe {(*s.get()).sym.subfunction_levels.len()}).sum();
            let unresolved_vtables: usize = self.sym.vtables.iter().map(|v| v.type_.is_none() as usize).sum();
            let (mut field_used_bytes, mut nested_names) = (0usize, 0usize);
            for shard in &self.shards {
                for t in unsafe {(*shard.get()).sym.types.iter()} {
                    nested_names += t.nested_names.len();
                    match &t.t {
                        Type::Struct(s) => field_used_bytes += s.fields().len() * mem::size_of::<StructField>(),
                        Type::Enum(e) => field_used_bytes += e.enumerands.len() * mem::size_of::<Enumerand>(),
                        _ => (),
                    }
                }
            }

            let peak_mem_str = match peak_memory_usage_of_current_process() {
                Ok(x) => {
                    self.sym.loading_memory_usage = Some(x);
                    format!("{}", PrettySize(x))
                }
                Err(e) => format!("<{}>", e),
            };

            let mut time_breakdown = String::new();
            if true {
                // Print how long different stages took relative to each other, in a form copy-pastable into the progress_per_stage initialization code.
                write!(time_breakdown, ", time taken per stage: [").unwrap();
                for stage in 0..self.progress_per_stage.len() {
                    let wall_ns = [self.prepare_time_per_stage_ns[stage], self.run_time_per_stage_ns[stage].iter().map(|t| t.load(Ordering::Relaxed)).max().unwrap()];
                    write!(time_breakdown, "\n[").unwrap();
                    for j in 0..2 {
                        write!(time_breakdown, "({:.3}, \"{}\"), ", wall_ns[j] as f64 / 1e9, self.progress_per_stage[stage][j].1).unwrap();
                    }
                    write!(time_breakdown, "],").unwrap();
                }
                write!(time_breakdown, "];").unwrap();
            }

            eprintln!("info: loaded symbols for {} in {:.3}s (cpu: {:.3}s) in {} threads, process peak memory usage: {}, stats: {} units, {} files \
                       ({:.2}x dedup, {:.2}x unused, {} of paths, {} of remap), \
                       {} functions ({:.2}x dedup, {}, {} of names), {} in misc arena, \
                       {} subfunctions ({} sf, {} levels, {} fixed up), \
                       {} + {} lines ({}, {} in .debug_line), {} local variables ({}), {} global variables ({}, names {}), \
                       {} types ({:.2}x dedup, {:.2}x offsets, {} names ({}), \
                       {} infos, {} fields ({:.2}% growth waste), {} nested names, {} misc, temp {} offset maps, temp {} dedup maps) \
                       ({} base types), {} vtables ({:.2}% unresolved){}",
                      self.sym.elves[0].name, total_wall_ns as f64 / 1e9, total_cpu_ns as f64 / 1e9, self.num_shards, peak_mem_str, PrettyCount(self.sym.units.len()), PrettyCount(self.sym.files.len()),
                      files_before_dedup as f64 / self.sym.files.len() as f64, self.sym.files.len() as f64 / self.sym.path_to_used_file.len() as f64, PrettySize(self.sym.file_paths.arena.used()), PrettySize(files_before_dedup * mem::size_of::<usize>()),
                      PrettyCount(self.sym.functions.len()), funcs_before_dedup as f64 / self.sym.functions.len() as f64, PrettySize(self.sym.functions.len() * mem::size_of::<FunctionInfo>()), PrettySize(function_names_len), PrettySize(misc_arena_size),
                      PrettyCount(subfunctions), PrettySize(subfunctions * mem::size_of::<Subfunction>()), PrettySize(subfunction_levels * mem::size_of::<usize>()), PrettyCount(subfunctions_needed_fixup),
                      PrettyCount(addr_to_lines), PrettyCount(line_to_addrs), PrettySize((addr_to_lines + line_to_addrs) * mem::size_of::<LineInfo>()), PrettyCount(lines_in_debug_line), PrettyCount(local_variables), PrettySize(local_variables * mem::size_of::<Variable>()), PrettyCount(global_variables), PrettySize(global_variables * mem::size_of::<Variable>()), PrettySize(global_variable_name_bytes),
                      PrettyCount(final_types), self.types_before_dedup as f64 / final_types as f64, self.type_offsets as f64 / self.types_before_dedup as f64, PrettyCount(type_names), PrettySize(type_names_len),
                      PrettySize(type_infos_bytes), PrettySize(fields_bytes), fields_bytes as f64 / field_used_bytes as f64 * 100.0 - 100.0, PrettyCount(nested_names), PrettySize(types_misc_bytes), PrettySize(self.type_offset_maps_bytes), PrettySize(self.type_dedup_maps_bytes),
                      PrettyCount(self.sym.base_types.len()), self.sym.vtables.len(), unresolved_vtables as f64 / self.sym.vtables.len() as f64 * 100.0, time_breakdown);
        }
    }
}

// A thing that traverses the tree of DIEs, one unit at a time.
// This is the slowest part of loading the debug symbols, so we should worry about speed the most here.
struct DwarfLoader<'a> {
    // Example tree, in order of iteration:
    //   compile_unit
    //     entry
    //     entry
    //       entry
    //       null
    //     entry
    //       entry
    //         entry
    //         entry
    //         null
    //       null
    //     null
    //
    // Notice that every nonempty list of children (except the root compile_unit) is terminated by a null entry (in code represented as abbrev == None).
    // abbrev.has_children() tells whether current entry has children.
    // These two pieces of information are enough to keep track of depth.
    loader: &'a SymbolsLoader,
    section_slice: DwarfSlice,
    shard_idx: usize,
    shard: &'a mut SymbolsLoaderShard,
    unit: &'a DwarfUnit,

    // Scope name, like "std::vector<int>". We append to it when going into a namespace/class/function/etc, then un-append when leaving the subtree.
    scope_name: String,

    temp: LoaderTempStorage,

    // Main stack contains a sentinel root entry, then all DIEs on the path from the unit's root to the current DIE.
    // When pushing to non-main stacks, make sure to set the corresponding flag in main_stack.top_mut().flags.
    main_stack: FastStack<MainStackEntry, 0>,
    scope_stack: FastStack<ScopeStackEntry, {StackFlags::HAS_SCOPE.bits()}>,
    function_stack: FastStack<FunctionStackEntry, {StackFlags::HAS_FUNCTION.bits()}>,
    subfunction_stack: FastStack<SubfunctionStackEntry, {StackFlags::HAS_SUBFUNCTION.bits()}>,
    type_stack: FastStack<TypeStackEntry, {StackFlags::HAS_TYPE.bits()}>,
    ranges_stack: FastStack<RangesStackEntry, {StackFlags::HAS_RANGES.bits()}>,
}

// Start or end of a tentative Subfunction.
struct SubfunctionEvent {
    addr: usize,
    subfunction_idx: u32, // in FunctionStackEntry.`subfunctions`
    // (level + 1) * sign, where sign is +1 if start of range, -1 if end of range.
    // Has to be this way for sorting to work (packed into one number to make sorting faster):
    // if multiple ranges start/end at the same address, first process the ends from deep to shallow, then process the starts from shallow to deep.
    signed_level: i16,
}

#[derive(Default)]
struct LoaderTempStorage {
    // Used by finish_function(). Reused to avoid allocations (they showed up in profiling).
    stack: Vec<(/*range_idx*/ usize, /*active*/ usize)>,
    levels: Vec<Vec<Subfunction>>,
}

// While DFSing the tree of DIEs we maintain a few stacks: main stack that has all DIEs we're currently inside of (pushed/popped very frequently, needs to be fast), and smaller stacks for specific kinds of DIEs, e.g. functions.

// Stack entries often contain Vec-s, which we don't want to destroy/reallocate on every pop/push. So we have this wrapper that doesn't call destructors.
#[derive(Default)]
struct FastStack<T: Default, const FLAG: u16> {
    s: Vec<T>,
    len: usize,
}
impl<T: Default, const FLAG: u16> FastStack<T, FLAG> {
    #[inline]
    fn push_uninit(&mut self, flags: &mut StackFlags) -> &mut T {
        if self.len == self.s.len() {
            self.s.resize_with((self.len + 1) * 4, Default::default);
        }
        debug_assert!(!flags.contains(StackFlags::from_bits_truncate(FLAG)) || FLAG == 0);
        flags.insert(StackFlags::from_bits_truncate(FLAG));
        self.len += 1;
        &mut self.s[self.len - 1]
    }
    fn pop(&mut self) -> &T { self.len -= 1; &self.s[self.len] }
    fn pop_mut(&mut self) -> &mut T { self.len -= 1; &mut self.s[self.len] }
    fn top(&self) -> &T { &self.s[self.len - 1] }
    fn top_mut(&mut self) -> &mut T { &mut self.s[self.len - 1] }
    fn top2(&self) -> &T { &self.s[self.len - 2] }
    fn top2_mut(&mut self) -> &mut T { &mut self.s[self.len - 2] }
}

bitflags! { struct StackFlags: u16 {
    // Which other stacks to pop when popping entry from the main stack.
    const HAS_SCOPE = 0x1;
    const HAS_FUNCTION = 0x2;
    const HAS_SUBFUNCTION = 0x4;
    const HAS_TYPE = 0x8;
    const HAS_RANGES = 0x10;

    // Whether discriminated union info in type_stack.top() needs to be updated when popping this entry from the main stack.
    // (We don't have a whole separate stack for VariantInfo-s because they seem to never be nested.)
    const HAS_VARIANT = 0x20;

    const HAS_ANYTHING = 0x3f; // OR of all HAS_* bits

    // Are we in a function scope, or type scope, or neither? E.g. if some types/functions are nested in one another, it'll describe the innermost one.
    // These two flags are mutually exclusive.
    const IS_FUNCTION_SCOPE = 0x40;
    const IS_TYPE_SCOPE = 0x80;
    // Unset if we're in function/type scope, but we decided to discard that function/type (e.g. the function is unused or inline-only, or we failed to parse something).
    // Used in combination with one of the IS_*_SCOPE flags above.
    // If unset, there may be no corresponding type/function/subfunction in the corresponding other stack, so this flag must be checked before e.g. adding local variables to the stack entry.
    const IS_VALID_SCOPE = 0x100;

    const IS_ANY_SCOPE = 0x1c0; // OR of all IS_*_SCOPE bits
}}

#[derive(Clone, Copy)]
struct MainStackEntry {
    tag: DwTag,
    flags: StackFlags,
}
impl Default for MainStackEntry { fn default() -> Self { Self {tag: DW_TAG_null, flags: StackFlags::empty()} } }

// Scope (namespace, struct, function, etc).
#[derive(Default, Clone, Copy)]
struct ScopeStackEntry {
    // TODO: Support replacing the whole scope name instead of appending, in case of function with linkage_name and no name.
    scope_name_len: usize, // excluding current DIE
    // Indicates that we're not inside an anonymous namespace or function, so scope_name should be somewhat legit and can be used for deduplication.
    scope_name_is_linkable: bool,
}

// Function (DW_TAG_subprogram).
#[derive(Default)]
struct FunctionStackEntry {
    // Index in `functions`.
    function: usize,
    subfunctions: Vec<(Subfunction, /*parent*/ u32)>, // inlined function calls in `function`; all have different identities, each may correspond to multiple address ranges (described by subfunction_events)
    subfunction_events: Vec<SubfunctionEvent>,
    ranges_stack_idx: usize, // where in ranges_stack are this function's address ranges
}
impl FunctionStackEntry { fn reset(&mut self, ranges_stack_idx: usize) { self.ranges_stack_idx = ranges_stack_idx; self.function = usize::MAX; self.subfunctions.clear(); self.subfunction_events.clear(); } }

// Subfunction (function or inlined function call).
#[derive(Default)]
struct SubfunctionStackEntry {
    // Index in FunctionStackEntry.subfunctions.
    subfunction_idx: u32,
    subfunction_level: u16,
    local_variables: Vec<Variable>,
}
impl SubfunctionStackEntry { #[inline] fn reset(&mut self, subfunction_idx: u32, subfunction_level: u16) { (self.subfunction_idx, self.subfunction_level) = (subfunction_idx, subfunction_level); self.local_variables.clear(); } }

// Type (struct, enum, pointer, etc).
struct TypeStackEntry {
    type_: *mut TypeInfo, // a real pointer (not DieOffset) to the type
    nested_names: Vec<(&'static str, NestedName)>, // if exact_type is not null

    // Information about discriminated union (usually Rust enum).
    discriminant_die: DieOffset, // from DW_TAG_variant_part
    variant_field_flags: FieldFlags, // if we're inside DW_TAG_variant: VARIANT or DEFAULT_VARIANT; otherwise empty
    discr_value: usize, // if we're inside DW_TAG_variant
}
impl Default for TypeStackEntry { fn default() -> Self { Self {type_: ptr::null_mut(), nested_names: Vec::new(), discriminant_die: DebugInfoOffset(0), variant_field_flags: FieldFlags::empty(), discr_value: 0} } }
impl TypeStackEntry { fn reset(&mut self, type_: *mut TypeInfo) { self.type_ = type_; self.nested_names.clear(); self.discriminant_die = DebugInfoOffset(0); self.variant_field_flags = FieldFlags::empty(); } }

// Something that has address ranges (unit, function, lexical scope, inlined function, etc).
#[derive(Default)]
struct RangesStackEntry {
    // Current address range(s) to use for local variables (unless they have loclist ranges).
    // Not necessarily sorted.
    pc_ranges: Vec<gimli::Range>,
}


dwarf_struct!{ CommonAttributes {
    // Keep these fields in sync with VariableAttributes and SubprogramAttributes, so that field numbers can be passed to chase_origin_pointers() without conversion.
    decl: DwarfCodeLocation, DW_AT_decl_file, CodeLocation;
    specification_or_abstract_origin: DwarfReference, DW_AT_specification, SpecificationOrAbstractOrigin;
    name: &'static str, DW_AT_name, String;
    linkage_name: &'static str, DW_AT_linkage_name, String;
    type_: /*DieOffset*/ usize, DW_AT_type, DebugInfoOffset;
}}

dwarf_struct!{ NamespaceAttributes {
    name: &'static str, DW_AT_name, String;
}}

dwarf_struct!{ VariableAttributes {
    // These fields must be identical to CommonAttributes, in the same order, and at the start.
    decl: DwarfCodeLocation, DW_AT_decl_file, CodeLocation;
    specification_or_abstract_origin: DwarfReference, DW_AT_specification, SpecificationOrAbstractOrigin;
    name: &'static str, DW_AT_name, String;
    linkage_name: &'static str, DW_AT_linkage_name, String;
    type_: /*DieOffset*/ usize, DW_AT_type, DebugInfoOffset;

    location_expr: /*Expression*/ &'static [u8], DW_AT_location, Expression;
    location_list: /*LocationListsOffset*/ usize, DW_AT_location, LocationListsOffset;
    const_value_usize: usize, DW_AT_const_value, MaybeSigned;
    const_value_slice: &'static [u8], DW_AT_const_value, Slice;
}}

dwarf_struct!{ SubprogramAttributes {
    // These fields must be identical to CommonAttributes, in the same order, and at the start.
    decl: DwarfCodeLocation, DW_AT_decl_file, CodeLocation;
    specification_or_abstract_origin: DwarfReference, DW_AT_specification, SpecificationOrAbstractOrigin;
    name: &'static str, DW_AT_name, String;
    linkage_name: &'static str, DW_AT_linkage_name, String;
    type_: /*DieOffset*/ usize, DW_AT_type, DebugInfoOffset;

    ranges: DwarfRanges, DW_AT_ranges, Ranges;
    frame_base_expr: /*Expression*/ &'static [u8], DW_AT_frame_base, Expression;
    frame_base_list: /*LocationListsOffset*/ usize, DW_AT_frame_base, LocationListsOffset;
    main_subprogram: bool, DW_AT_main_subprogram, Flag;
    inline: usize, DW_AT_inline, MaybeSigned;
}}

dwarf_struct!{ TypeAttributes {
    decl: DwarfCodeLocation, DW_AT_decl_file, CodeLocation;
    specification_or_abstract_origin: DwarfReference, DW_AT_specification, SpecificationOrAbstractOrigin;
    name: &'static str, DW_AT_name, String;
    type_: /*DieOffset*/ usize, DW_AT_type, DebugInfoOffset;
    containing_type: /*DieOffset*/ usize, DW_AT_containing_type, DebugInfoOffset;
    // byte_size/bit_size may in theory be exprloc, presumably for some kind of dynamically-sized types, but I haven't seen that in practice.
    byte_size: usize, DW_AT_byte_size, Unsigned;
    bit_size: usize, DW_AT_bit_size, Unsigned;
    declaration: bool, DW_AT_declaration, Flag;
    encoding: usize, DW_AT_encoding, Unsigned;
    byte_stride: usize, DW_AT_byte_stride, Unsigned;
    bit_stride: usize, DW_AT_bit_stride, Unsigned;
}}

dwarf_struct!{ FieldAttributes {
    decl: DwarfCodeLocation, DW_AT_decl_file, CodeLocation;
    name: &'static str, DW_AT_name, String;
    type_: /*DieOffset*/ usize, DW_AT_type, DebugInfoOffset;
    byte_size: usize, DW_AT_byte_size, Unsigned;
    bit_size: usize, DW_AT_bit_size, Unsigned;
    data_bit_offset: usize, DW_AT_data_bit_offset, Unsigned;
    // This can be exprloc in case of virtual inheritance. Not supported yet.
    data_member_location: usize, DW_AT_data_member_location, Unsigned;
    const_value_usize: usize, DW_AT_const_value, MaybeSigned;
    const_value_slice: &'static [u8], DW_AT_const_value, Slice;
    external: bool, DW_AT_external, Flag;
    artificial: bool, DW_AT_artificial, Flag;
}}

dwarf_struct!{ VariantPartAttributes {
    discr: usize, DW_AT_discr, DebugInfoOffset;
}}

dwarf_struct!{ VariantAttributes {
    discr_value: usize, DW_AT_discr_value, MaybeSigned;
    discr_list: &'static [u8], DW_AT_discr_list, Slice;
}}

dwarf_struct!{ SubrangeTypeAttributes {
    byte_stride: usize, DW_AT_byte_stride, Unsigned;
    bit_stride: usize, DW_AT_bit_stride, Unsigned;
    count: usize, DW_AT_count, Unsigned;
    count_expr: &'static [u8], DW_AT_count, Expression;
    lower_bound: usize, DW_AT_lower_bound, MaybeSigned;
    upper_bound: usize, DW_AT_upper_bound, MaybeSigned;
}}

dwarf_struct!{ LexicalBlockAttributes {
    ranges: DwarfRanges, DW_AT_ranges, Ranges;
}}

dwarf_struct!{ InlinedSubroutineAttributes {
    ranges: DwarfRanges, DW_AT_ranges, Ranges;
    call: DwarfCodeLocation, DW_AT_call_file, CodeLocation;
    abstract_origin: usize, DW_AT_abstract_origin, DebugInfoOffset;
}}

dwarf_struct!{ TemplateTypeParameterAttributes {
    name: &'static str, DW_AT_name, String;
    type_: /*DieOffset*/ usize, DW_AT_type, DebugInfoOffset;
}}

dwarf_struct!{ TemplateValueParameterAttributes {
    decl: DwarfCodeLocation, DW_AT_decl_file, CodeLocation;
    name: &'static str, DW_AT_name, String;
    type_: /*DieOffset*/ usize, DW_AT_type, DebugInfoOffset;
    const_value_usize: usize, DW_AT_const_value, MaybeSigned;
    const_value_slice: &'static [u8], DW_AT_const_value, Slice;
}}

enum DwarfVariableLocation {
    Expression(&'static [u8]),
    LocationListsOffset(usize),
    ConstUsize(usize),
    ConstSlice(&'static [u8]),
}


impl<'a> DwarfLoader<'a> {
    fn new(loader: &'a SymbolsLoader, shard: &'a mut SymbolsLoaderShard, unit_idx: usize) -> Result<Self> {
        let unit = &loader.sym.units[unit_idx];
        let section_slice = *loader.sym.dwarf.debug_info.reader();
        Ok(Self {loader, section_slice, shard_idx: unit.shard_idx, shard, unit, scope_name: String::new(), temp: LoaderTempStorage::default(), main_stack: FastStack::default(), scope_stack: FastStack::default(), function_stack: FastStack::default(), subfunction_stack: FastStack::default(), type_stack: FastStack::default(), ranges_stack: FastStack::default()})
    }

    fn append_namespace_to_scope_name(&mut self, s: &str, linkable: bool) {
        let top = self.main_stack.top_mut();
        if top.flags.contains(StackFlags::HAS_SCOPE) {
            self.scope_stack.top_mut().scope_name_is_linkable &= linkable;
        } else {
            let was_linkable = self.scope_stack.top().scope_name_is_linkable;
            *self.scope_stack.push_uninit(&mut top.flags) = ScopeStackEntry {scope_name_len: self.scope_name.len(), scope_name_is_linkable: was_linkable && linkable};
        }
        if !self.scope_name.is_empty() {
            self.scope_name.push_str("::");
        }
        self.scope_name.push_str(s);
    }

    fn parse_line_info(shard: &mut SymbolsLoaderShard, loader: &SymbolsLoader, unit: &DwarfUnit, loc: &DwarfCodeLocation) -> LineInfo {
        let Some(&file) = unit.file_idx_remap.get(loc.file) else {return LineInfo::invalid()};
        match LineInfo::new(0, Some(file), loc.line, loc.column, LineFlags::empty()) {
            Ok(x) => x,
            Err(e) => {
                if shard.warn.check(line!()) { eprintln!("warning: {}", e); }
                LineInfo::invalid()
            }
        }
    }

    fn attr_locations_offset(dwarf: &Dwarf<DwarfSlice>, unit: &Unit<DwarfSlice>, attr: AttributeValue<DwarfSlice>) -> Result<Option<LocationListsOffset<usize>>> {
        match attr {
            AttributeValue::LocationListsRef(offset) => Ok(Some(offset)),
            AttributeValue::DebugLocListsIndex(index) => Ok(Some(dwarf.locations_offset(unit, index)?)),
            _ => if let Some(offset) = attr.offset_value() {
                Ok(Some(LocationListsOffset(offset)))
            } else {
                Ok(None)
            }
        }
    }

    fn add_variable_locations(&mut self, loc: DwarfVariableLocation, linkage_name: &'static str, mut var: Variable, offset: DieOffset) -> Result<()> {
        let stack_flags = self.main_stack.top().flags;
        let subfunction_top = self.subfunction_stack.top_mut();
        let mut custom_ranges = false;
        let mut is_global = false;

        match loc {
            DwarfVariableLocation::Expression(ex) => var.location = PackedVariableLocation::expr(Expression(DwarfSlice::new(ex))),
            DwarfVariableLocation::LocationListsOffset(off) => {
                // Different locations for different address ranges. Add multiple local variables.
                // Or it's a static variable inside a function - then the range from location list is much wider
                // than the containing function (e.g. whole .text section).
                let mut locs_iter = self.loader.sym.dwarf.locations(&self.unit.unit, LocationListsOffset(off))?;
                custom_ranges = true;
                while let Some(entry) = locs_iter.next()? {
                    var.location = PackedVariableLocation::expr(entry.data);
                    is_global = false;
                    if stack_flags.contains(StackFlags::IS_FUNCTION_SCOPE) {
                        // We're inside a function. Guess whether it's a local or a static variable.
                        // (The `r.end + 1` is because I've seen ranges stick out like that in practice, idk why. Not sure if it was specifically variable vs function ranges, or some other kind of ranges of nested DIEs, I didn't check.)
                        // TODO: This is sometimes not enough: I've seen local variables being detected as global. Maybe also look at the DWARF expression: if it uses general-purpose registers, it's probably a local variable.
                        let mut is_local = var.flags().intersects(VariableFlags::FRAME_BASE | VariableFlags::PARAMETER);
                        if !is_local && stack_flags.contains(StackFlags::IS_VALID_SCOPE) {
                            let function_top = self.function_stack.top();
                            let function_pc_ranges = &self.ranges_stack.s[function_top.ranges_stack_idx].pc_ranges;
                            is_local = function_pc_ranges.iter().any(|r| r.begin <= entry.range.begin && r.end + 1 >= entry.range.end);
                        }
                        if stack_flags.contains(StackFlags::IS_VALID_SCOPE) {
                            subfunction_top.local_variables.push(var.with_range(entry.range));
                        }
                        if !is_local {
                            // Probably a static variable inside a function. Add both local variable (above) and global variable (if it's the last location list entry).
                            is_global = true;
                        }
                    } else {
                        is_global = true;
                    }
                }
            }
            DwarfVariableLocation::ConstUsize(val) => var.location = PackedVariableLocation::const_usize(val),
            DwarfVariableLocation::ConstSlice(slice) => var.location = PackedVariableLocation::const_slice(slice),
        }

        if !custom_ranges {
            if stack_flags.contains(StackFlags::IS_FUNCTION_SCOPE) {
                if stack_flags.contains(StackFlags::IS_VALID_SCOPE) {
                    for range in &self.ranges_stack.top().pc_ranges {
                        subfunction_top.local_variables.push(var.with_range(*range));
                    }
                }
            } else {
                is_global = true;
            }
        }

        if is_global {
            let mut var = var.with_range(gimli::Range {begin: 0, end: u64::MAX});
            var.add_flags(VariableFlags::GLOBAL);
            let mut unqualified_name = unsafe {var.name()};
            let mut demangled = false;
            // If name is missing, use demangled linkage_name.
            if unqualified_name.is_empty() && !linkage_name.is_empty() && self.unit.language.presumably_cpp() {
                if let Ok(symbol) = cpp_demangle::BorrowedSymbol::new_with_options(linkage_name.as_bytes(), &cpp_demangle::ParseOptions::default().recursion_limit(1000)) {
                    let options = cpp_demangle::DemangleOptions::new().recursion_limit(1000).no_return_type().no_params().hide_expression_literal_types();
                    if let Ok(r) = symbol.demangle(&options) {
                        var.set_name(self.shard.temp_global_var_arena.add_str(&r));
                        if stack_flags.contains(StackFlags::IS_TYPE_SCOPE | StackFlags::IS_VALID_SCOPE) {
                            let i = r.rfind(':').map_or(0, |i| i + 1);
                            unqualified_name = self.shard.types.temp_types.misc_arena.add_str(&r[i..]);
                        }
                        demangled = true;
                    }
                }
            }
            // If name is not missing, prepend it with parent namespace names.
            if !demangled {
                self.append_namespace_to_scope_name(unqualified_name, false);
                var.set_name(self.shard.temp_global_var_arena.add_str(&self.scope_name));
            }
            let name = unsafe {var.name()};
            let ptr = self.shard.sym.global_variables.add_mut(var) as *mut Variable;

            // Send the name to shard hash(name)%num_shards for deduplication.
            let hash = hash(name);
            let target_shard = hash % self.loader.shards.len();
            unsafe {(*(*self.loader.send_global_variable_names[self.shard_idx].get())[target_shard].get()).push(GlobalVariableNameMessage {name, ptr})};

            if stack_flags.contains(StackFlags::IS_TYPE_SCOPE | StackFlags::IS_VALID_SCOPE) {
                // TODO: This doesn't cover the case when the declaration is separate from definition. The definition has location, the declaration has parent type, we have to somehow join the two.
                self.type_stack.top_mut().nested_names.push((unqualified_name, NestedName::Variable(ptr)));
            }
        }

        Ok(())
    }

    // `fields` must use the same field numbering as CommonAttributes.
    fn chase_origin_pointers(shard: &mut SymbolsLoaderShard, loader: &SymbolsLoader, initial_attribute_context: &AttributeContext, mut specification_or_origin: DwarfReference, name: &mut &'static str, linkage_name: &mut &'static str, type_: &mut usize, decl: &mut DwarfCodeLocation, fields: &mut u32) -> Result<()> {
        let mut attribute_context = Cow::Borrowed(initial_attribute_context);
        while *fields & DwarfReference::HAS_SPECIFICATION_OR_ABSTRACT_ORIGIN != 0 {
            let next_offset = if *fields & DwarfReference::GLOBAL != 0 {
                let unit_idx = loader.sym.units.partition_point(|u| u.offset.0 <= specification_or_origin.offset);
                let u = &loader.sym.units[unit_idx.saturating_sub(1)];
                let Some(off) = DebugInfoOffset(specification_or_origin.offset).to_unit_offset(&u.unit.header) else {return err!(Dwarf, "specification/abstract_origin entry offset out of unit bounds")};
                attribute_context.to_mut().switch_unit(u);
                off
            } else {
                UnitOffset(specification_or_origin.offset)
            };

            let mut attrs = CommonAttributes::default();
            let mut cursor = SliceReader::new(attribute_context.unit.unit.header.range_from(next_offset..)?.slice());
            let Some(abbrev) = cursor.read_abbreviation(&attribute_context)? else {return err!(Dwarf, "specification/abstract_origin points to null entry")};
            unsafe {cursor.read_attributes(abbrev, /*which_layout*/ 1, &attribute_context, &raw mut attrs as *mut u8)?};

            let added_fields = attrs.fields & !*fields;
            if added_fields & CommonAttributes::decl != 0 {*decl = attrs.decl}
            if added_fields & CommonAttributes::name != 0 {*name = attrs.name}
            if added_fields & CommonAttributes::linkage_name != 0 {*linkage_name = attrs.linkage_name}
            if added_fields & CommonAttributes::type_ != 0 {*type_ = attrs.type_}

            let mask = DwarfReference::HAS_SPECIFICATION_OR_ABSTRACT_ORIGIN | DwarfReference::GLOBAL;
            *fields = ((*fields | attrs.fields) & !mask) | (attrs.fields & mask);
            specification_or_origin = attrs.specification_or_abstract_origin;
        }
        Ok(())
    }

    #[inline]
    fn fixup_subfunction_call_line(shard: &SymbolsLoaderShard, line: &mut LineInfo, addr: usize) {
        if line.line() == 0 && line.file_idx().is_some() {
            // Sometimes DW_TAG_inlined_subroutine has DW_AT_call_line == 0. Idk whether this is intended and what it's supposed to mean.
            // In the cases I've seen, there was a good line number (line of the inlined call) in .debug_line for a slightly lower address. Let's use that.
            // There are few such subfunctions, so performance is not very important here.

            // Look for address *strictly* less than the inlined function's range start.
            // The line at range start is usually the first line of code *inside* the inlined function, not at the call site.
            // (But also: .debug_line sometimes has multiple line numbers for the same address, and sometimes the earlier ones are from the inlined function's call site and the later ones are from inside the inlined function.
            //  Maybe the idea is that the debugger would somehow figure out which is which? Maybe we should preserve some information about such duplicates in parse_debug_line() and make use of it here somehow?)
            let i = shard.sym.addr_to_line[..shard.addr_to_line_len_after_debug_line].partition_point(|l| l.addr() < addr);
            if i > 0 {
                let prev = shard.sym.addr_to_line[i - 1];
                if prev.file_idx() == line.file_idx() && prev.line() != 0 {
                    line.set_line_and_column_from(prev);
                }
            }
        }
    }

    fn load(&mut self) -> Result<()> {
        {
            let start_offset = self.unit.unit.header.offset().as_debug_info_offset().unwrap();
            self.shard.types.set_unit(start_offset, DebugInfoOffset(start_offset.0 + self.unit.unit.header.length_including_self()));
        }

        // Fake sentinel values to avoid checking for empty stacks everywhere.
        {
            let mut _f = StackFlags::empty();
            *self.main_stack.push_uninit(&mut _f) = MainStackEntry {tag: DW_TAG_null, flags: StackFlags::IS_VALID_SCOPE};
            let f = &mut self.main_stack.top_mut().flags;
            *self.scope_stack.push_uninit(f) = ScopeStackEntry {scope_name_len: 0, scope_name_is_linkable: true};
            *self.ranges_stack.push_uninit(f) = RangesStackEntry::default();
            *self.subfunction_stack.push_uninit(f) = SubfunctionStackEntry {subfunction_idx: u32::MAX, ..Default::default()};
        }

        // Iterate over DIEs in depth-first order.
        let mut cursor = SliceReader::new(self.unit.unit.header.range_from(UnitOffset(self.unit.unit.header.header_size())..)?.slice());
        let attribute_context = AttributeContext {unit: self.unit, dwarf: &self.loader.sym.dwarf, shared: &self.loader.abbreviations_shared};
        let encoding = self.unit.unit.encoding();
        let mut prev_has_children = true;
        let mut skip_subtree = usize::MAX;
        loop {
            let offset = DebugInfoOffset(cursor.offset_from(self.section_slice.slice()));

            // Pop from the stack if needed.
            if !prev_has_children {
                // Expected stack contents: fake root, DW_TAG_compile_unit, ...
                if self.main_stack.len < 2 {
                    if cursor.as_slice().iter().find(|c| **c != 0u8).is_some() {
                        return err!(Dwarf, "tree stack underflow");
                    } else {
                        // Zig compiler sometimes outputs extra null bytes at the end of a unit: https://github.com/ziglang/zig/issues/22949
                        // gdb and llvm-dwarfdump silently ignore them for some reason, so let's do the same.
                        if self.shard.warn.check(line!()) { eprintln!("warning: unexpected null bytes at the end of unit @0x{:x}", offset.0 - 1); }
                        return Ok(());
                    }
                }
                let top = self.main_stack.pop();

                if skip_subtree == usize::MAX {
                    let flags = top.flags;
                    if flags.intersects(StackFlags::HAS_ANYTHING) {
                        if flags.contains(StackFlags::HAS_SCOPE) {
                            let scope_top = self.scope_stack.pop();
                            self.scope_name.truncate(scope_top.scope_name_len);
                        }
                        if flags.contains(StackFlags::HAS_RANGES) {
                            self.ranges_stack.pop();
                        }
                        if flags.contains(StackFlags::HAS_SUBFUNCTION) {
                            self.finish_subfunction();
                        }
                        if flags.contains(StackFlags::HAS_FUNCTION) {
                            self.finish_function();
                        }
                        if flags.contains(StackFlags::HAS_TYPE) {
                            self.finish_type();
                        }
                        if flags.contains(StackFlags::HAS_VARIANT) {
                            self.type_stack.top_mut().variant_field_flags = FieldFlags::empty();
                        }
                    }
                } else if self.main_stack.len < skip_subtree {
                    skip_subtree = usize::MAX;
                }
            }

            // Check if we ran out of bytes.
            if cursor.is_empty() {
                if self.main_stack.len != 1 { // expected stack contents: fake root
                    return err!(Dwarf, "tree ended early @0x{:x}", offset.0);
                }
                return Ok(());
            }

            // Read next DIE.
            let abbrev = cursor.read_abbreviation(&attribute_context)?;
            prev_has_children = abbrev.is_some_and(|e| e.has_children);

            let abbrev = match abbrev {
                Some(a) => a,
                None => continue,
            };

            let inherited_flags = self.main_stack.top().flags & StackFlags::IS_ANY_SCOPE;
            let mut _f = StackFlags::empty();
            let top = self.main_stack.push_uninit(&mut _f);
            *top = MainStackEntry {tag: abbrev.tag, flags: inherited_flags};

            if skip_subtree != usize::MAX {
                cursor.skip_attributes(abbrev, &attribute_context)?;
                continue;
            }

            // Each case here has to read/skip all attributes from `cursor`.
            match abbrev.tag {
                DW_TAG_compile_unit | DW_TAG_partial_unit | DW_TAG_type_unit => {
                    cursor.skip_attributes(abbrev, &attribute_context)?;
                    let ranges_top = self.ranges_stack.push_uninit(&mut self.main_stack.top_mut().flags);
                    parse_dwarf_ranges(&self.loader.sym.dwarf, &self.unit.unit, &self.unit.ranges, self.unit.fields, offset, self.loader.sym.code_addr_range.start, &mut ranges_top.pc_ranges, /*out_entry_pc*/ &mut 0, &mut self.shard.warn)?;
                    self.main_stack.top_mut().flags.remove(StackFlags::IS_FUNCTION_SCOPE | StackFlags::IS_TYPE_SCOPE); // this shouldn't do anything since this tag is always root, but just in case
                }

                // This tag means that the debug info is split into a separate file using DWARF's complicated mechanism for that.
                // Not sure if this is worth supporting, since simpler ways of splitting are available: debuglink, or just providing an unstripped executable on the side.
                DW_TAG_skeleton_unit => return err!(NotImplemented, "skeleton units not supported (too spooky)"),

                // Namespaces.
                DW_TAG_namespace => {
                    let mut attrs = NamespaceAttributes::default();
                    unsafe {cursor.read_attributes(abbrev, /*which_layout*/ 0, &attribute_context, &raw mut attrs as *mut u8)}?;
                    if attrs.fields & NamespaceAttributes::name != 0 {
                        self.append_namespace_to_scope_name(attrs.name, true);
                    } else {
                        self.append_namespace_to_scope_name("_", false);
                    }
                }

                // Variables.
                DW_TAG_variable | DW_TAG_formal_parameter => {
                    // Applicable attributes:
                    // Useful: DECL, name, linkage_name, location, type, declaration, specification, const_value
                    // Other: artificial, accessibility, alignment, const_expr, endianity, external, segment, start_scope, visibility
                    // Other (for parameters): default_value, is_optional, variable_parameter
                    let mut attrs = VariableAttributes::default();
                    const _: () = assert!(VariableAttributes::name == CommonAttributes::name && VariableAttributes::linkage_name == CommonAttributes::linkage_name && VariableAttributes::decl == CommonAttributes::decl && VariableAttributes::type_ == CommonAttributes::type_);
                    unsafe {cursor.read_attributes(abbrev, /*which_layout*/ 0, &attribute_context, &raw mut attrs as *mut u8)}?;
                    if attrs.fields & (VariableAttributes::location_expr | VariableAttributes::location_list | VariableAttributes::const_value_usize | VariableAttributes::const_value_slice) != 0 {
                        Self::chase_origin_pointers(&mut self.shard, &self.loader, &attribute_context, attrs.specification_or_abstract_origin, &mut attrs.name, &mut attrs.linkage_name, &mut attrs.type_, &mut attrs.decl, &mut attrs.fields)?;
                        let decl = if attrs.fields & VariableAttributes::decl != 0 {Self::parse_line_info(&mut self.shard, &self.loader, self.unit, &attrs.decl)} else {LineInfo::invalid()};
                        let var_flags = if abbrev.tag == DW_TAG_variable { VariableFlags::empty() } else { VariableFlags::PARAMETER };
                        let type_ = if attrs.fields & VariableAttributes::type_ != 0 {attrs.type_ as *const TypeInfo} else {self.loader.types.builtin_types.unknown};
                        let var = Variable::new(attrs.name, type_, offset, decl, var_flags);
                        let loc = if attrs.fields & VariableAttributes::location_expr != 0 {
                            DwarfVariableLocation::Expression(attrs.location_expr)
                        } else if attrs.fields & VariableAttributes::location_list != 0 {
                            DwarfVariableLocation::LocationListsOffset(attrs.location_list)
                        } else if attrs.fields & VariableAttributes::const_value_usize != 0 {
                            DwarfVariableLocation::ConstUsize(attrs.const_value_usize)
                        } else if attrs.fields & VariableAttributes::const_value_slice != 0 {
                            DwarfVariableLocation::ConstSlice(attrs.const_value_slice)
                        } else {
                            panic!("huh");
                        };
                        self.add_variable_locations(loc, attrs.linkage_name, var, offset)?;
                    }
                }

                // Varargs.
                DW_TAG_unspecified_parameters | DW_TAG_GNU_formal_parameter_pack => {
                    skip_subtree = self.main_stack.len;
                    cursor.skip_attributes(abbrev, &attribute_context)?;
                }

                // Call sites (seem to be very incomplete, presumed useless).
                DW_TAG_GNU_call_site | DW_TAG_call_site | DW_TAG_GNU_call_site_parameter | DW_TAG_call_site_parameter => {
                    skip_subtree = self.main_stack.len;
                    cursor.skip_attributes(abbrev, &attribute_context)?;
                }

                // Functions.
                DW_TAG_subprogram => {
                    // Applicable attributes:
                    // Useful: declaration, specification, frame_base, entry_pc, low_pc, high_pc, ranges, name, linkage_name, main_subprogram, object_pointer, return_addr, type, inline
                    // Other: artificial, calling_convention, start_scope (haven't seen it in practice), trampoline, virtuality, vtable_elem_location
                    // Other: accessibility, address_class, alignment, defaulted, deleted, elemental, pure, explicit, external, noreturn, prototyped, recursive, reference, rvalue_reference, segment, static_link, visibility
                    let mut attrs = SubprogramAttributes::default();
                    const _: () = assert!(SubprogramAttributes::name == CommonAttributes::name && SubprogramAttributes::linkage_name == CommonAttributes::linkage_name && SubprogramAttributes::decl == CommonAttributes::decl && SubprogramAttributes::type_ == CommonAttributes::type_);
                    unsafe {cursor.read_attributes(abbrev, /*which_layout*/ 0, &attribute_context, &raw mut attrs as *mut u8)}?;

                    // The exact value of this attribute seems unreliable, let's ignore it and only check that the attribute is present.
                    // I've seen it say DW_INL_declared_not_inlined when the function is actually inlined,
                    // and there are DW_TAG_inlined_subroutine-s with DW_AT_abstract_origin pointing to this exact DIE.
                    // (That was g++. Clang seems to only ever use DW_INL_inlined for this value.)
                    let is_inlined = attrs.inline != 0;

                    let ranges_stack_idx = self.ranges_stack.len;
                    let ranges_top = self.ranges_stack.push_uninit(&mut self.main_stack.top_mut().flags);
                    let mut entry_pc = 0usize;
                    parse_dwarf_ranges(&self.loader.sym.dwarf, &self.unit.unit, &attrs.ranges, attrs.fields, offset, self.loader.sym.code_addr_range.start, &mut ranges_top.pc_ranges, &mut entry_pc, &mut self.shard.warn)?;
                    self.main_stack.top_mut().flags.remove(StackFlags::IS_ANY_SCOPE);
                    self.main_stack.top_mut().flags.insert(StackFlags::IS_FUNCTION_SCOPE);

                    if !ranges_top.pc_ranges.is_empty() || is_inlined {
                        let function_top = self.function_stack.push_uninit(&mut self.main_stack.top_mut().flags);
                        function_top.reset(ranges_stack_idx);

                        // Chase the specification/origin pointers to reach the function name (for function declarations and inlining stuff).
                        // Functions can be missing one of the two names (linkage name or regular name), but not both (in the binaries I looked at).
                        Self::chase_origin_pointers(&mut self.shard, &self.loader, &attribute_context, attrs.specification_or_abstract_origin, &mut attrs.name, &mut attrs.linkage_name, &mut attrs.type_, &mut attrs.decl, &mut attrs.fields)?;
                        let decl = if attrs.fields & VariableAttributes::decl != 0 {Self::parse_line_info(&mut self.shard, &self.loader, self.unit, &attrs.decl)} else {LineInfo::invalid()};

                        let name_ref = if !attrs.linkage_name.is_empty() {
                            // Don't demangle it here because demangling is very slow for some reason.
                            attrs.linkage_name
                        } else {
                            // Usually we have DW_AT_linkage_name (fully qualified and mangled), but if it's missing we use namespace + DW_AT_name.
                            let mut out = self.shard.sym.misc_arena.write();
                            write!(out, "{}{}", self.scope_name, if self.scope_name.is_empty() {""} else {"::"})?;
                            if !attrs.name.is_empty() {
                                write!(out, "{}", attrs.name)?;
                            } else {
                                let mut found = false;
                                if let Some(file_idx) = decl.file_idx() {
                                    if let Some(file) = self.loader.sym.files.get(file_idx) {
                                        write!(out, "[function at {}:{}]", Path::new(file.filename.file_name().unwrap_or_else(|| OsStr::new("?"))).display(), decl.line()).unwrap();
                                        found = true;
                                    }
                                }
                                if !found {
                                    write!(out, "[function at DIE 0x{:x}]", offset.0)?;
                                }
                            }
                            out.finish_str()
                        };

                        // Function may have multiple ranges. In practice this happens because of compiler optimizations, e.g. splitting a function into hot and cold part.
                        // These ranges may also be present in .symtab with names like add_path.constprop.0.isra.0.cold , where "constprop", "isra", and "cold" are
                        // the transformations that the compiler did to arrive at these ranges.
                        // Do multi-ranges also appear on C++ coroutines or Rust async functions? No, they produce multiple functions instead.

                        function_top.function = self.shard.functions.len();
                        let mut f = FunctionInfo {addr: FunctionAddr(0), prev_addr: FunctionAddr(0), entry_addr: entry_pc, die: offset, mangled_name: name_ref.as_ptr(), mangled_name_len: name_ref.len() as u32, shard_idx: self.shard_idx as u16, flags: FunctionFlags::empty(), language: self.unit.language, subfunction_levels: 0..0};
                        if is_inlined {
                            f.flags.insert(FunctionFlags::INLINED);
                        }
                        if ranges_top.pc_ranges.is_empty() {
                            // Inline-only function. Don't create a subfunction and don't add IS_VALID_SCOPE flag.
                            f.addr = FunctionAddr::inline(f.die);
                            f.prev_addr = f.addr;
                            self.shard.functions.push(f);
                        } else {
                            self.main_stack.top_mut().flags.insert(StackFlags::IS_VALID_SCOPE);
                            ranges_top.pc_ranges.sort_unstable_by_key(|r| r.begin);
                            let sf_idx = 0u32;
                            function_top.subfunctions.push((Subfunction {callee_idx: offset.0, local_variables: Subfunction::pack_range(0..0), call_line: decl, addr_range: 0..0, identity: sf_idx}, u32::MAX));
                            self.subfunction_stack.push_uninit(&mut self.main_stack.top_mut().flags).reset(sf_idx, /*subfunction_level*/ 0);
                            for (i, range) in ranges_top.pc_ranges.iter().enumerate() {
                                let mut f = f.clone();
                                f.addr = FunctionAddr::new(range.begin as usize, &mut self.shard.warn);
                                f.prev_addr = FunctionAddr::new(ranges_top.pc_ranges[(i + ranges_top.pc_ranges.len() - 1) % ranges_top.pc_ranges.len()].begin as usize, &mut self.shard.warn);
                                self.shard.functions.push(f);

                                function_top.subfunction_events.push(SubfunctionEvent {addr: range.begin as usize, subfunction_idx: sf_idx, signed_level: 1});
                                function_top.subfunction_events.push(SubfunctionEvent {addr: range.end as usize, subfunction_idx: sf_idx, signed_level: -1});

                                // Functions often overlap, especially with .symtab functions, idk why. So don't add function end markers.
                                self.shard.max_function_end = self.shard.max_function_end.max(range.end as usize);
                            }

                            // (Suboptimal to slow down loading by comparing each function's name to "main", especially if it's cache misses because names live at random memory addresses e.g. in .debug_str.
                            //  The hope is that cache misses is mostly avoided by checking string length before checking contents, since very few functions have 4-character names.)
                            let is_main_function =
                                attrs.main_subprogram ||
                                // Often compilers don't emit DW_AT_main_subprogram and we have to guess by name.
                                attrs.linkage_name == "main" ||
                                // Zig compiler emits debug info for main function like this:
                                //  * no DW_AT_main_subprogram (https://github.com/ziglang/zig/issues/23896)
                                //  * DW_AT_name = "main"
                                //  * DW_AT_linkage_name = "<module_name>.main"
                                // (There may also be functions named "main" nested e.g. inside structs, which are nearly indistinguishable from the main function;
                                //  we don't try to distinguish them, it's ok to add all their addresses as MainFunction.)
                                (attrs.name == "main" && (attrs.linkage_name.is_empty() || attrs.linkage_name.ends_with(".main")));
                            if is_main_function {
                                self.shard.points_of_interest.entry(PointOfInterest::MainFunction).or_default().push(entry_pc);
                            }

                            if self.unit.language == LanguageFamily::Rust && attrs.name == "begin_panic_handler" {
                                self.shard.points_of_interest.entry(PointOfInterest::Panic).or_default().push(entry_pc);
                            }
                        }

                        if attrs.fields & (SubprogramAttributes::frame_base_expr | SubprogramAttributes::frame_base_list) != 0 {
                            let var = Variable::new("#frame_base", self.loader.types.builtin_types.void_pointer, offset, LineInfo::invalid(), VariableFlags::FRAME_BASE);
                            let loc = if attrs.fields & SubprogramAttributes::frame_base_expr != 0 {
                                DwarfVariableLocation::Expression(attrs.frame_base_expr)
                            } else if attrs.fields & SubprogramAttributes::frame_base_list != 0 {
                                DwarfVariableLocation::LocationListsOffset(attrs.frame_base_list)
                            } else {
                                panic!("huh");
                            };
                            self.add_variable_locations(loc, /*linkage_name*/ "", var, offset)?;
                        }
                    }

                    // Would be nice to use the actual function name instead of "_", but there are difficulties:
                    //  * DW_AT_name may be missing and only DW_AT_linkage_name present,
                    //  * DW_AT_linkage_name is fully qualified, so should override previous scope name rather than be appended to it,
                    //  * demangling DW_AT_linkage_name is slow, so it should only be done if the function actually contains nested types,
                    //  * function may be overloaded, so we'd need to include some description of its parameters,
                    //  * but if the function is not overloaded, it's better to omit the parameters.
                    self.append_namespace_to_scope_name("_", false);
                }

                DW_TAG_enumeration_type if self.main_stack.top().tag == DW_TAG_array_type => {
                    // Haven't seen these in C++ or Rust.
                    if self.shard.warn.check(line!()) { eprintln!("warning: enum-valued array indices are not supported (have one @0x{:x})", offset.0); }
                    cursor.skip_attributes(abbrev, &attribute_context)?;
                }

                // Types.
                DW_TAG_base_type | DW_TAG_unspecified_type | DW_TAG_structure_type | DW_TAG_class_type | DW_TAG_union_type | DW_TAG_enumeration_type | DW_TAG_pointer_type | DW_TAG_reference_type | DW_TAG_rvalue_reference_type | DW_TAG_array_type | DW_TAG_const_type | DW_TAG_restrict_type | DW_TAG_volatile_type | DW_TAG_atomic_type | DW_TAG_typedef | DW_TAG_subroutine_type | DW_TAG_ptr_to_member_type => {
                    // Applicable attributes (DW_AT_*) (DECL means decl_file, decl_line, decl_column):
                    // Useful: DECL, name, bit_size, byte_size, declaration, type, containing_type, signature, alignment
                    // For base types: encoding
                    // For arrays and enums used as array index: bit_stride, byte_stride, ordering, rank
                    // Possible in theory, but I haven't seen these on types: specification, abstract_origin
                    // Other: data_bit_offset, data_location
                    // Other: binary_scale, decimal_scale, decimal_sign, digit_count, picture_string, small
                    // Other: allocated, associated, enum_class, accessibility, visibility, start_scope, export_symbols, endianity, calling_convention, address_class
                    let mut attrs = TypeAttributes::default();
                    unsafe {cursor.read_attributes(abbrev, /*which_layout*/ 0, &attribute_context, &raw mut attrs as *mut u8)}?;
                    let mut is_alias = false;
                    let t = match abbrev.tag {
                        DW_TAG_base_type => Type::Primitive(PrimitiveFlags::empty()),
                        DW_TAG_unspecified_type => Type::Primitive(PrimitiveFlags::UNSPECIFIED),
                        DW_TAG_structure_type | DW_TAG_class_type | DW_TAG_union_type => Type::Struct(StructType::default()),
                        DW_TAG_enumeration_type => Type::Enum(EnumType {enumerands: &[], type_: self.loader.types.builtin_types.unknown}),
                        DW_TAG_pointer_type | DW_TAG_reference_type | DW_TAG_rvalue_reference_type => Type::Pointer(
                            PointerType {flags: if abbrev.tag == DW_TAG_pointer_type {PointerFlags::empty()} else {PointerFlags::REFERENCE},
                                         // pointer without DW_AT_type is a void*
                                         type_: self.loader.types.builtin_types.void}),
                        DW_TAG_array_type => Type::Array(ArrayType {flags: ArrayFlags::empty(), type_: self.loader.types.builtin_types.unknown, stride: 0, len: 0}),
                        DW_TAG_const_type | DW_TAG_restrict_type | DW_TAG_volatile_type | DW_TAG_atomic_type | DW_TAG_typedef => {
                            is_alias = true;
                            Type::Pointer(PointerType {flags: PointerFlags::empty(), type_: self.loader.types.builtin_types.unknown})
                        }
                        DW_TAG_subroutine_type => Type::Function,
                        DW_TAG_ptr_to_member_type => Type::PointerToMember(PointerToMemberType {type_: self.loader.types.builtin_types.void, containing_type: self.loader.types.builtin_types.unknown}),
                        _ => panic!("huh?") };
                    let mut info = TypeInfo {die: offset, binary_id: self.loader.binary_id, line: LineInfo::invalid(), t, language: self.unit.language, ..Default::default()};
                    let mut is_complex_float = false;

                    if attrs.fields & TypeAttributes::decl != 0 {
                        info.line = Self::parse_line_info(&mut self.shard, &self.loader, self.unit, &attrs.decl);
                    }

                    if attrs.name.is_empty() {
                        self.append_namespace_to_scope_name("_", false);
                    } else {
                        self.append_namespace_to_scope_name(attrs.name, true);
                        info.name = self.shard.types.temp_types.unsorted_type_names.add_str(&self.scope_name, 0);
                        if self.scope_stack.top().scope_name_is_linkable {
                            info.flags.insert(TypeFlags::LINKABLE_NAME);
                        }
                    }

                    if attrs.fields & TypeAttributes::byte_size != 0 {
                        info.size = attrs.byte_size;
                        info.flags.insert(TypeFlags::SIZE_KNOWN);
                    } else if attrs.fields & TypeAttributes::bit_size != 0 {
                        if attrs.bit_size & 7 != 0 {
                            if self.shard.warn.check(line!()) { eprintln!("warning: DW_AT_bit_size = {} on {} is not supported", attrs.bit_size, abbrev.tag); }
                            info.flags.insert(TypeFlags::UNSUPPORTED);
                        }
                    }

                    if attrs.fields & (TypeAttributes::byte_stride | TypeAttributes::bit_stride) != 0 { 
                        match &mut info.t {
                            Type::Array(a) => {
                                if attrs.fields & TypeAttributes::byte_stride != 0 {
                                    a.stride = attrs.byte_stride;
                                } else if attrs.bit_stride % 8 != 0 {
                                    if self.shard.warn.check(line!()) { eprintln!("warning: bit-packed arrays are not supported (have DW_AT_bit_stride @0x{:x})", offset.0); }
                                } else {
                                    a.stride = attrs.bit_stride / 8;
                                }
                            }
                            _ => if self.shard.warn.check(line!()) { eprintln!("warning: DW_AT_{{byte,bit}}_stride on {} is not supported", abbrev.tag); }
                        }
                    }
                
                    if attrs.declaration {
                        info.flags.insert(TypeFlags::DECLARATION);
                    }

                    if attrs.fields & DwarfReference::HAS_SPECIFICATION_OR_ABSTRACT_ORIGIN != 0 {
                        if self.shard.warn.check(line!()) { eprintln!("warning: DW_AT_specification/DW_AT_abstract_origin on {} is not supported (@0x{:x})", abbrev.tag, offset.0); }
                    }

                    if attrs.fields & TypeAttributes::type_ != 0 {
                        let type_ = attrs.type_ as *const TypeInfo;
                        match &mut info.t {
                            Type::Enum(e) => e.type_ = type_,
                            Type::Pointer(p) => p.type_ = type_,
                            Type::PointerToMember(p) => p.type_ = type_,
                            Type::Array(a) => a.type_ = type_,
                            Type::Function => (),
                            _ => if self.shard.warn.check(line!()) { eprintln!("warning: DW_AT_type on {} is not supported (@0x{:x})", abbrev.tag, offset.0); }
                        }
                    }

                    if attrs.fields & TypeAttributes::containing_type != 0 {
                        match &mut info.t {
                            Type::PointerToMember(p) => p.containing_type = attrs.containing_type as *const TypeInfo,
                            _ => (),
                        }
                    } else if let Type::PointerToMember(p) = &info.t {
                        if self.shard.warn.check(line!()) { eprintln!("warning: DW_AT_ptr_to_member_type without DW_AT_containing_type (@0x{:x})", offset.0); }
                    }

                    if attrs.fields & TypeAttributes::encoding != 0 {
                        match &mut info.t {
                            Type::Primitive(p) => match DwAte(attrs.encoding as u8) {
                                // Why did DW eat all these things? Stop it, DW! Bad dog!
                                DW_ATE_address => (),
                                DW_ATE_boolean => p.insert(PrimitiveFlags::BOOL),
                                DW_ATE_imaginary_float | DW_ATE_float => p.insert(PrimitiveFlags::FLOAT),
                                DW_ATE_signed => p.insert(PrimitiveFlags::SIGNED),
                                DW_ATE_signed_char => p.insert(PrimitiveFlags::SIGNED | PrimitiveFlags::CHAR | if self.unit.language.presumably_cpp() {PrimitiveFlags::AMBIGUOUS_CHAR} else {PrimitiveFlags::empty()}),
                                DW_ATE_unsigned => (),
                                DW_ATE_unsigned_char => p.insert(PrimitiveFlags::CHAR),
                                DW_ATE_UTF | DW_ATE_UCS | DW_ATE_ASCII => p.insert(PrimitiveFlags::CHAR | if self.unit.language.presumably_cpp() {PrimitiveFlags::AMBIGUOUS_CHAR} else {PrimitiveFlags::empty()}),
                                DW_ATE_complex_float => is_complex_float = true,
                                //DW_ATE_packed_decimal | DW_ATE_numeric_string | DW_ATE_edited | DW_ATE_signed_fixed | DW_ATE_unsigned_fixed | DW_ATE_decimal_float
                                _ => {
                                    if self.shard.warn.check(line!()) { eprintln!("warning: DW_AT_encoding = {} on {} is not supported", DwAte(attrs.encoding as u8), abbrev.tag); }
                                    info.flags.insert(TypeFlags::UNSUPPORTED);
                                }
                            }
                            // The spec doesn't seem to allow DW_AT_encoding on DW_TAG_enumeration_type, but it appears in most Linux standard libraries, e.g. libc.so.6
                            // In those cases, both DW_AT_encoding and DW_AT_type are present, and the former matches the encoding inside the type pointed to by the latter.
                            // So we just ignore it.
                            Type::Enum(_) => (),
                            _ => {
                                if self.shard.warn.check(line!()) { eprintln!("warning: DW_AT_encoding on {} is not supported", abbrev.tag); }
                                info.flags.insert(TypeFlags::UNSUPPORTED)
                            }
                        }
                    }

                    if is_complex_float {
                        // Treat complex float as a struct rather than primitive type.
                        let inner_size = if !info.flags.contains(TypeFlags::SIZE_KNOWN) {
                            if self.shard.warn.check(line!()) { eprintln!("warning: DW_ATE_complex_float without size @0x{:x}", offset.0); }
                            8
                        } else if info.size != 8 && info.size != 16 && info.size != 32 {
                            if self.shard.warn.check(line!()) { eprintln!("warning: DW_ATE_complex_float with unexpected size: {} @0x{:x}", info.size, offset.0); }
                            8
                        } else {
                            info.size / 2
                        };
                        let inner_type = match inner_size {
                            4 => self.loader.types.builtin_types.f32_,
                            8 => self.loader.types.builtin_types.f64_,
                            16 => self.loader.types.builtin_types.f128_,
                            _ => panic!("huh"),
                        };
                        let fields = [
                            StructField {name: "real", flags: FieldFlags::empty(), bit_offset: 0, bit_size: 0, type_: inner_type, discr_value: 0},
                            StructField {name: "imag", flags: FieldFlags::empty(), bit_offset: inner_size * 8, bit_size: 0, type_: inner_type, discr_value: 0}];
                        let fields = self.shard.types.temp_types.fields_arena.add_slice(&fields);
                        let mut struct_type = StructType::default();
                        struct_type.set_fields(fields);
                        info.t = Type::Struct(struct_type);
                    }

                    if !info.flags.contains(TypeFlags::SIZE_KNOWN) {
                        match &info.t {
                            Type::Primitive(_) | Type::Pointer(_) | Type::PointerToMember(_) => {
                                info.size = 8;
                                info.flags.insert(TypeFlags::SIZE_KNOWN);
                            }
                            _ => (),
                        }
                    }

                    if abbrev.tag == DW_TAG_base_type {
                        let type_enum = if let &Type::Primitive(flags) = &info.t {
                            match info.size {
                                8 if flags.contains(PrimitiveFlags::FLOAT) => ValueType::F64,
                                8 if flags.contains(PrimitiveFlags::SIGNED) => ValueType::I64,
                                8 => ValueType::U64,
                                4 if flags.contains(PrimitiveFlags::FLOAT) => ValueType::F32,
                                4 if flags.contains(PrimitiveFlags::SIGNED) => ValueType::I32,
                                4 => ValueType::U32,
                                2 if flags.contains(PrimitiveFlags::SIGNED) => ValueType::I16,
                                2 => ValueType::U16,
                                1 if flags.contains(PrimitiveFlags::SIGNED) => ValueType::I8,
                                1 => ValueType::U8,
                                _ => ValueType::Generic, // unexpected
                            }
                        } else {
                            ValueType::Generic // probably a 16-byte complex float, not really supported by gimli; use 8-byte Generic instead
                        };
                        debug_assert!(mem::size_of::<ValueType>() == 1);
                        self.shard.base_types.push((offset.0 as u64) << 8 | type_enum as u64);
                    }

                    let prev_type_stack_len = self.type_stack.len;
                    let ti;
                    if is_alias {
                        ti = info.t.as_pointer().unwrap().type_;
                        self.shard.types.add_alias(offset, DebugInfoOffset(ti as usize), info.name);
                    } else {
                        let t;
                        (t, ti) = self.shard.types.add_type(info);
                        assert!(t != ptr::null());
                        let top = self.main_stack.top_mut();
                        self.type_stack.push_uninit(&mut top.flags).reset(t as *mut TypeInfo);
                        top.flags.remove(StackFlags::IS_ANY_SCOPE);
                        top.flags.insert(StackFlags::IS_TYPE_SCOPE | StackFlags::IS_VALID_SCOPE);
                    }

                    if !attrs.name.is_empty() && self.main_stack.top2().flags.contains(StackFlags::IS_TYPE_SCOPE | StackFlags::IS_VALID_SCOPE) {
                        self.type_stack.s[prev_type_stack_len - 1].nested_names.push((attrs.name, NestedName::Type(ti)));
                    }
                }

                // Fields and enumerators.
                DW_TAG_inheritance | DW_TAG_member | DW_TAG_enumerator => {
                    // Applicable attributes:
                    // Useful: DECL, name, artificial, bit_size, byte_size, data_bit_offset, data_member_location, external (seems undocumented), declaration, type, const_value
                    // Other: accessibility, mutable, visibility, virtuality
                    let mut attrs = FieldAttributes::default();
                    unsafe {cursor.read_attributes(abbrev, /*which_layout*/ 0, &attribute_context, &raw mut attrs as *mut u8)}?;
                    let top = self.main_stack.top();
                    if !top.flags.contains(StackFlags::IS_TYPE_SCOPE | StackFlags::IS_VALID_SCOPE) {
                        if !top.flags.contains(StackFlags::IS_TYPE_SCOPE) {
                            if self.shard.warn.check(line!()) { eprintln!("warning: {} in {} is not supported (@0x{:x})", abbrev.tag, self.main_stack.top2().tag, offset.0); }
                        }
                    } else {
                        let type_top = self.type_stack.top_mut();
                        let type_ = type_top.type_;
                        let mut field = StructField {name: "", flags: FieldFlags::empty(), bit_offset: 0, bit_size: 0, type_: self.loader.types.builtin_types.unknown, discr_value: 0};
                        if offset == type_top.discriminant_die {
                            field.flags.insert(FieldFlags::DISCRIMINANT);
                        }
                        field.flags.insert(type_top.variant_field_flags);
                        field.discr_value = type_top.discr_value;
                        if abbrev.tag == DW_TAG_inheritance {
                            field.flags.insert(FieldFlags::INHERITANCE);
                            field.name = "#base";
                        }

                        if attrs.fields & FieldAttributes::name != 0 {
                            field.name = attrs.name;
                        }
                        if attrs.fields & FieldAttributes::type_ != 0 {
                            field.type_ = attrs.type_ as *const TypeInfo;
                        }
                        if attrs.fields & FieldAttributes::bit_size != 0 {
                            field.bit_size = attrs.bit_size;
                            field.flags.insert(FieldFlags::SIZE_KNOWN);
                        } else if attrs.fields & FieldAttributes::byte_size != 0 {
                            field.bit_size = attrs.byte_size * 8;
                            field.flags.insert(FieldFlags::SIZE_KNOWN);
                        }
                        if attrs.fields & FieldAttributes::data_bit_offset != 0 {
                            field.bit_offset = attrs.data_bit_offset;
                        } else if attrs.fields & FieldAttributes::data_member_location != 0 {
                            field.bit_offset = attrs.data_member_location * 8;
                        }
                        if attrs.artificial {
                            field.flags.insert(FieldFlags::ARTIFICIAL);
                        }

                        if abbrev.tag == DW_TAG_enumerator {
                            // Enumerand.
                            unsafe {
                                match &mut (*type_).t {
                                    Type::Enum(e) => self.shard.types.temp_types.add_enumerand(e, Enumerand {value: attrs.const_value_usize, name: field.name, flags: EnumerandFlags::empty()}),
                                    _ => if self.shard.warn.check(line!()) { eprintln!("warning: {} in {} is not supported", abbrev.tag, self.main_stack.top2().tag); }
                                }
                            }
                        } else {
                            if field.type_ == self.loader.types.builtin_types.unknown {
                                if self.shard.warn.check(line!()) { eprintln!("warning: field with no type @0x{:x}", offset.0); }
                            }
                            if attrs.external {
                                // Static constant inside a struct.
                                if attrs.fields & (FieldAttributes::const_value_usize | FieldAttributes::const_value_slice) != 0 {
                                    let loc = if attrs.fields & FieldAttributes::const_value_usize != 0 {
                                        DwarfVariableLocation::ConstUsize(attrs.const_value_usize)
                                    } else {
                                        DwarfVariableLocation::ConstSlice(attrs.const_value_slice)
                                    };
                                    let decl = Self::parse_line_info(&mut self.shard, &self.loader, self.unit, &attrs.decl);
                                    let var = Variable::new(field.name, field.type_, offset, decl, VariableFlags::empty());
                                    self.add_variable_locations(loc, /*linkage_name*/ "", var, offset)?;
                                } else {
                                    // Probably separate declaration and definition.
                                    //if self.shard.warn.check(line!()) { eprintln!("warning: static field with no DW_AT_const_value at @0x{:x}", offset.0); }
                                }
                            } else {
                                // Struct field.
                                let t = unsafe {&mut *type_};
                                match &mut t.t {
                                    Type::Struct(s) => self.shard.types.temp_types.add_field(s, field),
                                    _ => if self.shard.warn.check(line!()) { eprintln!("warning: {} in {} is not supported", abbrev.tag, self.main_stack.top2().tag); }
                                }
                            }
                        }
                    }
                }

                DW_TAG_variant_part | DW_TAG_variant if !self.main_stack.top().flags.contains(StackFlags::IS_TYPE_SCOPE | StackFlags::IS_VALID_SCOPE) => {
                    if !self.main_stack.top().flags.contains(StackFlags::IS_TYPE_SCOPE) {
                        if self.shard.warn.check(line!()) { eprintln!("warning: {} in {} is not supported", abbrev.tag, self.main_stack.top2().tag); }
                    }
                    cursor.skip_attributes(abbrev, &attribute_context)?;
                }

                // Rust enum.
                // The tree usually looks like this:
                //   structure_type
                //     variant_part - with DW_AT_discr pointing to the discriminant member
                //       member - discriminant
                //       variant - with DW_AT_discr_value
                //         member
                //       variant
                //         member
                //       ...
                DW_TAG_variant_part => {
                    // Applicable attributes:
                    // Useful: discr
                    // Other: accessibility, declaration, type
                    let mut attrs = VariantPartAttributes::default();
                    unsafe {cursor.read_attributes(abbrev, /*which_layout*/ 0, &attribute_context, &raw mut attrs as *mut u8)}?;
                    if attrs.discr == 0 {
                        // DW_AT_discr can be missing if there's only one reachable variant. Use nonzero value so that we can distinguish this from the whole DW_TAG_variant_part being missing.
                        attrs.discr = 1;
                    }
                    self.type_stack.top_mut().discriminant_die = DebugInfoOffset(attrs.discr);
                }
                DW_TAG_variant => {
                    // Applicable attributes:
                    // Useful: discr_value, discr_list
                    // Other: accessibility, declaration
                    let mut attrs = VariantAttributes::default();
                    unsafe {cursor.read_attributes(abbrev, /*which_layout*/ 0, &attribute_context, &raw mut attrs as *mut u8)}?;
                    let type_top = self.type_stack.top_mut();
                    if type_top.discriminant_die.0 == 0 {
                        if self.shard.warn.check(line!()) { eprintln!("warning: variant is not inside variant_part @0x{:x}", offset.0); }
                    } else if !type_top.variant_field_flags.is_empty() {
                        if self.shard.warn.check(line!()) { eprintln!("warning: nested DW_TAG_variant-s @0x{:x}", offset.0); }
                    } else if attrs.fields & VariantAttributes::discr_list != 0 {
                        if self.shard.warn.check(line!()) { eprintln!("warning: DW_AT_discr_list is not supported"); }
                    } else {
                        type_top.variant_field_flags.insert(if attrs.fields & VariantAttributes::discr_value != 0 {FieldFlags::VARIANT} else {FieldFlags::DEFAULT_VARIANT});
                        type_top.discr_value = attrs.discr_value;
                        // Clear variant_field_flags when leaving the DW_TAG_variant subtree.
                        self.main_stack.top_mut().flags.insert(StackFlags::HAS_VARIANT);
                    }
                }

                // Array dimensions.
                DW_TAG_subrange_type => {
                    // Applicable attributes:
                    // Useful: count, byte_stride, bit_stride, byte_size, bit_size, lower_bound, upper_bound, type
                    // Other: alignment, data_location, declaration, threads_scaled
                    // Other: DECL, name, accessibility, allocated, associated, visibility
                    let mut attrs = SubrangeTypeAttributes::default();
                    unsafe {cursor.read_attributes(abbrev, /*which_layout*/ 0, &attribute_context, &raw mut attrs as *mut u8)}?;

                    let array = if !self.main_stack.top().flags.contains(StackFlags::IS_TYPE_SCOPE | StackFlags::IS_VALID_SCOPE) {
                        None
                    } else {
                        let t = self.type_stack.top().type_;
                        unsafe {(*t).t.as_array_mut()}
                    };
                    if let Some(mut array) = array {
                        if !array.flags.contains(ArrayFlags::PARSED_SUBRANGE) {
                            array.flags.insert(ArrayFlags::PARSED_SUBRANGE);
                        } else {
                            // Turn multidimensional array into array of arrays.
                            // Point the stack entry to the inner array (so that subsequent DW_TAG_subrange_type-s apply to inner rather than outer dimensions).
                            // The outer array is still in `types`, but not in the stack, so finish_type() won't be called for it, which is ok.
                            // (Note that pushing another type onto type_stack won't work because the repeated DW_TAG_subrange_type are not nested in each other, so the stack entry will be popped immediately.)
                            let t = unsafe {&mut *self.type_stack.top().type_};
                            array = t.t.as_array_mut().unwrap(); // avoid UB
                            let info = TypeInfo {die: offset, binary_id: t.binary_id, line: t.line, language: self.unit.language, t: Type::Array(ArrayType {flags: ArrayFlags::PARSED_SUBRANGE, type_: array.type_, stride: 0, len: 0}), ..TypeInfo::default()};
                            let (ptr, off) = self.shard.types.add_type(info);
                            assert!(ptr != ptr::null());
                            array.type_ = off;
                            let ptr = ptr as *mut TypeInfo;
                            self.type_stack.top_mut().type_ = ptr;
                            array = unsafe {(*ptr).t.as_array_mut().unwrap()};
                        }

                        if attrs.fields & SubrangeTypeAttributes::byte_stride != 0 {
                            array.stride = attrs.byte_stride;
                        } else if attrs.fields & SubrangeTypeAttributes::bit_stride != 0 {
                            if attrs.bit_stride % 8 == 0 {
                                array.stride = attrs.bit_stride / 8;
                            } else {
                                if self.shard.warn.check(line!()) { eprintln!("warning: bit-packed arrays are not supported (have DW_AT_bit_stride @0x{:x})", offset.0); }
                            }
                        }
                        if attrs.lower_bound != 0 {
                            if self.shard.warn.check(line!()) { eprintln!("warning: non-zero-indexed arrays are not supported (have one @0x{:x})", offset.0); }
                        }
                        if attrs.fields & SubrangeTypeAttributes::count != 0 {
                            array.len = attrs.count;
                            array.flags.insert(ArrayFlags::LEN_KNOWN);
                        } else if attrs.fields & SubrangeTypeAttributes::count_expr != 0 {
                            if self.shard.warn.check(line!()) { eprintln!("warning: variable-length arrays are not supported (have one @0x{:x})", offset.0); }
                        } else if attrs.fields & SubrangeTypeAttributes::upper_bound != 0 {
                            if attrs.lower_bound > attrs.upper_bound || attrs.upper_bound - attrs.lower_bound == usize::MAX {
                                if self.shard.warn.check(line!()) { eprintln!("warning: array has lower bound {} > upper bound {} @0x{:x}", attrs.lower_bound, attrs.upper_bound, offset.0); }
                            } else {
                                array.len = (attrs.upper_bound - attrs.lower_bound + 1) as usize;
                                array.flags.insert(ArrayFlags::LEN_KNOWN);
                            }
                        }
                    } else {
                        if self.main_stack.top2().tag != DW_TAG_array_type {
                            if self.shard.warn.check(line!()) { eprintln!("warning: {} in {} is not supported", abbrev.tag, self.main_stack.top2().tag); }
                        } else {
                            // (Warning would already be printed when parsing the parent.)
                        }
                    }
                }

                DW_TAG_generic_subrange => {
                    // Haven't seen these in C++ or Rust.
                    if self.shard.warn.check(line!()) { eprintln!("warning: arrays with dynamic number of dimensions are not supported (got one @0x{:x})", offset.0); }
                    cursor.skip_attributes(abbrev, &attribute_context)?;
                }

                // Lexical block, just provides address ranges for the variables it contains.
                DW_TAG_lexical_block => {
                    let mut attrs = LexicalBlockAttributes::default();
                    unsafe {cursor.read_attributes(abbrev, /*which_layout*/ 0, &attribute_context, &raw mut attrs as *mut u8)}?;
                    if attrs.fields & (DwarfRanges::RANGES | DwarfRanges::LOW_PC) != 0 {
                        let ranges_top = self.ranges_stack.push_uninit(&mut self.main_stack.top_mut().flags);
                        parse_dwarf_ranges(&self.loader.sym.dwarf, &self.unit.unit, &attrs.ranges, attrs.fields, offset, self.loader.sym.code_addr_range.start, &mut ranges_top.pc_ranges, /*out_entry_pc*/ &mut 0, &mut self.shard.warn)?;
                    }
                }

                DW_TAG_inlined_subroutine if !self.main_stack.top().flags.contains(StackFlags::IS_FUNCTION_SCOPE | StackFlags::IS_VALID_SCOPE) => {
                    if !self.main_stack.top().flags.contains(StackFlags::IS_FUNCTION_SCOPE) {
                        if self.shard.warn.check(line!()) { eprintln!("warning: unexpected inlined_subroutine not inside function @0x{:x}", offset.0); }
                    }
                    cursor.skip_attributes(abbrev, &attribute_context)?;
                }

                // Inlined functions.
                DW_TAG_inlined_subroutine => {
                    // Applicable attributes:
                    // Useful: call_file, call_line, call_column, entry_pc, low_pc, high_pc, ranges, abstract_origin
                    // Other: const_expr, return_addr, segment, start_scope, trampoline
                    let mut attrs = InlinedSubroutineAttributes::default();
                    unsafe {cursor.read_attributes(abbrev, /*which_layout*/ 0, &attribute_context, &raw mut attrs as *mut u8)}?;
                    let ranges_top = self.ranges_stack.push_uninit(&mut self.main_stack.top_mut().flags);
                    let mut entry_pc = 0usize;
                    parse_dwarf_ranges(&self.loader.sym.dwarf, &self.unit.unit, &attrs.ranges, attrs.fields, offset, self.loader.sym.code_addr_range.start, &mut ranges_top.pc_ranges, &mut entry_pc, &mut self.shard.warn)?;

                    let call_line = Self::parse_line_info(&mut self.shard, &self.loader, self.unit, &attrs.call);
                    let callee_die = if attrs.fields & InlinedSubroutineAttributes::abstract_origin != 0 {
                        DebugInfoOffset(attrs.abstract_origin)
                    } else {
                        if self.shard.warn.check(line!()) { eprintln!("warning: inlined_subroutine doesn't say which function it is (DW_AT_abstract_origin) @0x{:x}", offset.0); }
                        DebugInfoOffset(usize::MAX)
                    };

                    let f = self.function_stack.top_mut();
                    let parent = self.subfunction_stack.top();
                    let level = parent.subfunction_level + 1;
                    let parent_idx = parent.subfunction_idx;

                    if f.subfunctions.len() >= u32::MAX as usize - 1 {
                        if self.shard.warn.check(line!()) { eprintln!("function @0x{:x} has more than {} inlined function calls; this is not supported", offset.0, u32::MAX-1); }
                        self.main_stack.top_mut().flags.remove(StackFlags::IS_VALID_SCOPE);
                    } else if level >= i16::MAX as u16 {
                        if self.shard.warn.check(line!()) { eprintln!("warning: inlined functions nested > {} levels deep @0x{:x}; this is not supported", i16::MAX - 1, offset.0); }
                        self.main_stack.top_mut().flags.remove(StackFlags::IS_VALID_SCOPE);
                    } else {
                        if call_line.file_idx().is_some() && entry_pc != 0 {
                            let mut entry_call_line = call_line.clone().with_addr_and_flags(entry_pc, LineFlags::INLINED_FUNCTION | LineFlags::STATEMENT);
                            Self::fixup_subfunction_call_line(&self.shard, &mut entry_call_line, entry_pc);
                            self.shard.sym.line_to_addr.push((entry_call_line, level - 1));
                        }

                        let sf_idx = f.subfunctions.len() as u32;
                        f.subfunctions.push((Subfunction {callee_idx: callee_die.0, local_variables: Subfunction::pack_range(0..0), call_line: call_line.clone(), addr_range: 0..0, identity: sf_idx}, parent_idx));
                        self.subfunction_stack.push_uninit(&mut self.main_stack.top_mut().flags).reset(sf_idx, level);
                        for range in &self.ranges_stack.top().pc_ranges {
                            f.subfunction_events.push(SubfunctionEvent {addr: range.begin as usize, subfunction_idx: sf_idx, signed_level: level as i16 + 1});
                            f.subfunction_events.push(SubfunctionEvent {addr: range.end as usize, subfunction_idx: sf_idx, signed_level: -(level as i16 + 1)});
                        }
                    }
                }

                // Things we (hopefully) don't care about.
                DW_TAG_label | DW_TAG_imported_declaration | DW_TAG_imported_module | DW_TAG_GNU_template_parameter_pack | DW_TAG_GNU_template_template_param => {
                    skip_subtree = self.main_stack.len;
                    cursor.skip_attributes(abbrev, &attribute_context)?;
                }

                // Function template arguments.
                DW_TAG_template_type_parameter if !self.main_stack.top().flags.contains(StackFlags::IS_TYPE_SCOPE | StackFlags::IS_VALID_SCOPE) => {
                    skip_subtree = self.main_stack.len;
                    cursor.skip_attributes(abbrev, &attribute_context)?;
                }

                // Struct template arguments. Treat them as typedefs, as if e.g. vector<int> had a 'using T = int' inside it. Useful for pretty printers.
                DW_TAG_template_type_parameter => {
                    // Applicable attributes:
                    // Useful: DECL, name, type
                    // Other: default_value
                    let mut attrs = TemplateTypeParameterAttributes::default();
                    unsafe {cursor.read_attributes(abbrev, /*which_layout*/ 0, &attribute_context, &raw mut attrs as *mut u8)}?;
                    if !attrs.name.is_empty() && attrs.fields & TemplateTypeParameterAttributes::type_ != 0 {
                        self.type_stack.top_mut().nested_names.push((attrs.name, NestedName::Type(attrs.type_ as *const TypeInfo)));
                    }
                }

                // Treat value template arguments as constant variables.
                DW_TAG_template_value_parameter => {
                    // Applicable attributes:
                    // Useful: DECL, const_value, name, type
                    // Other: default_value
                    let mut attrs = TemplateValueParameterAttributes::default();
                    unsafe {cursor.read_attributes(abbrev, /*which_layout*/ 0, &attribute_context, &raw mut attrs as *mut u8)}?;
                    if attrs.fields & (TemplateValueParameterAttributes::const_value_usize | TemplateValueParameterAttributes::const_value_slice) == 0 || attrs.fields & TemplateValueParameterAttributes::type_ == 0 {
                        // Missing value or type. Not sure what this means, but it's possible.
                        //if self.shard.warn.check(line!()) { eprintln!("warning: DW_TAG_template_value_parameter without DW_AT_const_value or DW_AT_type @0x{:x}", offset.0); }
                    } else {
                        let decl = Self::parse_line_info(&mut self.shard, &self.loader, self.unit, &attrs.decl);
                        let var = Variable::new(attrs.name, attrs.type_ as *const TypeInfo, offset, decl, VariableFlags::TEMPLATE_PARAMETER);
                        let loc = if attrs.fields & TemplateValueParameterAttributes::const_value_usize != 0 {
                            DwarfVariableLocation::ConstUsize(attrs.const_value_usize)
                        } else {
                            DwarfVariableLocation::ConstSlice(attrs.const_value_slice)
                        };
                        self.add_variable_locations(loc, /*linkage_name*/ "", var, offset)?;
                    }
                }

                _ => cursor.skip_attributes(abbrev, &attribute_context)?,
            }
        }
    }

    fn finish_subfunction(&mut self) {
        let top = self.subfunction_stack.pop_mut();
        let start = self.shard.sym.local_variables.len();
        self.shard.sym.local_variables.append(&mut top.local_variables);
        let end = self.shard.sym.local_variables.len();
        let subfunction_idx = top.subfunction_idx;
        self.function_stack.top_mut().subfunctions[subfunction_idx as usize].0.local_variables = Subfunction::pack_range(start..end);
    }
    
    fn finish_function(&mut self) {
        let top = self.function_stack.pop_mut();
        if top.subfunction_events.is_empty() {
            // Inline-only function.
            return;
        }

        // Do a sweeping line to turn arbitrary set of ranges into a well-formed tree of nested ranges,
        // (because who knows what garbage the debug info may contain in practice).
        // Imagine a flame graph being scanned left to right by a vertical line. Each iteration of the loop corresponds to a left or right edge of a rectangle.
        top.subfunction_events.sort_unstable_by_key(|e| (e.addr, e.signed_level));
        let temp = &mut self.temp;
        // stack: Vec<(/*subfunction_idx*/ usize, /*range_idx*/ usize, /*active*/ usize)>,
        temp.stack.clear();
        // (temp.levels[..num_levels] are cleared near the end of this function)
        let mut num_levels = 0usize; // effective length of temp.levels; we don't clear it to avoid reallocating inner Vec-s
        for event_idx in 0..top.subfunction_events.len() {
            let &SubfunctionEvent {addr, subfunction_idx, signed_level} = &top.subfunction_events[event_idx];
            let level = (signed_level.abs() - 1) as usize;
            if signed_level > 0 { // start of a range
                if level < temp.stack.len() {
                    if self.shard.warn.check(line!()) { eprintln!("warning: overlapping inlined function ranges at address 0x{:x} in function @0x{:x}", addr, self.shard.functions[top.function].die.0); }
                    // Ignore this range but increment the counter anyway, because the corresponding closing event will decrement it. This effectively extends
                    // the existing range to cover this range too, which is not the best behavior, but it's the simplest (?) to implement here (while ensuring the output ranges are well-nested).
                    temp.stack[level].1 += 1;
                    continue;
                }
                let start_level = temp.stack.len();
                temp.stack.resize(level + 1, (0, 0));
                if level >= num_levels {
                    num_levels = level + 1;
                    if num_levels > temp.levels.len() {
                        temp.levels.resize_with(num_levels * 4, || Vec::new());
                    }
                }

                // Open a range at current level and for all ancestors that don't have a range open.
                temp.stack.last_mut().unwrap().1 += 1;
                let mut cur_sf_idx = subfunction_idx;
                for cur_level in (start_level..level+1).rev() {
                    let &(ref cur_sf, parent) = &top.subfunctions[cur_sf_idx as usize];
                    let new_range_idx = temp.levels[cur_level].len();
                    temp.stack[cur_level].0 = new_range_idx;
                    let mut sf_clone = cur_sf.clone();
                    sf_clone.addr_range = addr..addr;
                    temp.levels[cur_level].push(sf_clone);

                    cur_sf_idx = parent;
                }
            } else {
                temp.stack[level].1 -= 1;
                let mut last_closed_idx = usize::MAX;
                while let Some(&(range_idx, active)) = temp.stack.last() {
                    if active != 0 {
                        break;
                    }
                    temp.stack.pop();
                    let range = &mut temp.levels[temp.stack.len()][range_idx];
                    range.addr_range.end = addr;
                    last_closed_idx = range_idx;
                }
                if last_closed_idx != usize::MAX && event_idx + 1 < top.subfunction_events.len() && top.subfunction_events[event_idx + 1].addr > addr {
                    let sf = &temp.levels[temp.stack.len()][last_closed_idx];
                    if sf.call_line.file_idx().is_some() {
                        // .debug_line often doesn't have a row at the end of inlined function. I.e. the first few instructions
                        // after the inlined function still have the same line number as the insides of the inlined function, which makes things really confusing.
                        // I'm not sure what's the intention there. I guess the debugger is supposed to realize that the instructions after an inlined function
                        // have the same line number as the inlined function's call site? Let's interpret it that way and add LineInfo, with lower priority than the
                        // LineInfo-s from .debug_line.
                        // This quirk sometimes appears in combination with the line() == 0 quirk, so we do fixup_subfunction_call_line() as well.
                        let mut line = sf.call_line;
                        Self::fixup_subfunction_call_line(&self.shard, &mut line, sf.addr_range.start);
                        self.shard.sym.addr_to_line.push(line.with_addr_and_flags(addr, LineFlags::INLINED_FUNCTION));
                    }
                }
            }
        }
        assert!(temp.stack.is_empty());

        // Concatenate the per-level range arrays into one array.
        if self.shard.sym.subfunction_levels.last() != Some(&self.shard.sym.subfunctions.len()) {
            self.shard.sym.subfunction_levels.push(self.shard.sym.subfunctions.len());
        }
        let levels_start = self.shard.sym.subfunction_levels.len() - 1;
        for level in 0..num_levels {
            for sf in &temp.levels[level] {
                let mut sf_clone = sf.clone();
                Self::fixup_subfunction_call_line(&self.shard, &mut sf_clone.call_line, sf_clone.addr_range.start);
                self.shard.sym.subfunctions.push(sf_clone);
            }

            self.shard.sym.subfunction_levels.push(self.shard.sym.subfunctions.len());

            temp.levels[level].clear();
        }
        let level_idxs = levels_start..self.shard.sym.subfunction_levels.len();
        assert!(level_idxs.len() == num_levels + 1);

        self.shard.functions[top.function].subfunction_levels = level_idxs;
    }

    fn finish_type(&mut self) {
        let type_top = self.type_stack.pop();
        let t = unsafe {&mut *type_top.type_};
        if !type_top.nested_names.is_empty() {
            t.nested_names = self.shard.types.temp_types.misc_arena.add_slice(&type_top.nested_names);
        }
    }
}

fn parse_dwarf_ranges(dwarf: &Dwarf<DwarfSlice>, unit: &Unit<DwarfSlice>, ranges: &DwarfRanges, fields: u32, offset: DieOffset, code_start: usize, out_ranges: &mut Vec<gimli::Range>, out_entry_pc: &mut usize, warn: &mut Limiter) -> Result<()> {
    out_ranges.clear();
    *out_entry_pc = 0;
    // Sometimes both low_pc and ranges are present on compilation units. In this case ranges take precedence, and low_pc acts as "base address" for all range lists in the unit (which gimli takes care of automatically).
    if fields & DwarfRanges::RANGES != 0 {
        // (Compatibility: in DWARF 4 we'd need to add DW_AT_GNU_ranges_base.)
        let mut it = dwarf.ranges(unit, RangeListsOffset(ranges.ranges))?;
        while let Some(range) = it.next()? {
            // In practice ranges often contain garbage near-zero addresses, even in debug builds without LTO. Presumably linker relocations get lost at some point, maybe because of compiler optimizations.
            // If the bad range is empty, I guess it's intended to be skipped. But sometimes these ranges are not empty, sometimes they don't start at 0, and sometimes none of the bad ranges in the list start at 0.
            // Sometimes bad ranges coexist with good ranges in the same list of ranges.
            // Idk if that's intended or compiler bug (or maybe DWARF parser bug, though I checked it against dwarfdump output). Let's silently ignore invalid ranges.
            // Maybe a cleaner way to detect bad ranges would be to check if the base address is zero (suggesting missing relocation) when parsing the range list data, but that's currently hidden inside gimli.
            if range.end as usize <= code_start || range.end <= range.begin {
                continue;
            }
            if out_ranges.is_empty() {
                *out_entry_pc = range.begin as usize;
            }
            out_ranges.push(range);
        }
    } else if fields & DwarfRanges::LOW_PC != 0 {
        if ranges.low_pc == 0 { // same as above, see other comment
            return Ok(());
        }
        let high_pc = if fields & DwarfRanges::HIGH_PC == 0 {
            ranges.low_pc + 1
        } else if fields & DwarfRanges::HIGH_PC_IS_RELATIVE != 0 {
            ranges.low_pc + ranges.high_pc
        } else {
            ranges.high_pc
        };
        if high_pc > ranges.low_pc {
            out_ranges.push(gimli::Range {begin: ranges.low_pc as u64, end: high_pc as u64});
        }
    }
    if fields & DwarfRanges::LOW_PC != 0 {
        *out_entry_pc = ranges.low_pc;
    }

    if fields & DwarfRanges::ENTRY_PC != 0 {
        if fields & DwarfRanges::ENTRY_PC_IS_RELATIVE != 0 {
            // DWARF5.pdf says:
            // "If the value of the DW_AT_entry_pc attribute is of class address that address is the entry address;
            //  or, if it is of class constant, the value is an unsigned integer offset which, when
            //  added to the base address of the function, gives the entry address.
            //  If no DW_AT_entry_pc attribute is present, then the entry address is assumed to
            //  be the same as the base address of the containing scope."
            //
            // This is so vague!
            // Does "function" in "base address of the function" refer to the containing DW_TAG_subprogram or to the same DIE that has the DW_AT_entry_pc?
            // What is "containing scope"? Is it the same DIE that has the DW_AT_entry_pc, or its nearest ancestor with address ranges (e.g. a DW_AT_lexical_block or DW_AT_subprogram)?
            // This code currently assumes that the answer to both questions is "the same DIE that has the DW_AT_entry_pc" because this seems like the most sensible choice, but I have no idea.
            //
            // "The base address of the scope for any of the debugging information entries listed
            //  above is given by either the DW_AT_low_pc attribute or the first address in the
            //  first range entry in the list of ranges given by the DW_AT_ranges attribute. If
            //  there is no such attribute, the base address is undefined."
            *out_entry_pc += ranges.entry_pc;
        } else {
            *out_entry_pc = ranges.entry_pc;
        }
    }
    
    Ok(())
}

pub fn run_load_symbols_tool(path: String, num_threads: usize) -> Result<()> {
    let file = File::open(&path)?;
    let elf = Arc::new(ElfFile::from_file(path.clone(), &file, file.metadata()?.len())?);
    let symbols;

    let status = Arc::new(SymbolsLoadingStatus::new());
    let progress_thread = {
        let status_copy = status.clone();
        thread::spawn(move || {
            while !status_copy.cancel.load(Ordering::Relaxed) {
                eprint!("\r{:.2}%\r", status_copy.progress_ppm.load(Ordering::Relaxed) as f64 / 1e4);
                thread::sleep(Duration::from_millis(100));
            }
            eprint!("\r");
        })
    };

    {
        let _prof = ProfileScope::new("loading symbols".to_string());

        let (loader, stage_names);
        {
            let start_time = Instant::now();

            loader = Arc::new(SyncUnsafeCell::new(SymbolsLoader::new(vec![elf], 1, num_threads, status.clone())?));

            stage_names = unsafe {&*loader.get()}.progress_per_stage.clone();
            println!("stage 0 prepare ({}) took {}", stage_names[0][0].1, PrettyDuration(start_time.elapsed().as_secs_f64()));
        }
        let num_shards = unsafe {&*loader.get()}.num_shards;
        let mut stage_idx = 1usize;

        loop {
            {
                let start_time = Instant::now();
                let not_done = unsafe {&mut *loader.get()}.prepare_stage(stage_idx)?;
                println!("stage {} prepare ({}) took {}", stage_idx, stage_names[stage_idx][0].1, PrettyDuration(start_time.elapsed().as_secs_f64()));
                if !not_done {
                    break;
                }
            }

            let start_time = Instant::now();
            let threads: Vec<thread::JoinHandle<(Instant, usize)>> = (0..num_shards).map(|shard_idx| {
                let loader_copy = loader.clone();
                let status_copy = status.clone();
                thread::spawn(move || {
                    let start_cpu_time = get_thread_cpu_time_ns();

                    if let Err(e) = unsafe {&*loader_copy.get()}.run(stage_idx, shard_idx) {
                        status_copy.cancel.store(true, Ordering::Relaxed);
                        eprintln!("error: {}", e);
                    }

                    (Instant::now(), get_thread_cpu_time_ns() - start_cpu_time)
                })
            }).collect();

            let thread_times: Vec<(Instant, usize)> = threads.into_iter().map(|t| t.join().unwrap()).collect();

            if status.cancel.load(Ordering::Relaxed) {
                return err!(Dwarf, "failed to load");
            }

            let end_time = Instant::now();
            let elapsed = (end_time - start_time).as_secs_f64();
            let threads_elapsed: f64 = thread_times.iter().map(|(ts, _)| (*ts - start_time).as_secs_f64()).sum();
            let threads_cpu_ns: usize = thread_times.iter().map(|(_, t)| *t).sum();
            println!("stage {} run ({}) took {}; thread time util {:.2}% * cpu util {:.2}%", stage_idx, stage_names[stage_idx][1].1, PrettyDuration(elapsed), threads_elapsed / num_shards as f64 / elapsed * 100.0, threads_cpu_ns as f64 / 1e9 / threads_elapsed * 100.0);

            stage_idx += 1;
        }
        symbols = Arc::into_inner(loader).unwrap().into_inner().into_result();
    }

    status.cancel.store(true, Ordering::Relaxed);
    progress_thread.join().unwrap();

    hint::black_box(symbols);

    Ok(())
}
