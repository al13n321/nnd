use std::{mem, fmt, cell::{Cell, UnsafeCell}};
use crate::{*, error::*, process_info::ptrace_get_extra_regs};
use libc::pid_t;

// Registers stored with each stack trace frame.
#[derive(Clone, Default)]
pub struct Registers {
    pub ints: [u64; RegisterIdx::COUNT],

    // Bitmask saying which values are populated in the array(s) above (including dubious values).
    pub mask: u64,
    // Which of the values are just guesses.
    pub dubious_mask: u64,
}

// Registers that are not in user_regs_struct, mostly simd. They're bulky and never callee-saved and ~never appear in unwind information.
// So we store them once per thread rather than once per stack frame.
#[derive(Clone)]
pub struct ExtraRegisters {
    pub a: [u64; ExtraRegisterIdx::SCALAR_COUNT],
    pub mask: u64,
    pub dubious_mask: u64,
    pub error: Option<Error>,
}
impl Default for ExtraRegisters { fn default() -> Self { Self {a: [0; ExtraRegisterIdx::SCALAR_COUNT], mask: 0, dubious_mask: 0, error: None} } }

pub struct LazyExtraRegisters {
    r: UnsafeCell<ExtraRegisters>,
    tid: Cell<Option<pid_t>>,
}

#[repr(u8)]
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum RegisterIdx {
    // x86-64 registers.
    Rax = 0,
    Rdx = 1,
    Rcx = 2,
    Rbx = 3,
    Rsi = 4,
    Rdi = 5,
    Rbp = 6,
    Rsp = 7,
    R8 = 8,
    R9 = 9,
    R10 = 10,
    R11 = 11,
    R12 = 12,
    R13 = 13,
    R14 = 14,
    R15 = 15,
    Rip = 16,
    Cs = 17,
    Ss = 18,
    Fs = 19,
    Gs = 20,
    FsBase = 21,
    GsBase = 22,

    // Other things in user_regs_struct. Not actually registers.
    Flags = 23,
    OrigRax = 24, // as in user_regs_struct

    // Other things for unwinding. Not actually registers.
    Cfa = 25, // Canonical Frame Address from .eh_frame
    Ret = 26, // return address according to .eh_frame
}
impl RegisterIdx {
    pub const COUNT: usize = RegisterIdx::Ret as usize + 1;

    pub fn from_dwarf(r: gimli::Register) -> Option<RegisterIdx> {
        match r.0 {
            0..=16 => Some(unsafe {mem::transmute(r.0 as u8)}),
            // 33-48 - obsolete floating point registers
            49 => Some(RegisterIdx::Flags),
            // 50 - es
            51 => Some(RegisterIdx::Cs),
            52 => Some(RegisterIdx::Ss),
            // 53 - ds
            54 => Some(RegisterIdx::Fs),
            55 => Some(RegisterIdx::Gs),
            // 56-57 - reserved
            58 => Some(RegisterIdx::FsBase),
            59 => Some(RegisterIdx::GsBase),
            _ => None,
        }
    }

    pub fn all() -> &'static [RegisterIdx] {
        &REGISTER_IDXS
    }

    pub fn name(self) -> &'static str {
        REGISTER_NAMES[self as usize]
    }

    pub fn parse_ignore_case(s: &str) -> Option<Self> {
        REGISTER_NAMES.iter().position(|n| n.eq_ignore_ascii_case(s)).map(|i| unsafe {mem::transmute(i as u8)})
    }
}
impl fmt::Display for RegisterIdx {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

// One of:
//  * xmm0-31  (xmm16-31 and ymm16-31 aren't a thing, but we currently allow them anyway)
//  * ymm0-31
//  * zmm0-31
//  * opmask  (representing the whole 512-byte value)
//  * opmask0-7
//  * mxcsr
// Represented as a range in array of 8-byte values. E.g. zmm1 is 8..16, ymm1 is 8..12.
#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct ExtraRegisterIdx {
    pub start: usize,
    pub len: usize,
}
impl ExtraRegisterIdx {
    pub const ZMM_START: usize = 0;
    pub const ZMM_STRIDE: usize = 8;
    pub const ZMM_COUNT: usize = 32;
    pub const OPMASK_START: usize = Self::ZMM_START + Self::ZMM_STRIDE*Self::ZMM_COUNT;
    pub const OPMASK_COUNT: usize = 8;
    pub const MXCSR_IDX: usize = Self::OPMASK_START + Self::OPMASK_COUNT;
    pub const SCALAR_COUNT: usize = Self::MXCSR_IDX + 1;

    pub const fn zmm(n: usize) -> Self {
        assert!(n < Self::ZMM_COUNT);
        let i = Self::ZMM_START + Self::ZMM_STRIDE*n;
        Self {start: i, len: 8}
    }
    pub const fn ymm(n: usize) -> Self {
        let i = Self::zmm(n).start;
        Self {start: i, len: 4}
    }
    pub const fn xmm(n: usize) -> Self {
        let i = Self::zmm(n).start;
        Self {start: i, len: 2}
    }
    pub const fn opmask() -> Self {
        Self {start: Self::OPMASK_START, len: Self::OPMASK_COUNT}
    }
    pub fn opmask_element(n: usize) -> Self {
        assert!(n < Self::OPMASK_COUNT);
        Self {start: Self::OPMASK_START + n, len: 1}
    }
    pub const fn mxcsr() -> Self {
        Self {start: Self::MXCSR_IDX, len: 1}
    }

    // Index in the bitmask saying which registers are known.
    pub fn mask_idx(self) -> u32 {
        match self.start {
            Self::ZMM_START..Self::OPMASK_START => 0,
            Self::OPMASK_START..Self::MXCSR_IDX => 1,
            Self::MXCSR_IDX => 2,
            _ => panic!("huh"),
        }
    }

    pub fn name(self) -> &'static str {
        match self.start {
            Self::ZMM_START..Self::OPMASK_START => {
                let i = self.start - Self::ZMM_START;
                assert!(i % Self::ZMM_STRIDE == 0);
                let i = i / Self::ZMM_STRIDE;
                let j = match self.len {
                    2 => 0,
                    4 => 1,
                    8 => 2,
                    _ => panic!("invalid ExtraRegisterIdx"),
                };
                EXTRA_REGISTER_NAMES_MM[j][i]
            }
            Self::OPMASK_START..Self::MXCSR_IDX => {
                if self.len == 8 {
                    "opmask"
                } else {
                    assert!(self.len == 1);
                    let i = self.start - Self::OPMASK_START;
                    EXTRA_REGISTER_NAMES_OPMASK[i]
                }
            }
            Self::MXCSR_IDX => "mxcsr",
            _ => panic!("invalid ExtraRegisterIdx"),
        }
    }

    pub fn from_dwarf(r: gimli::Register) -> Option<ExtraRegisterIdx> {
        let n = r.0 as usize;
        match n {
            17..=32 => Some(ExtraRegisterIdx::zmm(n - 17)),
            67..=82 => Some(ExtraRegisterIdx::zmm(n - 67 + 16)),
            118..=125 => Some(ExtraRegisterIdx::opmask_element(n - 118)),
            64 => Some(ExtraRegisterIdx::mxcsr()),
            _ => None,
        }
    }

    pub fn parse_ignore_case(s: &str) -> Option<Self> {
        if !s.is_ascii() {
            return None;
        }
        if s.eq_ignore_ascii_case("mxcsr") {
            return Some(Self::mxcsr());
        }
        let opmask = "opmask";
        if s.len() >= opmask.len() && s[..opmask.len()].eq_ignore_ascii_case(opmask) {
            let tail = &s[opmask.len()..];
            if tail.is_empty() {
                return Some(Self::opmask());
            }
            if let Ok(n) = tail.parse::<usize>() {
                if n < Self::OPMASK_COUNT {
                    return Some(Self::opmask_element(n));
                }
            }
            return None;
        }

        if s.len() < "xmm0".len() {return None;}
        if !s[1..3].eq_ignore_ascii_case("mm") {return None;}
        let len = match s.as_bytes()[0] {
            b'x' | b'X' => 2,
            b'y' | b'Y' => 4,
            b'z' | b'Z' => 8,
            _ => return None,
        };
        let Ok(n) = s[3..].parse::<usize>() else {return None};
        if n >= Self::ZMM_COUNT {return None;}
        let mut r = Self::zmm(n);
        r.len = len;
        Some(r)
    }

    // What to show in registers list in the UI. ("", [...]) means list these registers directly, ("group name", [...]) means show an group of registers as a collapsible tree node.
    pub fn groups_for_ui() -> &'static [(&'static str, &'static [ExtraRegisterIdx])] {
        &[("", &EXTRA_REGISTERS_EXCEPT_ZMM), ("zmm", &EXTRA_REGISTERS_ZMM)]
    }
}
impl fmt::Display for ExtraRegisterIdx {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

pub const REGISTER_IDXS: [RegisterIdx; RegisterIdx::COUNT] =  [RegisterIdx::Rax, RegisterIdx::Rdx, RegisterIdx::Rcx, RegisterIdx::Rbx, RegisterIdx::Rsi, RegisterIdx::Rdi, RegisterIdx::Rbp, RegisterIdx::Rsp, RegisterIdx::R8, RegisterIdx::R9, RegisterIdx::R10, RegisterIdx::R11, RegisterIdx::R12, RegisterIdx::R13, RegisterIdx::R14, RegisterIdx::R15, RegisterIdx::Rip, RegisterIdx::Cs, RegisterIdx::Ss, RegisterIdx::Fs, RegisterIdx::Gs, RegisterIdx::FsBase, RegisterIdx::GsBase, RegisterIdx::Flags, RegisterIdx::OrigRax, RegisterIdx::Cfa, RegisterIdx::Ret]; // rust
pub const REGISTER_NAMES: [&'static str; RegisterIdx::COUNT] = ["rax", "rdx", "rcx", "rbx", "rsi", "rdi", "rbp", "rsp", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15", "rip", "cs", "ss", "fs", "gs", "fs_base", "gs_base", "flags", "orig_rax", "cfa", "ret"];
// Generated with: '", "'.join([f'xmm{i}' for i in range(32)] + [f'ymm{i}' for i in range(32)] + [f'zmm{i}' for i in range(32)])
pub const EXTRA_REGISTER_NAMES_MM: [[&'static str; 32]; 3] = [["xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "xmm16", "xmm17", "xmm18", "xmm19", "xmm20", "xmm21", "xmm22", "xmm23", "xmm24", "xmm25", "xmm26", "xmm27", "xmm28", "xmm29", "xmm30", "xmm31"], ["ymm0", "ymm1", "ymm2", "ymm3", "ymm4", "ymm5", "ymm6", "ymm7", "ymm8", "ymm9", "ymm10", "ymm11", "ymm12", "ymm13", "ymm14", "ymm15", "ymm16", "ymm17", "ymm18", "ymm19", "ymm20", "ymm21", "ymm22", "ymm23", "ymm24", "ymm25", "ymm26", "ymm27", "ymm28", "ymm29", "ymm30", "ymm31"], ["zmm0", "zmm1", "zmm2", "zmm3", "zmm4", "zmm5", "zmm6", "zmm7", "zmm8", "zmm9", "zmm10", "zmm11", "zmm12", "zmm13", "zmm14", "zmm15", "zmm16", "zmm17", "zmm18", "zmm19", "zmm20", "zmm21", "zmm22", "zmm23", "zmm24", "zmm25", "zmm26", "zmm27", "zmm28", "zmm29", "zmm30", "zmm31"]];
pub const EXTRA_REGISTER_NAMES_OPMASK: [&'static str; 8] = ["opmask0", "opmask1", "opmask2", "opmask3", "opmask4", "opmask5", "opmask6", "opmask7"];
pub const EXTRA_REGISTERS_ZMM: [ExtraRegisterIdx; 32] = [ExtraRegisterIdx::zmm(0), ExtraRegisterIdx::zmm(1), ExtraRegisterIdx::zmm(2), ExtraRegisterIdx::zmm(3), ExtraRegisterIdx::zmm(4), ExtraRegisterIdx::zmm(5), ExtraRegisterIdx::zmm(6), ExtraRegisterIdx::zmm(7), ExtraRegisterIdx::zmm(8), ExtraRegisterIdx::zmm(9), ExtraRegisterIdx::zmm(10), ExtraRegisterIdx::zmm(11), ExtraRegisterIdx::zmm(12), ExtraRegisterIdx::zmm(13), ExtraRegisterIdx::zmm(14), ExtraRegisterIdx::zmm(15), ExtraRegisterIdx::zmm(16), ExtraRegisterIdx::zmm(17), ExtraRegisterIdx::zmm(18), ExtraRegisterIdx::zmm(19), ExtraRegisterIdx::zmm(20), ExtraRegisterIdx::zmm(21), ExtraRegisterIdx::zmm(22), ExtraRegisterIdx::zmm(23), ExtraRegisterIdx::zmm(24), ExtraRegisterIdx::zmm(25), ExtraRegisterIdx::zmm(26), ExtraRegisterIdx::zmm(27), ExtraRegisterIdx::zmm(28), ExtraRegisterIdx::zmm(29), ExtraRegisterIdx::zmm(30), ExtraRegisterIdx::zmm(31)];
pub const EXTRA_REGISTERS_EXCEPT_ZMM: [ExtraRegisterIdx; 2] = [ExtraRegisterIdx::mxcsr(), ExtraRegisterIdx::opmask()];

impl Registers {
    pub fn from_ptrace(s: &libc::user_regs_struct) -> Self {
        Registers {
            ints: [s.rax, s.rdx, s.rcx, s.rbx, s.rsi, s.rdi, s.rbp, s.rsp, s.r8, s.r9, s.r10, s.r11, s.r12, s.r13, s.r14, s.r15, s.rip, s.cs, s.ss, s.fs, s.gs, s.fs_base, s.gs_base, s.eflags, s.orig_rax, 0, 0],
            mask: (1u64 << (RegisterIdx::OrigRax as u32 + 1)) - 1,
            dubious_mask: 0,
        }
    }

    // From sigcontext_64, aka libc::mcontext_t.gregs
    pub fn from_context(r: &[i64; 23]) -> Self {
        // TODO: Take FsBase and GsBase from fpstate, it's used for TLS.
        Registers {
            ints: [r[13] as u64, r[12] as u64, r[14] as u64, r[11] as u64, r[9] as u64, r[8] as u64, r[10] as u64, r[15] as u64, r[0] as u64, r[1] as u64, r[2] as u64, r[3] as u64, r[4] as u64, r[5] as u64, r[6] as u64, r[7] as u64, r[16] as u64,
                   r[18] as u64 & 0xffff, (r[18] as u64) >> 48, ((r[18] as u64) >> 32) & 0xffff, ((r[18] as u64) >> 16) & 0xffff, 0, 0, r[17] as u64, 0, 0, 0],
            mask: ((1u64 << (RegisterIdx::Flags as u32 + 1)) - 1) & !(1 << RegisterIdx::FsBase as u32) & !(1 << RegisterIdx::GsBase as u32),
            dubious_mask: 0,
        }
    }

    pub fn set(&mut self, reg: RegisterIdx, val: u64, dubious: bool) {
        self.ints[reg as usize] = val;
        self.mask |= 1u64 << (reg as u32);
        if dubious {
            self.dubious_mask |= 1u64 << (reg as u32);
        }
    }

    pub fn has(&self, reg: RegisterIdx) -> bool {
        self.mask & (1u64 << reg as u32) != 0
    }

    pub fn is_dubious(&self, reg: RegisterIdx) -> bool {
        self.dubious_mask & (1u64 << reg as u32) != 0
    }

    pub fn get(&self, reg: RegisterIdx) -> Result<(u64, /*dubious*/ bool)> {
        if self.mask & (1u64 << reg as u32) == 0 {
            err!(ProcessState, "no {}", reg)
        } else {
            Ok((self.ints[reg as usize], self.is_dubious(reg)))
        }
    }

    pub fn get_option(&self, reg: RegisterIdx) -> Option<(u64, /*dubious*/ bool)> {
        if self.mask & (1u64 << reg as u32) == 0 {
            None
        } else {
            Some((self.ints[reg as usize], self.is_dubious(reg)))
        }
    }
}

// "XSAVE area" is how SSE and AVX registers are laid out, obtained through ptrace(PTRACE_GETREGSET), or NT_X86_XSTATE note in core dump, or fpregs in signal context.
// Format:
//  * 512 bytes - FXSAVE legacy region, ~same layout as user_fpregs_struct,
//  * 64 bytes - XSAVE header, which is a bitmask telling which register sets are present,
//  * ? bytes - extended area, where the available register sets live; the offset and size for each register set can be obtained using instruction CPID.(EAX=0xd, ECX=XFEATURE_*) -> (size=EAX, offset=EBX).
// The highest-offset register set we support is AVX-512 Hi16_ZMM, at offset 1152, containing 16 x 64-byte register values.
const XSAVE_PREFIX_SIZE: usize = 512 + 64;
const XSAVE_XMM_OFFSET: usize = 8 * 20;
const XSAVE_MXCSR_OFFSET: usize = 8 * 3;

const XFEATURE_SSE: u32 = 1;
const XFEATURE_YMM: u32 = 2;
const XFEATURE_OPMASK: u32 = 5;
const XFEATURE_ZMM_HI256: u32 = 6;
const XFEATURE_HI16_ZMM: u32 = 7;

pub const XSAVE_SIZE_UPPER_BOUND: usize = 3072; // expect that all XSAVE components we're interested in are within the first this many bytes; not guaranteed in principle, but should be ok in practice
const XSAVE_YMM_SIZE: usize = 16 * 16;
const XSAVE_OPMASK_SIZE: usize = 8 * 8;
const XSAVE_ZMM_HI256_SIZE: usize = 16 * 32;
const XSAVE_HI16_ZMM_SIZE: usize = 64 * 16;

// Cache the cpuid results, just in case.
static mut CACHED_XSAVE_YMM_OFFSET: usize = 0;
static mut CACHED_XSAVE_OPMASK_OFFSET: usize = 0;
static mut CACHED_XSAVE_ZMM_HI256_OFFSET: usize = 0;
static mut CACHED_XSAVE_HI16_ZMM_OFFSET: usize = 0;
fn precalc_xsave_component_offset(component: u32, expected_size: usize) -> usize {
    let res = unsafe {core::arch::x86_64::__cpuid_count(0xd, component)};
    let (offset, actual_size) = (res.ebx as usize, res.eax as usize);
    if actual_size == 0 || offset == 0 {
        // The CPU doesn't support this instruction set.
        return 0;
    }
    assert!(actual_size >= expected_size, "you seem to have a very weird cpu");
    assert!(offset + expected_size <= XSAVE_SIZE_UPPER_BOUND, "you seem to have a weird cpu, we may need to make a simple change to the debugger to make it work, please report");
    offset
}
pub fn precalc_globals_registers() {
    unsafe {CACHED_XSAVE_YMM_OFFSET = precalc_xsave_component_offset(XFEATURE_YMM, XSAVE_YMM_SIZE)};
    unsafe {CACHED_XSAVE_OPMASK_OFFSET = precalc_xsave_component_offset(XFEATURE_OPMASK, XSAVE_OPMASK_SIZE)};
    unsafe {CACHED_XSAVE_ZMM_HI256_OFFSET = precalc_xsave_component_offset(XFEATURE_ZMM_HI256, XSAVE_ZMM_HI256_SIZE)};
    unsafe {CACHED_XSAVE_HI16_ZMM_OFFSET = precalc_xsave_component_offset(XFEATURE_HI16_ZMM, XSAVE_HI16_ZMM_SIZE)};
}
pub fn xsave_ymm_offset() -> Option<usize> { let r = unsafe {CACHED_XSAVE_YMM_OFFSET}; if r == 0 {None} else {Some(r)} }
pub fn xsave_opmask_offset() -> Option<usize> { let r = unsafe {CACHED_XSAVE_OPMASK_OFFSET}; if r == 0 {None} else {Some(r)} }
pub fn xsave_zmm_hi256_offset() -> Option<usize> { let r = unsafe {CACHED_XSAVE_ZMM_HI256_OFFSET}; if r == 0 {None} else {Some(r)} }
pub fn xsave_hi16_zmm_offset() -> Option<usize> { let r = unsafe {CACHED_XSAVE_HI16_ZMM_OFFSET}; if r == 0 {None} else {Some(r)} }

impl ExtraRegisters {
    pub fn has(&self, idx: ExtraRegisterIdx) -> bool {
        self.mask & (1 << idx.mask_idx()) != 0
    }
    pub fn is_dubious(&self, idx: ExtraRegisterIdx) -> bool {
        self.dubious_mask & (1 << idx.mask_idx()) != 0
    }
    
    pub fn get(&self, idx: ExtraRegisterIdx) -> Result<(&[u64], /*dubious*/ bool)> {
        if !self.has(idx) {
            return if let Some(e) = &self.error {
                Err(e.clone())
            } else {
                err!(ProcessState, "no {}", idx)
            };
        }
        Ok((&self.a[idx.start..idx.start+idx.len], self.is_dubious(idx)))
    }

    pub fn set(&mut self, idx: ExtraRegisterIdx, v: &[u64], dubious: bool) {
        self.mask |= 1 << idx.mask_idx();
        if dubious {
            self.dubious_mask |= 1 << idx.mask_idx();
        }
        self.a[idx.start..idx.start+idx.len].copy_from_slice(v);
    }

    // XSAVE layout:
    //   // Legacy area (512 bytes, same as user_fpregs_struct)
    //   struct fxsave_area { // aka libc::user_fpregs_struct
    //       uint16_t cwd;                     // FPU control word
    //       uint16_t swd;                     // FPU status word
    //       uint16_t twd;                     // Tag word
    //       uint16_t fop;                     // Last instruction opcode
    //       uint64_t rip;                     // Instruction pointer
    //       uint64_t rdp;                     // Data pointer
    //       uint32_t mxcsr;                   // SSE control/status register
    //       uint32_t mxcsr_mask;             // Valid bits in mxcsr
    //       uint8_t st_space[128];           // 8 x87 registers in 80-bit format
    //       uint8_t xmm_space[256];          // 16 128-bit SSE registers
    //       uint8_t padding[48];
    //       uint8_t sw_reserved[48];
    //   };
    //
    //   // XSAVE header (64 bytes, starts at offset 512)
    //   struct xsave_header {
    //       uint64_t xstate_bv;       // States in this frame [bitmask of XSTATE_BIT_* values]
    //       uint64_t xcomp_bv;        // Compaction mode (should be 0 for user space)
    //       uint64_t reserved[6];     // Reserved for future use
    //   };

    // Given the first XSAVE_PREFIX_SIZE bytes, tell how many more bytes to read.
    pub fn calculate_xsave_full_size(prefix: &[u8]) -> Result<(/*suffix_size*/ usize, /*xstate_bv*/ u64)> {
        if prefix.len() < XSAVE_PREFIX_SIZE {
            return err!(ProcessState, "XSAVE prefix too short: {}", prefix.len());
        }
        let xcomp_bv = usize::from_le_bytes(prefix[512+8..512+16].try_into().unwrap());
        if xcomp_bv != 0 {
            return err!(ProcessState, "Unexpected compacted XSAVE state");
        }
        let mut mask = u64::from_le_bytes(prefix[512..512+8].try_into().unwrap());
        let mut n = XSAVE_PREFIX_SIZE;
        for (feat, size, offset) in [
            (XFEATURE_YMM, XSAVE_YMM_SIZE, xsave_ymm_offset()),
            (XFEATURE_OPMASK, XSAVE_OPMASK_SIZE, xsave_opmask_offset()),
            (XFEATURE_ZMM_HI256, XSAVE_ZMM_HI256_SIZE, xsave_zmm_hi256_offset()),
            (XFEATURE_HI16_ZMM, XSAVE_HI16_ZMM_SIZE, xsave_hi16_zmm_offset())] {
            if mask & (1 << feat) != 0 {
                if let Some(off) = offset {
                    n = n.max(off + size);
                } else {
                    mask ^= 1 << feat;
                }
            }
        }
        Ok((n, mask))
    }

    pub fn from_xsave(xsave: &[u8]) -> Self {
        let (full_size, mask) = match Self::calculate_xsave_full_size(xsave) {
            Err(e) => return Self::from_error(e),
            Ok((n, m)) if xsave.len() < n => return Self::from_error(error!(ProcessState, "XSAVE state too short: {} < {}", xsave.len(), n)),
            Ok(x) => x,
        };
        let mut res = Self::default();
        {
            let off = XSAVE_MXCSR_OFFSET;
            let slice = [u32::from_le_bytes(xsave[off..off+4].try_into().unwrap()) as u64];
            res.set(ExtraRegisterIdx::mxcsr(), &slice, /*dubious*/ false);
        }
        if mask & (1 << XFEATURE_SSE) != 0 {
            for i in 0..16 {
                let off = XSAVE_XMM_OFFSET + i*16;
                let slice = [u64::from_le_bytes(xsave[off..off+8].try_into().unwrap()), u64::from_le_bytes(xsave[off+8..off+16].try_into().unwrap())];
                res.set(ExtraRegisterIdx::xmm(i), &slice, /*dubious*/ false);
            }
        }
        if mask & (1 << XFEATURE_YMM) != 0 {
            let start_offset = xsave_ymm_offset().unwrap();
            for i in 0..16 {
                let off = start_offset + i*16;
                let ymm = ExtraRegisterIdx::ymm(i);
                // Upper half of ymm.
                res.a[ymm.start+2] = u64::from_le_bytes(xsave[off..off+8].try_into().unwrap());
                res.a[ymm.start+3] = u64::from_le_bytes(xsave[off+8..off+16].try_into().unwrap());
            }
        }
        if mask & (1 << XFEATURE_OPMASK) != 0 {
            let start_offset = xsave_opmask_offset().unwrap();
            for i in 0..8 {
                let off = start_offset + i*8;
                let slice = [u64::from_le_bytes(xsave[off..off+8].try_into().unwrap())];
                res.set(ExtraRegisterIdx::opmask_element(i), &slice, /*dubious*/ false);
            }
        }
        if mask & (1 << XFEATURE_ZMM_HI256) != 0 {
            let start_offset = xsave_zmm_hi256_offset().unwrap();
            for i in 0..16 {
                let off = start_offset + i*32;
                let zmm = ExtraRegisterIdx::zmm(i);
                res.a[zmm.start+4] = u64::from_le_bytes(xsave[off..off+8].try_into().unwrap());
                res.a[zmm.start+5] = u64::from_le_bytes(xsave[off+8..off+16].try_into().unwrap());
                res.a[zmm.start+6] = u64::from_le_bytes(xsave[off+16..off+24].try_into().unwrap());
                res.a[zmm.start+7] = u64::from_le_bytes(xsave[off+24..off+32].try_into().unwrap());
            }
        }
        if mask & (1 << XFEATURE_HI16_ZMM) != 0 {
            let start_offset = xsave_hi16_zmm_offset().unwrap();
            // (This loop should just be a memcpy, but I don't feel like fighting llvm right now.)
            for i in 0..16 {
                let off = start_offset + i*64;
                let zmm = ExtraRegisterIdx::zmm(16 + i);
                for j in 0..8 {
                    res.a[zmm.start + j] = u64::from_le_bytes(xsave[off+j*8..off+j*8+8].try_into().unwrap());
                }
            }
        }
        res
    }

    pub fn from_error(e: Error) -> Self { Self {error: Some(e), ..Self::default()} }
}

impl LazyExtraRegisters {
    pub fn reset_with_tid(&mut self, tid: pid_t) {
        self.tid.replace(Some(tid));
    }
    pub fn set_error(&mut self, e: Error) {
        *self.r.get_mut() = ExtraRegisters::from_error(e);
        self.tid.replace(None);
    }
    pub fn set(&mut self, r: ExtraRegisters) {
        *self.r.get_mut() = r;
        self.tid.replace(None);
    }

    // Gets the registers from ptrace on first call. Not thread safe.
    pub fn get<'a>(&'a self) -> &'a ExtraRegisters {
        if let Some(tid) = self.tid.take() {
            let r = ptrace_get_extra_regs(tid);
            unsafe {self.r.get().write(r);}
        }
        unsafe {&*(self.r.get() as *const ExtraRegisters)}
    }
}
impl Default for LazyExtraRegisters {
    fn default() -> Self { Self {r: UnsafeCell::new(ExtraRegisters::from_error(error!(Internal, "extra registers not initialized"))), tid: Cell::new(None)} }
}
