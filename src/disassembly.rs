use crate::{*, symbols::*, error::*, symbols_registry::*, util::*, procfs::*, settings::*, common_ui::*};
use std::{fmt::Write, ops::Range, collections::HashSet};
use iced_x86::*;

pub const MAX_X86_INSTRUCTION_BYTES: usize = 15;

// Disassembled function - a sequence of lines.
// For each line, a prefix is formatted by the UI on the fly (with some dynamic elements), a suffix is pre-formatted (in `text`).
//
// Example:
//  text                                                        DisassemblyLineKind       leaf_line   subfunction_idx
//
//  /usr/lib/x86_64-linux-gnu/libc.so.6                         Intro
//  dwarf offset: 0x1bee14                                      Intro
//                                                              Intro
//                         futex-internal.c:138:1               LeafLineNumber            138
//  7ffff7c91030 <  +0>    endbr64                              Instruction               138
//  7ffff7c91034 <  +4>    push r13                             Instruction               138
//  7ffff7c91036 <  +6>    mov r13d,esi                         Instruction               138
//                         futex-internal.c:138:1               LeafLineNumber            138
//  7ffff7c91039 <  +9>    push r12                             Instruction               138
//  7ffff7c9103b <  +b>    push rbx                             Instruction               138
//  7ffff7c9103c <  +c>    sub rsp,20h                          Instruction               138
//                         futex-internal.c:139:10              InlinedCallLineNumber     139         
//                         __futex_abstimed_wait_common         InlinedFunctionName       139
//                         ┆futex-internal.c:77:6               LeafLineNumber            77          42 (or whatever the idx of this inlined __futex_abstimed_wait_common is)
//  7ffff7c91040 < +10>    ┆test rcx,rcx                        Instruction               77          42
//  7ffff7c91043 < +13>  ↓ ┆jne near _+100h                     Instruction               77          42
//                         ┆futex-internal.c:80:6               LeafLineNumber            80          42
//  7ffff7c91049 < +19>    ┆cmp edx,1                           Instruction               80          42

pub struct Disassembly {
    pub text: StyledText,
    pub lines: Vec<DisassemblyLineInfo>, // parallel to `text` lines
    pub error: Option<Error>, // also baked into `lines`

    pub max_abs_relative_addr: usize,
    pub indent_width: usize,
    pub widest_line: usize,

    // Don't want to hold an Arc<Symbols> here, we look it up in SymbolsRegistry every frame. This shard_idx is just to assert that we found the correct one (so `subfunction` indices will match).
    pub symbols_shard: Option<usize>,
}

// Information about one line of text in the disassembly listing.
pub struct DisassemblyLineInfo {
    pub kind: DisassemblyLineKind,

    //  7ffff7c91043 < +13>  ↓ ┆jne near _+100h
    //  ^^^^^^^^^^^^   ^^^   ^  ^^^^^^^^^^^^^^^
    // static_addr     |     | |     `text`
    //     relative_addr     | |
    //          jump_indicator |
    //         subfunction_level

    // Address of the current or next instruction. For Intro: 0. For Error: usize::MAX. Binary-searchable. Should be rendered only for DisassemblyLineKind::Instruction.
    pub static_addr: usize,

    pub relative_addr: isize,
    pub jump_indicator: char,
    pub jump_target: Option<usize>,
    pub is_statement: bool,

    // Line number for the current or previous LeafLineNumber or InlinedCallLineNumber.
    pub leaf_line: Option<LineInfo>,
    // Innermost inlined function containing this line. For InlinedCallLineNumber and InlinedCallFunctionName: the *parent* subfunction (if any). Level always >= 1.
    pub subfunction: Option<usize>,
    pub subfunction_level: u16, // `subfunction` level, 0 if None; indentation level
}
impl Default for DisassemblyLineInfo { fn default() -> Self { Self {kind: DisassemblyLineKind::Error, static_addr: 0, relative_addr: 0, jump_indicator: ' ', jump_target: None, is_statement: false, subfunction_level: 0, leaf_line: None, subfunction: None} } }

#[derive(Clone, Copy, Eq, PartialEq, Debug)]
pub enum DisassemblyLineKind {
    Intro,
    InlinedCallLineNumber,
    InlinedFunctionName,
    LeafLineNumber,
    Instruction,
    Separator,
    Error,
}

impl Disassembly {
    pub fn new() -> Self { Self {text: StyledText::default(), lines: Vec::new(), error: None, max_abs_relative_addr: 0, indent_width: 1, widest_line: 0, symbols_shard: None} }

    pub fn static_addr_to_line(&self, static_addr: usize) -> Option<usize> {
        let idx = self.lines.partition_point(|l| l.static_addr <= static_addr);
        if idx > 0 && self.lines[idx-1].static_addr == static_addr && self.lines[idx-1].kind == DisassemblyLineKind::Instruction {
            Some(idx-1)
        } else {
            None
        }
    }

    // If pseudo_addr is in between instructions, round down to the previous instruction.
    // If pseudo_addr is out of range, return either first or last line (whichever is closed), with `found` = false.
    pub fn static_pseudo_addr_to_line(&self, static_pseudo_addr: usize) -> (usize, /*found*/ bool) {
        let idx = self.lines.partition_point(|l| l.static_addr <= static_pseudo_addr);
        if idx == 0 { return (0, false); }
        let l = &self.lines[idx-1];
        // (Would be better to compare to function addr ranges instead of the MAX_X86_INSTRUCTION_BYTES guesswork.)
        if l.kind == DisassemblyLineKind::Instruction && l.static_addr + MAX_X86_INSTRUCTION_BYTES > static_pseudo_addr {
            (idx-1, true)
        } else {
            (idx-1, false)
        }
    }

    pub fn with_error(mut self, e: Error, palette: &Palette) -> Self {
        assert!(self.error.is_none());
        styled_writeln!(self.text, palette.error, "{}", e);
        self.lines.push(DisassemblyLineInfo {kind: DisassemblyLineKind::Error, static_addr: usize::MAX, ..Default::default()});
        self.error = Some(e);
        self.finish()
    }

    pub fn finish(mut self) -> Self {
        assert_eq!(self.text.num_lines(), self.lines.len());
        for i in 0..self.lines.len() {
            self.widest_line = self.widest_line.max(self.lines[i].subfunction_level as usize * self.indent_width + str_width(self.text.get_line_str(i)));
            self.max_abs_relative_addr = self.max_abs_relative_addr.max(self.lines[i].relative_addr.abs() as usize);
        }
        self
    }
}

struct StyledFormatter<'a> {
    palette: &'a Palette,
    text: &'a mut StyledText,
}

impl<'a> FormatterOutput for StyledFormatter<'a> {
    fn write(&mut self, text: &str, kind: FormatterTextKind) {
        use FormatterTextKind::*;
        let s = match kind {
            Directive | Keyword => self.palette.disas_keyword,
            Prefix | Mnemonic => self.palette.disas_mnemonic,
            Register => self.palette.disas_register,
            Number => self.palette.disas_number,
            Function => self.palette.disas_function,
            _ => self.palette.disas_default,
        };

        self.text.chars.push_str(text);
        self.text.close_span(s);
    }
}

struct Resolver<'a> {
    symbols: Option<&'a Symbols>,
    current_function: core::ops::Range<usize>,
}

impl<'a> SymbolResolver for Resolver<'a> {
    fn symbol(&mut self, _: &Instruction, _operand: u32, _instruction_operand: Option<u32>, static_addr: u64, _address_size: u32) -> Option<SymbolResult<'a>> {
        let static_addr = static_addr as usize;
        if self.current_function.contains(&static_addr) {
            // Make jumps inside current function easier to read: "_+42h" instead of "__futex_abstimed_wait_cancelable64+42h".
            return Some(SymbolResult {address: self.current_function.start as u64, text: SymResTextInfo::new("_", FormatterTextKind::Function), flags: SymbolFlags::NONE, symbol_size: Some(MemorySize::UInt64)});
        }

        if let Some(symbols) = &self.symbols {
            if let Ok((f, _)) = symbols.addr_to_function(static_addr) {
                let name = f.demangle_name();
                let text = SymResString::String(name);
                return Some(SymbolResult {address: f.addr.addr().unwrap() as u64, text: SymResTextInfo::Text(SymResTextPart {text, color: FormatterTextKind::Function}), flags: SymbolFlags::NONE, symbol_size: Some(MemorySize::UInt64)});
            }
        }
        None
    }
}

pub fn disassemble_function(function_idx: usize, static_addr_ranges: Vec<Range<usize>>, symbols: &Symbols, intro: StyledText, palette: &Palette) -> Disassembly {
    disassemble_addr_ranges(Some((function_idx, symbols)), static_addr_ranges, None, intro, palette)
}

pub fn disassemble_memory(range: Range<usize>, code: &[u8], intro: StyledText, palette: &Palette) -> Disassembly {
    disassemble_addr_ranges(None, vec![range], Some(code), intro, palette)
}

fn disassemble_addr_ranges(function: Option<(usize, &Symbols)>, mut addr_ranges: Vec<Range<usize>>, memory_code: Option<&[u8]>, intro: StyledText, palette: &Palette) -> Disassembly {
    clean_up_ranges(&mut addr_ranges);

    let mut res = Disassembly {text: intro, lines: Vec::new(), error: None, max_abs_relative_addr: 0, indent_width: str_width(&palette.tree_indent.0), widest_line: 0, symbols_shard: None};
    let mut subfunc_idxs: Vec<Range<usize>> = Vec::new();
    let mut subfunctions: &[Subfunction] = &[];
    let mut seen_subfunction_identities: HashSet<u32> = HashSet::new();

    while res.lines.len() < res.text.num_lines() {
        res.lines.push(DisassemblyLineInfo {kind: DisassemblyLineKind::Intro, static_addr: 0, ..Default::default()});
    }

    if let Some((function_idx, symbols)) = function {
        let function = &symbols.functions[function_idx];
        res.symbols_shard = Some(function.shard_idx());
        subfunc_idxs = (1..function.num_levels()).map(|i| symbols.subfunction_idxs_at_level(i, function)).collect();
        subfunctions = &symbols.shards[function.shard_idx()].subfunctions;
    }

    for (addr_range_idx, static_addr_range) in addr_ranges.iter().enumerate() {
        if static_addr_range.len() > 100_000_000 {
            return res.with_error(error!(Sanity, "{} MB to disassemble, suspiciously much", static_addr_range.len() / 1_000_000), palette);
        }

        let code: &[u8] = if let Some(code) = memory_code {
            assert_eq!(addr_ranges.len(), 1);
            code
        } else if let Some((_, symbols)) = function {
            // Read the machine code from file rather than memory so that it doesn't show our breakpoint instructions.
            match symbols.elves[0].addr_range_to_offset_range(static_addr_range.start, static_addr_range.end) {
                None => return res.with_error(error!(Dwarf, "function address range out of bounds of executable: {:x}-{:x}", static_addr_range.start, static_addr_range.end), palette),
                Some((start, end)) => &symbols.elves[0].data()[start..end],
            }
        } else {
            panic!("huh");
        };

        if addr_range_idx != 0 {
            styled_write!(res.text, palette.disas_default,  "──────────");
            res.text.close_line();
            res.lines.push(DisassemblyLineInfo {kind: DisassemblyLineKind::Separator, static_addr: static_addr_range.start, ..Default::default()});
        }

        let resolver = Resolver {symbols: function.map(|(_, symbols)| symbols), current_function: static_addr_range.clone()};
        // NasmFormatter wants to own the symbol resolver for some reason. (Probably it would be too inconvenient or inefficient to have lifetime argument all throughout the formatter implementation.)
        // We trust that the SymbolResolver reference isn't retained after the formatter is destroyed, so it should be ok to fudge the lifetime here.
        let resolver: Resolver<'static> = unsafe { std::mem::transmute(resolver) };

        let mut decoder = Decoder::with_ip(64, code, static_addr_range.start as u64, DecoderOptions::NONE);
        let mut formatter = NasmFormatter::with_options(Some(Box::new(resolver)), None);

        let mut line_iter = if let Some((_, symbols)) = function {
            let mut line_iter = symbols.addr_to_line_iter(static_addr_range.start).peekable();
            line_iter.next_if(|line| line.addr() < static_addr_range.start);
            Some(line_iter)
        } else {
            None
        };

        let mut instruction = Instruction::default();
        let mut prev_static_addr = 0usize;
        let mut cur_leaf_line: Option<LineInfo> = None;

        while decoder.can_decode() {
            decoder.decode_out(&mut instruction);

            if let Some(l) = res.lines.last() {
                assert!(instruction.ip() as usize >= l.static_addr); // can be == because the "-----[...]" separator above is assigned to address of the first instruction after it
            }
            let static_addr = instruction.ip() as usize;
            let mut subfunction_level = 0u16;
            let mut cur_subfunction: Option<usize> = None;
            let mut is_statement = false;

            if let Some((function_idx, symbols)) = function {
                let write_line_number = |line: LineInfo, kind: DisassemblyLineKind, res: &mut Disassembly, subfunction_level: u16, leaf_line: &mut Option<LineInfo>, subfunction: Option<usize>| {
                    let file = match line.file_idx() {
                        None => return,
                        Some(f) => f };
                    *leaf_line = Some(line.clone());
                    let file = &symbols.files[file];
                    let name = file.filename.as_os_str().to_string_lossy();
                    styled_write!(res.text, palette.disas_filename, "{}", name);
                    if line.line() != 0 {
                        styled_write!(res.text, palette.line_number, ":{}", line.line());
                        if line.column() != 0 {
                            styled_write!(res.text, palette.column_number, ":{}", line.column());
                        }
                    }
                    res.text.close_line();
                    res.lines.push(DisassemblyLineInfo {kind, static_addr, subfunction_level, leaf_line: leaf_line.clone(), subfunction, ..Default::default()});
                };

                // Add inlined function calls information: function names, call line numbers, and indentation.
                let function = &symbols.functions[function_idx];
                for r in subfunc_idxs.iter_mut() {
                    while r.start < r.end && subfunctions[r.start].addr_range.end <= static_addr {
                        r.start += 1;
                    }
                    if r.start == r.end || subfunctions[r.start].addr_range.start > static_addr {
                        break;
                    }
                    cur_subfunction = Some(r.start);
                    let subfunction = &subfunctions[r.start];
                    subfunction_level += 1;
                    if subfunction.addr_range.start > prev_static_addr {
                        let callee_name = if subfunction.callee_idx == usize::MAX {
                            "?".to_string()
                        } else {
                            symbols.functions[subfunction.callee_idx].demangle_name()
                        };

                        write_line_number(subfunction.call_line.clone(), DisassemblyLineKind::InlinedCallLineNumber, &mut res, subfunction_level, &mut cur_leaf_line, cur_subfunction.clone());

                        styled_write!(res.text, palette.default_dim, "{}", callee_name);

                        if !seen_subfunction_identities.insert(subfunction.identity) {
                            // Indicate that the inlined function has multiple address ranges.
                            styled_write!(res.text, palette.default_dim, " [cont]");
                        }
                        res.text.close_line();
                        res.lines.push(DisassemblyLineInfo {kind: DisassemblyLineKind::InlinedFunctionName, static_addr, subfunction_level, leaf_line: cur_leaf_line.clone(), subfunction: cur_subfunction.clone(), ..Default::default()});
                    }
                }

                // Add line number information.
                while let Some(line) = line_iter.as_mut().unwrap().next_if(|line| line.addr() <= static_addr) {
                    write_line_number(line, DisassemblyLineKind::LeafLineNumber, &mut res, subfunction_level, &mut cur_leaf_line, cur_subfunction.clone());

                    if line.addr() == static_addr && line.flags().contains(LineFlags::STATEMENT) {
                        is_statement = true;
                    }
                }
            }

            prev_static_addr = static_addr;

            let mut jump_target: Option<usize> = None;
            let jump_indicator = match instruction.flow_control() {
                FlowControl::Next => ' ',
                FlowControl::Return => '←',
                FlowControl::Call | FlowControl::IndirectCall => '→',
                FlowControl::Interrupt | FlowControl::XbeginXabortXend | FlowControl::Exception => '!',
                FlowControl::UnconditionalBranch | FlowControl::IndirectBranch | FlowControl::ConditionalBranch => {
                    let target_known = instruction.flow_control() != FlowControl::IndirectBranch && match instruction.op0_kind() {
                        iced_x86::OpKind::NearBranch16 | iced_x86::OpKind::NearBranch32 | iced_x86::OpKind::NearBranch64 => true,
                        _ => false };
                    if !target_known {
                        '↕'
                    } else {
                        jump_target = Some(instruction.near_branch_target() as usize);
                        if instruction.near_branch_target() > instruction.ip() {
                            '↓'
                        } else {
                            '↑'
                        }
                    }
                }
            };

            // Finally write the actual asm instruction.
            formatter.format(&instruction, &mut StyledFormatter {palette, text: &mut res.text});

            res.text.close_line();
            res.lines.push(DisassemblyLineInfo {kind: DisassemblyLineKind::Instruction, static_addr, relative_addr: static_addr as isize - static_addr_range.start as isize, subfunction_level, jump_indicator, jump_target, is_statement, leaf_line: cur_leaf_line.clone(), subfunction: cur_subfunction.clone()});
        }
    }
    res.finish()
}

/// Finds a unique candidate instruction stream at or before `ip`.
/// `ip` is assumed to be a real instruction pointer, so candidates are kept only
/// if decoding from them reaches `ip` as an instruction start.
///
/// This probes candidate stream starts near `probe_start`, up to one maximum x86
/// instruction length away. `probe_len` bounds the accepted probe window, but the
/// caller is expected to advance `probe_start` when it wants to test later starts.
pub fn find_unique_instruction_start_before_ip(code: &[u8], range_start: usize, probe_start: usize, probe_len: usize, ip: usize) -> Option<usize> {
    let range_end = range_start.saturating_add(code.len());
    if probe_start < range_start || probe_start >= range_end || ip < probe_start || ip >= range_end || probe_len == 0 {
        return None;
    }
    let last_probe_start = probe_start.saturating_add(probe_len).min(range_end - 1);
    let last_start = ip.min(last_probe_start);
    if last_start < probe_start {
        return None;
    }

    let mut found = None;
    let initial_last_start = probe_start.saturating_add(MAX_X86_INSTRUCTION_BYTES - 1).min(last_start);
    for start in probe_start..=initial_last_start {
        let mut decoder = Decoder::with_ip(64, &code[start - range_start..], start as u64, DecoderOptions::NONE);
        while decoder.can_decode() {
            let instruction = decoder.decode();
            if instruction.is_invalid() || instruction.len() == 0 {
                break;
            }
            let instruction_start = instruction.ip() as usize;
            if instruction_start == ip {
                if found.is_some() {
                    return None;
                }
                found = Some(start);
                break;
            }
            if instruction_start > ip {
                break;
            }
        }
    }
    found
}

pub fn find_best_instruction_start_before_addr(code: &[u8], range_start: usize, probe_start: usize, probe_len: usize, addr: usize, ip_anchor: Option<usize>) -> Option<usize> {
    let range_end = range_start.saturating_add(code.len());
    if probe_start < range_start || probe_start >= range_end || addr < probe_start || addr >= range_end {
        return None;
    }
    let ip_anchor = ip_anchor.filter(|ip| range_start <= *ip && *ip < range_end);
    if probe_len == 0 {
        return None;
    }
    let last_probe_start = probe_start.saturating_add(probe_len).min(range_end - 1);

    let first_start = addr.saturating_sub(MAX_X86_INSTRUCTION_BYTES - 1).max(probe_start);
    let last_start = addr.min(last_probe_start);
    if first_start > last_start {
        return None;
    }
    let mut best: Option<(usize, usize)> = None; // (decoded_until, instruction_start)

    for start in first_start..=last_start {
        let mut decoder = Decoder::with_ip(64, &code[start - range_start..], start as u64, DecoderOptions::NONE);
        let instruction = decoder.decode();
        if instruction.is_invalid() || instruction.len() == 0 {
            continue;
        }
        let instruction_start = instruction.ip() as usize;
        let instruction_end = instruction_start.saturating_add(instruction.len());
        if instruction_start <= addr && addr < instruction_end {
            let mut decoded_until = instruction_end;
            let mut saw_ip_anchor = ip_anchor.map_or(true, |ip| instruction_start == ip);
            while decoder.can_decode() && decoded_until < range_end {
                let instruction = decoder.decode();
                if instruction.is_invalid() || instruction.len() == 0 {
                    break;
                }
                if ip_anchor == Some(instruction.ip() as usize) {
                    saw_ip_anchor = true;
                }
                decoded_until = instruction.ip().saturating_add(instruction.len() as u64) as usize;
            }
            // If we know nearby RIP, use it as a hard instruction-boundary anchor: real execution
            // can only stop at instruction starts, which disambiguates many valid-but-wrong x86 decodes.
            if !saw_ip_anchor {
                continue;
            }

            // Prefer the stream that remains valid the longest; if alternatives converge equally far,
            // use the earliest start so manual `g` can recover from landing inside a real instruction.
            if best.map_or(true, |(best_until, best_start)| decoded_until > best_until || decoded_until == best_until && instruction_start < best_start) {
                best = Some((decoded_until, instruction_start));
            }
        }
    }
    best.map(|(_, instruction_start)| instruction_start)
}

fn clean_up_ranges(ranges: &mut Vec<Range<usize>>) {
    if ranges.is_empty() {
        return;
    }
    ranges.sort_unstable_by_key(|r| r.start);
    let mut j = 0;
    for i in 1..ranges.len() {
        if ranges[i].start > ranges[j].end {
            // Normal case.
            j += 1;
            ranges[j] = ranges[i].clone();
        } else if ranges[i].end <= ranges[j].end {
            // This range is contained in another. Discard.
        } else {
            // This range overlaps another. Extend.
            ranges[j].end = ranges[i].end;
        }
    }
    ranges.truncate(j+1);
}

#[cfg(test)]
mod tests {
    use super::*;

    const BASE: usize = 0x1000;

    struct UniqueStartCase {
        name: &'static str,
        code: &'static [u8],
        range_start: usize,
        probe_start: usize,
        probe_len: usize,
        ip: usize,
        expected: Option<usize>,
    }

    struct BestStartCase {
        name: &'static str,
        code: &'static [u8],
        range_start: usize,
        probe_start: usize,
        probe_len: usize,
        addr: usize,
        ip_anchor: Option<usize>,
        expected: Option<usize>,
    }

    const UNIQUE_RET: &[u8] = &[0x0f, 0x0f, 0x0f, 0x0f, 0xc3];
    const LONG_NOP_THEN_RET: &[u8] = &[
        // 14 operand-size prefixes + nop: every suffix ending at 0x90 is also a viable instruction.
        0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
        0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x90,
        0xc3,
    ];
    const JIT_HELLO_PREFIX: &[u8] = &[
        0xb8, 0x01, 0x00, 0x00, 0x00,             // mov eax, 1
        0xbf, 0x01, 0x00, 0x00, 0x00,             // mov edi, 1
        0x48, 0x8d, 0x35, 0x08, 0x00, 0x00, 0x00, // lea rsi, [rip+8]
        0xba, 0x0c, 0x00, 0x00, 0x00,             // mov edx, 12
        0x0f, 0x05,                               // syscall
        0xc3,                                     // ret
    ];

    #[test]
    fn find_unique_instruction_start_before_ip_cases() {
        let cases = [
            UniqueStartCase {
                name: "address_at_probe_start",
                code: JIT_HELLO_PREFIX,
                range_start: BASE,
                probe_start: BASE,
                probe_len: JIT_HELLO_PREFIX.len(),
                ip: BASE,
                expected: Some(BASE),
            },
            UniqueStartCase {
                name: "unique_anchored_stream",
                code: &[
                    0x0f, 0x0f, 0x0f, 0x0f, 0x0f, 0x0f, 0x0f,
                    0x0f, 0x0f, 0x0f, 0x0f, 0x0f, 0x0f, 0x0f,
                    0xc3, 0xc3, 0xc3, 0xc3, 0xc3, 0xc3, 0xc3,
                ],
                range_start: BASE,
                probe_start: BASE,
                probe_len: 21,
                ip: BASE + 20,
                expected: Some(BASE + 14),
            },
            UniqueStartCase {
                name: "does_not_scan_whole_probe_window",
                code: &[
                    0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc,
                    0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc,
                    0x0f, 0x05, 0xc3,
                ],
                range_start: BASE,
                probe_start: BASE,
                probe_len: 19,
                ip: BASE + 18,
                expected: None,
            },
            UniqueStartCase {
                name: "single_byte_instruction_stream_is_ambiguous",
                code: &[0x90, 0x90, 0x90, 0x90, 0xc3],
                range_start: BASE,
                probe_start: BASE,
                probe_len: 5,
                ip: BASE + 4,
                expected: None,
            },
            UniqueStartCase {
                name: "prefix_chain_is_ambiguous",
                code: LONG_NOP_THEN_RET,
                range_start: BASE,
                probe_start: BASE,
                probe_len: LONG_NOP_THEN_RET.len(),
                ip: BASE + 15,
                expected: None,
            },
            UniqueStartCase {
                name: "anchor_filters_unanchored_candidate",
                code: &[0x0f, 0x1f, 0x40, 0x00, 0xc3],
                range_start: BASE,
                probe_start: BASE,
                probe_len: 5,
                ip: BASE + 4,
                expected: None,
            },
            UniqueStartCase {
                name: "multiple_anchored_candidates_are_ambiguous",
                code: &[0x90, 0x0f, 0x05, 0xc3],
                range_start: BASE,
                probe_start: BASE,
                probe_len: 4,
                ip: BASE + 3,
                expected: None,
            },
            UniqueStartCase {
                name: "probe_before_range",
                code: UNIQUE_RET,
                range_start: BASE,
                probe_start: BASE - 1,
                probe_len: UNIQUE_RET.len(),
                ip: BASE + 4,
                expected: None,
            },
            UniqueStartCase {
                name: "probe_after_range",
                code: UNIQUE_RET,
                range_start: BASE,
                probe_start: BASE + UNIQUE_RET.len(),
                probe_len: 1,
                ip: BASE + 4,
                expected: None,
            },
            UniqueStartCase {
                name: "zero_len_probe",
                code: UNIQUE_RET,
                range_start: BASE,
                probe_start: BASE,
                probe_len: 0,
                ip: BASE + 4,
                expected: None,
            },
        ];

        for case in cases {
            let found = find_unique_instruction_start_before_ip(case.code, case.range_start, case.probe_start, case.probe_len, case.ip);
            assert_eq!(case.expected, found, "{}", case.name);
        }
    }

    #[test]
    fn find_best_instruction_start_before_addr_cases() {
        let cases = [
            BestStartCase {
                name: "address_inside_instruction",
                code: &[0x0f, 0x05],
                range_start: BASE,
                probe_start: BASE,
                probe_len: 1,
                addr: BASE + 1,
                ip_anchor: None,
                expected: Some(BASE),
            },
            BestStartCase {
                name: "jit_mov_eax_one_prefers_real_stream_without_anchor",
                code: JIT_HELLO_PREFIX,
                range_start: BASE,
                probe_start: BASE,
                probe_len: JIT_HELLO_PREFIX.len(),
                addr: BASE + 1,
                ip_anchor: None,
                expected: Some(BASE),
            },
            BestStartCase {
                name: "jit_mov_eax_one_uses_ip_anchor",
                code: JIT_HELLO_PREFIX,
                range_start: BASE,
                probe_start: BASE,
                probe_len: JIT_HELLO_PREFIX.len(),
                addr: BASE + 1,
                ip_anchor: Some(BASE),
                expected: Some(BASE),
            },
            BestStartCase {
                name: "jit_mov_eax_one_rejects_wrong_ip_anchor",
                code: JIT_HELLO_PREFIX,
                range_start: BASE,
                probe_start: BASE,
                probe_len: JIT_HELLO_PREFIX.len(),
                addr: BASE + 1,
                ip_anchor: Some(BASE + 1),
                expected: Some(BASE + 1),
            },
            BestStartCase {
                name: "anchor_before_candidate_window_rejects_all_candidates",
                code: &[0x90, 0x90, 0x0f, 0x05],
                range_start: BASE,
                probe_start: BASE,
                probe_len: 4,
                addr: BASE + 3,
                ip_anchor: Some(BASE),
                expected: None,
            },
            BestStartCase {
                name: "address_at_instruction_start",
                code: UNIQUE_RET,
                range_start: BASE,
                probe_start: BASE,
                probe_len: UNIQUE_RET.len(),
                addr: BASE + 4,
                ip_anchor: None,
                expected: Some(BASE + 4),
            },
            BestStartCase {
                name: "address_in_following_instruction",
                code: UNIQUE_RET,
                range_start: BASE,
                probe_start: BASE,
                probe_len: UNIQUE_RET.len(),
                addr: BASE + 4,
                ip_anchor: None,
                expected: Some(BASE + 4),
            },
            BestStartCase {
                name: "single_byte_stream_chooses_only_containing_start",
                code: &[0x90, 0x90, 0x90, 0x90, 0xc3],
                range_start: BASE,
                probe_start: BASE,
                probe_len: 5,
                addr: BASE + 2,
                ip_anchor: None,
                expected: Some(BASE + 2),
            },
            BestStartCase {
                name: "prefix_chain_tie_chooses_earliest_start",
                code: LONG_NOP_THEN_RET,
                range_start: BASE,
                probe_start: BASE,
                probe_len: LONG_NOP_THEN_RET.len(),
                addr: BASE + 14,
                ip_anchor: None,
                expected: Some(BASE),
            },
            BestStartCase {
                name: "prefix_chain_ret_chooses_ret",
                code: LONG_NOP_THEN_RET,
                range_start: BASE,
                probe_start: BASE,
                probe_len: LONG_NOP_THEN_RET.len(),
                addr: BASE + 15,
                ip_anchor: None,
                expected: Some(BASE + 15),
            },
            BestStartCase {
                name: "address_after_stream",
                code: UNIQUE_RET,
                range_start: BASE,
                probe_start: BASE,
                probe_len: UNIQUE_RET.len(),
                addr: BASE + UNIQUE_RET.len(),
                ip_anchor: None,
                expected: None,
            },
        ];

        for case in cases {
            let found = find_best_instruction_start_before_addr(case.code, case.range_start, case.probe_start, case.probe_len, case.addr, case.ip_anchor);
            assert_eq!(case.expected, found, "{}", case.name);
        }
    }
}
