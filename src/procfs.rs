use crate::{*, error::*, elf::*, util::*, log::*, os::*};
use std::io::{BufReader, BufRead};
use std::{fs, fs::File, os::fd::{OwnedFd, AsRawFd}, str::FromStr, ops::Range, cmp::Ordering, collections::HashSet, mem::MaybeUninit, sync::Arc};
use bitflags::*;
use libc::{pid_t, c_void};

#[derive(Eq, PartialEq, Ord, PartialOrd, Hash, Default, Clone, Debug)]
pub struct BinaryLocator {
    pub path: String,
    // Inode number, to notice if binary version doesn't match, e.g. if it was recompiled.
    // Doesn't notice if the file was modified in place, but that hardly ever happens in practice.
    // For vdso, this is pid instead of inode.
    // 0 if unknown.
    pub inode: u64,

    // If it's an executable segment not backed by an ELF file.
    pub special: SpecialSegmentId,
}
impl BinaryLocator {
    // When a BinaryLocator is saved and loaded across debugger restarts, we don't want to save inode number or vdso address, because they may change (e.g. if the binary was recompiled).
    // So a loaded BinaryLocator is "incomplete" and needs to be searched in the list of loaded binaries at runtime.
    pub fn save_state_incomplete(&self, out: &mut Vec<u8>) -> Result<()> {
        out.write_str(&self.path)?;
        out.write_u8(self.special.is_vdso() as u8)?;
        Ok(())
    }
    pub fn load_state_incomplete(inp: &mut &[u8]) -> Result<Self> {
        Ok(Self {path: inp.read_str()?, inode: 0, special: if inp.read_u8()? == 1 {SpecialSegmentId::Vdso(0..0)} else {SpecialSegmentId::None}})
    }
    pub fn matches_incomplete(&self, incomplete: &BinaryLocator) -> bool {
        (&self.path, self.special.is_vdso()) == (&incomplete.path, incomplete.special.is_vdso())
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum SpecialSegmentId {
    None,
    Vdso(Range<usize>), // in process's address space
}
impl Default for SpecialSegmentId { fn default() -> Self { Self::None } }
impl Ord for SpecialSegmentId {
    fn cmp(&self, other: &Self) -> Ordering {
        let key = |s: &Self| -> [usize; 3] { match s { Self::None => [0; 3], Self::Vdso(r) => [1, r.start, r.end] } };
        key(self).cmp(&key(other))
    }
}
impl PartialOrd for SpecialSegmentId { fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) } }
impl SpecialSegmentId {
    fn is_vdso(&self) -> bool { match self { Self::Vdso(_) => true, _ => false } }
}

// VMA from /proc/<pid>/maps . (This codebase uses the word "mmap" or "map" instead of "VMA" because I didn't know what they're called, sorry, feel free to rename.)
#[derive(Clone, Debug)]
pub struct MemMapInfo {
    pub start: usize,
    pub len: usize,
    pub perms: MemMapPermissions,
    pub offset: usize,
    pub inode: u64,
    pub path: Option<String>,

    // If this mapping appears to be an executable or shared library.
    pub binary_locator: Option<BinaryLocator>,
    pub binary_id: Option<usize>, // if added to SymbolsRegistry
    pub elf_seen: bool, // CoreDumpMemorySource was updated to point to the loaded binary, if needed
}

bitflags! { pub struct MemMapPermissions: u8 {
        const READ = 0b00001;
        const WRITE = 0b00010;
        const EXECUTE = 0b00100;
        const SHARED = 0b01000;
        const PRIVATE = 0b10000;
}}

// Information from /proc/[pid]/maps
#[derive(Default, Clone)]
pub struct MemMapsInfo {
    pub maps: Vec<MemMapInfo>, // sorted by address
}

// ELF file contains virtual memory addresses for segments. But actual addresses at which segments are mapped at runtime (by the ELF loader) may be different, especially for dynamic libraries (PIC).
// We'll call these "static" vs "dynamic" addresses. This struct is responsible for mapping between the two.
// We expect that the difference between dynamic and static addresses is consistent across all sections that we care about (.text, .data, etc).
// So, the "mapping" is just one number that needs to be added/subtracted. (It gets a whole struct because it turned out more convenient this way, and in case this mapping turns out to be more complex on other platforms.)
// This offset could also be taken from link_map in r_debug rendezvous struct, but why rely on that.
// We assume that all executable mmaps backed by ELF files are created by the ELF loader, not e.g. by the program itself.
// (Maybe the correct word is "relocated" addresses instead of "dynamic"?)
#[derive(Clone)]
pub struct AddrMap {
    // `dynamic - static`. May be "negative", use wrapping_add.
    pub diff: usize,
    known: bool,
    // If different executable sections are offset by a different amount, this is set to false, so that we can show some warning in the UI or something.
    // Not to be confused with the difference between address and file offset - this difference may be different for different sections, we make no assumptions about that.
    // We currently only look at executable sections here, but the offset needs to be consistent for non-executable sections too, e.g. .text and .data must have the same offset;
    // if this assumption is violated, we won't notice.
    consistent: bool,
}
impl Default for AddrMap { fn default() -> Self { Self {diff: 0, known: false, consistent: true} } }
impl AddrMap {
    pub fn update(&mut self, map: &MemMapInfo, elf: &ElfFile, /* just for logging */ path: &str) {
        match &map.binary_locator.as_ref().unwrap().special {
            SpecialSegmentId::None => (),
            SpecialSegmentId::Vdso(range) => {
                self.diff = range.start;
                self.known = true;
                return;
            }
        }
        if !map.perms.contains(MemMapPermissions::WRITE) {
            // Don't look at non-executable maps as they often include things like:
            //  * the program mmapping itself for introspection,
            //  * some special sections loaded at different offsets, e.g. .iplt
            return;
        }
        let mut idx = elf.section_by_offset.partition_point(|t| t.0 < map.offset);
        while idx < elf.section_by_offset.len() && elf.section_by_offset[idx].1 <= map.offset + map.len {
            let s = &elf.sections[elf.section_by_offset[idx].2];
            if s.section_type != SHT_PROGBITS || s.flags & SHF_EXECINSTR == 0 {
                idx += 1;
                continue;
            }
            let diff = map.start.wrapping_sub(map.offset).wrapping_sub(s.address.wrapping_sub(s.offset));
            if !self.known {
                self.diff = diff;
                self.known = true;
            } else if diff != self.diff && self.consistent {
                eprintln!("warning: inconsistent address differences between sections: section {} has diff 0x{:x}, some other section has diff 0x{:x} in {}", s.name, diff, self.diff, path);
                self.consistent = false;
            }
            idx += 1;
        }
    }

    pub fn static_to_dynamic(&self, s: usize) -> usize {
        s.wrapping_add(self.diff)
    }

    pub fn dynamic_to_static(&self, d: usize) -> usize {
        d.wrapping_sub(self.diff)
    }
}

impl MemMapsInfo {
    pub fn read_proc_maps(pid: pid_t) -> Result<MemMapsInfo> {
        let reader = BufReader::new(File::open(format!("/proc/{}/maps", pid))?);
        let mut res: Vec<MemMapInfo> = Vec::new();
        for line in reader.lines() {
            let line = line?;

            // The last field of the line is path. It can contain spaces (including trailing).
            // So we can't just use line.split_whitespace() (SplitWhitespace.remainder() is currently nightly-only).
            // We also can't just use splitn(5) because it doesn't skip repeated spaces.
            // We also can't just re-concatenate split_whitespace() trailing tokens because that loses repeated and trailing spaces in path.

            let mut s = line.trim_start().splitn(2, ' ');
            let (range, rest) = (s.next(), s.next());
            if rest.is_none() { return err!(Format, "too few fields"); }

            let mut s = range.unwrap().splitn(2, '-');
            let (start, end) = (s.next(), s.next());
            if end.is_none() { return err!(Format, "bad range"); }
            let start = usize::from_str_radix(start.unwrap(), 16)?;
            let end = usize::from_str_radix(end.unwrap(), 16)?;

            let mut s = rest.unwrap().trim_start().splitn(2, ' ');
            let (perms, rest) = (s.next(), s.next());
            if rest.is_none() { return err!(Format, "too few fields"); }
            let mut permissions = MemMapPermissions::empty();
            for ch in perms.unwrap().chars() {
                match ch {
                    'r' => permissions.insert(MemMapPermissions::READ),
                    'w' => permissions.insert(MemMapPermissions::WRITE),
                    'x' => permissions.insert(MemMapPermissions::EXECUTE),
                    's' => permissions.insert(MemMapPermissions::SHARED),
                    'p' => permissions.insert(MemMapPermissions::PRIVATE),
                    _ => (),
                }
            }

            let mut s = rest.unwrap().trim_start().splitn(2, ' ');
            let (offset, rest) = (s.next(), s.next());
            if rest.is_none() { return err!(Format, "too few fields"); }
            let offset = usize::from_str_radix(offset.unwrap(), 16)?;

            let mut s = rest.unwrap().trim_start().splitn(2, ' ');
            let (_dev, rest) = (s.next(), s.next());
            if rest.is_none() { return err!(Format, "too few fields"); }

            let mut s = rest.unwrap().trim_start().splitn(2, ' ');
            let (inode, rest) = (s.next(), s.next());
            if inode.is_none() { return err!(Format, "too few fields"); }
            let inode = u64::from_str_radix(inode.unwrap(), 10)?;

            let path = match rest {
                None => None,
                Some(p) => match p.trim_start() {
                    "" => None,
                    p => Some(p.to_string()),
                }
            };

            res.push(MemMapInfo {start, len: end - start, perms: permissions, offset, inode, path, binary_locator: None, binary_id: None, elf_seen: false});
        }

        res.sort_by_key(|m| m.start);

        let mut r = MemMapsInfo {maps: res};
        r.detect_executables(pid);

        Ok(r)
    }

    // Guess which files are executables and assign binary_locator for all their maps.
    pub fn detect_executables(&mut self, pid: pid_t) {
        let mut executables: HashSet<BinaryLocator> = HashSet::new();
        for m in &mut self.maps {
            if let Some(p) = &m.path {
                if p == "[vdso]" && m.perms.contains(MemMapPermissions::EXECUTE) {
                    m.binary_locator = Some(BinaryLocator {path: p.clone(), inode: pid as u64, special: SpecialSegmentId::Vdso(m.start..m.start+m.len)});
                } else if !p.is_empty() && !p.starts_with('[') {
                    // If the executable file was deleted (e.g. recompiled), /proc/maps shows its filename as "/path/to/executable (deleted)". Discard this suffix.
                    // It's also possible that the executable is named literally "/path/to/executable (deleted)" and not deleted - we'll fail to find it in this case;
                    // AFAICT there's no reliable way to distinguish these cases (but we may try harder if needed, e.g. check if this file exists; it'll always be vulnerable to race conditions with renaming the file).
                    let path = p.strip_suffix(" (deleted)").unwrap_or(p).to_string();
                    m.binary_locator = Some(BinaryLocator {path, inode: m.inode, special: SpecialSegmentId::None});
                }
                // We currently ignore executable anon (p.is_empty()) mappings, e.g. JITted code.
            }
            if m.perms.contains(MemMapPermissions::EXECUTE) {
                if let Some(id) = &m.binary_locator {
                    executables.insert(id.clone());
                }
            }
        }

        // Unset binary_locator for files that have no executable maps - they're probably mmapped data files rather than executables.
        // For files that are mapped as executable at least once, leave binary_locator for all, including non-executable ones (e.g. .rodata).
        for m in &mut self.maps {
            if let Some(id) = &m.binary_locator {
                if !executables.contains(id) {
                    m.binary_locator = None;
                }
            }
        }
    }

    pub fn list_binaries(&self) -> Vec<BinaryLocator> {
        let mut v: Vec<(usize, &BinaryLocator)> = Vec::new();
        for i in 0..self.maps.len() {
            let id = match &self.maps[i].binary_locator {
                None => continue,
                Some(i) => i };
            v.push((i, id));
        }
        v.sort_by_key(|t| t.1);
        v.dedup_by_key(|t| t.1);
        v.sort_by_key(|(i, _)| *i);
        v.iter().map(|t| t.1).cloned().collect()
    }

    pub fn addr_to_map(&self, addr: usize) -> Option<&MemMapInfo> {
        let idx = self.maps.partition_point(|m| m.start + m.len <= addr);
        if idx < self.maps.len() && self.maps[idx].start <= addr {
            Some(&self.maps[idx])
        } else {
            None
        }
    }

    pub fn clear(&mut self) { self.maps.clear(); }
}

// Thing for reading debuggee's memory, either from a running process or from core dump.
// Copyable for convenience, even though it adds extra Arc dereference when reading from core dump.
#[derive(Clone)]
pub enum MemReader {
    Invalid,
    Pid(PidMemReader),
    CoreDump(Arc<CoreDumpMemReader>),
}
impl MemReader {
    pub fn check_valid(&self) -> Result<()> { match &self {Self::Invalid => err!(ProcessState, "no process"), _ => Ok(())} }

    pub fn read_uninit<'a>(&self, offset: usize, buf: &'a mut [MaybeUninit<u8>]) -> Result<&'a mut [u8]> {
        match self {
            Self::Invalid => return err!(ProcessState, "no process"),
            Self::Pid(r) => return r.read_uninit(offset, buf),
            Self::CoreDump(r) => return r.read_uninit(offset, buf),
        }
    }

    pub fn read(&self, offset: usize, buf: &mut [u8]) -> Result<()> {
        unsafe {self.read_uninit(offset, std::slice::from_raw_parts_mut(buf.as_mut_ptr() as *mut MaybeUninit<u8>, buf.len()))}?;
        Ok(())
    }

    pub fn read_u64(&self, offset: usize) -> Result<u64> {
        let mut buf = [0u8; 8];
        self.read(offset, &mut buf)?;
        Ok(u64::from_le_bytes(buf))
    }

    pub fn read_u8(&self, offset: usize) -> Result<u8> {
        let mut buf = [0u8; 1];
        self.read(offset, &mut buf)?;
        Ok(buf[0])
    }
}

#[derive(Clone)]
pub struct PidMemReader {
    pid: pid_t,
}
impl PidMemReader {
    pub fn new(pid: pid_t) -> Self { PidMemReader {pid: pid} }

    pub fn read_uninit<'a>(&self, addr: usize, buf: &'a mut [MaybeUninit<u8>]) -> Result<&'a mut [u8]> {
        unsafe {
            let local_iov = libc::iovec {iov_base: buf.as_mut_ptr() as *mut c_void, iov_len: buf.len()};
            let mut remote_iov = libc::iovec {iov_base: addr as *mut c_void, iov_len: buf.len()};
            let r = libc::process_vm_readv(self.pid, &local_iov as *const libc::iovec, 1, &mut remote_iov as *mut libc::iovec, 1, 0);
            if r < 0 {
                if *libc::__errno_location() == libc::EFAULT {
                    return err!(ProcessState, "bad address: 0x{:x}", addr); // shorter message for common error (e.g. null pointer dereference in watch expression)
                } else {
                    return errno_err!("process_vm_readv failed");
                }
            }
            if r != buf.len() as isize {
                // "Partial transfers apply at the granularity of iovec elements.  These system calls won't perform a partial transfer that splits  a  single  iovec  element."
                return err!(ProcessState, "unexpected EOF in mem @{:x}:0x{:x}", addr, buf.len());
            }
            Ok(std::slice::from_raw_parts_mut(buf.as_mut_ptr() as *mut u8, buf.len()))
        }
    }
}

const PAGE_SIZE: usize = 4096;

// Reads debuggee's memory, caches last read page. Good for sequential small reads.
pub struct CachedMemReader {
    pub mem: MemReader,
    addr: Option<usize>,
    page: [MaybeUninit<u8>; PAGE_SIZE],
}
impl CachedMemReader {
    pub fn new(mem: MemReader) -> Self { Self {mem, addr: None, page: unsafe {MaybeUninit::uninit().assume_init()}} }

    pub fn read_uninit<'a>(&mut self, mut offset: usize, mut buf: &'a mut [MaybeUninit<u8>]) -> Result<&'a mut [u8]> {
        if buf.is_empty() {
            return Ok(&mut []);
        }
        if buf.len() > usize::MAX - offset {
            return err!(Runtime, "bad memory range: 0x{:x} + 0x{:x}", offset, buf.len());
        }
        let last_page = (offset + buf.len() - 1) & !(PAGE_SIZE - 1);
        // Read non-last pages without populating cache.
        while offset & !(PAGE_SIZE - 1) < last_page {
            let start = offset & (PAGE_SIZE - 1);
            let len = PAGE_SIZE - start;
            if &self.addr == &Some(offset & !(PAGE_SIZE - 1)) {
                buf[..len].copy_from_slice(&self.page[start..start+len]);
            } else {
                self.mem.read_uninit(offset, &mut buf[..len])?;
            }
            buf = &mut buf[len..];
            offset += len;
        }
        // Read last page through cache.
        if &self.addr != &Some(last_page) {
            self.addr = None;
            self.mem.read_uninit(last_page, &mut self.page)?;
            self.addr = Some(last_page);
        }
        let start = offset & (PAGE_SIZE - 1);
        buf.copy_from_slice(&self.page[start..start + buf.len()]);
        Ok(unsafe {std::slice::from_raw_parts_mut(buf.as_mut_ptr() as *mut u8, buf.len())})
    }

    pub fn read(&mut self, offset: usize, buf: &mut [u8]) -> Result<()> {
        unsafe {self.read_uninit(offset, std::slice::from_raw_parts_mut(buf.as_mut_ptr() as *mut MaybeUninit<u8>, buf.len()))}?;
        Ok(())
    }

    pub fn read_u8(&mut self, offset: usize) -> Result<u8> {
        if &self.addr == &Some(offset & !(PAGE_SIZE - 1)) {
            // Fast path.
            return Ok(unsafe {self.page[offset & (PAGE_SIZE - 1)].assume_init()});
        }
        let mut buf = [0u8; 1];
        self.read(offset, &mut buf)?;
        Ok(buf[0])
    }
    pub fn read_u16(&mut self, offset: usize) -> Result<u16> {
        let mut buf = [0u8; 2];
        self.read(offset, &mut buf)?;
        Ok(u16::from_le_bytes(buf))
    }
    pub fn read_u32(&mut self, offset: usize) -> Result<u32> {
        let mut buf = [0u8; 4];
        self.read(offset, &mut buf)?;
        Ok(u32::from_le_bytes(buf))
    }
    pub fn read_usize(&mut self, offset: usize) -> Result<usize> {
        let mut buf = [0u8; 8];
        self.read(offset, &mut buf)?;
        Ok(usize::from_le_bytes(buf))
    }

    pub fn eat_uleb128(&mut self, offset: &mut usize) -> Result<usize> {
        Ok(self.leb128_impl(offset)?.0)
    }
    pub fn eat_sleb128(&mut self, offset: &mut usize) -> Result<isize> {
        let (mut res, byte, shift) = self.leb128_impl(offset)?;
        if byte & 0x40 != 0 && shift < 64 {
            res |= !0 << shift;
        }
        Ok(res as isize)
    }
    fn leb128_impl(&mut self, offset: &mut usize) -> Result<(usize, u8, u32)> {
        let mut res = 0usize;
        let mut byte: u8;
        let mut shift = 0u32;
        loop {
            byte = self.read_u8(*offset)?;
            *offset += 1;
            res |= (byte as usize & 0x7f) << shift;
            shift += 7;
            if byte & 0x80 == 0 {
                break;
            }
            if shift >= 64 {
                return err!(Sanity, "uleb128 too long");
            }
        }
        Ok((res, byte, shift))
    }

    pub fn read_null_terminated(&mut self, mut offset: usize, limit: usize) -> Result<(Vec<u8>, /*terminated*/ bool)> {
        let mut chunk_size = 1usize << 7;
        let mut res: Vec<u8> = Vec::new();
        let mut terminated = false;
        while res.len() < limit {
            let n = (offset & !(chunk_size - 1)) + chunk_size - offset;
            let n = n.min(limit - res.len());
            let start = res.len();
            res.resize(start + n, 0);
            // We assume that each aligned 4 KiB range is either fully readable or fully unreadable.
            self.read(offset, &mut res[start..])?;
            if let Some(i) = res[start..].iter().position(|c| *c == 0) {
                res.truncate(start + i);
                terminated = true;
                break;
            }
            offset += n;
            if n == chunk_size && chunk_size < PAGE_SIZE {
                chunk_size <<= 1;
            }
        }
        Ok((res, terminated))
    }
}

pub fn peak_memory_usage_of_current_process() -> Result<usize> {
    let reader = BufReader::new(File::open("/proc/self/status")?);
    for line in reader.lines() {
        let line = line?;
        let mut s = line.split_whitespace();
        let name = s.next();
        if name != Some("VmHWM:") {
            continue;
        }
        let (number, unit, extra) = (s.next(), s.next(), s.next());
        if let Some(x) = extra {
            return err!(Format, "unexpected tokens in VmHWM line: {}", x);
        }
        if unit != Some("kB") {
            return err!(Format, "unexpected unit in VmHWM line: {}", unit.unwrap_or("<none>"));
        }
        let number = usize::from_str(number.unwrap())?;
        return Ok(number << 10);
    }
    err!(Format, "No VmHWM line")
}

// Contents of /proc/[pid]/stat
pub struct ProcStat {
    comm: [u8; 33], // length, then bytes
    pub state: char,
    pub utime: usize, // in _SC_CLK_TCK units
    pub stime: usize,
    rss: usize, // in pages
}
impl Default for ProcStat { fn default() -> Self { Self {comm: [0; 33], state: '?', utime: 0, stime: 0, rss: 0} } }
impl ProcStat {
    pub fn parse(path: &str, prof: &mut ProfileBucket) -> Result<ProcStat> {
        let timer = TscScope::new();
        let line = std::fs::read_to_string(path)?;
        prof.syscall_count += 1;
        prof.syscall_tsc += timer.finish();

        // We panic if parsing fails. The data comes from the kernel, not from a real file, so it should always be valid.

        let open_paren = line.char_indices().find(|(_, c)| *c == '(').unwrap().0;
        let close_paren = line.char_indices().rev().find(|(_, c)| *c == ')').unwrap().0;
        let mut comm = [0u8; 33];
        let comm_len = (close_paren - open_paren - 1).min(comm.len() - 1);
        comm[1..1+comm_len].copy_from_slice(&line.as_bytes()[open_paren+1..open_paren+1+comm_len]);
        comm[0] = comm_len as u8;

        let mut tokens = line[close_paren+1..].split_whitespace();

        let state = tokens.next().unwrap();
        assert!(state.len() == 1);
        let state = state.chars().next().unwrap();

        let utime = usize::from_str(tokens.nth(10).unwrap())?;
        let stime = usize::from_str(tokens.nth(0).unwrap())?;
        let rss = usize::from_str(tokens.nth(8).unwrap())?;

        Ok(ProcStat {comm, state, utime, stime, rss})
    }

    // Thread name.
    pub fn comm(&self) -> &str {
        std::str::from_utf8(&self.comm[1..1+self.comm[0] as usize]).unwrap() // valid by construction
    }

    pub fn rss_bytes(&self) -> usize {
        self.rss * sysconf_PAGE_SIZE()
    }
}

pub fn list_threads(pid: pid_t) -> Result<Vec<pid_t>> {
    let mut r: Vec<pid_t> = Vec::new();
    for entry in fs::read_dir(format!("/proc/{}/task/", pid))? {
        let entry = entry?;
        r.push(pid_t::from_str(&entry.file_name().into_string().unwrap()).unwrap());
    }
    Ok(r)
}
