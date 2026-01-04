use crate::{*, error::*, log::*, os::*};
use libc::{pid_t, c_char, c_void};
use std::{io, io::{Read, BufReader, BufRead, Write}, str::FromStr, ptr, mem, mem::{ManuallyDrop, MaybeUninit}, fmt, fmt::Write as fmtWrite, os::fd::{RawFd, AsRawFd}, ffi::{CStr, OsString, CString}, os::unix::ffi::{OsStringExt, OsStrExt}, arch::asm, cell::UnsafeCell, sync::atomic::{AtomicBool, Ordering}, ops::{Deref, DerefMut, FnOnce}, fs::File, collections::{BinaryHeap, hash_map::DefaultHasher}, hash::{Hash, Hasher}, cmp::Ord, cmp, path::{Path, PathBuf}, slice};

pub unsafe fn ptrace(request: i32, pid: pid_t, addr: u64, data: u64) -> Result<i64> {
    (*libc::__errno_location()) = 0;
    let r = profile_syscall!(libc::ptrace(request as _, pid, addr, data));
    //eprintln!("trace: ptrace({}, {}, 0x{:x}, 0x{:x}) -> 0x{:x}", ptrace_request_name(request), pid, addr, data, r);
    if r == -1 {
        if (*libc::__errno_location()) != 0 {
            return errno_err!("ptrace({}, {}, {}, {}) failed", ptrace_request_name(request), pid, addr, data);
        }
        assert!([PTRACE_PEEKDATA, PTRACE_PEEKSIGINFO, PTRACE_PEEKTEXT, PTRACE_PEEKUSER].contains(&request));
    }
    Ok(r)
}

// Epoll fd. Closed in destructor.
pub struct Epoll {
    fd: i32,
}

impl Epoll {
    pub fn new() -> Result<Epoll> {
        unsafe {
            let fd = libc::epoll_create1(0);
            if fd < 0 { return errno_err!("epoll_create1(0) failed"); }
            Ok(Epoll {fd: fd})
        }
    }

    // (This is very basic and not rust-like: no RAII to automatically remove fds, no const/mut distinction. None of these things seem useful for this project, and I care about amout of code more than about conforming to rust's style of doing things.)
    pub fn add(&self, fd: i32, events: i32, data: u64) -> Result<()> {
        unsafe {
            let mut event = libc::epoll_event {events: events as u32, u64: data};
            let r = libc::epoll_ctl(self.fd, libc::EPOLL_CTL_ADD, fd, &mut event);
            if r != 0 { return errno_err!("epoll_ctl(EPOLL_CTL_ADD) failed"); }
        }
        Ok(())
    }

    pub fn modify(&self, fd: i32, events: i32, data: u64) -> Result<()> {
        unsafe {
            let mut event = libc::epoll_event {events: events as u32, u64: data};
            let r = libc::epoll_ctl(self.fd, libc::EPOLL_CTL_MOD, fd, &mut event);
            if r != 0 { return errno_err!("epoll_ctl(EPOLL_CTL_MOD) failed"); }
        }
        Ok(())
        
    }

    pub fn del(&self, fd: i32) -> Result<()> {
        unsafe {
            let r = libc::epoll_ctl(self.fd, libc::EPOLL_CTL_DEL, fd, ptr::null_mut());
            if r != 0 { return errno_err!("epoll_ctl(EPOLL_CTL_DEL) failed"); }
        }
        Ok(())
    }

    // Returns Ok(0) on EINTR.
    pub fn wait(&self, out: &mut [libc::epoll_event]) -> Result<usize> {
        unsafe {
            let r = libc::epoll_wait(self.fd, out.as_mut_ptr(), out.len() as i32, -1);
            if r < 0 {
                if *libc::__errno_location() == libc::EINTR {
                    return Ok(0);
                }
                return errno_err!("epoll_wait() failed");
            }
            Ok(r as usize)
        }
    }
}

impl Drop for Epoll {
    fn drop(&mut self) {
        unsafe {
            let r = libc::close(self.fd);
            if r != 0 { eprintln!("warning: close() failed on epoll fd: {:?}", io::Error::last_os_error()); }
        }
    }
}

pub struct TimerFD {
    pub fd: i32,
}
impl TimerFD {
    pub fn new() -> Self {
        let fd = unsafe {libc::timerfd_create(libc::CLOCK_MONOTONIC, libc::TFD_CLOEXEC | libc::TFD_NONBLOCK)};
        if fd < 0 { panic!("timerfd_create() failed: {:?}", io::Error::last_os_error()); }
        Self {fd}
    }

    pub fn set(&self, value_ns: usize, interval_ns: usize) -> usize {
        const NANO: usize = 1000_000_000;
        let to_timespec = |ns| libc::timespec {tv_sec: (ns / NANO) as i64, tv_nsec: (ns % NANO) as i64};
        let v = libc::itimerspec {it_value: to_timespec(value_ns), it_interval: to_timespec(interval_ns)};
        let mut prev: libc::itimerspec = unsafe {std::mem::zeroed()};
        let r = unsafe {libc::timerfd_settime(self.fd, 0, &v as *const libc::itimerspec, &mut prev as *mut libc::itimerspec)};
        if r != 0 { panic!("timerfd_settime() failed: {:?}", io::Error::last_os_error()); }
        prev.it_value.tv_sec as usize * NANO + prev.it_value.tv_nsec as usize
    }

    pub fn read(&self) -> usize {
        loop {
            let mut res = 0usize;
            let r = unsafe {libc::read(self.fd, &mut res as *mut usize as *mut libc::c_void, 8)};
            if r < 0 && io::Error::last_os_error().kind() == io::ErrorKind::Interrupted {
                continue;
            }
            // Once in a blue moon it fails with errno 11 (WOULDBLOCK). Idk why, guess timerfd just can cause spurious epoll wakeups. Let's ignore it.
            if r < 0 && io::Error::last_os_error().kind() == io::ErrorKind::WouldBlock {
                return 0;
            }
            if r != 8 { panic!("read() from timerfd returned {}: {:?}", r, io::Error::last_os_error()); }
            return res;
        }
    }
}
impl Drop for TimerFD {
    fn drop(&mut self) {
        unsafe {
            let r = libc::close(self.fd);
            if r != 0 { eprintln!("warning: close() failed on timer fd: {:?}", io::Error::last_os_error()); }
        }
    }
}

pub struct EventFD {
    pub fd: i32,
}
impl EventFD {
    pub fn new() -> Self {
        let fd = unsafe {libc::eventfd(0, libc::EFD_CLOEXEC | libc::EFD_NONBLOCK)};
        if fd < 0 { panic!("eventfd() failed: {:?}", io::Error::last_os_error()); }
        Self {fd}
    }

    pub fn read(&self) -> usize {
        loop {
            let mut res = 0usize;
            let r = unsafe {libc::read(self.fd, &mut res as *mut usize as *mut libc::c_void, 8)};
            if r < 0 && io::Error::last_os_error().kind() == io::ErrorKind::Interrupted {
                continue;
            }
            if r != 8 { panic!("read() from eventfd returned {}: {:?}", r, io::Error::last_os_error()); }
            return res;
        }
    }

    pub fn write(&self, v: usize) {
        loop {
            let r = unsafe {libc::write(self.fd, &v as *const usize as *const libc::c_void, 8)};
            if r < 0 && io::Error::last_os_error().kind() == io::ErrorKind::Interrupted {
                continue;
            }
            if r != 8 { panic!("write() to eventfd returned {}: {:?}", r, io::Error::last_os_error()); }
            break;
        }
    }
}
impl Drop for EventFD {
    fn drop(&mut self) {
        unsafe {
            let r = libc::close(self.fd);
            if r != 0 { eprintln!("warning: close() failed on event fd: {:?}", io::Error::last_os_error()); }
        }
    }
}

pub struct INotifyFD {
    pub fd: i32,
}
impl INotifyFD {
    pub fn new() -> Result<Self> {
        let fd = unsafe {libc::inotify_init1(libc::IN_NONBLOCK | libc::IN_CLOEXEC)};
        if fd < 0 {
            return Err(io::Error::last_os_error().into());
        }
        Ok(Self {fd})
    }

    pub fn add_watch(&self, path: &Path, mask: u32) -> Result<i32> {
        let c_path = CString::new(path.as_os_str().as_bytes()).unwrap();
        let r = unsafe {libc::inotify_add_watch(self.fd, c_path.as_ptr() as *const i8, mask)};
        if r < 0 {
            return Err(io::Error::last_os_error().into());
        }
        Ok(r)
    }

    pub fn read(&self) -> Vec<(libc::inotify_event, /*name*/ Vec<u8>)> {
        let mut res: Vec<(libc::inotify_event, Vec<u8>)> = Vec::new();
        loop {
            let mut buf: [mem::MaybeUninit<u8>; 8192] = unsafe {mem::MaybeUninit::uninit().assume_init()};
            let r = unsafe {libc::read(self.fd, buf.as_mut_ptr() as *mut libc::c_void, buf.len())};
            if r < 0 {
                let e = io::Error::last_os_error();
                match e.kind() {
                    io::ErrorKind::Interrupted => continue,
                    io::ErrorKind::WouldBlock => break,
                    _ => panic!("read() from inotify fd returned {}: {:?}", r, e),
                }
            }
            if r == 0 {
                break;
            }
            let mut slice = unsafe {slice::from_raw_parts(buf.as_ptr() as *const u8, r as usize)};
            while !slice.is_empty() {
                let sizeof = mem::size_of::<libc::inotify_event>();
                // man inotify: "Each successful read(2) returns a buffer containing one or more of the following structures".
                if slice.len() < sizeof {
                    panic!("read() from inotify fd returned only {} bytes", slice.len());
                }
                let mut ev: libc::inotify_event;
                unsafe {
                    ev = mem::zeroed();
                    std::ptr::copy_nonoverlapping(slice.as_ptr() as *const u8, &mut ev as *mut libc::inotify_event as *mut u8, sizeof);
                }
                slice = &slice[sizeof..];
                let name_len = ev.len as usize;
                if name_len > slice.len() {
                    panic!("inotify_event has len = {}, but only {} more bytes were returned by read()", name_len, slice.len());
                }
                let n = slice[..name_len].iter().position(|c| *c == 0u8).unwrap_or(name_len);
                let name = slice[..n].to_owned();
                res.push((ev, name));
                slice = &slice[name_len..];
            }
        }
        res
    }
}
impl Drop for INotifyFD {
    fn drop(&mut self) {
        unsafe {
            let r = libc::close(self.fd);
            if r != 0 { eprintln!("warning: close() failed on inotify fd: {:?}", io::Error::last_os_error()); }
        }
    }
}

// A thing for limiting the number of warnings printed from each line of source code.
// Usage: if limiter.check(line!()) { eprintln!("warning: ...") }
pub struct Limiter {
    count_by_line: Vec<u16>,
}

impl Limiter {
    pub fn new() -> Self { Self {count_by_line: Vec::new()} }

    // Allow one per line.
    pub fn check(&mut self, line: u32) -> bool {
        self.check_n(line, 1)
    }

    // Allow n per line.
    pub fn check_n(&mut self, line: u32, n: u16) -> bool {
        let idx = line as usize;
        if idx >= self.count_by_line.len() {
            self.count_by_line.resize(idx + 1, 0);
        }
        if self.count_by_line[idx] < n {
            self.count_by_line[idx] += 1;
            true
        } else {
            false
        }        
    }
}

#[repr(align(128))]
pub struct CachePadded<T> {
    pub t: T,
}

impl<T> CachePadded<T> {
    pub fn new(t: T) -> Self { Self {t: t} }
    pub fn into_inner(self) -> T { self.t }
}
unsafe impl<T: Send> Send for CachePadded<T> {}
unsafe impl<T: Sync> Sync for CachePadded<T> {}
impl<T> Deref for CachePadded<T> { type Target = T; fn deref(&self) -> &T { &self.t } }
impl<T> DerefMut for CachePadded<T> { fn deref_mut(&mut self) -> &mut T { &mut self.t } }
impl<T> From<T> for CachePadded<T> { fn from(t: T) -> Self { CachePadded::new(t) } }

pub struct ScopeGuard<F: FnOnce()> { f: ManuallyDrop<F> }
impl<F: FnOnce()> ScopeGuard<F> { pub fn new(f: F) -> Self { Self {f: ManuallyDrop::new(f)} } }
impl<T: FnOnce()> Drop for ScopeGuard<T> { fn drop(&mut self) { (unsafe {ManuallyDrop::take(&mut self.f)})(); } }
#[macro_export]
macro_rules! defer { ($($t:tt)*) => { let _guard = ScopeGuard::new(|| { $($t)* }); }; }

// Prints numbers with a few digits of precision and optional K/M/G suffix, e.g. "42", "12.4K", "123M".
pub struct PrettyCount(pub usize);
impl fmt::Display for PrettyCount {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (den, name) = match self.0 {
            x if x < 1000 => return write!(f, "{}", x),
            x if x < 1000_000 => (1000, "K"),
            x if x < 1000_000_000 => (1000_000, "M"),
            x if x < 1000_000_000_000usize => (1000_000_000, "G"),  
            x if x < 1000_000_000_000_000usize => (1000_000_000_000, "T"),
            x if x < 1000_000_000_000_000_000usize => (1000_000_000_000_000, "P"),
            _ => (1000_000_000_000_000_000usize, "E"),
        };
        // Use at most 4 digits.
        match self.0 as f64 / den as f64 {
            x if x < 9.995 - 1e-12 => write!(f, "{:.2} {}", x, name), // e.g. 1.23
            x if x < 99.95 - 1e-12 => write!(f, "{:.1} {}", x, name), // e.g. 12.3
            x                      => write!(f, "{:.0} {}", x, name), // e.g. 1000
        }
    }
}
impl PrettyCount {
    pub const MAX_LEN: usize = 6;
}

// Prints byte sizes with a few digits of precision and B/KiB/MiB/GiB/TiB suffix, e.g. "42 B", "12.4 KiB".
// The result is at most PrettySize::MAX_LEN characters long.
pub struct PrettySize(pub usize);
impl fmt::Display for PrettySize {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (den, name) = match self.0 {
            x if x < 1usize<<10 => return write!(f, "{} B", x),
            x if x < 1usize<<20 => (1usize<<10, "KiB"),
            x if x < 1usize<<30 => (1usize<<20, "MiB"),
            x if x < 1usize<<40 => (1usize<<30, "GiB"),
            x if x < 1usize<<50 => (1usize<<40, "TiB"),
            x if x < 1usize<<60 => (1usize<<50, "PiB"),
            _              => (1usize<<60, "EiB"),
        };
        // Use at most 4 digits.
        match self.0 as f64 / den as f64 {
            x if x < 9.995 - 1e-12 => write!(f, "{:.2} {}", x, name), // e.g. 1.23
            x if x < 99.95 - 1e-12 => write!(f, "{:.1} {}", x, name), // e.g. 12.3
            x                      => write!(f, "{:.0} {}", x, name), // e.g. 1023
        }
    }
}
impl PrettySize {
    pub const MAX_LEN: usize = 8;
}

pub struct PrettyDuration(pub f64); // seconds
impl fmt::Display for PrettyDuration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (den, name) = match self.0 {
            x if x < 1e-9 => (1e-12, "ps"),
            x if x < 1e-6 => (1e-9, "ns"),
            x if x < 1e-3 => (1e-6, "us"),
            x if x < 1e0 => (1e-3, "ms"),
            x if x < 3600.0 => (1e0, "s"),
            x if x < 3600.0 * 24.0 => (3600.0, "h"),
            x if x < 3600.0 * 24.0 * 7.0 => (3600.0 * 24.0, "d"),
            x if x < 3600.0 * 24.0 * 7.0 * 9999.0 => (3600.0 * 24.0 * 7.0, "w"),
            _ => return write!(f, ">180 y"),
        };
        // Use at most 4 digits.
        match self.0 as f64 / den as f64 {
            x if x < 9.995 - 1e-12 => write!(f, "{:.2} {}", x, name), // e.g. 1.23
            x if x < 99.95 - 1e-12 => write!(f, "{:.1} {}", x, name), // e.g. 12.3
            x                      => write!(f, "{:.0} {}", x, name), // e.g. 1023
        }
    }
}
impl PrettyDuration {
    pub const MAX_LEN: usize = 7;
}

#[derive(Ord, Eq)]
struct MergeIteratorEntry<K: Ord> {
    key: K,
    src: usize,
}
impl<K: Ord> PartialOrd for MergeIteratorEntry<K> { fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> { Some(self.key.cmp(&other.key)) } }
impl<K: Ord> PartialEq for MergeIteratorEntry<K> { fn eq(&self, other: &Self) -> bool { self.key == other.key } }

pub struct MergeIterator<'a, T, K: Ord, F: FnMut(&T) -> K> {
    sources: Vec<&'a [T]>,
    key_func: F,
    heap: BinaryHeap<MergeIteratorEntry<K>>,
}

impl<'a, T, K: Ord, F: FnMut(&T) -> K> MergeIterator<'a, T, K, F> {
    pub fn new(sources: Vec<&'a [T]>, key_func: F) -> Self {
        let mut r = Self {sources, key_func, heap: BinaryHeap::new()};
        for (i, s) in r.sources.iter().enumerate() {
            if !s.is_empty() {
                r.heap.push(MergeIteratorEntry {key: (r.key_func)(&s[0]), src: i});
            }
        }
        r
    }

    pub fn peek(&self) -> Option<&'a T> {
        match self.heap.peek() {
            None => None,
            Some(e) => Some(&self.sources[e.src][0]) }
    }
}

impl<'a, T, K: Ord, F: FnMut(&T) -> K> Iterator for MergeIterator<'a, T, K, F> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let entry = match self.heap.pop() {
            None => return None,
            Some(e) => e };
        let src = &mut self.sources[entry.src];
        let r = &src[0];
        *src = &src[1..];
        if !src.is_empty() {
            self.heap.push(MergeIteratorEntry {key: (self.key_func)(&src[0]), src: entry.src});
        }
        Some(r)
    }
}

// SyncUnsafeCell copied from the nightly standard library.
#[repr(transparent)]
pub struct SyncUnsafeCell<T> { value: UnsafeCell<T> }
unsafe impl<T: Sync> Sync for SyncUnsafeCell<T> {}
impl<T> SyncUnsafeCell<T> {
    pub const fn new(value: T) -> Self { Self { value: UnsafeCell::new(value) } }
    pub fn into_inner(self) -> T { self.value.into_inner() }
    #[inline]
    pub fn get(&self) -> *mut T { self.value.get() }
    #[inline]
    pub fn get_mut(&mut self) -> &mut T { self.value.get_mut() }
}
impl<T> From<T> for SyncUnsafeCell<T> { fn from(t: T) -> SyncUnsafeCell<T> { SyncUnsafeCell::new(t) } }

pub fn hash<T: Hash + ?Sized>(value: &T) -> usize {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish() as usize
}

pub struct HashingBufReader<R: Read> {
    inner: R,
    buf: Vec<u8>,
    filled: usize,
    pos: usize,
    pub hasher: md5::Context,
    pub count: usize,
}
impl<R: Read> HashingBufReader<R> {
    pub fn new(inner: R) -> Self { Self {inner, buf: vec![0u8; 1 << 13], filled: 0, pos: 0, hasher: md5::Context::new(), count: 0} }
}
impl<R: Read> BufRead for HashingBufReader<R> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        if self.pos >= self.filled {
            self.filled = self.inner.read(&mut self.buf)?;
            self.pos = 0;
        }
        Ok(&self.buf[self.pos..self.filled])
    }
    fn consume(&mut self, amt: usize) {
        self.hasher.consume(&self.buf[self.pos..self.pos + amt]);
        self.count += amt;
        self.pos += amt;
    }
}
impl<R: Read> Read for HashingBufReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let b = self.fill_buf()?;
        let n = b.len().min(buf.len());
        buf[..n].copy_from_slice(&b[..n]);
        Ok(n)
    }
}

pub trait ByteRead : BufRead {
    fn read_u8(&mut self) -> io::Result<u8>;
    fn read_u16(&mut self) -> io::Result<u16>;
    fn read_u32(&mut self) -> io::Result<u32>;
    fn read_u64(&mut self) -> io::Result<u64>;
    fn read_usize(&mut self) -> io::Result<usize>;
    fn read_i8(&mut self) -> io::Result<i8>;
    fn read_i16(&mut self) -> io::Result<i16>;
    fn read_i32(&mut self) -> io::Result<i32>;
    fn read_i64(&mut self) -> io::Result<i64>;
    fn read_isize(&mut self) -> io::Result<isize>;
    fn read_bool(&mut self) -> io::Result<bool>;
    fn read_slice(&mut self) -> io::Result<Vec<u8>>;
    fn read_str(&mut self) -> io::Result<String>;
    fn read_path(&mut self) -> io::Result<PathBuf>;
}
impl<R: BufRead> ByteRead for R {
    fn read_u8(&mut self) -> io::Result<u8> { let mut b = [0u8]; self.read_exact(&mut b)?; Ok(b[0]) }
    fn read_u16(&mut self) -> io::Result<u16> { let mut b = [0u8; 2]; self.read_exact(&mut b)?; Ok(u16::from_le_bytes(b)) }
    fn read_u32(&mut self) -> io::Result<u32> { let mut b = [0u8; 4]; self.read_exact(&mut b)?; Ok(u32::from_le_bytes(b)) }
    fn read_u64(&mut self) -> io::Result<u64> { let mut b = [0u8; 8]; self.read_exact(&mut b)?; Ok(u64::from_le_bytes(b)) }
    fn read_usize(&mut self) -> io::Result<usize> { let mut b = [0u8; 8]; self.read_exact(&mut b)?; Ok(usize::from_le_bytes(b)) }
    fn read_i8(&mut self) -> io::Result<i8> { let mut b = [0u8]; self.read_exact(&mut b)?; Ok(b[0] as i8) }
    fn read_i16(&mut self) -> io::Result<i16> { let mut b = [0u8; 2]; self.read_exact(&mut b)?; Ok(i16::from_le_bytes(b)) }
    fn read_i32(&mut self) -> io::Result<i32> { let mut b = [0u8; 4]; self.read_exact(&mut b)?; Ok(i32::from_le_bytes(b)) }
    fn read_i64(&mut self) -> io::Result<i64> { let mut b = [0u8; 8]; self.read_exact(&mut b)?; Ok(i64::from_le_bytes(b)) }
    fn read_isize(&mut self) -> io::Result<isize> { let mut b = [0u8; 8]; self.read_exact(&mut b)?; Ok(isize::from_le_bytes(b)) }
    fn read_bool(&mut self) -> io::Result<bool> {
        let mut b = [0u8];
        self.read_exact(&mut b)?;
        Ok(match b[0] {
            0 => false,
            1 => true,
            x => return Err(io::Error::new(io::ErrorKind::Other, "invalid bool")),
        })
    }
    fn read_slice(&mut self) -> io::Result<Vec<u8>> {
        let n = self.read_usize()?;
        // Don't unconditionally allocate the whole n bytes because it may be huge if the input contains garbage.
        // We could just refuse to read slices longer than e.g. 100 MB, but for no particular reason we're being
        // more permissive and read in chunks until we either complete or reach end of file.
        let block_size = 1usize << 20;
        let mut v: Vec<u8> = Vec::new();
        let mut pos = 0usize;
        while pos < n {
            let add = block_size.min(n - pos);
            v.resize(v.len() + add, 0u8);
            self.read_exact(&mut v[pos..])?;
            pos += add;
        }
        Ok(v)
    }
    fn read_str(&mut self) -> io::Result<String> { let v = self.read_slice()?; String::from_utf8(v).map_err(|e| io::Error::new(io::ErrorKind::Other, e)) }
    fn read_path(&mut self) -> io::Result<PathBuf> { let v = self.read_slice()?; Ok(PathBuf::from(OsString::from_vec(v))) }
}

pub trait ByteWrite : Write {
    fn write_u8(&mut self, x: u8) -> io::Result<()>;
    fn write_u16(&mut self, x: u16) -> io::Result<()>;
    fn write_u32(&mut self, x: u32) -> io::Result<()>;
    fn write_u64(&mut self, x: u64) -> io::Result<()>;
    fn write_usize(&mut self, x: usize) -> io::Result<()>;
    fn write_i8(&mut self, x: i8) -> io::Result<()>;
    fn write_i16(&mut self, x: i16) -> io::Result<()>;
    fn write_i32(&mut self, x: i32) -> io::Result<()>;
    fn write_i64(&mut self, x: i64) -> io::Result<()>;
    fn write_isize(&mut self, x: isize) -> io::Result<()>;
    fn write_bool(&mut self, x: bool) -> io::Result<()>;
    fn write_slice(&mut self, s: &[u8]) -> io::Result<()>;
    fn write_str(&mut self, s: &str) -> io::Result<()>;
    fn write_path(&mut self, s: &Path) -> io::Result<()>;
    fn write_struct<T>(&mut self, s: &T) -> io::Result<()>;
}
impl<R: Write> ByteWrite for R {
    fn write_u8(&mut self, x: u8) -> io::Result<()> { self.write_all(&[x]) }
    fn write_u16(&mut self, x: u16) -> io::Result<()> { self.write_all(&x.to_le_bytes()) }
    fn write_u32(&mut self, x: u32) -> io::Result<()> { self.write_all(&x.to_le_bytes()) }
    fn write_u64(&mut self, x: u64) -> io::Result<()> { self.write_all(&x.to_le_bytes()) }
    fn write_usize(&mut self, x: usize) -> io::Result<()> { self.write_all(&x.to_le_bytes()) }
    fn write_i8(&mut self, x: i8) -> io::Result<()> { self.write_all(&x.to_le_bytes()) }
    fn write_i16(&mut self, x: i16) -> io::Result<()> { self.write_all(&x.to_le_bytes()) }
    fn write_i32(&mut self, x: i32) -> io::Result<()> { self.write_all(&x.to_le_bytes()) }
    fn write_i64(&mut self, x: i64) -> io::Result<()> { self.write_all(&x.to_le_bytes()) }
    fn write_isize(&mut self, x: isize) -> io::Result<()> { self.write_all(&x.to_le_bytes()) }
    fn write_bool(&mut self, x: bool) -> io::Result<()> { self.write_all(&[x as u8]) }
    fn write_slice(&mut self, s: &[u8]) -> io::Result<()> { self.write_usize(s.len())?; self.write_all(s) }
    fn write_str(&mut self, s: &str) -> io::Result<()> { self.write_slice(s.as_bytes()) }
    fn write_path(&mut self, s: &Path) -> io::Result<()> { self.write_slice(s.as_os_str().as_bytes()) }
    fn write_struct<T>(&mut self, s: &T) -> io::Result<()> { unsafe {self.write_all(slice::from_raw_parts(s as *const T as *const u8, mem::size_of::<T>()))} }
}

#[macro_export]
macro_rules! D {
    () => {
        Default::default()
    };
}

pub trait SetMinMax {
    fn set_min(&mut self, other: Self);
    fn set_max(&mut self, other: Self);
}

impl<T: Ord+Copy> SetMinMax for T {
    fn set_min(&mut self, other: Self) {
        *self = std::cmp::min(*self, other);
    }
    fn set_max(&mut self, other: Self) {
        *self = std::cmp::max(*self, other);
    }
}

// copy_from_slice() is very slow for short slices of variable length because it does a function call, so here's a hack to make it a little faster.
// (Maybe we should enforce padding of strings everywhere and then it'll be just a 4-byte load+store.)
#[inline]
pub fn small_memcpy(from: &[u8], to: &mut [u8; 4]) {
    match from.len() {
        1 => to[0] = from[0],
        2 => to[..2].copy_from_slice(from),
        3 => to[..3].copy_from_slice(from),
        4 => to.copy_from_slice(from),
        _ => panic!("unexpected small_memcpy length"),
    }
}

// String's fmt::Write::write_char implementation is slow because it copies the character using variable-length copy_from_slice(), which does non-inlined memcpy call.
// This wrapper works around it.
pub struct FmtString<'a> {
    pub s: &'a mut String,
}
impl<'a> FmtString<'a> {
    pub fn new(s: &'a mut String) -> Self { Self {s} }
}
impl fmt::Write for FmtString<'_> {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.s.push_str(s);
        Ok(())
    }

    #[inline]
    fn write_char(&mut self, c: char) -> fmt::Result {
        unsafe {
            let v = self.s.as_mut_vec();
            let mut buf = [0u8; 4];
            let bp = buf.as_ptr();
            let s = c.encode_utf8(&mut buf);
            assert_eq!(s.as_ptr(), bp);
            v.reserve(4);
            ptr::copy_nonoverlapping(bp, v.spare_capacity_mut().as_ptr() as *mut u8, 4);
            v.set_len(v.len() + s.len());
        }
        Ok(())
    }
}

pub fn hexdump(s: &[u8], lim: usize) -> String {
    let mut r = String::new();
    for x in &s[..lim.min(s.len())] {
        write!(r, "{:02x}", x).unwrap();
    }
    if s.len() > lim {
        write!(r, "… {} more bytes", s.len() - lim).unwrap();
    }
    r
}

pub struct Mmap {
    ptr: *mut libc::c_void,
    file_len: usize,
    mapped_len: usize,
}
impl Mmap {
    // If mapped_len > file_len, ensures the whole mapped_len range is readable (e.g. for simd padding).
    pub fn new(file: &File, file_len: usize, mapped_len: usize) -> Result<Mmap> {
        // First mmap() an anon region for file+padding, then mmap() the file at the same address (remapping the first ~file_len bytes to point to the file instead).
        let anon_map = unsafe {libc::mmap(ptr::null_mut(), mapped_len, libc::PROT_READ, libc::MAP_PRIVATE | libc::MAP_ANONYMOUS, -1, 0)};
        if anon_map == libc::MAP_FAILED { return errno_err!("anon mmap of size {} failed", mapped_len); }
        let file_map = unsafe {libc::mmap(anon_map, file_len, libc::PROT_READ, libc::MAP_PRIVATE | libc::MAP_FIXED, file.as_raw_fd(), 0)};
        if file_map == libc::MAP_FAILED { return errno_err!("failed to mmap file of size {}", file_len); }
        assert_eq!(anon_map, file_map);

        Ok(Mmap {ptr: file_map, file_len, mapped_len})
    }

    pub fn data(&self) -> &[u8] { unsafe {slice::from_raw_parts(self.ptr as *const u8, self.file_len)} }
}
impl Drop for Mmap {
    fn drop(&mut self) {
        unsafe {libc::munmap(self.ptr, self.mapped_len)};
    }
}
unsafe impl Send for Mmap {}
unsafe impl Sync for Mmap {}

pub unsafe fn memcpy_struct<'a, T: Copy>(a: &'a [u8], name: &'static str) -> Result<(T, /*remainder*/ &'a [u8])> {
    let sizeof = mem::size_of::<T>();
    if a.len() < sizeof {
        return err!(MalformedExecutable, "{} too short: {} < {}", name, a.len(), sizeof);
    }
    unsafe {
        let mut t: MaybeUninit<T> = MaybeUninit::uninit();
        ptr::copy_nonoverlapping(a.as_ptr(), &raw mut t as *mut u8, sizeof);
        Ok((t.assume_init(), &a[sizeof..]))
    }
}

// Adapter for voracious_radix_sort's questionable API.
// Example:
//   // at global scope:
//   radix_sort_key!(Foo, FooSortByCuteness, usize, {x.cuteness})
//   // to sort:
//   FooSortByCuteness::sort(&mut my_array_of_foos);
// This currently requires Copy, for no good reason.
// TODO: The Copy requirement prevents us from using this in a few places where it may be useful, e.g. TypesLoadingShard::offset_map and sort_die_to_function.
//       Maybe get rid of voracious_radix_sort and make our own.
#[macro_export]
macro_rules! radix_sort_key {
    ($src:ty, $name:ident, $key:ty, |$x:ident| $($body:tt)*) => {
        #[repr(transparent)]
        #[derive(Clone, Copy)]
        struct $name($src);
        impl $name {
            fn radix_key(&self) -> $key {
                (|$x: &$src| -> $key { $($body)* })(&self.0)
            }
            fn sort(arr: &mut [$src]) {
                use voracious_radix_sort::RadixSort;
                // Hope this is not UB.
                unsafe {slice::from_raw_parts_mut(arr.as_mut_ptr().cast::<$name>(), arr.len()).voracious_sort();}
            }
        }
        impl voracious_radix_sort::Radixable<$key> for $name {
            type Key = $key;
            fn key(&self) -> $key {
                self.radix_key()
            }
        }
        impl core::cmp::Ord for $name {
            fn cmp(&self, other: &Self) -> core::cmp::Ordering { self.radix_key().cmp(&other.radix_key()) }
        }
        impl core::cmp::PartialOrd for $name {
            fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> { Some(self.cmp(other)) }
        }
        impl core::cmp::PartialEq for $name {
            fn eq(&self, other: &Self) -> bool { self.radix_key() == other.radix_key() }
        }
        impl core::cmp::Eq for $name {}
    };
}
