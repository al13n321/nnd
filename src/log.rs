use crate::{*, util::*, common_ui::*};
use std::{collections::VecDeque, time::Instant, mem, fmt::Write, sync::atomic::{AtomicUsize, AtomicU64, Ordering}};
use core::arch::x86_64::_rdtsc;

// We should rework logging. I initially thought we'd want to show a very minimal log on screen.
// (Not at all like a typical server log, where you spam 1 MB/s of garbage.)
// That's what this current struct is about.
// But that's probably not very useful, and instead we should have two separate things:
//  1. Showing nice errors in intelligently chosen places in the UI. E.g. if a binary is missing debug symbols, show that in the list of binaries. We already do this.
//  2. Optionally writing various warnings to a log file, intended for the developer (me). E.g. if DWARF contains something unexpected or is missing something important.
//     Currently I'm using stderr for that, which may or may not be good enough.
pub struct Log {
    pub lines: VecDeque<String>,
    pub prof: Profiling,
}

const MAX_LINES: usize = 100;

impl Log {
    pub fn new() -> Log {
        Log {lines: VecDeque::new(), prof: Profiling::new()}
    }

    pub fn add_line(&mut self, line: String) {
        self.lines.push_back(line);
        while self.lines.len() > MAX_LINES {
            self.lines.pop_front();
        }
    }

    pub fn clear(&mut self) {
        self.lines.clear();
    }
}
#[macro_export]
macro_rules! log {
    ($log:expr, $($arg:tt)*) => (
        ($log).add_line(format!($($arg)*))
    );
}

// A minimal profiling thing. Prints to stderr in destructor.
pub struct ProfileScope {
    name: String,
    start: Instant,
    start_tsc: u64,
    total_tsc: u64,
    threshold_secs: f64,
    active: bool,
    multi: bool,
}

fn rdtsc() -> u64 {
    unsafe {_rdtsc()} // why is it unsafe?
}

impl ProfileScope {
    pub fn new(name: String) -> Self {
        ProfileScope {start: Instant::now(), start_tsc: 0, total_tsc: 0, name: name, threshold_secs: 0.0, active: true, multi: false}
    }

    pub fn with_threshold(secs: f64, name: String) -> Self {
        ProfileScope {start: Instant::now(), start_tsc: 0, total_tsc: 0, name: name, threshold_secs: secs, active: true, multi: false}
    }

    pub fn multi(name: String) -> Self {
        ProfileScope {start: Instant::now(), start_tsc: rdtsc(), total_tsc: 0, name: name, threshold_secs: 0.0, active: true, multi: true}
    }

    pub fn multi_with_threshold(secs: f64, name: String) -> Self {
        ProfileScope {start: Instant::now(), start_tsc: rdtsc(), total_tsc: 0, name: name, threshold_secs: secs, active: true, multi: true}
    }

    pub fn add(&mut self, tsc: u64) {
        assert!(self.multi);
        self.total_tsc += tsc;
    }
}

impl Drop for ProfileScope {
    fn drop(&mut self) {
        if !self.active {
            return;
        }
        let mut secs = self.start.elapsed().as_secs_f64();
        if self.multi {
            let end_tsc = rdtsc();
            let end_tsc = end_tsc.max(self.start_tsc + 1);
            secs = secs * (self.total_tsc as f64 / ((end_tsc - self.start_tsc) as f64));
        }
        if self.threshold_secs <= 0.0 || secs >= self.threshold_secs {
            eprintln!("info: {} took {:.3}s", self.name, secs);
        }
    }
}

pub struct TscScope {
    start: u64,
}
impl TscScope {
    pub fn new() -> Self {
        Self {start: rdtsc()}
    }

    pub fn restart(&mut self) -> u64 {
        let t = rdtsc();
        t.saturating_sub(mem::replace(&mut self.start, t))
    }

    pub fn finish(mut self) -> u64 {
        self.restart()
    }
}

pub struct TscScopeExcludingSyscalls {
    scope: TscScope,
    prev_syscall_tsc: u64,
}
impl TscScopeExcludingSyscalls {
    pub fn new(prof: &ProfileBucket) -> Self { Self {scope: TscScope::new(), prev_syscall_tsc: prof.syscall_tsc} }

    pub fn restart(&mut self, prof: &ProfileBucket) -> u64 {
        let t = prof.syscall_tsc;
        self.scope.restart().saturating_sub(t.saturating_sub(mem::replace(&mut self.prev_syscall_tsc, t)))
    }
    pub fn finish(mut self, prof: &ProfileBucket) -> u64 {
        self.restart(prof)
    }
}

pub struct LogTimestampInDestructor(pub &'static str);
impl Drop for LogTimestampInDestructor {
    fn drop(&mut self) {
        let mut t: libc::timespec;
        let r;
        unsafe {
            t = mem::zeroed();
            r = libc::clock_gettime(libc::CLOCK_MONOTONIC, &mut t as _);
        }
        assert!(r == 0);
        eprintln!("[{}.{:09}] {}", t.tv_sec, t.tv_nsec, self.0);
    }
}

pub fn get_thread_cpu_time_ns() -> usize {
    let mut ts = libc::timespec {
        tv_sec: 0,
        tv_nsec: 0,
    };
    unsafe {
        libc::clock_gettime(libc::CLOCK_THREAD_CPUTIME_ID, &mut ts);
    }
    ts.tv_sec as usize * 1_000_000_000 + ts.tv_nsec as usize
}

pub struct ProfileBucket {
    // Currently not all syscalls are instrumented, only the few ones that are likely to be frequent in practice (especially syscalls that happen for each thread or for each ptrace event).
    pub syscall_count: usize,
    pub syscall_tsc: u64,
    pub debugger_count: usize,
    pub debugger_tsc: u64,
    pub ui_max_tsc: u64,
    pub other_tsc: u64,

    pub ui_build_max_tsc: u64,
    pub ui_render_max_tsc: u64,
    pub ui_fill_max_tsc: u64,
    pub ui_input_bytes: usize,
    pub ui_output_bytes: usize,

    pub s_per_tsc: f64,

    pub start_tsc: u64,
    pub start_time: Instant,
    pub end_tsc: u64,
    pub end_time: Instant,
}
impl ProfileBucket {
    pub fn new(start_time: Instant, start_tsc: u64) -> Self {
        let mut r = ProfileBucket::invalid();
        r.start_time = start_time;
        r.start_tsc = start_tsc;
        r
    }

    pub fn invalid() -> Self { Self {start_time: unsafe {mem::zeroed()}, start_tsc: 0, syscall_count: 0, syscall_tsc: 0, debugger_count: 0, debugger_tsc: 0, ui_max_tsc: 0, s_per_tsc: 0.0, end_tsc: 0, end_time: unsafe {mem::zeroed()}, other_tsc: 0, ui_build_max_tsc: 0, ui_render_max_tsc: 0, ui_fill_max_tsc: 0, ui_input_bytes: 0, ui_output_bytes: 0} }

    pub fn finish(&mut self, end_time: Instant, end_tsc: u64) {
        assert!(self.start_tsc != 0);
        // rdtsc may go backwards e.g. after hibernation.
        let end_tsc = end_tsc.max(self.start_tsc + 1);
        self.end_tsc = end_tsc;
        self.end_time = end_time;
        self.s_per_tsc = (end_time - self.start_time).as_secs_f64() / (end_tsc - self.start_tsc) as f64;
    }
}

// Global counters that are periodically added to ProfileBucket and zeroed. Because passing ProfileBucket to all syscall sites would be too inconvenient (specifically for MemReader, all other sites would be fine with explicit passing of ProfileBucket).
pub static SYSCALL_COUNT: AtomicUsize = AtomicUsize::new(0);
pub static SYSCALL_TSC: AtomicU64 = AtomicU64::new(0);

pub struct Profiling {
    pub buckets: VecDeque<ProfileBucket>,
    pub bucket: ProfileBucket,
}
impl Profiling {
    pub fn new() -> Self { Self {buckets: VecDeque::new(), bucket: ProfileBucket::new(Instant::now(), rdtsc())} }

    // (Mutates global variables.)
    pub fn advance_bucket(&mut self) {
        // May have torn read between the two atomics. This is fine, in part because we currently only do syscalls in main thread.
        self.bucket.syscall_count += SYSCALL_COUNT.swap(0, Ordering::Relaxed);
        self.bucket.syscall_tsc += SYSCALL_TSC.swap(0, Ordering::Relaxed);
        let time = Instant::now();
        let tsc = rdtsc();
        self.bucket.finish(time, tsc);
        let new_bucket = ProfileBucket::new(time, tsc);
        self.buckets.push_back(mem::replace(&mut self.bucket, new_bucket));

        while self.buckets.len() > 1000 {
            self.buckets.pop_front();
        }
    }
}

#[macro_export]
macro_rules! profile_syscall {
    ($($code:tt)*) => {{
        let timer = TscScope::new();
        let r = {$($code)*};
        SYSCALL_TSC.fetch_add(timer.finish(), std::sync::atomic::Ordering::Relaxed);
        SYSCALL_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        r
    }};
}
