use crate::{*, debugger::*, error::*, util::*, symbols::*, symbols_registry::*, procfs::*, unwind::*, registers::*, log::*, settings::*};
use std::{collections::{HashMap, hash_map::Entry}, time::Instant};
use std::mem;
use libc::pid_t;

#[derive(Default)]
pub struct ProcessInfo {
    pub maps: MemMapsInfo,
    // Pointers to symbols for all mapped binaries. Guaranteed to be present in SymbolsRegistry.
    pub binaries: HashMap<BinaryId, BinaryInfo>,

    // CPU and memory usage, total across all threads, recalculated periodically.
    pub total_resource_stats: ResourceStats,
}

#[derive(Default)]
pub struct ThreadInfo {
    pub regs: Registers,

    // These are calculated lazily and cleared when the thread switches from Running to Suspended. None means it wasn't requested yet.
    // Errors are reported through StackTrace.truncated field.
    //
    // The "partial" stack trace is intended to be shown in the list of threads, for each thread.
    // Usually debuggers show the current function name there, but that function is usually something boring like epoll or futex wait.
    // Maybe we can do better and also show the most "interesting" function from the stack trace - maybe the first function from main
    // binary, or maybe let the user specify a regex for functions to exclude, or something.
    pub partial_stack: Option<StackTrace>,
    pub stack: Option<StackTrace>,

    pub resource_stats: ResourceStats,
}

#[derive(Default)]
pub struct ResourceStatsBucket {
    utime: usize,
    stime: usize,
    duration_ns: usize,
}

// Information about thread's recent CPU usage, excluding periods of time when the thread was suspended by the debugger.
#[derive(Default)]
pub struct ResourceStats {
    pub latest: ProcStat,
    // Time when `latest` was collected. None if the thread is suspended by the debugger.
    time: Option<Instant>,
    pub error: Option<Error>, // if we failed to read /proc/.../stat last time we tried

    // If all stats updates happened by periodic timer every 250ms then calculating current CPU usage would be simple:
    // subtract the stat values between current and previous tick. But we want to (1) exclude periods when the thread
    // was suspended by the debugger, and (2) show updated stats immediately when the thread is suspended or resumed.
    // Suppose the user suspends the program 1ms after a periodic refresh. Should we show CPU usage for the 1ms?
    // Or ignore the 1ms and show usage for previous 250ms? Ideally we'd show usage for the whole 251ms. That's why
    // we're keeping two buckets of history here. If the latest bucket is big enough we show stats from it, otherwise
    // we show merged stats from two buckets.
    // (Perhaps this is overengineered, and it would be better to just have a threshold and ignore the 1ms.)
    bucket: ResourceStatsBucket,
    prev_bucket: ResourceStatsBucket,
}
impl ResourceStats {
    pub fn update(&mut self, s: Result<ProcStat>, now: Instant, suspended: bool, periodic_timer_ns: usize) {
        self.error = None;
        let s = match s {
            Err(e) => {
                self.error = Some(e);
                return;
            }
            Ok(s) => s,
        };
        if let &Some(t) = &self.time {
            let ns = (now - t).as_nanos() as usize;
            if (self.bucket.duration_ns + ns) * 2 > periodic_timer_ns {
                self.prev_bucket = mem::take(&mut self.bucket);
            }
            self.bucket.duration_ns += ns;
            self.bucket.utime += s.utime - self.latest.utime;
            self.bucket.stime += s.stime - self.latest.stime;
        }
        self.latest = s;
        self.time = if suspended {None} else {Some(now)};
    }

    pub fn cpu_percentage(&self, periodic_timer_ns: usize) -> f64 {
        let mut t = self.bucket.duration_ns;
        let mut cpu = self.bucket.utime + self.bucket.stime;
        if self.bucket.duration_ns * 2 <= periodic_timer_ns {
            t += self.prev_bucket.duration_ns;
            cpu += self.prev_bucket.utime + self.prev_bucket.stime;
        }
        if t == 0 {
            return 0.0;
        }
        cpu as f64 * 1e9 / sysconf_SC_CLK_TCK() as f64 / t as f64 * 100.0
    }
}

impl ProcessInfo {
    pub fn addr_to_binary(&self, addr: usize) -> Result<&BinaryInfo> {
        let idx = self.maps.maps.partition_point(|m| m.start + m.len <= addr);
        if idx == self.maps.maps.len() || self.maps.maps[idx].start > addr {
            return err!(ProcessState, "address not mapped");
        }
        let id = match &self.maps.maps[idx].binary_id {
            None => return err!(ProcessState, "address not mapped to executable file"),
            Some(b) => b
        };
        Ok(self.binaries.get(id).unwrap())
    }

    pub fn clear(&mut self) {
        self.maps.clear();
        self.binaries.clear();
    }
}

impl ThreadInfo {
    pub fn invalidate(&mut self) {
        self.regs = Registers::default();
        self.partial_stack = None;
        self.stack = None;
    }
}

pub fn refresh_maps_and_binaries_info(debugger: &mut Debugger) {
    let maps = match MemMapsInfo::read_proc_maps(debugger.pid) {
        Err(e) => {
            eprintln!("error: failed to read maps: {:?}", e);
            return;
        }
        Ok(m) => m
    };

    let mut binaries: HashMap<BinaryId, BinaryInfo> = HashMap::new();

    // Avoid returning (including '?') in this scope.
    {
        let mut prev_binaries = mem::take(&mut debugger.info.binaries);
        for map in &maps.maps {
            let id = match &map.binary_id {
                None => continue,
                Some(b) => b,
            };
            let new_entry = match binaries.entry(id.clone()) {
                Entry::Occupied(mut e) => {
                    let bin = e.get_mut();
                    if let Ok(elf) = &bin.elf {
                        bin.addr_map.update(map, elf, &id.path);
                    }
                    continue;
                }
                Entry::Vacant(v) => v,
            };

            let latest = debugger.symbols.get_or_load(id, &debugger.memory);

            let mut binary = match prev_binaries.remove(id) {
                Some(mut bin) => {
                    bin.elf = bin.elf.or(latest.elf);
                    bin.symbols = bin.symbols.or(latest.symbols);
                    bin.unwind = bin.unwind.or(latest.unwind);
                    bin
                }
                None => latest,
            };

            if let Ok(elf) = &binary.elf {
                binary.addr_map.update(map, elf, &id.path);
            }

            new_entry.insert(binary);
        }

        debugger.info.maps = maps;
        debugger.info.binaries = binaries;
    }
}

// Must be called when the thread gets suspended (and not immediately resumed) - to assign registers, so we can unwind the stack.
// Should also be called when the thread is created (to assign thread name) or resumed (to update stats).
// We skip calling this if the thread was suspended and immediately resumed, e.g. skipped conditional breakpoints or passed-through user signals.
pub fn refresh_thread_info(pid: pid_t, t: &mut Thread, prof: &mut ProfileBucket, settings: &Settings) {
    if !t.exiting {
        let s = ProcStat::parse(&format!("/proc/{}/task/{}/stat", pid, t.tid), prof);
        t.info.resource_stats.update(s, Instant::now(), t.state == ThreadState::Suspended, settings.periodic_timer_ns);
    }

    if t.state == ThreadState::Suspended {
        t.info.regs = match ptrace_getregs(t.tid, prof) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("error: GETREGS failed: {:?}", e);
                Registers::default()
            }
        }
    }
}

// Called periodically to refresh stats for all threads, and totals. Stats are also refreshed by refresh_thread_info() when threads are suspended or resumed.
pub fn refresh_all_resource_stats(pid: pid_t, my_stats: &mut ResourceStats, debuggee_stats: &mut ResourceStats, threads: &mut HashMap<pid_t, Thread>, prof: &mut ProfileBucket, settings: &Settings) -> Option<Error> {
    let now = Instant::now();
    my_stats.update(ProcStat::parse("/proc/self/stat", prof), now, false, settings.periodic_timer_ns);
    let mut any_error = my_stats.error.clone();
    debuggee_stats.update(ProcStat::parse(&format!("/proc/{}/stat", pid), prof), now, false, settings.periodic_timer_ns);
    any_error = any_error.or_else(|| debuggee_stats.error.clone());

    for (tid, t) in threads {
        if !t.exiting {
            let s = ProcStat::parse(&format!("/proc/{}/task/{}/stat", pid, tid), prof);
            t.info.resource_stats.update(s, Instant::now(), t.state == ThreadState::Suspended, settings.periodic_timer_ns);
            any_error = any_error.or_else(|| t.info.resource_stats.error.clone());
        }
    }

    any_error
}

pub fn ptrace_getregs(tid: pid_t, prof: &mut ProfileBucket) -> Result<Registers> {
    unsafe {
        let mut regs: libc::user_regs_struct = mem::zeroed();
        ptrace(libc::PTRACE_GETREGS, tid, 0, &mut regs as *mut _ as u64, prof)?;
        Ok(Registers::from_ptrace(&regs))
    }
}
