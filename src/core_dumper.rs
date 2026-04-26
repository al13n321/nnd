use crate::{*, util::*, error::*, procfs::*, elf::*, os::*};
use std::{ptr, process, collections::HashSet, io, io::{Read, Write}, panic, fs, str, os::unix::io::FromRawFd, mem, mem::MaybeUninit, time::{Instant, Duration}, slice};
use libc::pid_t;

// TODO: Colors.
// TODO: Write to file if stdout is tty.

const CLEAR_LINE: &'static str = "\x1B[2K";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CoreDumperMode {
    Direct,
    Live,
    Fork,
    // TODO: Consider userfaultfd.
}

struct RangeToDump {
    start: usize,
    len: usize,
    file_offset: usize,
    file_size: usize,
    perms: MemMapPermissions,
}

struct RegisterSet {
    name: &'static str,
    id: u32,
    data: Vec<u8>,
}

struct ForkInjectionState {
    tid: pid_t,
    addr: usize,
    original_code: u64,
    regsets: [RegisterSet; 3],
}

struct CoreDumper {
    pid: pid_t,
    buffer_size: usize,
    mode: CoreDumperMode,

    attached_threads: Vec<pid_t>,
    forked_pid: Option<pid_t>,
    // If set, we're currently in the precarious critical section where the target process is in a broken state, and we must restore it before exiting.
    // (We have it here to do cleanup in case we die during that short critical section; e.g. if for some reason waitpid gets stuck, and the user hits control-C.
    //  Alternatively, we could just have a timeout for waitpid and be extra careful to not do anything risky in that critical section, but this seems better.)
    fork_state: Option<ForkInjectionState>,

    notes_buf: Vec<u8>,

    start_time: Instant,
    read_duration: Duration,
    write_duration: Duration,
    bytes_written: usize,
    bytes_read: usize,
    bytes_total: usize,
    bytes_at_last_progress_update: usize,
}
impl CoreDumper {
    fn cleanup(&mut self) {
        if let Some(state) = self.fork_state.take() {
            Self::restore_state_after_fork(&state, false);
        }
        if let Some(forked_pid) = self.forked_pid.take() {
            let r = unsafe {libc::kill(forked_pid, libc::SIGKILL)};
            if r == 0 {
                eprintln!("(killed the forked pid {})", forked_pid);
            } else {
                eprintln!("error: failed to kill forked process with pid {}: {}", forked_pid, io::Error::last_os_error());
            }
        }
    }

    fn detach_ptrace(&mut self) {
        if !self.attached_threads.is_empty() {
            eprintln!("(resuming and detaching {} threads)", self.attached_threads.len());
            for &tid in &self.attached_threads {
                if let Err(e) = unsafe { ptrace(PTRACE_DETACH, tid, 0, 0) } {
                    eprintln!("warning: failed to detach thread {}: {}", tid, e);
                }
            }
            self.attached_threads.clear();
            let detach_time = Instant::now();
            eprintln!("the process was paused for {:.3}s", (detach_time - self.start_time).as_secs_f64());
        }
    }

    fn try_dump(&mut self) -> Result<()> {
        let mut seen_threads: HashSet<pid_t> = HashSet::new();
        let mut weird_race_count: usize = 0;
        let ptrace_seize_flags = if self.mode == CoreDumperMode::Fork {PTRACE_O_TRACEFORK} else {0};
        for round in 0.. {
            if round > 30 {
                return err!(Sanity, "suspiciously many attach attempts were required, giving up");
            }

            let threads = match list_threads(self.pid) {
                Ok(x) => x,
                Err(e) if e.is_io_not_found() => return err!(ProcessState, "no process with pid {}", self.pid),
                Err(e) => return Err(e),
            };
            let added_threads: Vec<pid_t> = threads.iter().copied().filter(|t| seen_threads.insert(*t)).collect();
            if added_threads.is_empty() {
                break;
            }
            eprintln!("(attaching to {} threads)", added_threads.len());
            let mut running_threads: HashSet<pid_t> = HashSet::new();
            for tid in added_threads {
                match unsafe {ptrace(PTRACE_SEIZE, tid, 0, ptrace_seize_flags as u64)} {
                    Ok(_) => (),
                    Err(e) if e.is_io_permission_denied() => return err!(Usage, "ptrace({}) failed: operation not permitted - missing sudo?", tid),
                    Err(e) => return Err(e),
                }
                self.attached_threads.push(tid);
                running_threads.insert(tid);
                unsafe {ptrace(PTRACE_INTERRUPT, tid, 0, 0)}?;
            }

            eprintln!("(waiting for {} threads to stop)", running_threads.len());
            while !running_threads.is_empty() {
                let mut wstatus = 0i32;
                let tid = unsafe {libc::waitpid(-1, &mut wstatus, 0)};
                if tid < 0 {
                    let err = io::Error::last_os_error();
                    if err.kind() == io::ErrorKind::Interrupted {
                        continue;
                    }
                    return Err(err.into());
                }
                if !running_threads.contains(&tid) {
                    eprintln!("warning: got event 0x{:x} for unexpected thread {}", wstatus, tid);
                    continue;
                }

                if libc::WIFEXITED(wstatus) || libc::WIFSIGNALED(wstatus) {
                    eprintln!("info: thread {} exited during attach", tid);
                    self.attached_threads.retain(|t| *t != tid);
                    running_threads.remove(&tid);
                } else if wstatus>>16 == PTRACE_EVENT_STOP {
                    // The expected way for thread to stop after PTRACE_INTERRUPT.
                    running_threads.remove(&tid);
                } else if libc::WIFSTOPPED(wstatus) {
                    // Is the following scenario possible?:
                    //  1. We do PTRACE_SEIZE.
                    //  2. An unrelated signal is sent to the thread, e.g. SIGUSR1.
                    //  3. We do PTRACE_INTERRUPT. It gets queued up behing the SIGUSR1 (is that how it works?).
                    //  4. We do waitpid() and see that the thread was stopped by the unrelated signal (SIGUSR1 in our example).
                    //  5. We dump the core, PTRACE_CONT the thread, and exit.
                    //  6. The thread is stopped again because of our previous PTRACE_INTERRUPT. It stays stopped forever.
                    // Idk. Just in case, let's avoid this by not trusting non-PTRACE_EVENT_STOP stops.
                    let signal = libc::WSTOPSIG(wstatus);
                    weird_race_count += 1;
                    if weird_race_count > 30 {
                        return err!(Sanity, "hit signal delivery race condition suspiciously many times, giving up");
                    }
                    eprintln!("warning: thread {} stopped in unexpected way (signal {}). Resuming and retrying", tid, signal_name(signal));
                    // Deliver the presumably-unrelated signal and re-request a ptrace stop.
                    unsafe {ptrace(PTRACE_CONT, tid, 0, signal as u64)}?;
                    unsafe {ptrace(PTRACE_INTERRUPT, tid, 0, 0)}?;
                } else {
                    return err!(Internal, "waitpid() returned unexpected status: {}", wstatus);
                }
            }

            // New threads may have been spawned while we were attaching, so list threads again and re-check.
        }
        if self.attached_threads.is_empty() {
            return err!(Sanity, "no threads");
        }

        eprintln!("(retrieving memory maps and registers)");
        let maps = MemMapsInfo::read_proc_maps(self.pid)?;
        self.prepare_notes(&maps)?;
        let ranges = self.write_headers(&maps)?;
        let headers_end_time = Instant::now();
        eprintln!("(wrote {} of headers in {:.3}s)", PrettySize(self.bytes_written), (headers_end_time - self.start_time).as_secs_f64());
        self.bytes_written = 0; // show just memory dump files in progress bar

        match self.mode {
            CoreDumperMode::Direct => (),
            CoreDumperMode::Live => self.detach_ptrace(),
            CoreDumperMode::Fork => {
                self.do_the_fork_nonsense(&maps)?;
                self.detach_ptrace();
                // Tell OOM killer to kill our forked process first if the system runs out of memory.
                match Self::set_oom_score_to_max(self.forked_pid.clone().unwrap()) {
                    Ok(()) => (),
                    Err(e) => eprintln!("info: failed to adjust oom score: {}", e),
                }
            }
        }

        self.bytes_total = ranges.iter().map(|r| r.file_size).sum();
        eprintln!("dumping {} of memory", PrettySize(self.bytes_total));
        let mut buf: Vec<u8> = Vec::with_capacity(self.buffer_size.min(self.bytes_total));

        self.dump_memory_ranges(&ranges, &mut buf)?;
        eprint!("\r{}", CLEAR_LINE); // erase progress bar

        self.cleanup();
        self.detach_ptrace();

        eprintln!("(writing remaining buffered data)");
        self.flush_buf(&mut buf)?;
        eprint!("\r{}", CLEAR_LINE);

        let (read_secs, write_secs) = (self.read_duration.as_secs_f64(), self.write_duration.as_secs_f64());
        let gib = self.bytes_total as f64 / (1usize << 30) as f64;
        eprintln!("all done! spent {:.3}s reading ({:.3} GiB/s), {:.3}s writing ({:.3} GiB/s)", read_secs, gib / read_secs, write_secs, gib / write_secs);

        Ok(())
    }

    fn do_the_fork_nonsense(&mut self, maps: &MemMapsInfo) -> Result<()> {
        // There's no syscall to fork another process. So we have to manipulate the target process into running some machine code that does fork.
        // There's also no syscall to allocate memory in another process. So we'll have to commandeer a few bytes of executable memory in the target
        // process for the fork machine code.
        // There's also no syscall to create a thread in another process. So we'll have to hijack some thread to run the fork machine code.
        // Then we'll have to restore everything: revert the machine code we've overwritten and the thread state we hijacked.
        // I with ptrace had some nicer mechanism for running code inside in the tracee.

        // Use the first thread listed, usually main thread.
        let tid_to_hijack = self.attached_threads[0];
        let code_to_inject: u64 = u64::from_le_bytes([
            0x0f, 0x05, // syscall
            0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, // pad with int3 instructions
        ]);

        let mut regsets: [RegisterSet; 3] = [
            RegisterSet {name: "NT_PRSTATUS", id: NT_PRSTATUS, data: Vec::new()},
            RegisterSet {name: "NT_PRFPREG", id: NT_PRFPREG, data: Vec::new()},
            RegisterSet {name: "NT_X86_XSTATE", id: NT_X86_XSTATE, data: Vec::new()}];
        for RegisterSet {name, id, data} in &mut regsets {
            data.resize(10000, 0u8);
            let len = Self::ptrace_getregset(tid_to_hijack, *id, data)?.len();
            if len == data.len() {
                return err!(Sanity, "unexpectedly big register set state {}: >= {} bytes", name, len);
            }
            if *id == NT_PRSTATUS && len != mem::size_of::<libc::user_regs_struct>() {
                // We're going to modify this struct, so be paranoid about its layout.
                return err!(Sanity, "unexpected size of general-purpose registers: expected {} bytes, got {}", mem::size_of::<libc::user_regs_struct>(), len);
            }
            data.truncate(len);
        }
        let (mut regs_struct, _) = unsafe {memcpy_struct::<libc::user_regs_struct>(&regsets[0].data, "user_regs_struct")}?;

        // Use the start of the first executable memory range, usually the start of .text section of the main executable.
        let mut addr = usize::MAX;
        for map in &maps.maps {
            if map.perms.contains(MemMapPermissions::EXECUTE | MemMapPermissions::READ) {
                addr = addr.min(map.start);
            }
        }
        if addr == usize::MAX {
            return err!(ProcessState, "the process appears to have no executable mapped memory");
        }
        // (Uncomment this to overwrite code at current instruction pointer instead, for testing:)
        //  addr = regs_struct.rip as usize & !7;

        regs_struct.rip = addr as u64;
        regs_struct.rax = 0x39; // fork syscall number

        let reader = PidMemReader::new(self.pid);
        let mut original_code_buf = [MaybeUninit::zeroed(); 8];
        let original_code = reader.read_uninit(addr, &mut original_code_buf)?;
        let original_code = u64::from_le_bytes(original_code.try_into().unwrap());
        let state = ForkInjectionState {tid: tid_to_hijack, addr, original_code, regsets};

        eprintln!("(picked thread {} and address 0x{:x} for injecting a fork call)", tid_to_hijack, addr);
        eprintln!("(doing a practice run first)");

        // We're going to temporarily put the process in a broken state, then restore it.
        // Be extra careful to avoid leaving it in the broken state.

        // Before we break the process, run the recovery procedure to make sure it doesn't fail.
        if !Self::restore_state_after_fork(&state, true) {
            return err!(Sanity, "code injection dry run failed, aborting");
        }

        eprintln!("(practice run succeeded, proceeding to injecting the fork call)");
        self.fork_state = Some(state);

        let inject_failed = match self.inject_fork(tid_to_hijack, addr, code_to_inject, &regs_struct) {
            Ok(()) => false,
            Err(e) => {
                eprintln!("error: failed to inject fork: {}", e);
                true
            }
        };

        let state = self.fork_state.take().unwrap();
        eprintln!("(restoring state)");
        if !Self::restore_state_after_fork(&state, false) {
            return err!(Sanity, "failed to restore state after injecting fork");
        }

        if inject_failed {
            return err!(Environment, "failed to inject fork call");
        }

        Ok(())
    }

    fn inject_fork(&mut self, tid: pid_t, addr: usize, code: u64, regs_struct: &libc::user_regs_struct) -> Result<()> {
        unsafe {
            // Write the machine code.
            ptrace(PTRACE_POKETEXT, tid, addr as u64, code)?;

            // Set thread's registers (rip and rax) to teleport it to our code.
            let mut iov = libc::iovec {iov_base: regs_struct as *const libc::user_regs_struct as *mut libc::c_void, iov_len: mem::size_of::<libc::user_regs_struct>()};
            ptrace(PTRACE_SETREGSET, tid, NT_PRSTATUS as u64, &mut iov as *mut libc::iovec as u64)?;

            // Resume the thread.
            ptrace(PTRACE_CONT, tid, 0, 0)?;

            // What we expect to happen:
            //  * PTRACE_EVENT_FORK. We get the new process's pid through PTRACE_GETEVENTMSG.
            //    So we can just restore registers and detach ptrace after this, right? Wrong!
            //    This event is reported "before return from fork", so the syscall return would assign rax when
            //    the thread is resumed, *after* we restore registers.
            //    We PTRACE_CONT the thread instead.
            //  * SIGTRAP when the thread hits the int3 after the syscall. Now we can restore and detach.
            //    (Then why do we need PTRACE_O_TRACEFORK at all? To make ptrace attach+stop the newly forked process,
            //    instead of letting it run and immediately die on the int3.)
            //  * There's also ptrace stop event for the newly forked process, but we don't need it and don't call
            //    waitpid() for the new process.
            loop {
                let mut wstatus = 0i32;
                let r = libc::waitpid(tid, &mut wstatus, 0);
                if r < 0 {
                    let err = io::Error::last_os_error();
                    if err.kind() == io::ErrorKind::Interrupted {
                        continue;
                    }
                    return Err(err.into());
                }
                if r != tid {
                    return err!(Sanity, "unexpected tid returned from waitpid({}): {}", tid, r);
                }

                if libc::WIFSTOPPED(wstatus) {
                    let signal = libc::WSTOPSIG(wstatus);
                    if signal != libc::SIGTRAP {
                        return err!(ProcessState, "hijacked thread stopped with unexpected signal {}", signal_name(signal));
                    }
                    match wstatus >> 16 {
                        PTRACE_EVENT_FORK => {
                            let mut new_pid = 0usize;
                            ptrace(PTRACE_GETEVENTMSG, tid, 0, &mut new_pid as *mut _ as u64)?;
                            eprintln!("(forked pid: {})", new_pid);
                            if self.forked_pid.is_some() {
                                eprintln!("error: multiple fork events were reported by ptrace");
                                // Keep going, can't stop+restore in this state.
                            }
                            self.forked_pid = Some(new_pid as pid_t);
                            ptrace(PTRACE_CONT, tid, 0, 0)?;
                        }
                        0 if self.forked_pid.is_none() => return err!(ProcessState, "fork failed"),
                        _ if self.forked_pid.is_none() => return err!(ProcessState, "hijacked thread got unexpected ptrace stop before fork"),
                        0 => break,
                        _ => {
                            eprintln!("warning: hijacked thread got unexpected ptrace stop after fork");
                            break;
                        }
                    }
                } else if libc::WIFEXITED(wstatus) {
                    return err!(ProcessState, "hijacked thread exited with code {}", libc::WEXITSTATUS(wstatus));
                } else if libc::WIFSIGNALED(wstatus) {
                    return err!(ProcessState, "hijacked thread was terminated by signal {}", signal_name(libc::WTERMSIG(wstatus)));
                } else if libc::WIFSTOPPED(wstatus) {
                    return err!(ProcessState, "hijacked thread stopped in unexpected way (status=0x{:x})", wstatus);
                } else {
                    return err!(Internal, "waitpid() returned unexpected status: {}", wstatus);
                }
            }
        }
        Ok(())
    }

    fn restore_state_after_fork(state: &ForkInjectionState, dry_run: bool) -> bool {
        let (mut failed_code, mut failed_thread) = (false, false);
        for RegisterSet {name, id, data} in &state.regsets {
            unsafe {
                let mut iov = libc::iovec {iov_base: data.as_ptr() as *mut libc::c_void, iov_len: data.len()};
                match ptrace(PTRACE_SETREGSET, state.tid, *id as u64, &mut iov as *mut libc::iovec as u64) {
                    Ok(_) => (),
                    Err(e) => {
                        eprintln!("error: PTRACE_SETREGSET {} failed: {}", name, e);
                        failed_thread = true;
                    }
                }
            }
        }
        match unsafe { ptrace(PTRACE_POKETEXT, state.tid, state.addr as u64, state.original_code) } {
            Ok(_) => (),
            Err(e) => {
                eprintln!("error: PTRACE_POKETEXT failed: {}", e);
                failed_code = true;
            }
        }
        if !dry_run && (failed_code || failed_thread) {
            eprintln!("!! failed to restore process state after injecting a fork call, the target process may be broken, oh no !!");
            if failed_thread {
                eprintln!("!! thread {} in the target process may be broken !!", state.tid);
            }
            if failed_code {
                eprintln!("!! 8 bytes of machine code at address 0x{:x} were overwritten !!", state.addr);
            }
            return false;
        }
        true
    }

    fn set_oom_score_to_max(pid: pid_t) -> Result<()> {
        let path = format!("/proc/{}/oom_score_adj", pid);
        let value = "1000";
        eprintln!("(writing '{}' to {})", value, path);
        fs::File::create(path)?.write_all(value.as_bytes())?;
        Ok(())
    }

    fn ptrace_getregset<'a>(tid: pid_t, regset: u32, buf: &'a mut [u8]) -> Result<&'a [u8]> {
        unsafe {
            let mut iov = libc::iovec {iov_base: buf.as_mut_ptr() as *mut libc::c_void, iov_len: buf.len()};
            ptrace(PTRACE_GETREGSET, tid, regset as u64, &mut iov as *mut libc::iovec as u64)?;
            Ok(&buf[..iov.iov_len])
        }
    }

    fn parse_proc_stat(pid: pid_t, prpsinfo: &mut elf_prpsinfo) -> Result<()> {
        let s = fs::read(format!("/proc/{}/stat", pid))?;
        let Some(name_end) = s.iter().copied().position(|c| c == b')') else {return err!(Internal, "no ')'")};
        let Some(name_start) = s[..name_end].iter().copied().position(|c| c == b'(') else {return err!(Internal, "no '('")};
        for (i, tok) in str::from_utf8(&s[name_end+1..])?.split_whitespace().enumerate() {
            match i {
                0 => {
                    let state = tok.as_bytes()[0];
                    prpsinfo.pr_state = state as i8;
                    prpsinfo.pr_sname = state as i8;
                    prpsinfo.pr_zomb = if state == b'Z' {1} else {0};
                }
                1 => prpsinfo.pr_ppid = tok.parse::<pid_t>()?,
                2 => prpsinfo.pr_pgrp = tok.parse::<pid_t>()?,
                3 => prpsinfo.pr_sid = tok.parse::<pid_t>()?,
                16 => prpsinfo.pr_nice = tok.parse::<i8>()?,
                _ => (),
            }
        }

        let name = &s[name_start + 1..name_end];
        let name = &name[..name.len().min(15)];
        prpsinfo.pr_fname[..name.len()].copy_from_slice(name);
        Ok(())
    }

    fn parse_cmdline(pid: pid_t, prpsinfo: &mut elf_prpsinfo) -> Result<()> {
        let mut f = fs::File::open(format!("/proc/{}/cmdline", pid))?;
        let mut pos = 0usize;
        while pos < prpsinfo.pr_psargs.len() {
            pos += match f.read(&mut prpsinfo.pr_psargs[pos..]) {
                Ok(0) => break,
                Ok(n) => n,
                Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
                Err(e) => return Err(e.into()),
            };
        }
        assert!(pos <= prpsinfo.pr_psargs.len());
        *prpsinfo.pr_psargs.last_mut().unwrap() = 0;
        for c in &mut prpsinfo.pr_psargs[..pos.saturating_sub(1)] {
            if *c == b'\0' {
                *c = b' ';
            }
        }
        Ok(())
    }

    fn add_note(&mut self, name: &str, desc: &[u8], type_: u32) {
        self.notes_buf.write_u32((name.len() + 1) as u32).unwrap();
        self.notes_buf.write_u32(desc.len() as u32).unwrap();
        self.notes_buf.write_u32(type_).unwrap();
        let name_null_terminator_and_padding = 4 - name.len() % 4;
        let desc_padding = desc.len().wrapping_neg() % 4;
        self.notes_buf.extend_from_slice(name.as_bytes());
        self.notes_buf.extend_from_slice(&[0u8; 4][..name_null_terminator_and_padding]);
        self.notes_buf.extend_from_slice(desc);
        self.notes_buf.extend_from_slice(&[0u8; 3][..desc_padding]);
    }

    fn add_regset_note(&mut self, tid: pid_t, regset: u32, buf: &mut [u8]) -> Result<()> {
        let desc = Self::ptrace_getregset(tid, regset, buf)?;
        self.add_note("CORE", desc, regset);
        Ok(())
    }

    fn add_prstatus_note(&mut self, tid: pid_t) -> Result<()> {
        unsafe {
            // (Note that we can't just use PTRACE_GETREGSET with NT_PRSTATUS. Despite its name, it outputs user_regs_struct rather than prstatus struct,
            //  same as PTRACE_GETREGS.)
            let mut prstatus: elf_prstatus = mem::zeroed();
            ptrace(PTRACE_GETREGS, tid, 0, &mut prstatus.pr_reg as *mut _ as u64)?;
            prstatus.pr_pid = tid;
            // (Leaving lots of fields of prstatus zero, they all seem either useless or unfilled by linux's normal core dump code.)

            let desc = slice::from_raw_parts(&prstatus as *const _ as *const u8, mem::size_of::<elf_prstatus>());
            self.add_note("CORE", desc, NT_PRSTATUS);
        }
        Ok(())
    }

    fn prepare_notes(&mut self, maps: &MemMapsInfo) -> Result<()> {
        // (Big enough for the ~2.7 KB NT_X86_XSTATE.)
        let mut buf = [0u8; 10000];

        self.add_prstatus_note(self.pid)?;

        // Piece together prpsinfo from procfs.
        let mut prpsinfo: elf_prpsinfo = unsafe {mem::zeroed()};
        prpsinfo.pr_pid = self.pid;
        if let Err(e) = Self::parse_proc_stat(self.pid, &mut prpsinfo) {
            eprintln!("warning: failed to parse /proc/{}/stat: {}", self.pid, e);
        }
        if let Err(e) = Self::parse_cmdline(self.pid, &mut prpsinfo) {
            eprintln!("warning: failed to parse /proc/{}/cmdline: {}", self.pid, e);
        }
        // (Leaving these zero, seem unimportant: pr_flag, pr_uid, pr_gid.)
        let sizeof = mem::size_of::<elf_prpsinfo>();
        unsafe {ptr::copy_nonoverlapping(&prpsinfo as *const elf_prpsinfo as *const u8, buf.as_mut_ptr(), sizeof)};
        self.add_note("CORE", &buf[..sizeof], NT_PRPSINFO);

        let sizeof = mem::size_of::<libc::siginfo_t>();
        unsafe {ptrace(PTRACE_GETSIGINFO, self.pid, 0, buf.as_mut_ptr() as u64)}?;
        self.add_note("CORE", &buf[..sizeof], NT_SIGINFO);

        self.add_note("CORE", &fs::read(format!("/proc/{}/auxv", self.pid))?, NT_AUXV);

        let mut files_buf: Vec<u8> = Vec::new();
        // (The "[" is to exclude things like "[vdso]", to match linux core dumper's behavior.)
        let file_maps: Vec<MemMapInfo> = maps.maps.iter().filter(|m| m.path.as_ref().is_some_and(|p| !p.starts_with("["))).cloned().collect();
        files_buf.write_usize(file_maps.len()).unwrap();
        let page_size = sysconf_PAGE_SIZE();
        files_buf.write_usize(page_size).unwrap();
        for map in &file_maps {
            files_buf.write_usize(map.start - map.offset % page_size).unwrap();
            files_buf.write_usize(map.start + map.len).unwrap();
            files_buf.write_usize(map.offset / page_size).unwrap();
        }
        for map in &file_maps {
            let path = map.path.as_ref().unwrap().as_bytes();
            let path = &path[..path.iter().copied().position(|c| c == b'\0').unwrap_or(path.len())];
            files_buf.extend_from_slice(path);
            files_buf.push(b'\0');
        }
        self.add_note("CORE", &files_buf, NT_FILE);

        self.add_regset_note(self.pid, NT_PRFPREG, &mut buf)?;
        self.add_regset_note(self.pid, NT_X86_XSTATE, &mut buf)?;

        let mut tids_to_write: Vec<pid_t> = self.attached_threads.iter().copied().filter(|t| *t != self.pid).collect();
        tids_to_write.sort();
        for tid in tids_to_write {
            self.add_prstatus_note(tid)?;
            self.add_regset_note(tid, NT_PRFPREG, &mut buf)?;
            self.add_regset_note(tid, NT_X86_XSTATE, &mut buf)?;
        }

        Ok(())
    }

    fn write_headers(&mut self, maps: &MemMapsInfo) -> Result<Vec<RangeToDump>> {
        let page_size = sysconf_PAGE_SIZE();
        assert!(page_size & (page_size - 1) == 0);
        let phdr_count_limit = maps.maps.len() + 1;
        let phdr_start_offset = mem::size_of::<libc::Elf64_Ehdr>();
        let notes_offset = phdr_start_offset + phdr_count_limit * mem::size_of::<libc::Elf64_Phdr>();
        assert!(notes_offset % 4 == 0); // notes require 4-byte alignment
        let notes_end_offset = notes_offset + self.notes_buf.len();
        let mem_dump_offset = (notes_end_offset + page_size - 1) & !(page_size - 1); // page offsets must be aligned

        let mut ranges: Vec<RangeToDump> = Vec::new();
        let mut file_offset = mem_dump_offset;
        for map in &maps.maps {
            // Don't dump file mmaps bigger than 20 MiB.
            // Usually that's just the main executable, while things like libc are smaller and get dumped, for debugger's convenience.
            // (In contrast, linux core dumper seems to omit all file-backed mapped files regardless of size.)
            // Also exclude maps we can't read (at least not using process_vm_readv): maps with no read permission
            // (usually guard pages with no useful information), [vvar], and [vsyscall].
            let file_backed = map.path.as_ref().is_some_and(|p| !p.starts_with("["));
            let unreadable = !map.perms.contains(MemMapPermissions::READ) || map.path.as_ref().is_some_and(|p| p == "[vvar]" || p == "[vsyscall]");
            let skip = (file_backed && map.len > (20<<20)) || unreadable;
            // (Surely /proc/pid/maps can't have unaligned address ranges, but let's be paranoid.)
            let start = map.start & !(page_size - 1);
            let len = (map.start + map.len - start + page_size - 1) & !(page_size - 1);
            let file_size = if skip {0} else {len};
            ranges.push(RangeToDump {start, len, file_offset, file_size, perms: map.perms});
            file_offset += file_size;
        }

        let mut buf: Vec<u8> = Vec::new();
        let ehdr = libc::Elf64_Ehdr {
            e_ident: [
                libc::ELFMAG0, libc::ELFMAG1, libc::ELFMAG2, libc::ELFMAG3,
                libc::ELFCLASS64, libc::ELFDATA2LSB, libc::EV_CURRENT as u8, libc::ELFOSABI_SYSV,
                0, 0, 0, 0, 0, 0, 0, 0],
            e_type: libc::ET_CORE,
            e_machine: libc::EM_X86_64,
            e_version: libc::EV_CURRENT,
            e_entry: 0,
            e_phoff: phdr_start_offset as u64,
            e_shoff: 0,
            e_flags: 0,
            e_ehsize: mem::size_of::<libc::Elf64_Ehdr>() as u16,
            e_phentsize: mem::size_of::<libc::Elf64_Phdr>() as u16,
            e_phnum: ranges.len() as u16,
            e_shentsize: 0,
            e_shnum: 0,
            e_shstrndx: 0,
        };
        buf.write_struct(&ehdr).unwrap();

        assert!(buf.len() == phdr_start_offset);
        let notes_phdr = libc::Elf64_Phdr {
            p_type: libc::PT_NOTE,
            p_flags: 0,
            p_offset: notes_offset as u64,
            p_vaddr: 0,
            p_paddr: 0,
            p_filesz: self.notes_buf.len() as u64,
            p_memsz: 0,
            p_align: 4,
        };
        buf.write_struct(&notes_phdr).unwrap();
        for range in &ranges {
            let mut flags = 0;
            if range.perms.contains(MemMapPermissions::READ) {
                flags |= libc::PF_R;
            }
            if range.perms.contains(MemMapPermissions::WRITE) {
                flags |= libc::PF_W;
            }
            if range.perms.contains(MemMapPermissions::EXECUTE) {
                flags |= libc::PF_X;
            }
            let phdr = libc::Elf64_Phdr {
                p_type: libc::PT_LOAD,
                p_flags: flags,
                p_offset: range.file_offset as u64,
                p_vaddr: range.start as u64,
                p_paddr: 0,
                p_filesz: range.file_size as u64,
                p_memsz: range.len as u64,
                p_align: page_size as u64,
            };
            buf.write_struct(&phdr).unwrap();
        }

        assert!(buf.len() <= notes_offset);
        buf.resize(notes_offset, 0u8);
        buf.extend_from_slice(&self.notes_buf);

        assert!(buf.len() <= mem_dump_offset);
        buf.resize(mem_dump_offset, 0u8);

        self.flush_buf(&mut buf)?;

        Ok(ranges)
    }

    fn flush_buf(&mut self, buf: &mut Vec<u8>) -> Result<()> {
        let mut pos = 0usize;
        while pos < buf.len() {
            // Unbuffered.
            let write_start_time = Instant::now();
            let lim = (buf.len() - pos).min(1 << 27); // avoid huge writes to keep progress bar smooth
            let n = unsafe {libc::write(libc::STDOUT_FILENO, buf.as_ptr().add(pos) as *const libc::c_void, lim)};
            if n >= 0 {
                pos += n as usize;
                self.bytes_written += n as usize;
            } else {
                if io::Error::last_os_error().kind() != io::ErrorKind::Interrupted {
                    return errno_err!("failed to write to stdout");
                }
            }
            self.write_duration += write_start_time.elapsed();
            self.update_progress_bar_if_needed();
        }
        buf.clear();
        Ok(())
    }

    // buf.capacity() determines how much to buffer before writing to stdout.
    // Doesn't flush the buffer at the end (to allow the caller to detach from the process first, especially in buffered mode).
    fn dump_memory_ranges(&mut self, ranges: &Vec<RangeToDump>, buf: &mut Vec<u8>) -> Result<()> {
        assert!(buf.capacity() > 0 || self.bytes_total == 0);
        let reader = PidMemReader::new(self.forked_pid.clone().unwrap_or(self.pid));
        for range in ranges {
            if range.file_size == 0 {
                continue;
            }
            assert!(range.file_size <= range.len);
            let mut pos = 0usize;
            while pos < range.file_size {
                let cap = buf.spare_capacity_mut();
                if cap.is_empty() {
                    assert!(!buf.is_empty());
                    self.flush_buf(buf)?;
                    assert!(buf.is_empty());
                    continue;
                }
                let n = cap.len().min(range.file_size - pos).min(1 << 27);
                let read_start_time = Instant::now();
                match reader.read_uninit(range.start + pos, &mut cap[..n]) {
                    Ok(_) => (),
                    Err(e) => {
                        eprintln!("warning: couldn't read memory 0x{:x}-0x{:x}: {}", range.start + pos, range.start + pos + n, e);
                        unsafe {ptr::write_bytes(cap.as_mut_ptr(), 0u8, n)};
                    }
                }
                self.read_duration += read_start_time.elapsed();
                unsafe {buf.set_len(buf.len() + n)};
                pos += n;
                self.bytes_read += n;
                self.update_progress_bar_if_needed();
            }
        }
        Ok(())
    }

    fn update_progress_bar_if_needed(&mut self) {
        if self.bytes_total == 0 {
            return;
        }
        let bytes = self.bytes_read + self.bytes_written;
        let period_bytes = 1 << 28;
        if bytes > self.bytes_at_last_progress_update + period_bytes {
            self.bytes_at_last_progress_update = bytes;
            let bytes_per_second = bytes as f64 / (self.read_duration + self.write_duration).as_secs_f64();
            let eta = (self.bytes_total * 2 - bytes) as f64 / bytes_per_second;
            eprint!("\r{}{}/{}/{}  eta: {:.0}s", CLEAR_LINE, PrettySize(self.bytes_written), PrettySize(self.bytes_read), PrettySize(self.bytes_total), eta);
            let _ = io::stderr().flush();
        }
    }
}

struct CoreDumperPtr(*mut CoreDumper);
unsafe impl Sync for CoreDumperPtr {}
static CORE_DUMPER: SyncUnsafeCell<CoreDumperPtr> = SyncUnsafeCell::new(CoreDumperPtr(ptr::null_mut()));

extern "C" fn fatal_signal_handler(sig: i32, _: *mut libc::siginfo_t, _: *mut libc::c_void) {
    // This is all not signal-safe, but it's better than leaving the process in a broken state.
    unsafe {
        let dumper_ptr = (*CORE_DUMPER.get()).0;
        if dumper_ptr != ptr::null_mut() {
            (*dumper_ptr).cleanup(); // don't detach_ptrace, it's not required
            eprintln!("failed: fatal signal");
        }

        // Restore default signal handler and re-raise the signal to proceed with crashing.

        let mut action: libc::sigaction = mem::zeroed();
        action.sa_sigaction = libc::SIG_DFL;
        libc::sigemptyset(&mut action.sa_mask);
        action.sa_flags = 0;
        libc::sigaction(sig, &action, std::ptr::null_mut());

        libc::raise(sig);

        // In case raising doesn't kill us (shouldn't happen).
        process::exit(128 + sig as i32);
    }
}

pub fn run_core_dumper_tool(pid: pid_t, buffer_size: usize, mode: CoreDumperMode) {
    let mut dumper = CoreDumper {pid, forked_pid: None, buffer_size, mode, attached_threads: Vec::new(), notes_buf: Vec::new(), bytes_written: 0, bytes_read: 0, bytes_total: 0, bytes_at_last_progress_update: 0, start_time: Instant::now(), read_duration: Duration::default(), write_duration: Duration::default(), fork_state: None};
    unsafe { *CORE_DUMPER.get() = CoreDumperPtr(&mut dumper as *mut CoreDumper); }

    // Use panic hook to make sure we correctly resume the process even if we have a bug.
    // Can't use catch_unwind because we're usually built with panic='abort'.
    {
        let default_hook = panic::take_hook();
        panic::set_hook(Box::new(move |info| {
            eprintln!("failed: panic!");
            unsafe {
                let dumper_ptr = (*CORE_DUMPER.get()).0;
                if dumper_ptr != ptr::null_mut() {
                    (*dumper_ptr).cleanup();
                    (*dumper_ptr).detach_ptrace();
                }
            }

            // Print stack trace.
            default_hook(info);

            process::exit(2);
        }));
    }
    // Same but with signal handlers. In particular SIGTERM if the user hit control-C.
    for sig in [libc::SIGSEGV, libc::SIGABRT, libc::SIGILL, libc::SIGFPE, libc::SIGTERM, libc::SIGINT] {
        unsafe {
            let mut action: libc::sigaction = mem::zeroed();
            action.sa_flags = libc::SA_SIGINFO;
            action.sa_sigaction = fatal_signal_handler as *const () as libc::sighandler_t;
            let mut mask: libc::sigset_t = mem::zeroed();
            libc::sigemptyset(&mut mask);
            action.sa_mask = mask;
            let r = libc::sigaction(sig, &action, std::ptr::null_mut());
            if r != 0 {
                eprintln!("warning sigaction({}) failed: {}", signal_name(sig), io::Error::last_os_error());
            }
        }
    }

    match dumper.try_dump() {
        Ok(()) => (),
        Err(e) => {
            eprintln!("failed: {}", e);
            dumper.cleanup();
            dumper.detach_ptrace(); // probably not required when exiting, but why not
            process::exit(3);
        }
    }

    unsafe { *CORE_DUMPER.get() = CoreDumperPtr(ptr::null_mut()); }
}
