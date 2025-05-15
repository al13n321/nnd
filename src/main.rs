#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_imports)]
use nnd::{*, elf::*, error::*, debugger::*, util::*, ui::*, log::*, process_info::*, symbols::*, symbols_registry::*, procfs::*, unwind::*, range_index::*, settings::*, context::*, executor::*, persistent::*, doc::*, terminal::*, common_ui::*, core_dumper::*};
use std::{rc::Rc, mem, fs, os::fd::{FromRawFd}, io::Read, io, io::Write, panic, process, thread, thread::ThreadId, cell::UnsafeCell, ptr, pin::Pin, sync::Arc, str::FromStr, path::PathBuf, collections::HashSet};
use libc::{self, STDIN_FILENO, pid_t};

// Pipes written from corresponding signal handlers, read from main loop. We could use one pipe and write signal number to it, but it would break in the unlikely case when one signal fills up the whole pipe before the main loop drains it - then other signals would get lost. Probably not actually important.
static mut SIGNAL_PIPES_WRITE: [i32; 32] = [-1; 32];

static MAIN_THREAD_ID: SyncUnsafeCell<Option<ThreadId>> = SyncUnsafeCell::new(None);
struct DebuggerPtr(*mut Debugger);
unsafe impl Sync for DebuggerPtr {}
static DEBUGGER_TO_DROP_ON_PANIC: SyncUnsafeCell<DebuggerPtr> = SyncUnsafeCell::new(DebuggerPtr(ptr::null_mut()));

extern "C" fn signal_handler(sig: i32, _: *mut libc::siginfo_t, _: *mut libc::c_void) {
    unsafe {
        libc::write(SIGNAL_PIPES_WRITE[sig as usize], "+".as_ptr() as *const libc::c_void, 1);
    }
}

fn drain_signal_pipe(fd: i32) {
    unsafe {
        let mut temp = [0u8; 128];
        libc::read(fd, temp.as_mut_ptr() as *mut libc::c_void, temp.len());
    }
}

fn parse_arg(args: &mut &[String], seen_args: &mut HashSet<String>, long_name: &str, short_name: &str, bool_switch: bool, repeatable: bool) -> Option<String> {
    assert!(!args.is_empty());
    if args[0].is_empty() {
        return None;
    }
    let check_duplicate = |seen_args: &mut HashSet<String>, long_name: &str, short_name: &str, name: &str, repeatable: bool| {
        if !repeatable {
            if !seen_args.insert(name.to_string()) {
                eprintln!("{} can't be specified multiple times", name);
                process::exit(1);
            }
        }
    };
    if !long_name.is_empty() && args[0].starts_with(long_name) && args[0][long_name.len()..].starts_with("=") {
        check_duplicate(seen_args, long_name, short_name, long_name, repeatable);
        if bool_switch {
            eprintln!("{} doesn't accept a value", long_name);
            process::exit(1);
        }
        let v = args[0][long_name.len()+1..].to_string();
        *args = &args[1..];
        return Some(v);
    }
    if &args[0][..] == short_name || &args[0][..] == long_name {
        let name = if &args[0][..] == short_name {short_name} else {long_name};
        check_duplicate(seen_args, long_name, short_name, name, repeatable);
        if bool_switch {
            *args = &args[1..];
            return Some(String::new());
        }
        if args.len() == 1 {
            eprintln!("{} requires an argument", name);
            process::exit(1);
        }
        let v = args[1].clone();
        *args = &args[2..];
        return Some(v);
    }
    None
}

fn main() {
    precalc_globals_util();
    std::env::set_var("RUST_BACKTRACE", "short");

    let mut settings = Settings::default();
    let mut attach_pid: Option<pid_t> = None;
    let mut command_line: Option<Vec<String>> = None;
    let mut tty_file: Option<String> = None;
    let mut core_dump_path: Option<String> = None;

    let all_args: Vec<String> = std::env::args().collect();
    let mut args = &all_args[1..];
    let mut seen_args: HashSet<String> = HashSet::new();
    let mut use_default_debuginfod_urls = false;
    let mut dump_core = false;
    let mut core_dumper_buffer_size = 1usize << 20;
    let mut core_dumper_mode = CoreDumperMode::Fork;
    while !args.is_empty() && args[0].starts_with("-") {
        if let Some(v) = parse_arg(&mut args, &mut seen_args, "--pid", "-p", false, false) {
            attach_pid = match pid_t::from_str(&v) {
                Err(_) => {
                    eprintln!("invalid pid: {}", v);
                    process::exit(1);
                }
                Ok(x) => Some(x),
            };
        } else if let Some(v) = parse_arg(&mut args, &mut seen_args, "--tty", "-t", false, false) {
            tty_file = Some(v);
        } else if let Some(v) = parse_arg(&mut args, &mut seen_args, "--stdin", "", false, false) {
            settings.stdin_file = Some(v);
        } else if let Some(v) = parse_arg(&mut args, &mut seen_args, "--stdout", "", false, false) {
            settings.stdout_file = Some(v);
        } else if let Some(v) = parse_arg(&mut args, &mut seen_args, "--stderr", "", false, false) {
            settings.stderr_file = Some(v);
        } else if let Some(_) = parse_arg(&mut args, &mut seen_args, "--stop", "-s", true, false) {
            settings.stop_on_main = true;
        } else if let Some(_) = parse_arg(&mut args, &mut seen_args, "--stop-early", "-S", true, false) {
            settings.stop_on_initial_exec = true;
        } else if let Some(m) = parse_arg(&mut args, &mut seen_args, "--mouse", "", false, false) {
            settings.mouse_mode = match &m.to_lowercase()[..] {
                "full" => MouseMode::Full,
                "no-hover" => MouseMode::NoHover,
                "disabled" | "no" | "none" => MouseMode::Disabled,
                _ => {
                    eprintln!("unrecognized --mouse mode: '{}'; expected one of: full, no-hover, disabled", m);
                    process::exit(1);
                }
            };
        } else if let Some(s) = parse_arg(&mut args, &mut seen_args, "--session", "-n", false, false) {
            settings.session_name = match &s[..] {
                "-" => SessionName::Temp,
                "--" => SessionName::None,
                name => SessionName::Name(name.to_string()),
            };
        } else if let Some(_) = parse_arg(&mut args, &mut seen_args, "--echo-input", "", true, false) {
            match run_input_echo_tool() {
                Ok(()) => (),
                Err(e) => eprintln!("error: {}", e),
            }
            return;
        } else if let Some(_) = parse_arg(&mut args, &mut seen_args, "--dump-core", "", true, false) {
            dump_core = true;
        } else if let Some(m) = parse_arg(&mut args, &mut seen_args, "--mode", "", false, false) {
            core_dumper_mode = match &m.to_lowercase()[..] {
                "direct" => CoreDumperMode::Direct,
                "live" => CoreDumperMode::Live,
                "fork" => CoreDumperMode::Fork,
                _ => {
                    eprintln!("unrecognized --mode (core dumping mode): '{}'; expected one of: direct, fork, live", m);
                    process::exit(1);
                }
            };
        } else if let Some(s) = parse_arg(&mut args, &mut seen_args, "--buffer-size", "", false, false) {
            core_dumper_buffer_size = match s.parse::<isize>() {
                Ok(n) if n == -1 => usize::MAX,
                Ok(n) if n > 0 => n as usize,
                Ok(_) | Err(_) => {
                    eprintln!("invalid --buffer-size (core dumper buffer size): '{}'; expected a positive number or -1 (representing infinity)", s);
                    process::exit(1);
                }
            };
        } else if let Some(_) = parse_arg(&mut args, &mut seen_args, "--fixed-fps", "", true, false) {
            settings.fixed_fps = true;
        } else if let Some(path) = parse_arg(&mut args, &mut seen_args, "--dir", "-d", false, false) {
            settings.code_dirs.push(PathBuf::from(path));
        } else if let Some(path) = parse_arg(&mut args, &mut seen_args, "--module", "-m", false, /*repeatable*/ true) {
            settings.supplementary_binary_paths.push(path);
        } else if let Some(s) = parse_arg(&mut args, &mut seen_args, "--period", "", false, false) {
            let seconds = match s.parse::<f64>() {
                Ok(p) if p >= 0.0 && p <= 4e9 => p,
                _ => {
                    eprintln!("invalid --period: '{}', expected real number in [0, 4e9] (in seconds)", s);
                    process::exit(1);
                }
            };
            settings.periodic_timer_ns = (seconds * 1e9) as usize;
        } else if let Some(_) = parse_arg(&mut args, &mut seen_args, "--verbose", "", true, false) {
            settings.trace_logging = true;
        } else if let Some(v) = parse_arg(&mut args, &mut seen_args, "--max-threads", "", false, false) {
            settings.max_threads = match usize::from_str(&v) {
                Err(_) => {
                    eprintln!("invalid --max-threads (expected nonnegative integer): {}", v);
                    process::exit(1);
                }
                Ok(x) => x,
            };
        } else if let Some(s) = parse_arg(&mut args, &mut seen_args, "--core", "-c", false, false) {
            core_dump_path = Some(s);
        } else if let Some(_) = parse_arg(&mut args, &mut seen_args, "--debuginfod", "-o", true, false) {
            use_default_debuginfod_urls = true;
        } else if let Some(_) = parse_arg(&mut args, &mut seen_args, "--aslr", "", true, false) {
            settings.disable_aslr = false;
        } else if let Some(s) = parse_arg(&mut args, &mut seen_args, "--breakpoint", "", false, true) {
            // This allows the path to contain ':' characters.
            let parts: Vec<&str> = s.rsplitn(2, ':').collect();
            if parts.len() != 2 {
                eprintln!("invalid --breakpoint format: '{}', expected path:line", s);
                process::exit(1);
            }
            let line = match parts[0].parse::<usize>() {
                Err(_) => {
                    eprintln!("invalid --breakpoint line number: '{}', expected nonnegative integer", parts[0]);
                    process::exit(1);
                }
                Ok(l) => l,
            };
            let path = parts[1].to_string();

            settings.breakpoints.push(LineBreakpoint {path: path.into(), file_version: FileVersionInfo::default(), line: line, adjusted_line: None});
        } else if print_help_chapter(&args[0], &all_args[0]) {
            process::exit(0);
        } else {
            eprintln!("unrecognized argument: '{}' (if it's the command to run, prepend '\\' to escape)", args[0]);
            process::exit(1);
        }
    }

    if dump_core {
        if attach_pid.is_none() {
            eprintln!("--dump-core requires -p <pid>");
            process::exit(1);
        }
        run_core_dumper_tool(attach_pid.unwrap(), core_dumper_buffer_size, core_dumper_mode);
        return;
    }

    if settings.code_dirs.is_empty() {
        settings.code_dirs.push(PathBuf::from(""));
    }

    settings.debuginfod_urls = get_debuginfod_urls(use_default_debuginfod_urls);

    // Autodetect core dump without requiring -c.
    if core_dump_path.is_none() && attach_pid.is_none() && !args.is_empty() {
        let r = is_core_dump_file(&args[0]);
        if let Ok(true) = r { // silently ignore errors
            core_dump_path = Some(args[0].clone());
            args = &args[1..];
        }
    }
    if core_dump_path.is_some() && !args.is_empty() {
        settings.supplementary_binary_paths.insert(0, args[0].clone());
        args = &args[1..];
    }

    if !args.is_empty() {
        let mut cmd = args[..].to_vec();
        if cmd[0].starts_with("\\") {
            cmd[0] = cmd[0][1..].to_string();
        }
        command_line = Some(cmd);
    }

    if let Some(v) = tty_file {
        settings.stdin_file = Some(v.clone());
        settings.stdout_file = Some(v);
    }

    if attach_pid.is_none() && command_line.is_none() && core_dump_path.is_none() {
        eprintln!("usage: {} (-p pid | executable_path [args..] | [-c] core_dump_path [[--exe] executable_path] | --help)", all_args[0]);
        process::exit(1);
    }
    if (attach_pid.is_some() as usize) + (command_line.is_some() as usize) + (core_dump_path.is_some() as usize) > 1 {
        eprintln!("must have exactly one of: --pid, --core, command line");
        process::exit(1);
    }
    if command_line.is_none() && (settings.stdin_file.is_some() || settings.stdout_file.is_some() || settings.stderr_file.is_some()) {
        eprintln!("--stdin/--stdout/--stderr/--tty are not allowed with --pid or --core");
        process::exit(1);
    }

    // This redirects stderr to the log file, so we have to do it early.
    let persistent = match PersistentState::init(&settings) {
        Ok(x) => x,
        Err(e) => {
            // (This only happens if session name was provided on the command line. Otherwise PersistentState has fallback behavior if directory couldn't be created.)
            eprintln!("error: {}", e);
            process::exit(1);
        }
    };
    settings.debuginfod_cache_path = persistent.debuginfod_cache_path.clone();
    let (log_file_path, original_stderr_fd) = (persistent.log_file_path.clone(), persistent.original_stderr_fd);

    let supplementary_binaries = match SymbolsRegistry::open_supplementary_binaries(&settings) {
        Ok(x) => x,
        Err(e) => {
            eprintln!("{}", e);
            if let &Some(fd) = &original_stderr_fd {
                let mut original_stderr = std::mem::ManuallyDrop::new(unsafe {std::fs::File::from_raw_fd(fd)});
                let _ = writeln!(original_stderr, "error: {}", e);
                let _ = original_stderr.flush();
            }
            process::exit(1);
        }
    };

    // There are two pieces of best-effort cleanup we need to do on panic:
    //  * Remove breakpoints and detach from the process, if attached with -p.
    //    Currently we only do it if the panic happened in the main thread.
    //  * Restore terminal state.
    // We do these things in panic handler.
    // We avoid unwinding and calling destructors because that can cause additional bogus errors.
    //
    // (Alternatively, we could panic-safe all the code, propagate panics to the main thread, and enable unwinding.
    //  But that sounds worse: (a) more work, (b) hard to have adequate test coverage for all possible panic unwind scenarios.
    //  E.g. maybe some destructor anywhere in the code base inadvertently expects the struct to be in certain clean state -
    //  usually no one will ever notice that until it happens in practice. Or maybe some destructor does something unnecessary and slow,
    //  e.g. wait for background work to complete. In contrast, the panic handler is small and doesn't make many assumptions.)
    unsafe {*MAIN_THREAD_ID.get() = Some(thread::current().id())}; // assign before spawning any threads
    {
        let default_hook = panic::take_hook();
        panic::set_hook(Box::new(move |info| {
            // Print stack trace.
            default_hook(info);

            // Remove breakpoints and detach. This is sketchy if the panic was thrown from inside a Debugger method,
            // but should be almost always fine, and this is best-effort anyway.
            unsafe {
                if Some(thread::current().id()) == *MAIN_THREAD_ID.get() {
                    #[allow(static_mut_refs)]
                    let d = (*DEBUGGER_TO_DROP_ON_PANIC.get()).0;
                    if d != ptr::null_mut() {
                        ptr::drop_in_place(d);
                    }
                }
            }

            // This is not fully reliable because other threads still execute while this hook is running,
            // so the main thread may hide cursor or output a rendered frame after we restored the terminal.
            // To minimize the chance of that, we put this near the end of the hook, importantly after the slow default hook.
            restore_terminal();

            // Print something to the console, otherwise it'll be left confusingly empty, as if the debugger just quit silently.
            if let &Some(fd) = &original_stderr_fd {
                let mut original_stderr = std::mem::ManuallyDrop::new(unsafe {std::fs::File::from_raw_fd(fd)});
                let _ = writeln!(original_stderr, "panic! this usually indicates a bug, please report (create an issue at https://github.com/al13n321/nnd/issues or send an email to mk.al13n+nnd@gmail.com)");
                if let Some(p) = &log_file_path {
                    let _ = writeln!(original_stderr, "there should be an error message and stack trace at the end of {} - please include them in the report", p.display());
                }
                let _ = original_stderr.flush();
            }

            process::exit(2); // this is redundant with panic='abort', but why not
        }));
    }

    match run(settings, attach_pid, core_dump_path, command_line, persistent, supplementary_binaries) {
        Ok(()) => (),
        Err(e) => {
            eprintln!("fatal: {}", e);
            if let &Some(fd) = &original_stderr_fd {
                let mut original_stderr = std::mem::ManuallyDrop::new(unsafe {std::fs::File::from_raw_fd(fd)});
                let _ = writeln!(original_stderr, "error: {}", e);
                let _ = original_stderr.flush();
            }
            process::exit(1);
        }
    }
}

fn run(settings: Settings, attach_pid: Option<pid_t>, core_dump_path: Option<String>, command_line: Option<Vec<String>>, persistent: PersistentState, supplementary_binaries: SupplementaryBinaries) -> Result<()> {
    let num_threads = thread::available_parallelism().map_or(8, |n| n.get()).min(settings.max_threads).max(1);
    let context = Arc::new(Context {settings, executor: Executor::new(num_threads), wake_main_thread: Arc::new(EventFD::new())});

    let epoll = Rc::new(Epoll::new()?);

    // Forward some signals into pipes that wake up the main loop.
    // SIGCHLD is raised when we need to frob ptrace.
    // (I also tried using pidfd, but it turned out to be currenlty broken/annoying in Linux in multiple ways: (1) it's not reported to the tracer if this process is itself ptraced (e.g. if you strace the debugger), (2) the signal needs to be blocked in all threads individually, (3) the fd is inherited by forked processes and needs to be closed manually.)
    let mut signal_pipes_read = [-1i32; 32];
    for sig in [libc::SIGCHLD, libc::SIGWINCH] {
        unsafe {
            // Create a pipe.
            let mut pipe = [0i32; 2];
            let r = libc::pipe2(pipe.as_mut_ptr(), libc::O_NONBLOCK | libc::O_CLOEXEC);
            if r != 0 { return errno_err!("pipe() failed"); }
            SIGNAL_PIPES_WRITE[sig as usize] = pipe[1];
            signal_pipes_read[sig as usize] = pipe[0];

            // Set signal handler.
            let mut action: libc::sigaction = mem::zeroed();
            action.sa_flags = libc::SA_SIGINFO;
            action.sa_sigaction = signal_handler as libc::sighandler_t;
            let mut mask: libc::sigset_t = mem::zeroed();
            libc::sigemptyset(&mut mask);
            action.sa_mask = mask;
            let r = libc::sigaction(sig, &action, std::ptr::null_mut());
            if r != 0 { return errno_err!("sigaction() failed"); }

            epoll.add(pipe[0], libc::EPOLLIN, pipe[0] as u64)?;
        }
    }

    let frame_ns = (1e9 / context.settings.fps) as usize;
    let render_timer = TimerFD::new();

    // Timer for various periodic tasks.
    let periodic_timer = TimerFD::new();
    // 0 means no periodic timer.
    periodic_timer.set(1, context.settings.periodic_timer_ns);

    epoll.add(STDIN_FILENO, libc::EPOLLIN, STDIN_FILENO as u64)?;
    epoll.add(render_timer.fd, libc::EPOLLIN, render_timer.fd as u64)?;
    epoll.add(periodic_timer.fd, libc::EPOLLIN, periodic_timer.fd as u64)?;

    let _restorer = TerminalRestorer;
    configure_terminal(context.settings.mouse_mode)?;

    let mut debugger: Pin<Box<Debugger>>;
    if let &Some(pid) = &attach_pid {
        debugger = Pin::new(Box::new(Debugger::attach(pid, context.clone(), persistent, supplementary_binaries)?));
        #[allow(static_mut_refs)]
        unsafe { *DEBUGGER_TO_DROP_ON_PANIC.get() = DebuggerPtr(&mut *debugger); }
    } else if let Some(path) = &core_dump_path {
        debugger = Pin::new(Box::new(Debugger::open_core_dump(path, context.clone(), persistent, supplementary_binaries)?));
    } else {
        debugger = Pin::new(Box::new(Debugger::from_command_line(&command_line.unwrap(), context.clone(), persistent, supplementary_binaries)));

        // Apply this only for the first time we start the program. For subsequent starts, the user can use steps instead (e.g. 's' to start and run to main()).
        let initial_step = if context.settings.stop_on_initial_exec {
            Some(BreakpointOn::InitialExec)
        } else if context.settings.stop_on_main {
            Some(BreakpointOn::PointOfInterest(PointOfInterest::MainFunction))
        } else {
            None
        };
        debugger.start_child(initial_step)?;
    }
    defer! {
        #[allow(static_mut_refs)]
        unsafe {*DEBUGGER_TO_DROP_ON_PANIC.get() = DebuggerPtr(ptr::null_mut());}
    }

    let mut ui = DebuggerUI::new();

    let config_change_fd = PersistentState::load_state_and_configs(&mut debugger, &mut ui);

    let symbols_event_fd = debugger.symbols.event_fd();
    epoll.add(symbols_event_fd.fd, libc::EPOLLIN, symbols_event_fd.fd as u64)?;

    let misc_wakeup_fd = debugger.context.wake_main_thread.clone();
    epoll.add(misc_wakeup_fd.fd, libc::EPOLLIN, misc_wakeup_fd.fd as u64)?;

    if let &Some(fd) = &config_change_fd {
        epoll.add(fd, libc::EPOLLIN, fd as u64)?;
    }

    // Throttle rendering to <= fps. Render only when something changes.
    let mut pending_render = true;
    render_timer.set(1, 0);

    let mut have_debugger_events = false;

    if context.settings.fixed_fps {
        render_timer.set(1, frame_ns);
    }

    for line_breakpoint in &context.settings.breakpoints {
        let existing_id = debugger.find_line_breakpoint_fuzzy(&line_breakpoint);
        if let Some(id) = existing_id {
            let _ = debugger.set_breakpoint_enabled(id, true);
        } else {
            let _ = debugger.add_breakpoint(BreakpointOn::Line(line_breakpoint.clone()));
        }
    }

    // The debugger.process_events() path of this loop should be kept light, it'll likely be the bottleneck for conditional breakpoints (including thread-specific breakpoints, including temporary breakpoints when stepping).
    loop {
        let mut events: [libc::epoll_event; 32] = unsafe { mem::zeroed() };
        let n = epoll.wait(&mut events)?;
        let mut render_now = false;
        let mut schedule_render = false;
        for event in &events[..n] {
            let fd = event.u64 as i32;
            let prof = TscScopeExcludingSyscalls::new(&debugger.prof.bucket);
            schedule_render = true;
            if fd == signal_pipes_read[libc::SIGCHLD as usize] {
                drain_signal_pipe(fd);
                have_debugger_events = true;
            } else if fd == signal_pipes_read[libc::SIGWINCH as usize] {
                drain_signal_pipe(fd);
            } else if fd == misc_wakeup_fd.fd {
                misc_wakeup_fd.read();
            } else if fd == STDIN_FILENO {
                let significant = ui.buffer_input(&mut debugger.prof.bucket)?;
                if !significant {
                    schedule_render = false;
                } else if !pending_render && !context.settings.fixed_fps {
                    render_now = true;
                }
            } else if fd == render_timer.fd {
                render_timer.read();
                pending_render = false;
                render_now = true;
            } else if fd == symbols_event_fd.fd {
                let drop_caches = debugger.symbols.process_events();
                if drop_caches {
                    // After symbols are loaded, recalculate things like stack traces, retry activating breakpoints, etc.
                    // (As currently implemented, this call can't be omitted or delayed, Debugger has some asserts that rely on drop_caches() being called after symbols are loaded before anything else happens.)
                    debugger.drop_caches()?;
                    ui.drop_caches();
                }
                debugger.prof.bucket.other_tsc += prof.finish(&debugger.prof.bucket);
            } else if fd == periodic_timer.fd {
                periodic_timer.read();
                debugger.refresh_all_resource_stats();
                PersistentState::try_to_save_state_if_changed(&mut debugger, &mut ui);
                debugger.prof.bucket.other_tsc += prof.finish(&debugger.prof.bucket);
                debugger.prof.advance_bucket();
            } else if &Some(fd) == &config_change_fd {
                PersistentState::process_events(&mut debugger, &mut ui);
            } else {
                return err!(Internal, "epoll returned unexpected data: {}", fd);
            }
        }

        if have_debugger_events {
            let mut prof = TscScopeExcludingSyscalls::new(&debugger.prof.bucket);
            let drop_caches;
            (have_debugger_events, drop_caches) = debugger.process_events()?;
            debugger.prof.bucket.debugger_tsc += prof.restart(&debugger.prof.bucket);
            if drop_caches {
                debugger.drop_caches()?;
                ui.drop_caches();
                debugger.prof.bucket.other_tsc += prof.finish(&debugger.prof.bucket);
            }

            if have_debugger_events {
                // process_events() yielded to give us a chance to render a frame; need to call it again right after that.
                debugger.context.wake_main_thread.write(1);
            }
        }

        if render_now {
            assert!(!pending_render);
            schedule_render = false;

            ui.update_and_render(&mut debugger)?;

            if ui.should_quit {
                // Clean exit. We need to:
                //  * Save PersistentState.
                //  * Detach from the process if in Attach mode. (If in Run mode, the process will get killed automatically because of PR_SET_PDEATHSIG).
                //  * Restore terminal state.
                //  * Flush stderr.
                // After that, just quit without wasting time on calling all the destructors.
                // In particular, destroying Symbols can take seconds, which is really annoying for the user. (That's mostly because of lots of small Vec-s in Symbols; it would be nice to get rid of them for loading performance too.)
                PersistentState::try_to_save_state_if_changed(&mut debugger, &mut ui);
                debugger.shutdown();
                restore_terminal();
                LogTimestampInDestructor("shutdown complete");
                std::process::exit(0); // flushes stderr
            }

            schedule_render |= ui.ui.should_redraw || ui.should_drop_caches;
            if ui.should_drop_caches {
                let prof = TscScopeExcludingSyscalls::new(&debugger.prof.bucket);
                debugger.drop_caches()?;
                ui.drop_caches();
                debugger.prof.bucket.other_tsc += prof.finish(&debugger.prof.bucket);
            }
        }

        if schedule_render && !pending_render && !context.settings.fixed_fps {
            pending_render = true;
            render_timer.set(frame_ns, 0);
        }
    }
}
