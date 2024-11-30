use crate::{*, elf::*, error::*, util::*, log::*, symbols::*, process_info::*, symbols_registry::*, unwind::*, procfs::*, registers::*, disassembly::*, pool::*, settings::*, context::*, disassembly::*, expr::*, persistent::*, interp::*};
use libc::{pid_t, c_char, c_void};
use iced_x86::FlowControl;
use std::{io, ptr, rc::Rc, collections::{HashMap, VecDeque, HashSet}, mem, path::{Path, PathBuf}, sync::Arc, ffi::CStr, ops::Range, os::fd::AsRawFd, fs, time::{Instant, Duration}};

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum RunMode {
    Run, // start the program inside the debugger
    Attach, // attach to a running process
    // TODO: CoreDump,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ProcessState {
    NoProcess,
    Starting,
    Exiting,

    Running,
    Suspended,

    Stepping,
}
impl ProcessState {
    pub fn process_ready(self) -> bool {
        match self {
            Self::NoProcess | Self::Starting | Self::Exiting => false,
            Self::Running | Self::Suspended | Self::Stepping => true,
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ThreadState {
    Running,
    Suspended,
}

pub struct Thread {
    pub idx: usize,
    pub tid: pid_t,
    // Whether the thread is running or suspended, as seen by ptrace.
    // We often want to do things when this changes, so keep the number of code sites than change it to a minimum.
    pub state: ThreadState,

    pub info: ThreadInfo,

    // If not empty, the thread is currently stopped because it hit these breakpoints (which all have the same address) or fatal signals.
    // Empty if the thread is stopped as part of stopping all threads (e.g. with C-c or because a different thread hit a breakpoint).
    // Just for UI, not used by the debugger core.
    pub stop_reasons: Vec<StopReason>,

    // How many times this thread was stopped visibly to the user. Excludes spurious stops that we immediately resumed, e.g. conditional breakpoints with unsatisfied condition.
    // May also be incremented for no-op "steps", e.g. step-into from non-top stack subframe just switches to the previous stack subframe without actually stepping; in that case we assign subframe_to_select and increment stop_count.
    // If this didn't change then things like registers and stack trace also didn't change.
    pub stop_count: usize,
    // If the last stop was caused by a completed step or breakpoint hit, this field may tell what subframe of the stack trace should be made current, for the user.
    // E.g. if we started in function A and did a step-over over an inlined function X and immediately got into another inlined function Y, we should show subframe A instead of Y.
    // If we hit a breakpoint on a line that contains inlined function call, select the subframe that shows the call, not the top subframe that shows the insides of the inlined function.
    pub subframe_to_select: Option<usize>,

    // Indicates whether we resumed or should resume this thread using PTRACE_SINGLESTEP instead of PTRACE_CONT.
    // We have to keep track of this to handle software breakpoints correctly, see comment in handle_breakpoint_trap().
    //
    // As usual with ptrace, there's a complication: a spurious SIGTRAP may get delivered if:
    //  (1) we do SINGLESTEP, then
    //  (2) we get a non-SIGTRAP signal (e.g. an unrelated group-stop), then
    //  (3) we do CONT, then
    //  (4) we maybe get a SIGTRAP out of nowhere, even if instruction pointer didn't change.
    // See singlestep_vs_group_stop.cpp for repro. We can't allow spurious SIGTRAPs.
    //
    // We prevent this scenario by preventing part (3). After doing one SINGLESTEP, we keep doing SINGLESTEP until we get a SIGTRAP.
    // This way the spurious SIGTRAP gets correctly interpreted as relating to a SINGLESTEP, with no ambiguity.
    // To this end, the single_stepping flag is unset only when we get SIGTRAP, and while it's set we always do SINGLESTEP instead of CONT.
    single_stepping: bool,

    // This serves two purposes:
    //  * When a software breakpoint is hit, we convert it to hardware breakpoint. After we resume the thread that hit the sw breakpoint,
    //    it immediately hits the hw breakpoint. This field is used to automatically resume the thread after such duplicate hit.
    //  * When a new breakpoint is added on the current line, the user is probably interested in the *next* time this line is hit,
    //    so we skip the initial hit that will happen right away.
    // Applies only to user breakpoints and single-instruction-step-into. For internal breakpoints we want to handle spurious hits too, to re-request single step when needed.
    ignore_next_hw_breakpoint_hit_at_addr: Option<usize>,

    waiting_for_initial_stop: bool,

    // We did PTRACE_INTERRUPT for this thread and didn't get a corresponding stop event yet.
    sent_interrupt: bool,

    // Signal to inject the next time this thread resumes.
    // Usually a user signal to pass-through, e.g. SIGUSR1 or SIGPIPE.
    // (It's stored here instead of being passed-through immediately because of a corner case: if the signal arrived at the same time when we decided to suspend
    //  the process for unrelated reasons, we don't want to resume the thread right away, so the signal injection needs to wait until the next time we resume the thread.)
    //
    // Be careful with this. `man ptrace` says:
    //  > Restarting ptrace commands issued in ptrace-stops other than signal-delivery-stop are not guaranteed to inject a signal, even if sig is nonzero.
    //  > No error is reported; a nonzero sig may simply be ignored.  Ptrace users should not try to "create a new signal" this way: use tgkill(2) instead.
    // So, this field should only be assigned when a thread is stopped by a signal, and should always be delivered next time the thread is resumed.
    pending_signal: Option<i32>,

    // Just for an assert around a minor race condition between attaching and creating threads.
    attached_late: bool,

    // Got PTRACE_EVENT_EXIT, this thread will exit soon. If it's running, it may have already disappeared, so we shouldn't try to read its information from /proc/
    pub exiting: bool,
}

// A debug session, where we are attached to some process (child or otherwise).
pub struct Debugger {
    pub mode: RunMode,
    command_line: Vec<String>,
    pub context: Arc<Context>,

    pub pid: pid_t,
    // What we would like threads to be doing: run or be suspended. If a thread gets stopped spuriously (e.g. by a signal or a thread spawn), but we want threads to be running, we resume the thread immediately.
    // Whoever changes this state must also suspend/resume all threads accordingly.
    pub target_state: ProcessState,

    pub next_thread_idx: usize,
    pub threads: HashMap<pid_t, Thread>,

    pub info: ProcessInfo,
    pub my_resource_stats: ResourceStats, // for debugger itself, as opposed to info.total_resource_stats
    pub symbols: SymbolsRegistry,

    pub memory: MemReader,

    // Stages of starting the child process that need some special handling.
    waiting_for_initial_sigstop: bool,

    // We're suspending all threads to do something with breakpoints. Once all threads are stopped, we do the thing and resume (if target_state says so).
    pub stopping_to_handle_breakpoints: bool,

    // Whether we're keeping all threads suspended (despite target_state being Running or Stepping) until symbols are loaded.
    // The value is an id of one of the binaries that are still loading (last time we checked).
    // We do this if there are any active breakpoints or pending steps (e.g. step to start of main()) that require symbols.
    // (Why not just always keep the process stopped until symbols are loaded, since the debugger can't do much without symbols loaded?
    //  Because of this use case: start some long-running server, then go send requests to it right away. It's convenient to be able to
    //  always start the server in the debugger, just in case (to be able to debug it if it crashes or if you later want to set a breakpoint).
    //  If the debugger delays server startup by few seconds, that's a non-starter.)
    pub stopped_until_symbols_are_loaded: Option<usize>,

    pub stepping: Option<StepState>,

    // Start this step when we're ready: on PTRACE_EVENT_EXEC and/or after symbols are loaded.
    pub pending_step: Option<(pid_t, BreakpointOn)>,

    pub breakpoint_locations: Vec<BreakpointLocation>, // sorted by address
    pub breakpoints: Pool<Breakpoint>,
    pub hardware_breakpoints: [HardwareBreakpoint; 4],

    // ptrace may report a signal for a thread before reporting the clone() that created that thread.
    // We buffer such signals in this queue and process them as soon as the thread appears in `threads`.
    pending_wait_events: VecDeque<(pid_t, i32)>,

    pub log: Log,
    pub prof: Profiling,
    pub persistent: PersistentState,
}

#[derive(Clone, Copy, Eq, PartialEq, Debug)]
pub enum StepKind {
    Into,
    Over,
    Out,
    // Run-to-cursor.
    Cursor,
}

#[derive(Debug)]
pub struct StepState {
    pub tid: pid_t,
    pub keep_other_threads_suspended: bool, // must stay constant for the duration of the step (we rely on it for a small optimization in process_events())
    pub disable_breakpoints: bool,

    // How to determine if the step is complete:
    //  * Into && by_instructions: addr not in step.addr_ranges
    //  * Into: cfa != step.cfa || addr not in step.addr_ranges
    //  * Over: cfa > step.cfa || (cfa == step.cfa && addr not in step.addr_ranges)
    //  * Out: cfa > step.cfa
    // `internal_kind` may be different from the user-level step kind. E.g. step-out-of-inlined-function is turned into step-over.
    pub internal_kind: StepKind,
    pub by_instructions: bool,
    pub addr_ranges: Vec<Range<usize>>,
    // Canonical frame address, i.e. something like the RBP register - identifies the current call frame.
    pub cfa: usize,
    // Do repeated PTRACE_SINGLESTEP instead of using internal breakpoints.
    pub single_steps: bool,
    // Identities of stack subframes before the step. Helps determine which subframe to select after the step, depending on internal_kind:
    //  * If stack_digest is empty, select the top subframe. E.g. for instruction steps.
    //  * If Over or Out, select the lowest common ancestor (LCA) of the pre-step and post-step stacks.
    //    (Without inlined functions we could just select the top. But with inlined functions, a single instruction step may take us
    //     out of multiple levels of inlined calls and into multiple levels of new inlined calls. In such case we don't want
    //     the focus to enter those new subframes, that would be confusing.)
    //  * If Into, find the LCA of the pre-step and post-step stacks. If it's the top of the pre-step stack (i.e. we really stepped into)
    //    then go one subframe deeper. Otherwise stay on the LCA.
    pub stack_digest: Vec<usize>,
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Clone, Copy)]
pub enum StepBreakpointType {
    Call,
    JumpOut,
    AfterRet,
    AfterRange,
    Catch,
    Cursor(/*subfunction_level*/ u16),
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub enum BreakpointRef {
    Step(StepBreakpointType), // temporary breakpoint for Debugger::stepping
    Id {id: BreakpointId, subfunction_level: u16},
}

pub type BreakpointId = Id;

pub struct BreakpointLocation {
    pub addr: usize,
    pub original_byte: u8, // that we replaced with 0xcc
    pub hardware: bool,
    // Whether the breakpoint is actually poked into the machine code (if software) or assigned to debug registers of all threads (if hardware).
    // False only for newly added breakpoints or if there was an error activating it (e.g. ran out of hardware breakpoints).
    // handle_breakpoints() is the main place where we activate or deactivate breakpoint locations, and it tries to activate all locations all the time.
    pub active: bool,
    // Multiple breakpoints can have the same location, e.g. line number breakpoint vs function entry breakpoint vs single-step temporary breakpoint.
    // If empty, we should deactivate and remove this location; this operation can be deferred until any thread is suspended (see "PTRACE_POKETEXT is dumb").
    pub breakpoints: Vec<BreakpointRef>,
    pub error: Option<Error>,
}

#[derive(Clone, Debug)]
pub struct HardwareBreakpoint {
    pub active: bool,
    // We allocate hardware breakpoint slots as if no breakpoints are thread-specific. This is fine currently since only steps use thread-specific breakpoints, but
    // if we add support for user-provided thread-specific breakpoints we may want to make thread-specific hw breakpoint allocation be per thread.
    pub thread_specific: Option<pid_t>,
    pub addr: usize,
}

#[derive(Debug, Clone)]
pub struct LineBreakpoint {
    pub path: PathBuf,
    pub file_version: FileVersionInfo,
    pub line: usize,
    // If the `line` corresponds to no machine instructions (e.g. it points to a comment or it's optimized out), we put the breakpoint on the next line that has code and point `adjusted_line` to that line, and the UI shows different breakpoint markers on both lines.
    // We don't modify `line` because that would be confusing in the UI in case when breakpoint is set before symbols are loaded (e.g. in a dynamic library), and we can't adjust the line right away.
    pub adjusted_line: Option<usize>,
}

#[derive(Debug, Clone)]
pub struct AddressBreakpoint {
    // We remember the address relative to its function to make the breakpoint survive changes to the executable.
    pub function: Option<(FunctionLocator, /*offset*/ usize)>,
    pub addr: usize, // in case `function` is None or not found
    pub subfunction_level: u16,
}

#[derive(Debug, Clone)]
pub enum BreakpointOn {
    Line(LineBreakpoint),
    Address(AddressBreakpoint),
    InitialExec, // right after initial exec (PTRACE_EVENT_EXEC)
    PointOfInterest(PointOfInterest),
    // Could add data breakpoints, syscall, signal, etc.
}

pub struct Breakpoint {
    pub on: BreakpointOn,
    pub condition: Option<(String, Result<Expression>, Option<Error>)>,
    pub hits: usize, // including spurious stops of all kinds
    // Cached list of addresses, determined using the BreakpointOn and debug symbols. NotCalculated if we didn't resolve this yet.
    // The addresses are dynamic, not static, so we clear this list when restarting the debuggee as runtime addresses may have changed.
    // If the breakpoint is on a line that has inlined function call, subfunction_level is the depth of that inlined call.
    // When the breakpoint is hit we should select the stack subframe at that inline depth, not the top subframe that shows the insides
    // of the inlined function (it's very confusing otherwise). If u16::MAX, no subframe selection is made (so ui probably selects the top subframe).
    pub addrs: Result<Vec<(usize, /*subfunction_level*/ u16)>>,
    // Directly controlled by the user, may be true even if we failed to activate the breakpoint.
    pub enabled: bool,
    // True if this breakpoint's addresses are added to breakpoint_locations (even if these locations failed to activate).
    pub active: bool,
}
impl Breakpoint {
    fn save_state(&self, out: &mut Vec<u8>) -> Result<()> {
        match &self.on {
            BreakpointOn::Line(b) => {
                out.write_u8(0)?;
                out.write_path(&b.path)?;
                b.file_version.save_state(out)?;
                out.write_usize(b.line)?;
            }
            BreakpointOn::Address(b) => {
                out.write_u8(1)?;
                match &b.function {
                    None => out.write_u8(0)?,
                    Some((f, off)) => {
                        out.write_u8(1)?;
                        f.save_state(out)?;
                        out.write_usize(*off)?;
                    }
                }
                out.write_usize(b.addr)?;
                out.write_u16(b.subfunction_level)?;
            }
            BreakpointOn::InitialExec => out.write_u8(2)?,
            BreakpointOn::PointOfInterest(point) => {
                out.write_u8(3)?;
                point.save_state(out)?;
            }
        }
        if let Some((s, _, _)) = &self.condition {
            out.write_u8(1)?;
            out.write_str(s)?;
        } else {
            out.write_u8(0)?;
        }
        Ok(())
    }

    fn load_state(inp: &mut &[u8]) -> Result<Breakpoint> {
        let on = match inp.read_u8()? {
            0 => BreakpointOn::Line(LineBreakpoint {path: inp.read_path()?, file_version: FileVersionInfo::load_state(inp)?, line: inp.read_usize()?, adjusted_line: None}),
            1 => {
                let function = match inp.read_u8()? {
                    0 => None,
                    1 => Some((FunctionLocator::load_state(inp)?, inp.read_usize()?)),
                    x => return err!(Environment, "unexpected AddressBreakpoint function flag: {}", x),
                };
                BreakpointOn::Address(AddressBreakpoint {function, addr: inp.read_usize()?, subfunction_level: inp.read_u16()?})
            }
            2 => BreakpointOn::InitialExec,
            3 => BreakpointOn::PointOfInterest(PointOfInterest::load_state(inp)?),
            x => return err!(Environment, "unexpected breakpoint type in save file: {}", x),
        };
        let condition = match inp.read_u8()? {
            0 => None,
            1 => {
                let s = inp.read_str()?;
                let expr = parse_watch_expression(&s);                
                Some((s, expr, None))
            }
            x => return err!(Environment, "unexpected breakpoint condition flag in save file: {}", x),
        };
        Ok(Breakpoint {on, condition, hits: 0, addrs: err!(NotCalculated, ""), enabled: false, active: false})
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum StopReason {
    Breakpoint(BreakpointId),
    Step,
    Signal(i32),
    Exception,
}
impl StopReason {
    // If different threads simultaneously stopped for different reasons, the ui should switch to the one with highest-priority reason.
    pub fn priority(&self) -> isize /* >= 0 */ {
        match self {
            Self::Breakpoint(_) => 0,
            Self::Step => 1,
            Self::Exception => 2,
            Self::Signal(_) => 3,
        }
    }
}

impl Thread {
    fn new(idx: usize, tid: pid_t, state: ThreadState) -> Self {
        Thread {idx: idx, tid: tid, state: state, single_stepping: false, ignore_next_hw_breakpoint_hit_at_addr: None, stop_reasons: Vec::new(), info: ThreadInfo::default(), pending_signal: None, waiting_for_initial_stop: true, sent_interrupt: false, stop_count: 0, attached_late: false, exiting: false, subframe_to_select: None}
    }
}

impl Debugger {
    fn new(mode: RunMode, command_line: Vec<String>, context: Arc<Context>, symbols: SymbolsRegistry, breakpoints: Pool<Breakpoint>, persistent: PersistentState, my_resource_stats: ResourceStats, prof: Profiling) -> Self {
        Debugger {mode, command_line, context, pid: 0, target_state: ProcessState::NoProcess, log: Log::new(), prof, threads: HashMap::new(), pending_wait_events: VecDeque::new(), next_thread_idx: 1, info: ProcessInfo::default(), my_resource_stats, symbols, memory: MemReader::invalid(), waiting_for_initial_sigstop: false, stepping: None, pending_step: None, breakpoint_locations: Vec::new(), breakpoints, stopping_to_handle_breakpoints: false, stopped_until_symbols_are_loaded: None, hardware_breakpoints: std::array::from_fn(|_| HardwareBreakpoint {active: false, thread_specific: None, addr: 0}), persistent}
    }

    pub fn save_state(&self, out: &mut Vec<u8>) -> Result<()> {
        for (id, bp) in self.breakpoints.iter() {
            out.write_u8(1)?;
            bp.save_state(out)?;
        }
        out.write_u8(0)?;
        Ok(())
    }

    pub fn load_state(&mut self, inp: &mut &[u8]) -> Result<()> {
        loop {
            match inp.read_u8()? {
                0 => break,
                1 => (),
                x => return err!(Environment, "unexpected bool in save file: {}", x),
            }
            self.breakpoints.add(Breakpoint::load_state(inp)?);
        }
        Ok(())
    }

    pub fn from_command_line(args: &[String], context: Arc<Context>, persistent: PersistentState) -> Self {
        Self::new(RunMode::Run, args.into(), context.clone(), SymbolsRegistry::new(context), Pool::new(), persistent, ResourceStats::default(), Profiling::new())
    }

    pub fn attach(pid: pid_t, context: Arc<Context>, persistent: PersistentState) -> Result<Self> {
        let mut r = Self::new(RunMode::Attach, Vec::new(), context.clone(), SymbolsRegistry::new(context), Pool::new(), persistent, ResourceStats::default(), Profiling::new());
        r.pid = pid;
        r.target_state = ProcessState::Running;
        r.memory = MemReader::new(pid);

        let mut seen_threads: HashSet<pid_t> = HashSet::new();
        for round in 0.. {
            let threads = match list_threads(pid) {
                Ok(x) => x,
                Err(e) if e.is_io_not_found() => return err!(ProcessState, "no process with pid {}", pid),
                Err(e) => return Err(e),
            };
            let mut found_new_threads = false;
            for tid in threads {
                if !seen_threads.insert(tid) {
                    continue;
                }
                found_new_threads = true;
                match unsafe {ptrace(libc::PTRACE_SEIZE, tid, 0, (libc::PTRACE_O_TRACECLONE | libc::PTRACE_O_TRACEEXEC | libc::PTRACE_O_TRACEEXIT | libc::PTRACE_O_TRACESYSGOOD) as u64, &mut r.prof.bucket)} {
                    Ok(_) => (),
                    Err(e) if e.is_io_permission_denied() => return err!(Usage, "ptrace({}) failed: operation not permitted - missing sudo?", tid),
                    Err(e) => return Err(e),
                }
                let mut thread = Thread::new(r.next_thread_idx, tid, ThreadState::Running);
                r.next_thread_idx += 1;

                // The newly appeared thread may also be noticed by PTRACE_O_TRACECLONE (if we already attached parent thread when it was spawned). Set a flag saying that it's ok.
                thread.attached_late = round > 0;

                r.threads.insert(tid, thread);
            }
            if !found_new_threads {
                break;
            }
            // New threads may have been spawned while we were attaching (before we attached to their parent thread), so list threads again and re-check.
        }

        refresh_maps_and_binaries_info(&mut r);
        for t in r.threads.values_mut() {
            refresh_thread_info(pid, t, &mut r.prof.bucket, &r.context.settings);
        }

        Ok(r)
    }

    pub fn start_child(&mut self, initial_step: Option<BreakpointOn>) -> Result<()> {
        if self.mode != RunMode::Run { return err!(Usage, "can't start new process in attach mode"); }
        if self.target_state != ProcessState::NoProcess { return err!(Usage, "already debugging, can't start"); }
        eprintln!("info: starting child");

        {
            // Clear all fields but a few. I guess this suggests that these fields should be grouped into a struct (or a few). Would probably
            // make sense to split things up somewhat (in particular, probably separate breakpoints from threads), but not go overboard and nest everything 10 layers deep.
            let mode = self.mode;
            let command_line = mem::take(&mut self.command_line);
            let context = mem::replace(&mut self.context, Context::invalid());
            let symbols = mem::replace(&mut self.symbols, SymbolsRegistry::new(Context::invalid()));
            let persistent = mem::take(&mut self.persistent);
            let my_resource_stats = mem::replace(&mut self.my_resource_stats, ResourceStats::default());
            let mut breakpoints = mem::replace(&mut self.breakpoints, Pool::new());
            let prof = mem::replace(&mut self.prof, Profiling::new());
            for (id, b) in breakpoints.iter_mut() {
                // Have to redo the mapping source-line -> address because dynamic libraries may be loaded at different addresses.
                b.addrs = err!(NotCalculated, "");
                b.active = false;
            }
            *self = Debugger::new(mode, command_line, context, symbols, breakpoints, persistent, my_resource_stats, prof);
        }

        let pid;
        unsafe {
            // Convert strings to C format.
            let mut args_0: Vec<String> = Vec::new();
            let mut c_args: Vec<*const c_char> = Vec::new();
            for s in &self.command_line {
                args_0.push(s.to_string() + "\0");
            }
            for s in &args_0 {
                c_args.push(s.as_ptr() as *const c_char);
            }
            c_args.push(0 as *const c_char);

            let stdin_file = match &self.context.settings.stdin_file {
                None => open_dev_null()?,
                Some(path) => match fs::File::open(path) {
                    Ok(x) => x,
                    Err(e) => {
                        log!(self.log, "stdin failed: {}", e);
                        eprintln!("failed to open stdin file '{}': {}", path, e);
                        open_dev_null()?
                    }
                }
            };
            let stdout_file = match &self.context.settings.stdout_file {
                None => self.persistent.open_or_create_file("stdout"),
                Some(path) => match fs::File::create(path) {
                    Ok(x) => x,
                    Err(e) => {
                        log!(self.log, "stdout failed: {}", e);
                        eprintln!("failed to create stdout file '{}': {}", path, e);
                        open_dev_null()?
                    }
                }
            };
            let stderr_file = match &self.context.settings.stderr_file {
                None => self.persistent.open_or_create_file("stderr"),
                Some(path) => match fs::File::create(path) {
                    Ok(x) => x,
                    Err(e) => {
                        log!(self.log, "stderr failed: {}", e);
                        eprintln!("failed to create stderr file '{}': {}", path, e);
                        open_dev_null()?
                    }
                }
            };

            pid = libc::fork();

            if pid == 0 {
                // Child process. Do as little as possible here, avoid memory allocations,
                // and always end with either a successful exec or a hard exit.

                // We should probably close file descriptors here.

                let msg: &[u8];

                'child: {
                    // Make the child die if debugger process dies. Somewhat redundant with PTRACE_O_EXITKILL, but should cover the case when parent dies before seizing this process.
                    if libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGKILL) != 0 {
                        msg = b"child: prctl failed\0";
                        break 'child;
                    }

                    if libc::getppid() == 1 {
                        msg = b"child: parent already exited\0";
                        break 'child;
                    }

                    // This is probably not necessary, but makes debugging sessions more reproducible.
                    if libc::personality(libc::ADDR_NO_RANDOMIZE as u64) == -1 {
                        msg = b"child: failed to disable ASLR\0";
                        break 'child;
                    }

                    // Redirect debuggee's stdout and stderr to files, otherwise they'd mess up the debugger UI.
                    if libc::dup2(stdin_file.as_raw_fd(), 0) < 0 {
                        msg = b"child: dup2 stdin failed\0";
                        break 'child;
                    }
                    if libc::dup2(stdout_file.as_raw_fd(), 1) < 0 {
                        msg = b"child: dup2 stdout failed\0";
                        break 'child;
                    }
                    if libc::dup2(stderr_file.as_raw_fd(), 2) < 0 {
                        msg = b"child: dup2 stderr failed\0";
                        break 'child;
                    }

                    // SIGSTOP ourselves to make sure the PTRACE_SEIZE reliably happens before the execvp.
                    if libc::raise(libc::SIGSTOP) != 0 {
                        msg = b"child: raise(SIGSTOP) failed\0";
                        break 'child;
                    }

                    libc::execvp(c_args[0], c_args.as_ptr());
                    msg = b"child: exec failed\0";
                }

                libc::perror(msg.as_ptr() as *const i8);
                libc::_exit(1);
            }

            if pid < 0 { return errno_err!("fork() failed"); }

            ptrace(libc::PTRACE_SEIZE, pid, 0, (libc::PTRACE_O_EXITKILL | libc::PTRACE_O_TRACECLONE | libc::PTRACE_O_TRACEEXEC | libc::PTRACE_O_TRACEEXIT | libc::PTRACE_O_TRACESYSGOOD) as u64, &mut self.prof.bucket)?;
        }

        self.pid = pid;
        self.target_state = ProcessState::Starting;
        self.pending_step = initial_step.map(|on| (pid, on));
        self.waiting_for_initial_sigstop = true;
        self.memory = MemReader::new(pid);
        let thread = Thread::new(self.next_thread_idx, pid, ThreadState::Running);
        self.threads.insert(pid, thread);
        self.next_thread_idx += 1;

        Ok(())
    }

    pub fn process_events(&mut self) -> Result<(/*have_more_events_to_process*/ bool, /*drop_caches*/ bool)> {
        // If all we did was skip conditional breakpoints, don't waste time refreshing process info. Otherwise conditional breakpoints would be very slow.
        // (Also useful for other spurious traps, e.g. when doing step-over in a recursive function.)
        let mut refresh_info = false;
        let mut is_initial_exec = false;
        let mut stack_digests_to_select: Vec<(pid_t, (Vec<usize>, bool, u16))> = Vec::new();

        // If events arrive faster than we can process them, periodically yield to avoid blocking the main thread indefinitely.
        let start_time = Instant::now();
        let time_limit = if self.context.settings.periodic_timer_ns == 0 {250000000} else {self.context.settings.periodic_timer_ns};
        let time_limit = Duration::from_nanos(time_limit as u64);
        let mut stopped_early = false;

        for iteration in 0usize.. {
            if self.target_state == ProcessState::NoProcess {
                break;
            }

            if (iteration + 1) & 1023 == 1023 && Instant::now() - start_time > time_limit {
                stopped_early = true;
                break;
            }

            unsafe {
                let mut tid: pid_t = 0;
                let mut wstatus = 0i32;
                let mut thread: Option<&mut Thread> = None;

                if let Some((tid_, wstatus_)) = self.pending_wait_events.front() {
                    if let Some(t) = self.threads.get_mut(tid_) {
                        thread = Some(t);
                        tid = *tid_;
                        wstatus = *wstatus_;
                        self.pending_wait_events.pop_front();
                    }
                }
                if thread.is_none() {
                    tid = profile_syscall!(self.prof.bucket, {
                        libc::waitpid(-1, &mut wstatus, libc::WNOHANG)
                    });
                    if tid < 0 { return errno_err!("waitpid() failed"); }
                    if tid == 0 {
                        break;
                    }
                    if let Some(t) = self.threads.get_mut(&tid) {
                        thread = Some(t);
                    } else {
                        eprintln!("info: deferring event {:x} for tid {} that doesn't exist yet", wstatus, tid);
                        self.pending_wait_events.push_back((tid, wstatus));
                        continue;
                    }
                }
                self.prof.bucket.debugger_count += 1;
                let thread = thread.unwrap();
                thread.sent_interrupt = false;

                if thread.state != ThreadState::Running && !(libc::WIFSTOPPED(wstatus) && libc::WSTOPSIG(wstatus) == libc::SIGTRAP && wstatus >> 16 == libc::PTRACE_EVENT_EXIT) {
                    eprintln!("warning: got event {:x} for thread {} that is already stopped", wstatus, tid);
                }

                let mut skip_refresh = false;

                if libc::WIFEXITED(wstatus) || libc::WIFSIGNALED(wstatus) {
                    let stepping_this_thread = self.stepping.as_ref().is_some_and(|s| s.tid == tid);
                    if libc::WIFEXITED(wstatus) {
                        let exit_code = libc::WEXITSTATUS(wstatus);
                        eprintln!("info: thread {} exited with status {}", tid, exit_code);
                        if tid == self.pid || exit_code != 0 || stepping_this_thread {
                            log!(self.log, "{} {} exited with status {}", if tid == self.pid {"process"} else {"thread"}, tid, exit_code);
                        }
                    } else {
                        let signal = libc::WTERMSIG(wstatus);
                        eprintln!("info: thread {} was terminated by signal {} {}", tid, signal, signal_name(signal));
                        let core_dumped = libc::WCOREDUMP(wstatus);
                        log!(self.log, "{} {} was terminated by signal {} {}{}", if tid == self.pid {"process"} else {"thread"}, tid, signal, signal_name(signal), if core_dumped {" (core dumped)"} else {""});
                    }
                    self.threads.remove(&tid);
                    if self.threads.is_empty() {
                        self.target_state = ProcessState::NoProcess;
                        self.info.clear();
                        self.memory = MemReader::invalid();
                    } else if stepping_this_thread {
                        self.suspend()?;
                    }
                } else if libc::WIFSTOPPED(wstatus) {
                    let signal = libc::WSTOPSIG(wstatus);

                    let thread_prev_state = mem::replace(&mut thread.state, ThreadState::Suspended);
                    let mut thread_initial_stop = false;
                    thread.subframe_to_select = None;
                    thread.info.invalidate();
                    let mut force_resume = thread.exiting;

                    if signal == libc::SIGSTOP && self.waiting_for_initial_sigstop {
                        // Ignore the initial SIGSTOP, it has served its purpose (ensuring that we PTRACE_SEIZE the child before it does execvp()).
                        // The `wstatus>>16` value in this case is inconsistent: sometimes it's 0, sometimes PTRACE_EVENT_STOP.
                        eprintln!("info: got initial SIGSTOP");
                        force_resume = true;
                        self.waiting_for_initial_sigstop = false;
                        assert!(thread.waiting_for_initial_stop);
                        assert_eq!(tid, self.pid);
                        assert_eq!(self.target_state, ProcessState::Starting);
                        thread.waiting_for_initial_stop = false;
                        self.set_debug_registers_for_thread(tid)?;
                    } else if wstatus>>16 == libc::PTRACE_EVENT_STOP { // group-stop, PTRACE_INTERRUPT, or newly created thread
                        if thread.waiting_for_initial_stop {
                            // The `signal` value in this case for newly created thread is inconsistent: sometimes SIGSTOP, sometimes SIGTRAP.
                            if self.context.settings.trace_logging { eprintln!("trace: thread {} got initial stop {} {}", tid, signal, signal_name(signal)); }
                            thread.waiting_for_initial_stop = false;
                            thread_initial_stop = true;
                            self.set_debug_registers_for_thread(tid)?;
                        } else {
                            //eprintln!("trace: group-stop or interrupt, tid {} signal {} {}", tid, signal, signal_name(signal));
                        }
                    } else if signal == libc::SIGTRAP && wstatus>>16 != 0 { // various ptrace stops
                        match wstatus>>16 {
                            libc::PTRACE_EVENT_EXEC => {
                                eprintln!("info: exec tid {}", tid);
                                assert!(!self.waiting_for_initial_sigstop);

                                if self.target_state == ProcessState::Starting {
                                    // This is a point after dynamic libraries are loaded, but before main() or any static variable initialization.
                                    is_initial_exec = true;
                                    self.target_state = ProcessState::Suspended; // will resume below if needed
                                } else {
                                    // Here we're supposed to also handle the case when a multi-threaded process does an exec, and all its threads vanish.
                                    // See "execve(2) under ptrace" section in `man ptrace`. This is currently not implemented.
                                }
                            }
                            libc::PTRACE_EVENT_CLONE => {
                                let new_tid;
                                {
                                    let mut t: pid_t = 0;
                                    ptrace(libc::PTRACE_GETEVENTMSG, tid, 0, &mut t as *mut pid_t as u64, &mut self.prof.bucket)?;
                                    new_tid = t;
                                }
                                if let Some(existing_thread) = self.threads.get(&new_tid) {
                                    if !existing_thread.attached_late {
                                        eprintln!("error: duplicate tid: {}", new_tid);
                                        log!(self.log, "error: duplicate tid: {}", new_tid);
                                    }
                                } else {
                                    if self.context.settings.trace_logging { eprintln!("info: new thread: {}", new_tid); }
                                    let thread = Thread::new(self.next_thread_idx, new_tid, ThreadState::Running);
                                    self.next_thread_idx += 1;
                                    self.threads.insert(new_tid, thread);
                                }
                            }
                            libc::PTRACE_EVENT_EXIT => {
                                eprintln!("info: thread {} exiting", tid);
                                if thread.exiting {
                                    eprintln!("warning: got multiple PTRACE_EVENT_EXIT for tid {}", tid);
                                }
                                thread.exiting = true;
                                force_resume = true;
                                if self.threads.iter().all(|(_, t)| t.exiting) {
                                    eprintln!("info: process exiting");
                                    // Make sure we don't try to read things like /proc/<pid>/maps when the pid may not exist anymore.
                                    self.target_state = ProcessState::Exiting;
                                    self.stepping = None;
                                }
                            }
                            _ => return err!(Internal, "unexpected ptrace event: {}", wstatus >> 16),
                        }
                    } else if signal == libc::SIGTRAP { // hit a breakpoint
                        if self.context.settings.trace_logging { eprintln!("trace: thread {} got SIGTRAP", tid); }

                        let thread_single_stepping = mem::take(&mut thread.single_stepping);
                        let thread_ignore_next_hw_breakpoint_hit_at_addr = mem::take(&mut thread.ignore_next_hw_breakpoint_hit_at_addr);

                        let (hit, regs, stack_digest_to_select) = self.handle_breakpoint_trap(tid, thread_single_stepping, thread_ignore_next_hw_breakpoint_hit_at_addr)?;

                        if hit || self.stopping_to_handle_breakpoints {
                            if hit || self.target_state == ProcessState::Running || self.stepping.as_ref().is_some_and(|s| !s.keep_other_threads_suspended || s.tid != tid) {
                                self.ptrace_interrupt_all_running_threads()?;
                            }
                            if hit {
                                assert!(self.stepping.is_none());
                                self.target_state = ProcessState::Suspended;

                                // Can't do determine_subframe_to_select() right here. Before we unwind the stack, we need to refresh thread info and mmaps info (in case new dynamic libraries were loaded).
                                if let Some(x) = stack_digest_to_select {
                                    stack_digests_to_select.push((tid, x));
                                }
                            }
                        } else {
                            // Fast path for conditional breakpoints when condition is not satisfied (among other things).
                            force_resume = true;
                            skip_refresh = true;
                        }
                    } else { // other signals, with no special meaning for the debugger
                        if self.context.settings.trace_logging { eprintln!("trace: thread {} stopped by signal {} {}", tid, signal, signal_name(signal)); }
                        thread.pending_signal = Some(signal);

                        if [libc::SIGSEGV, libc::SIGABRT, libc::SIGILL, libc::SIGFPE].contains(&signal) {
                            thread.stop_reasons.push(StopReason::Signal(signal));
                            log!(self.log, "thread {} got {}", tid, signal_name(signal));
                            self.target_state = ProcessState::Suspended;
                            self.cancel_stepping();
                            self.ptrace_interrupt_all_running_threads()?;
                        }
                    }

                    if force_resume || self.target_state_for_thread(tid) == ThreadState::Running {
                        // When to refresh thread info after resuming the thread:
                        //  * For newly created thread - to assign thread name (without waiting for periodic timer).
                        //  * For thread that was previously suspended - to assign thread state (without waiting for periodic timer).
                        //  * Avoid refreshing if the thread was running, then suspended and immediately resumed.
                        //    In particular, for conditional breakpoints and for benign signals (e.g. if the debuggee sends itself SIGUSR1 every millisecond for profiling).
                        let should_refresh_thread_info = !force_resume && (thread_initial_stop || thread_prev_state == ThreadState::Suspended);

                        self.resume_thread(tid, should_refresh_thread_info)?;
                    } else {
                        let t = self.threads.get_mut(&tid).unwrap();
                        t.stop_count += 1;
                        refresh_thread_info(self.pid, t, &mut self.prof.bucket, &self.context.settings);
                    }
                } else {
                    return err!(Internal, "waitpid() returned unexpected status: {}", wstatus);
                }

                if !skip_refresh {
                    refresh_info = true;
                }
            }
        }

        // Don't load process information if any of:
        //  * There is no process.
        //  * The forked child process didn't do the initial exec() yet. In particular, don't kick off loading symbols because that would uselessly load symbols for the debugger itself.
        //  * All we did was skip conditional breakpoints. This path must be kept fast, otherwise conditional breakpoints will be slow.
        let mut drop_caches = false;
        if refresh_info && self.target_state.process_ready() {
            // Re-read /proc/<pid>/maps to see what dynamic libraries are loaded. Re-resolve breakpoints if there are any new ones.
            // TODO: Also trigger this on dynamic library load, using r_debug rendezvoud thing (put breakpoint on _dl_debug_state?).
            //       Once we have that, maybe don't refresh on any stop (but maybe refresh periodically to handle custom dynamic linkers).
            drop_caches |= refresh_maps_and_binaries_info(self);
            drop_caches |= self.symbols.do_eviction();

            if is_initial_exec {
                // The executable and the dynamic libraries should be mmapped by now (except the ones dlopen()ed at runtime, e.g. by custom dynamic linkers).
                // Activate breakpoints, start initial step if requested (e.g. step to start of main()), stop right here if needed (if stop on exec was requested).
                self.target_state = if self.pending_step.is_some() {ProcessState::Stepping} else {ProcessState::Running};
                self.try_pending_step_and_activate_breakpoints()?;
            }

            // This looks O(n^2): any_thread_in_state iterates over all threads, and this happens after each thread stopping.
            // But it's actually O(kinda n log n) because any_thread_in_state iterates in effectively random order and stops early.
            if self.stopping_to_handle_breakpoints && self.any_thread_in_state(ThreadState::Running).is_none() {
                self.handle_breakpoints()?;

                self.stopping_to_handle_breakpoints = false;

                // (We refreshed after suspending, so should refresh after resuming, even though the suspension was probably brief.
                //  Otherwise the UI will show the threads as suspended for a second after adding a breakpoint - confusing.
                //  Actually it's confusing anyway: this refresh will usually show the thread as R[unning], even if it's usually S[leeping].)
                let should_refresh_thread_info = true;
                self.resume_threads_if_needed(should_refresh_thread_info)?;
            }
        }

        for (tid, (digest, step_into, subfunction_level)) in stack_digests_to_select {
            match self.threads.get_mut(&tid) {
                Some(t) if t.state == ThreadState::Suspended => (),
                _ => continue,
            }
            let stack = self.get_stack_trace(tid, /*partial*/ false);
            self.threads.get_mut(&tid).unwrap().subframe_to_select = Self::determine_subframe_to_select(&stack, &digest, step_into, subfunction_level);
        }

        Ok((stopped_early, drop_caches))
    }

    pub fn refresh_all_resource_stats(&mut self) {
        if let Some(error) = refresh_all_resource_stats(self.pid, &mut self.my_resource_stats, &mut self.info.total_resource_stats, &mut self.threads, &mut self.prof.bucket, &self.context.settings) {
            eprintln!("failed to refresh resource stats: {}", error);
        }
    }

    fn target_state_for_thread(&self, tid: pid_t) -> ThreadState {
        if self.stopping_to_handle_breakpoints || self.stopped_until_symbols_are_loaded.is_some() {
            return ThreadState::Suspended;
        }
        match self.target_state {
            ProcessState::NoProcess | ProcessState::Starting | ProcessState::Exiting | ProcessState::Running => ThreadState::Running,
            ProcessState::Suspended => ThreadState::Suspended,
            ProcessState::Stepping => {
                let s = self.stepping.as_ref().unwrap();
                if s.tid == tid || !s.keep_other_threads_suspended { ThreadState::Running } else { ThreadState::Suspended }
            }
        }
    }

    // Removes temporary breakpoints associated with current step operation.
    // The caller is responsible for assigning target_state and suspending/resuming threads as needed.
    fn cancel_stepping(&mut self) {
        if self.stepping.is_some() {
            eprintln!("info: cancel stepping");
            for location in &mut self.breakpoint_locations {
                location.breakpoints.retain(|b| match b {BreakpointRef::Step(_) => false, _ => true});
            }        
            self.stepping = None;
        }
        if self.pending_step.is_some() {
            eprintln!("info: cancel pending step");
            self.pending_step = None;
        }
    }

    pub fn drop_caches(&mut self) -> Result<()> {
        eprintln!("info: drop caches");
        if self.target_state.process_ready() {
            refresh_maps_and_binaries_info(self);
            for t in self.threads.values_mut() {
                t.info.invalidate();
                refresh_thread_info(self.pid, t, &mut self.prof.bucket, &self.context.settings);
            }

            self.try_pending_step_and_activate_breakpoints()?;
        }

        Ok(())
    }

    pub fn resume(&mut self) -> Result<()> {
        match self.target_state {
            ProcessState::Suspended => (),
            ProcessState::Stepping => self.cancel_stepping(),
            ProcessState::Running if self.stopped_until_symbols_are_loaded.is_some() => (),
            _ => return err!(Usage, "not suspended, can't resume") }
        eprintln!("info: resume");

        self.target_state = ProcessState::Running;

        self.check_if_we_should_wait_for_symbols_to_load();
        self.resume_threads_if_needed(/*refresh_info*/ true)?;

        Ok(())
    }

    pub fn suspend(&mut self) -> Result<()> {
        match self.target_state {
            ProcessState::Running | ProcessState::Stepping => (),
            _ => return err!(Usage, "not running, can't suspend") }
        eprintln!("info: suspend");
        self.cancel_stepping();

        self.target_state = ProcessState::Suspended;
        self.stopped_until_symbols_are_loaded = None;
        self.ptrace_interrupt_all_running_threads()?;
        Ok(())
    }

    fn ptrace_interrupt_all_running_threads(&mut self) -> Result<usize> {
        let mut n = 0;
        for (tid, t) in &mut self.threads {
            if t.state == ThreadState::Running && !t.exiting {
                if !t.sent_interrupt {
                    unsafe {ptrace(libc::PTRACE_INTERRUPT, *tid, 0, 0, &mut self.prof.bucket)?};
                    t.sent_interrupt = true;
                }
                n += 1;
            }
        }
        Ok(n)
    }

    pub fn murder(&mut self) -> Result<()> {
        if self.mode == RunMode::Attach { return err!(Usage, "not killing attached process"); }
        if self.target_state == ProcessState::NoProcess || self.target_state == ProcessState::Exiting { return err!(Usage, "no process"); }
        eprintln!("info: kill");
        unsafe {
            let r = libc::kill(self.pid, libc::SIGKILL);
            if r != 0 {
                return errno_err!("kill failed");
            }
        }
        Ok(())
    }

    // Assigns stopped_until_symbols_are_loaded.
    fn check_if_we_should_wait_for_symbols_to_load(&mut self) {
        assert!(self.target_state.process_ready());
        // Check if anything needs symbols.
        if self.pending_step.is_none() {
            // (Case that is not handled very correctly: conditional breakpoint in a binary that's already loaded, but the condition looks at variable higher up the stack that live in binary that's still loading.
            //  We won't wait for symbols to load, and the condition evaluation may fail unnecessarily. Which is ok if condition evaluation error triggers a stop, not so ok if the condition ignores errors.
            //  I guess the fix would be to just always wait for symbols if any breakpoints are active; anything more complex seems too error-prone and not worth it.)
            if !self.breakpoints.iter().any(|(_, b)| b.enabled && b.addrs.as_ref().is_err_and(|e| e.is_loading())) {
                // Symbols not needed.
                self.stopped_until_symbols_are_loaded = None;
                return;
            }
        }
        if let &Some(binary_id) = &self.stopped_until_symbols_are_loaded {
            if let Some(binary) = self.symbols.get(binary_id) {
                if !binary.symbols_loaded() {
                    return; // still loading the same binary as before
                }
            }
        }
        for binary in self.symbols.iter() {
            if !binary.symbols_loaded() {
                self.stopped_until_symbols_are_loaded = Some(binary.id);
                return; // found a binary that's still loading
            }
        }
        debug_assert!(false); // try_pending_step_and_activate_breakpoints() should've handled breakpoints and pending step
        self.stopped_until_symbols_are_loaded = None;
    }

    // Try resolving breakpoints into addresses and starting the pending step if present.
    // If this requires symbols to be loaded, and they're not loaded, sets stopped_until_symbols_are_loaded. (Then this is called again from drop_caches() when symbols are loaded.)
    fn try_pending_step_and_activate_breakpoints(&mut self) -> Result<()> {
        assert!(self.target_state.process_ready());

        self.activate_breakpoints(self.breakpoints.iter().map(|t| t.0).collect())?;

        if let &Some((tid, ref on)) = &self.pending_step {
            assert_eq!(self.target_state, ProcessState::Stepping);
            assert!(self.stepping.is_none());
            if let &BreakpointOn::InitialExec = on {
                self.target_state = ProcessState::Suspended;
                self.pending_step = None;
            } else {
                let mut breakpoint = Breakpoint {on: on.clone(), condition: None, hits: 0, addrs: err!(NotCalculated, ""), enabled: true, active: false};
                Self::determine_locations_for_breakpoint(&self.symbols, &mut breakpoint);
                match breakpoint.addrs {
                    Err(e) if e.is_loading() => (),
                    Err(e) => {
                        log!(self.log, "{}", e);
                        self.target_state = ProcessState::Suspended;
                        self.pending_step = None;
                    }
                    Ok(addrs) => {
                        eprintln!("info: step to cursor thread {} cursor {:?}", tid, breakpoint.on);

                        let step = StepState {tid, keep_other_threads_suspended: false, disable_breakpoints: true, internal_kind: StepKind::Cursor, by_instructions: false, addr_ranges: Vec::new(), cfa: 0, single_steps: false, stack_digest: Vec::new()};
                        self.stepping = Some(step);
                        self.pending_step = None;

                        for (addr, subfunction_level) in addrs {
                            self.add_breakpoint_location(BreakpointRef::Step(StepBreakpointType::Cursor(subfunction_level)), addr);
                        }
                        self.arrange_handle_breakpoints()?;
                    }
                }
            }
        }

        self.check_if_we_should_wait_for_symbols_to_load();

        if self.stopped_until_symbols_are_loaded.is_some() {
            self.ptrace_interrupt_all_running_threads()?;
        } else {
            self.resume_threads_if_needed(/*refresh_info*/ true)?;
        }

        Ok(())
    }
    
    fn make_instruction_decoder<'a>(&self, range: Range<usize>, buf: &'a mut Vec<u8>) -> Result<iced_x86::Decoder<'a>> {
        if range.len() > 100_000_000 { return err!(Sanity, "{} MB code range, suspiciously long", range.len() / 1_000_000); }
        buf.resize(range.len(), 0);
        self.memory.read(range.start, buf)?;

        // Fix up the INT3 breakpoint instructions. (We could read the code from the binary instead of memory to avoid
        // having to do this, but then stepping wouldn't work for code generated at runtime, not even single-instruction-step.)
        let mut i = self.breakpoint_locations.partition_point(|b| b.addr < range.start);
        while self.breakpoint_locations.get(i).map_or(false, |b| b.addr < range.end) {
            let b = &self.breakpoint_locations[i];
            i += 1;
            if !b.hardware && b.active {
                buf[b.addr - range.start] = b.original_byte;
            }
        }
        Ok(iced_x86::Decoder::with_ip(64, buf, range.start as u64, 0))
    }

    fn jump_target_may_be_outside_ranges(instruction: &iced_x86::Instruction, ranges: &Vec<Range<usize>>) -> bool {
        if instruction.flow_control() == FlowControl::IndirectBranch {
            return true;
        }
        match instruction.op0_kind() {
            iced_x86::OpKind::NearBranch16 | iced_x86::OpKind::NearBranch32 | iced_x86::OpKind::NearBranch64 => (),
            _ => return true }
        let addr = instruction.near_branch_target() as usize;
        let i = ranges.partition_point(|r| r.end <= addr);
        i == ranges.len() || ranges[i].start > addr
    }

    pub fn step(&mut self, tid: pid_t, mut subframe_idx: usize, kind: StepKind, by_instructions: bool, use_line_number_with_column: bool) -> Result<()> {
        if self.target_state != ProcessState::Suspended {
            return err!(Usage, "not suspended");
        }
        assert!(self.stepping.is_none());
        assert!(self.breakpoint_locations.iter().all(|loc| loc.breakpoints.iter().all(|b| match b { BreakpointRef::Step(_) => false, _ => true })));

        let thread = match self.threads.get_mut(&tid) {
            None => return err!(Usage, "no thread"),
            Some(t) => t,
        };
        if thread.state != ThreadState::Suspended {
            return err!(Usage, "thread not suspended");
        }
        eprintln!("info: step {} subframe {} {:?} instr {} col {}", tid, subframe_idx, kind, by_instructions, use_line_number_with_column);

        // Special no-op case: step-into from non-top subframe.
        // Just switch to the child subframe. This seems like the least confusing behavior for the user, but I'm not very sure.
        if kind == StepKind::Into && !by_instructions && subframe_idx != 0 {
            thread.subframe_to_select = Some(subframe_idx - 1);
            thread.stop_count += 1;
            return Ok(());
        }

        let mut buf: Vec<u8> = Vec::new();
        let mut step = StepState {tid, keep_other_threads_suspended: true, disable_breakpoints: true, internal_kind: kind, by_instructions, addr_ranges: Vec::new(), cfa: 0, single_steps: false, stack_digest: Vec::new()};
        let mut breakpoint_types: Vec<StepBreakpointType> = Vec::new();
        let mut unwind: Option<(Arc<UnwindInfo>, AddrMap)> = None;

        // There are 2 things that can be missing:
        //  * Debug symbols (.debug_info).
        //  * Unwind information (.eh_frame).
        // JIT-generated code has neither.
        // Stripped binaries have unwind but no symbols.
        //
        // Here we should be careful to ensure that:
        //  * Instruction-level step-into always works, even if both unwind and symbols are missing.
        //  * Instruction-level step-over and step-out work even if symbols are missing (but unwind is required).

        // Overview of the cases:
        //  * Into && by_instructions - single-instruction step, i.e. PTRACE_SINGLESTEP
        //  * Over && by_instructions && standing on non-call instruction - converted to single-instruction step
        //  * Over && by_instructions && standing on call instruction - put breakpoint after the call, conditional on cfa (to handle recursion correctly)
        //  * Over - determine address ranges for current line and for inlined functions on it; run until control leaves those ranges, conditional on cfa;
        //           to detect leaving the ranges, put breakpoints on jumps, return address, and after each range;
        //           when a jump breakpoint is hit, we do a single step to see where it lands
        //  * Into - determine address ranges for current line, run until control leaves those ranges or cfa changes;
        //           breakpoints on calls, jumps, return address, and after each range
        //  * Out of inlined function - converted to Over, i.e. run until control leaves the determined address ranges, conditional on cfa
        //  * Out of non-inlined function - put breakpoint on return address, conditional on cfa

        // The top frame+subframe of the stack trace is available even without symbols and unwind information.
        let stack = self.get_stack_trace(tid, /*partial*/ false);
        if stack.frames.is_empty() {
            return match stack.truncated.clone() {
                None => err!(Internal, "no stack"),
                Some(e) => Err(e),
            };
        }

        // Instruction-based steps ignore selected frame and don't care about inlined functions.
        if by_instructions {
            subframe_idx = stack.frames[0].subframes.end - 1;
        }

        let subframe = match stack.subframes.get(subframe_idx) {
            None => return err!(ProcessState, "no stack frame"), // possible if multiple things happened at once in UI
            Some(s) => s };
        let frame = &stack.frames[subframe.frame_idx];

        // 1. Decide the internal step kind, address ranges, and types of internal breakpoints to add.

        if (kind == StepKind::Into || kind == StepKind::Over) && by_instructions {
            // Special robust case: single-instruction step-into.
            // Doesn't require debug symbols, stack unwinding, or even reading the machine code.
            // Also instruction-level step-over, which requires only unwind information.

            let addr = frame.addr;
            // Decode one instruction to check if it's a call/syscall, just as an optimization to avoid suspending other threads unnecessarily.
            // (This read will incorrectly fail if we're <15 bytes before end of mmap.)
            match self.make_instruction_decoder(addr..addr+MAX_X86_INSTRUCTION_BYTES, &mut buf) {
                // Allow single-instruction-stepping even if we can't read the process's memory for some reason.
                Err(e) if kind == StepKind::Into => {
                    eprintln!("warning: failed to read instruction at {:x}: {}", addr, e);
                    step.addr_ranges.push(addr..addr+1);
                    step.keep_other_threads_suspended = false;
                }
                Err(e) => return Err(e),
                Ok(mut decoder) => {
                    let instruction = decoder.decode();
                    let is_syscall = instruction.code() == iced_x86::Code::Syscall;
                    let is_call = [FlowControl::Call, FlowControl::IndirectCall].contains(&instruction.flow_control());
                    step.keep_other_threads_suspended &= !is_syscall;
                    step.addr_ranges.push(addr..addr+instruction.len()); // may be unset later
                    if kind == StepKind::Into || !is_call {
                        step.internal_kind = StepKind::Into;
                    } else {
                        // Step over a call instruction.
                        step.keep_other_threads_suspended = false;
                        breakpoint_types = vec![StepBreakpointType::AfterRange];
                    }
                }
            }
        } else if kind == StepKind::Out && subframe_idx == frame.subframes.end - 1 {
            // Step out of a real function. Doesn't require debug symbols, just unwind.
            step.keep_other_threads_suspended = false;
            breakpoint_types = vec![StepBreakpointType::AfterRet];
        } else {
            // Source-code-based steps. Require line numbers and inlined functions information from debug symbols.

            assert!(!by_instructions);

            let function_idx = stack.subframes[frame.subframes.end - 1].function_idx.clone()?;
            let binary = match self.symbols.get(frame.binary_id.clone().unwrap()) {
                None => return err!(Internal, "binary was unloaded after generating backtrace"),
                Some(x) => x };
            let symbols = binary.symbols.as_ref_clone_error()?;
            unwind = Some((binary.unwind.clone()?, binary.addr_map.clone()));
            let function = &symbols.functions[function_idx];
            let static_pseudo_addr = binary.addr_map.dynamic_to_static(frame.pseudo_addr);
            let mut static_addr_ranges: Vec<Range<usize>> = Vec::new();

            // Find address ranges of inlined function calls that we need to skip. For step-out, it's the call we're in, for step-over it's all calls on current line.
            let subfunctions = &symbols.shards[function.shard_idx()].subfunctions;
            if kind == StepKind::Out {
                step.internal_kind = StepKind::Over;
                assert!(subframe.subfunction_idx.is_some());
                for r in symbols.subfunctions_at_level(frame.subframes.end - 1 - subframe_idx, function) {
                    if r.identity == subframe.subfunction_identity {
                        static_addr_ranges.push(r.addr_range.clone());
                    }
                }
                assert!(!static_addr_ranges.is_empty());
            }
            if kind == StepKind::Over && frame.subframes.end - subframe_idx < function.num_levels() {
                let subfuncs = symbols.subfunctions_at_level(frame.subframes.end - subframe_idx, function);
                if let Some(start_line) = &subframe.line {
                    // Step over all inlined function calls on this line/column.
                    for s in subfuncs {
                        let l = &s.call_line;
                        if l.file_idx() == start_line.line.file_idx() && l.line() == start_line.line.line() && (!use_line_number_with_column || l.column() == start_line.line.column()) {
                            static_addr_ranges.push(s.addr_range.clone());
                        }
                    }
                } else if subframe_idx > frame.subframes.start {
                    // Step over one specific inlined function call.
                    assert!(subframe.subfunction_idx.is_some());
                    for s in subfuncs {
                        if s.identity == subframe.subfunction_identity {
                            static_addr_ranges.push(s.addr_range.clone());
                        }
                    }
                } else {
                    return err!(MissingSymbols, "no line number for current address");
                }
            }

            // Outside the inlined function calls, look for address ranges corresponding to the current line directly.
            if kind == StepKind::Over || kind == StepKind::Into {
                if let Some(start_line) = &subframe.line {
                    let mut gaps: Vec<Range<usize>> = Vec::new();
                    for w in static_addr_ranges.windows(2) {
                        gaps.push(w[0].end..w[1].start);
                    }
                    if let Some(last) = static_addr_ranges.last() {
                        gaps.push(last.end..usize::MAX);
                    }
                    gaps.push(binary.addr_map.dynamic_to_static(frame.pseudo_addr)..usize::MAX); // overlapping is ok

                    for gap in gaps {
                        let mut line_iter = symbols.addr_to_line_iter(gap.start);
                        let mut prev = usize::MAX;
                        while let Some(l) = line_iter.next() {
                            let matches = l.file_idx() == start_line.line.file_idx() && l.line() == start_line.line.line() && (!use_line_number_with_column || l.column() == start_line.line.column());
                            if !matches {
                                if prev != usize::MAX {
                                    static_addr_ranges.push(prev..l.addr());
                                }
                                break;
                            }
                            if prev == usize::MAX {
                                prev = l.addr();
                            }
                        }
                    }
                }
                if static_addr_ranges.is_empty() {
                    return err!(MissingSymbols, "no line number for current address");
                }
            }
            
            // Clean up overlapping ranges.
            let mut events: Vec<(usize, isize)> = Vec::new();
            for r in &static_addr_ranges {
                assert!(r.start <= r.end);
                events.push((r.start, -1)); // (important that -1 < 1)
                events.push((r.end, 1));
            }
            for (a, _) in &mut events {
                *a = binary.addr_map.static_to_dynamic(*a);
            }
            events.sort_unstable();
            let mut d = 0;
            let mut prev = 0;
            for (addr, sign) in events {
                if d == 0 { prev = addr; }
                d -= sign;
                if d == 0 { step.addr_ranges.push(prev..addr); }
            }
            assert!(d == 0);

            breakpoint_types = vec![StepBreakpointType::AfterRange, StepBreakpointType::AfterRet, StepBreakpointType::JumpOut];
            if step.internal_kind == StepKind::Into {
                breakpoint_types.push(StepBreakpointType::Call);
            }
        }
        assert!(step.addr_ranges.windows(2).all(|a| a[0].end < a[1].start));

        // 2. Decode instructions in the address ranges, determine locations for internal breakpoints.

        let mut breakpoints_to_add: Vec<(StepBreakpointType, usize)> = Vec::new();

        if step.internal_kind == StepKind::Into && step.by_instructions {
            step.single_steps = true;
        } else {
            // Need unwind information, potentially for all binaries (if we wind up checking for step completion while in another function).
            // (Unwind info is separate from symbols and loads much faster, so it's hard to run into this in practice.)
            if self.symbols.iter().any(|b| b.is_mapped && b.unwind.as_ref().is_err_and(|e| e.is_loading())) {
                return err!(Loading, "can't step while loading unwind info");
            }

            step.cfa = frame.regs.get_int(RegisterIdx::Cfa)?.0 as usize;
        }

        if breakpoint_types.contains(&StepBreakpointType::AfterRet) {
            match frame.regs.get_int(RegisterIdx::Ret) {
                Ok((addr, _dubious)) => breakpoints_to_add.push((StepBreakpointType::AfterRet, addr as usize)),
                Err(e) if step.internal_kind == StepKind::Out => return err!(ProcessState, "no return address"),
                Err(_) => (),
            }
        }
        if breakpoint_types.contains(&StepBreakpointType::AfterRange) {
            for r in &step.addr_ranges {
                breakpoints_to_add.push((StepBreakpointType::AfterRange, r.end));
            }
        }
        breakpoint_types.retain(|t| *t != StepBreakpointType::AfterRet && *t != StepBreakpointType::AfterRange);

        if !breakpoint_types.is_empty() {
            let bp_on_call = breakpoint_types.contains(&StepBreakpointType::Call);
            let bp_on_jump_out = breakpoint_types.contains(&StepBreakpointType::JumpOut);
            for range in &step.addr_ranges {
                let mut decoder = self.make_instruction_decoder(range.clone(), &mut buf)?;
                let mut instruction = iced_x86::Instruction::default();
                while decoder.can_decode() {
                    decoder.decode_out(&mut instruction);
                    match instruction.flow_control() {
                        FlowControl::Call if instruction.code() == iced_x86::Code::Syscall => step.keep_other_threads_suspended = false,
                        FlowControl::Call | FlowControl::IndirectCall if bp_on_call => breakpoints_to_add.push((StepBreakpointType::Call, instruction.ip() as usize)),
                        FlowControl::Call | FlowControl::IndirectCall => step.keep_other_threads_suspended = false,
                        FlowControl::UnconditionalBranch | FlowControl::ConditionalBranch | FlowControl::IndirectBranch => {
                            if bp_on_jump_out && Self::jump_target_may_be_outside_ranges(&instruction, &step.addr_ranges) {
                                breakpoints_to_add.push((StepBreakpointType::JumpOut, instruction.ip() as usize));
                            }
                        }
                        FlowControl::Return | FlowControl::Next | FlowControl::XbeginXabortXend | FlowControl::Exception | FlowControl::Interrupt => (),
                    }
                }
            }
        }

        if self.context.settings.exception_aware_steps && (step.internal_kind == StepKind::Over || step.internal_kind == StepKind::Out) {
            // If we're stepping over/out-of a function and the function throws an exception, control jumps to the 'catch' block, bypassing our AfterRet breakpoints.
            // Put breakpoints on all catch blocks in the call stack.
            let mut memory = CachedMemReader::new(self.memory.clone());
            let mut start_frame = subframe.frame_idx + 1;
            let mut addrs: Vec<usize> = Vec::new();
            if step.internal_kind == StepKind::Over {
                if let Some((unwind, addr_map)) = unwind {
                    // Find catch blocks in current function for the address ranges over which we're stepping.
                    if let Err(e) = find_catch_blocks_for_ranges(&step.addr_ranges, &unwind, &addr_map, &mut memory, &mut addrs) {
                        eprintln!("warning: lsda error: {}", e);
                    }
                } else {
                    // For step-over-instruction, find catch blocks covering just that instruction.
                    start_frame -= 1;
                }
            }
            for frame in &stack.frames[start_frame..] {
                if let Err(e) = find_catch_blocks_for_frame(frame, &mut memory, &mut addrs) {
                    eprintln!("warning: lsda error: {}", e);
                }
            }
            for addr in addrs {
                breakpoints_to_add.push((StepBreakpointType::Catch, addr));
            }
        }

        // Annoyingly, if a syscall is in progress, the instruction pointer may point to the *next* instruction after `syscall`.
        // So we have to heuristically check if the previous instruction is syscall (2 bytes: 0f05). This may produce false positives
        // because a longer instruction may end with bytes 0f05 (e.g. if it's an immediate operand); that's ok, this is just an optimization.
        if step.keep_other_threads_suspended {
            // (This will incorrectly fail if we're within 2 bytes from the start of the memory map range.)
            let mut buf = [0u8; 2];
            let addr = stack.frames[0].addr.saturating_sub(2);
            match self.memory.read(addr, &mut buf) {
                Err(e) => {
                    eprintln!("warning: failed to read previous instruction at {:x}: {}", addr, e);
                    step.keep_other_threads_suspended = false;
                }
                Ok(()) => {
                    if buf == [0x0f, 0x05] {
                        step.keep_other_threads_suspended = false;
                    }
                }
            }
        }

        if step.internal_kind == StepKind::Into && step.by_instructions {
            if step.keep_other_threads_suspended {
                // For single-instruction-step, stop after one PTRACE_SINGLESTEP, even if instruction pointer doesn't change.
                // Useful in case of recursive `call` immediately followed by `ret`.
                step.addr_ranges.clear();
            } else {
                // PTRACE_SINGLESTEP produces spurious traps when stepping from syscall instruction, i.e. when pre-step ip is on or after syscall instruction.
                // Leave addr_ranges nonempty to ignore such stops until ip moves. This doesn't interfere with the case of recursive call followed by ret (above).
            }
        }

        if !step.by_instructions {
            step.stack_digest = (subframe_idx..stack.subframes.len()).map(|i| stack.subframe_identity(i)).collect();
        }

        // 3. Actually initiate the step and add breakpoints.

        eprintln!("info: proceeding with step from addr 0x{:x} {:?}", frame.addr, step);
        
        self.stepping = Some(step);
        self.target_state = ProcessState::Stepping;

        if !breakpoints_to_add.is_empty() {
            for &(type_, breakpoint_addr) in &breakpoints_to_add {
                self.add_breakpoint_location(BreakpointRef::Step(type_), breakpoint_addr);
            }

            // If we're already standing on one of the breakpoints we're adding, handle it the same way as if breakpoint was hit.
            // In addition to this, the breakpoint may or may not get actually hit immediately after we resume the thread.
            // There's no good way to guarantee that it will get hit (if the thread is currently stopped by hardware breakpoint),
            // so we have to do this handling manually here.
            for (type_, breakpoint_addr) in breakpoints_to_add {
                if breakpoint_addr == stack.frames[0].addr {
                    let mut request_single_step = false;
                    Self::handle_step_breakpoint_hit(self.stepping.as_mut().unwrap(), type_, &mut request_single_step);
                    if request_single_step {
                        self.threads.get_mut(&tid).unwrap().single_stepping = true;
                    }
                }
            }

            self.arrange_handle_breakpoints()?;
        } else if self.stepping.as_ref().unwrap().single_steps {
            // Interaction between SINGLESTEP and breakpoints.
            //
            // We need to be careful to avoid single-stepping while standing on a software breakpoint.
            // Otherwise on SIGTRAP we won't be able to tell whether we stopped because of the
            // breakpoint or because of a SINGLESTEP that jumped to the address just *after* the breakpoint.
            // So when single-stepping from a software breakpoint, we make sure handle_breakpoints() is called first, which will convert it to a hardware breakpoint.
            //
            // There's a corresponding problem when adding a breakpoint while single-stepping. We solve it in a similar way: by making sure handle_breakpoints() happens
            // before the new breakpoint is activated (all threads are suspended first, including the single-stepping thread).
            if let Some(idx) = self.find_breakpoint_location(stack.frames[0].addr) {
                if !self.breakpoint_locations[idx].hardware {
                    self.arrange_handle_breakpoints()?;
                }
            }
        }

        if self.stepping.as_ref().unwrap().keep_other_threads_suspended {
            if self.target_state_for_thread(tid) == ThreadState::Running {
                self.resume_thread(tid, true)?;
            }
        } else {
            self.resume_threads_if_needed(/*refresh_info*/ true)?;
        }

        Ok(())
    }

    pub fn step_to_cursor(&mut self, tid: pid_t, cursor: BreakpointOn) -> Result<()> {
        match self.target_state {
            ProcessState::Suspended | ProcessState::Running | ProcessState::Stepping => (),
            ProcessState::NoProcess => return self.start_child(Some(cursor)),
            ProcessState::Starting | ProcessState::Exiting => return err!(Usage, "not ready"),
        }
        if self.threads.get(&tid).is_none() {
            return err!(Usage, "no thread");
        }

        self.cancel_stepping();

        self.pending_step = Some((tid, cursor));
        self.target_state = ProcessState::Stepping;
        self.try_pending_step_and_activate_breakpoints()?;

        if self.stopped_until_symbols_are_loaded.is_some() {
            self.ptrace_interrupt_all_running_threads()?;
        }

        Ok(())
    }

    fn any_thread_in_state(&self, state: ThreadState) -> Option<pid_t> {
        for (tid, t) in &self.threads {
            if t.state == state {
                return Some(*tid);
            }
        }
        None
    }

    fn resume_threads_if_needed(&mut self, refresh_info: bool) -> Result<()> {
        let tids_to_resume: Vec<pid_t> = self.threads.keys().filter(|tid| self.target_state_for_thread(**tid) == ThreadState::Running).copied().collect();
        for t in tids_to_resume {
            self.resume_thread(t, refresh_info)?;
        }
        Ok(())
    }

    fn resume_thread(&mut self, tid: pid_t, refresh_info: bool) -> Result<()> {
        let thread = self.threads.get_mut(&tid).unwrap();
        if thread.state == ThreadState::Running {
            return Ok(());
        }
        if !thread.single_stepping {
            match &self.stepping {
                Some(step) if step.tid == tid && step.single_steps => thread.single_stepping = true,
                _ => () };
        }
        let op = if thread.single_stepping {libc::PTRACE_SINGLESTEP} else {libc::PTRACE_CONT};
        let sig = thread.pending_signal.take().unwrap_or(0);
        unsafe {ptrace(op, tid, 0, sig as u64, &mut self.prof.bucket)?};
        thread.state = ThreadState::Running;
        thread.stop_reasons.clear();

        if refresh_info {
            refresh_thread_info(self.pid, thread, &mut self.prof.bucket, &self.context.settings);
        }

        Ok(())
    }


    pub fn get_stack_trace(&mut self, tid: pid_t, partial: bool) -> StackTrace {
        let t = match self.threads.get(&tid) {
            Some(t) if t.state != ThreadState::Suspended => return StackTrace::error(error!(Usage, "running")),
            Some(t) => t,
            None if self.target_state == ProcessState::NoProcess => return StackTrace::error(error!(Usage, "no process")),
            None => return StackTrace::error(error!(Usage, "no thread")),
        };
        let memoized = if partial { &t.info.partial_stack } else { &t.info.stack };
        if let Some(s) = memoized {
            s.clone()
        } else {
            let mut stack = StackTrace::default();
            match self.unwind_stack(tid, partial, &mut stack) {
                Ok(()) => (),
                Err(e) => stack.truncated = Some(e),
            };

            let t = self.threads.get_mut(&tid).unwrap(); // have to re-lookup because rust
            let memoized = if partial { &mut t.info.partial_stack } else { &mut t.info.stack };
            *memoized = Some(stack.clone());
            stack
        }
    }

    fn unwind_stack(&self, tid: pid_t, partial: bool, stack: &mut StackTrace) -> Result<()> {
        let thread = self.threads.get(&tid).unwrap();
        if thread.state != ThreadState::Suspended {
            return err!(ProcessState, "running");
        }

        let mut regs = thread.info.regs.clone();
        let mut scratch = UnwindScratchBuffer::default();
        let mut pseudo_addr = regs.get_int(RegisterIdx::Rip)?.0 as usize;
        let mut memory = CachedMemReader::new(self.memory.clone());

        loop {
            let idx = stack.frames.len();

            if idx > 1000 {
                return err!(ProcessState, "stack too deep");
            }

            let addr = regs.get_int(RegisterIdx::Rip).unwrap().0 as usize;
            stack.subframes.push(StackSubframe {frame_idx: stack.frames.len(), function_idx: err!(MissingSymbols, "unwind failed"), ..Default::default()});
            stack.frames.push(StackFrame {addr, pseudo_addr, regs: regs.clone(), subframes: stack.subframes.len()-1..stack.subframes.len(), .. Default::default()});
            let frame = &mut stack.frames.last_mut().unwrap();

            // Would be nice to fall back to unwinding using some default ABI (rbp and callee cleanup, or something).
            // But for now we just stop if we can't find the binary (may be a problem for JIT-generated code) or .eh_frame section in it.
            let (_, mut static_pseudo_addr, binary, _) = self.addr_to_binary(pseudo_addr)?;
            frame.binary_id = Some(binary.id);
            frame.addr_static_to_dynamic = binary.addr_map.static_to_dynamic(static_pseudo_addr).wrapping_sub(static_pseudo_addr);

            // This populates CFA "register", so needs to happen before symbolizing the frame (because frame_base expression might use CFA).
            let unwind = binary.unwind.as_ref_clone_error()?;
            let step_result = unwind.step(&mut memory, &binary.addr_map, &mut scratch, pseudo_addr, frame, &**binary.elf.as_ref().unwrap());

            if step_result.as_ref().is_ok_and(|(_, is_signal_trampoline)| *is_signal_trampoline) {
                // Un-decrement the instruction pointer, there's no `call` in signal trampoline.
                frame.pseudo_addr = frame.regs.get_int(RegisterIdx::Rip).unwrap().0 as usize;
                static_pseudo_addr = binary.addr_map.dynamic_to_static(frame.pseudo_addr);
            }

            self.symbolize_stack_frame(static_pseudo_addr, binary, frame, &mut stack.subframes, &mut memory);

            if partial {
                return Ok(());
            }

            let (next_regs, is_signal_trampoline) = step_result?;
            if !next_regs.has(RegisterIdx::Rip) {
                // This is how stacks usually end.
                return Ok(());
            }
            let next_addr = next_regs.get_int(RegisterIdx::Rip).unwrap().0 as usize;
            if next_addr == 0 {
                // I've seen this in MUSL's clone.s, which has bad unwind info.
                return err!(Dwarf, "zero return address");
            }
            if next_addr == addr && next_regs.has(RegisterIdx::Rsp) && regs.has(RegisterIdx::Rsp) && next_regs.get_int(RegisterIdx::Rsp).unwrap().0 == regs.get_int(RegisterIdx::Rsp).unwrap().0 {
                // RIP and RSP didn't change. We'd almost certainly be stuck in a loop if we continue. I've seen this in MUSL's clone.s, which has bad unwind info.
                return err!(Dwarf, "cycle");
            }

            regs = next_regs;
            pseudo_addr = if is_signal_trampoline {next_addr} else {next_addr - 1};
        }
    }

    pub fn addr_to_binary(&self, addr: usize) -> Result<(/* offset */ usize, /* static addr */ usize, &Binary, &MemMapInfo)> {
        let map = match self.info.maps.addr_to_map(addr) {
            None => return err!(ProcessState, "address not mapped"),
            Some(m) => m,
        };
        let binary_id = match &map.binary_id {
            None => return err!(ProcessState, "address not mapped to a binary"),
            Some(b) => *b,
        };
        let binary = self.symbols.get(binary_id).unwrap();
        Ok((addr - map.start + map.offset, binary.addr_map.dynamic_to_static(addr), binary, map))
    }

    pub fn find_binary_fuzzy<'a>(symbols: &'a SymbolsRegistry, binary_locator: &BinaryLocator) -> Result<&'a Binary> {
        Ok(if let Some(id) = symbols.locator_to_id.get(binary_locator) {
            symbols.get(*id).unwrap()
        } else if let Some(b) = symbols.iter().find(|b| b.is_mapped && b.locator.matches_incomplete(binary_locator)) {
            b
        } else if let Some(b) = symbols.iter().find(|b| b.locator.matches_incomplete(binary_locator)) {
            b
        } else {
            return err!(NoFunction, "no binary: {}", binary_locator.path);
        })
    }

    fn calculate_frame_base(&self, frame: &mut StackFrame, static_addr: usize, binary: &Binary, symbols: &Symbols, function: &FunctionInfo, root_subfunction: &Subfunction, memory: &mut CachedMemReader) -> Result<()> {
        let debug_info_offset = match function.debug_info_offset() {
            Some(o) => o,
            None => return Ok(()) };
        let unit = symbols.find_unit(debug_info_offset)?;
        let mut context = DwarfEvalContext {memory, symbols: Some(symbols), addr_map: &binary.addr_map, encoding: unit.unit.header.encoding(), unit: Some(unit), regs: Some(&frame.regs), frame_base: None, local_variables: &[]};
        for v in symbols.local_variables_in_subfunction(root_subfunction, function.shard_idx()) {
            if !v.flags().contains(VariableFlags::FRAME_BASE) {
                // Frame bases are always first in the list.
                break;
            }
            if !v.range().contains(&static_addr) {
                continue;
            }
            let (val, dubious) = eval_variable(&v.location, &mut context)?;
            
            // Not sure how exactly the result of DW_AT_frame_base expression is meant to be interpreted.
            // I've seen only two different expressions ever used as DW_AT_frame_base:
            //  * [DW_OP_reg(rsp)]. I.e. the *value* of the frame base is in the register rsp.
            //  * [DW_OP_call_frame_cfa]. I.e. push CFA onto the stack, end of expression. CFA is usually rsp+const.
            //    Normally if an expression doesn't explicitly report the variable location, the value on the stack is the *address* of the variable.
            //    But here clearly we're not supposed to dereference rsp+const.
            // So is rsp+const the frame base *value* or the frame base *address*? Seems inconsistent. The two cases above are easy to cover,
            // as we do here, but idk what the general case is supposed to be, maybe compilers can produce symbols on which this doesn't work.
            let v = match val {
                AddrOrValueBlob::Addr(a) => a,
                AddrOrValueBlob::Blob(v) => v.get_usize()?,
            };
            frame.frame_base = Ok((v, dubious));
            break;
        }
        Ok(())
    }
    
    fn symbolize_stack_frame(&self, static_addr: usize, binary: &Binary, frame: &mut StackFrame, subframes: &mut Vec<StackSubframe>, memory: &mut CachedMemReader) {
        assert!(frame.subframes.len() == 1 && frame.subframes.start + 1 == subframes.len());
        let frame_idx = subframes.last().unwrap().frame_idx;
        let symbols = match binary.symbols.as_ref_clone_error() {
            Ok(s) => s,
            Err(e) => {
                subframes.last_mut().unwrap().function_idx = Err(e);
                return;
            }
        };

        let make_file_line_info = |line: LineInfo| -> FileLineInfo {
            let file = &symbols.files[line.file_idx().unwrap()];
            FileLineInfo {line, filename: file.filename.to_owned(), path: file.path.to_owned(), version: file.version.clone()}
        };
        
        match symbols.addr_to_function(static_addr) {
            Err(e) => subframes.last_mut().unwrap().function_idx = Err(e.clone()),
            Ok((function, function_idx)) => {
                let shard = &symbols.shards[function.shard_idx()];
                let sf = subframes.last_mut().unwrap();
                sf.function_idx = Ok(function_idx);
                sf.function_name = function.demangle_name();
                if let Some((root_subfunction, root_subfunction_idx)) = symbols.root_subfunction(function) {
                    sf.subfunction_idx = Some(root_subfunction_idx);
                    sf.subfunction_identity = shard.subfunctions[root_subfunction_idx].identity;

                    match self.calculate_frame_base(frame, static_addr, binary, symbols, function, root_subfunction, memory) {
                        Ok(()) => (),
                        Err(e) => frame.frame_base = Err(e) }

                    for level in 1..function.num_levels() {
                        let idxs = symbols.subfunction_idxs_at_level(level, function);
                        let ranges = &symbols.shards[function.shard_idx()].subfunctions[idxs.clone()];
                        let i = ranges.partition_point(|r| r.addr_range.end <= static_addr);
                        if i == ranges.len() || ranges[i].addr_range.start > static_addr {
                            break;
                        }
                        let subfunction_idx = idxs.start + i;
                        let subfunction = &ranges[i];

                        if subfunction.call_line.file_idx().is_some() {
                            subframes.last_mut().unwrap().line = Some(make_file_line_info(subfunction.call_line.clone()));
                        }

                        let mut callee_name = String::new();
                        let callee_idx = if subfunction.callee_idx == usize::MAX {
                            err!(Dwarf, "missing inline call info")
                        } else {
                            callee_name = symbols.functions[subfunction.callee_idx].demangle_name();
                            Ok(subfunction.callee_idx)
                        };

                        subframes.push(StackSubframe {frame_idx, subfunction_idx: Some(subfunction_idx), subfunction_identity: subfunction.identity, function_idx: callee_idx, function_name: callee_name, ..Default::default()});
                        frame.subframes.end += 1;
                    }
                    subframes[frame.subframes.clone()].reverse();
                }
            }
        }

        if let Some(line) = symbols.find_line(static_addr) {
            subframes[frame.subframes.start].line = Some(make_file_line_info(line));
        }
    }

    pub fn make_eval_context<'a>(&'a self, stack: &'a StackTrace, selected_subframe: usize) -> EvalContext<'a> {
        EvalContext {memory: CachedMemReader::new(self.memory.clone()), process_info: &self.info, symbols_registry: &self.symbols, stack, selected_subframe}
    }

    pub fn add_breakpoint(&mut self, on: BreakpointOn) -> Result<BreakpointId> {
        let breakpoint = Breakpoint {on, condition: None, hits: 0, addrs: err!(NotCalculated, ""), enabled: true, active: false};
        let id = self.breakpoints.add(breakpoint).0;
        if self.target_state.process_ready() {
            self.activate_breakpoints(vec![id])?;
        }
        Ok(id)
    }
    pub fn remove_breakpoint(&mut self, id: BreakpointId) -> bool {
        if self.breakpoints.try_get(id).is_none() {
            return false;
        }
        self.deactivate_breakpoint(id);
        self.breakpoints.remove(id);
        true
    }

    pub fn set_breakpoint_enabled(&mut self, id: BreakpointId, enabled: bool) -> Result<bool> {
        let b = match self.breakpoints.try_get_mut(id) {
            None => return Ok(false),
            Some(x) => x };
        if b.enabled == enabled {
            return Ok(true);
        }
        b.enabled = enabled;
        if !enabled {
            self.deactivate_breakpoint(id);
        } else if self.target_state.process_ready() {
            self.activate_breakpoints(vec![id])?;
        }
        Ok(true)
    }

    pub fn set_breakpoint_condition(&mut self, id: BreakpointId, condition: Option<String>) {
        let b = match self.breakpoints.try_get_mut(id) {
            None => return,
            Some(x) => x };
        if let Some(condition) = condition {
            let expr = parse_watch_expression(&condition);
            b.condition = Some((condition, expr, None));
        } else {
            b.condition = None;
        }
    }

    fn activate_breakpoints(&mut self, ids: Vec<BreakpointId>) -> Result<()> {
        assert!(self.target_state.process_ready());
        let mut added_locations = false;
        let mut wait_for_symbols = false;
        for id in ids {
            let b = self.breakpoints.get_mut(id);
            if !b.enabled || b.active {
                continue;
            }
            if let Err(e) = &b.addrs {
                Self::determine_locations_for_breakpoint(&self.symbols, b);
            }
            match &b.addrs {
                Ok(addrs) => {
                    assert!(!addrs.is_empty());
                    added_locations = true;
                    b.active = true;
                    for (addr, subfunction_level) in addrs.clone() {
                        self.add_breakpoint_location(BreakpointRef::Id {id, subfunction_level}, addr);
                    }
                }
                Err(e) if e.is_loading() => wait_for_symbols = true,
                Err(_) => (),
            }
        }
        if added_locations {
            self.arrange_handle_breakpoints()?;
        }
        if wait_for_symbols && self.stopped_until_symbols_are_loaded.is_none() {
            self.check_if_we_should_wait_for_symbols_to_load();
            assert!(self.stopped_until_symbols_are_loaded.is_some());
            self.ptrace_interrupt_all_running_threads()?;
        }
        Ok(())
    }
    fn deactivate_breakpoint(&mut self, id: BreakpointId) {
        if !mem::replace(&mut self.breakpoints.get_mut(id).active, false) {
            return;
        }
        for location in &mut self.breakpoint_locations {
            // Don't bother deactivating the breakpoint locations here, just wait for the next handle_breakpoints() call to do everything.
            // (Don't bother scheduling such call either, it'll happen if the stale breakpoint gets hit.)
            location.breakpoints.retain(|b| match b { BreakpointRef::Id {id: id_, ..} if id_ == &id => false, _ => true });
        }
    }

    fn determine_locations_for_breakpoint(symbols_registry: &SymbolsRegistry, breakpoint: &mut Breakpoint) {
        assert!(breakpoint.addrs.is_err());
        match &mut breakpoint.on {
            BreakpointOn::Line(ref mut bp) => {
                bp.adjusted_line = None;
                let mut res: (usize, Vec<(usize, u16)>) = (usize::MAX, Vec::new());
                let (mut loading, mut found_file) = (false, false);
                for binary in symbols_registry.iter() {
                    if !binary.is_mapped {
                        continue;
                    }
                    let symbols = match &binary.symbols {
                        Ok(s) => s,
                        Err(e) if e.is_loading() => {
                            loading = true;
                            continue;
                        }
                        Err(_) => continue,
                    };
                    let file_idx = match symbols.path_to_used_file.get(&bp.path as &Path) {
                        Some(i) => *i,
                        None => continue };
                    found_file = true;
                    let addrs = match symbols.line_to_addrs(file_idx, bp.line, true) {
                        Ok(x) => x,
                        Err(None) => continue,
                        Err(Some(adjusted_line)) => match symbols.line_to_addrs(file_idx, adjusted_line, true){
                            Ok(x) => x,
                            Err(_) => continue,
                        }
                    };
                    if addrs.is_empty() {
                        continue;
                    }
                    if addrs[0].0.line() > res.0 {
                        continue;
                    }
                    if addrs[0].0.line() < res.0 {
                        res = (addrs[0].0.line(), Vec::new());
                    }

                    // There are often multiple nearby addresses for the same line, usually with different column numbers.
                    // E.g. if the line contains a function call where some arguments are function calls too, there would usually be an address for each of the arguments and a location for the outer function call.
                    // We want to set breakpoint on only the first of those addresses. Otherwise continuing from such breakpoint is very confusing: you continue and immediately stop without leaving the line.
                    // On the other hand, a line can have multiple addresses corresponding to different inlining sites of the containing function; we don't want to deduplicate those.
                    // So we group addresses by the containing (sub)function and keep the lowest address in each.
                    let mut subfuncs_and_addrs: Vec<(/*function_idx*/ usize, /*subfunction_idx*/ usize, /*addr*/ usize, u16)> = addrs.iter().map(|(line, level)| {
                        let addr = line.addr();
                        if let Ok((function, function_idx)) = symbols.addr_to_function(addr) {
                            if let Some((sf, l)) = symbols.containing_subfunction_at_level(addr, *level, function) {
                                return (function_idx, sf, addr, l);
                            }
                        }
                        (usize::MAX, addr, addr, *level)
                    }).collect();
                    subfuncs_and_addrs.sort_unstable();
                    for (i, &(f, sf, addr, level)) in subfuncs_and_addrs.iter().enumerate() {
                        if i > 0 {
                            let &(prev_f, prev_sf, _, _) = &subfuncs_and_addrs[i-1];
                            if (prev_f, prev_sf) == (f, sf) {
                                continue;
                            }
                        }

                        let addr = binary.addr_map.static_to_dynamic(addr);
                        res.1.push((addr, level));
                    }
                }
                if res.1.is_empty() {
                    breakpoint.addrs = if loading {
                        err!(Loading, "symbols are not loaded yet")
                    } else if found_file {
                        err!(NoCodeLocations, "no machine code at or below line {}", bp.line)
                    } else {
                        err!(NoCodeLocations, "no machine code for file")
                    };
                } else {
                    if res.0 != bp.line {
                        bp.adjusted_line = Some(res.0);
                    }
                    breakpoint.addrs = Ok(res.1);
                }
            }
            BreakpointOn::Address(bp) => {
                if let Some((locator, offset)) = &mut bp.function {
                    match Self::resolve_function_breakpoint_location(symbols_registry, locator, *offset) {
                        Ok(a) => bp.addr = a,
                        Err(e) if e.is_loading() => {
                            breakpoint.addrs = Err(e); // we'll retry when loaded
                            return;
                        }
                        Err(_) => (), // fall back to last known address (bp.addr)
                    }
                }
                breakpoint.addrs = Ok(vec![(bp.addr, bp.subfunction_level)]);
            }
            BreakpointOn::PointOfInterest(point) => {
                let mut loading = false;
                let mut addrs: Vec<(usize, u16)> = Vec::new();
                for binary in symbols_registry.iter() {
                    let symbols = match &binary.symbols {
                        Ok(s) if binary.is_mapped => s,
                        Err(e) if e.is_loading() => {
                            loading = true;
                            continue;
                        }
                        _ => continue,
                    };
                    if let Some(static_addrs) = symbols.points_of_interest.get(point) {
                        for &static_addr in static_addrs {
                            let addr = binary.addr_map.static_to_dynamic(static_addr);
                            addrs.push((addr, u16::MAX));
                        }
                    }
                }
                breakpoint.addrs = if !addrs.is_empty() {
                    Ok(addrs)
                } else if loading {
                    err!(Loading, "symbols are not loaded yet")
                } else {
                    err!(NoFunction, "{} not found", point.name_for_ui())
                };
            }
            BreakpointOn::InitialExec => breakpoint.addrs = err!(Internal, "unexpected InitialExec breakpoint"),
        }
    }

    fn resolve_function_breakpoint_location(symbols_registry: &SymbolsRegistry, locator: &mut FunctionLocator, offset: usize) -> Result<usize> {
        let binary = Self::find_binary_fuzzy(symbols_registry, &locator.binary_locator)?;
        if !binary.is_mapped {
            return err!(ProcessState, "binary not mapped: {}", locator.binary_locator.path);
        }
        locator.binary_locator = binary.locator.clone();
        let symbols = binary.symbols.as_ref_clone_error()?;
        let function_idx = match symbols.find_nearest_function(&locator.mangled_name, locator.addr) {
            Some(x) => x,
            None => return err!(NoFunction, "function not found: {}", locator.demangled_name),
        };
        let function = &symbols.functions[function_idx];
        locator.mangled_name = function.mangled_name().to_vec();
        locator.demangled_name = function.demangle_name();
        locator.addr = function.addr;
        Ok(binary.addr_map.static_to_dynamic(function.addr.0 + offset))
    }

    fn add_breakpoint_location(&mut self, breakpoint: BreakpointRef, addr: usize) {
        let idx = self.breakpoint_locations.partition_point(|x| x.addr < addr);
        if idx < self.breakpoint_locations.len() && self.breakpoint_locations[idx].addr == addr {
            self.breakpoint_locations[idx].breakpoints.push(breakpoint);
        } else {
            self.breakpoint_locations.insert(idx, BreakpointLocation {addr, original_byte: 0, hardware: false, active: false, breakpoints: vec![breakpoint], error: None});
        }
    }

    // All threads must be suspended.
    fn activate_breakpoint_location(&mut self, idx: usize, any_suspended_tid: pid_t) -> Result<()> {
        let location = &self.breakpoint_locations[idx];
        if location.active { return Ok(()); }
        let addr = location.addr;
        if location.hardware {
            assert!(self.any_thread_in_state(ThreadState::Running).is_none());
            let hw_idx = match self.hardware_breakpoints.iter().position(|b| !b.active) {
                None => return err!(OutOfHardwareBreakpoints, "out of hw breakpoints"),
                Some(i) => i };

            // Currently only step breakpoints are thread-specific.
            let all_threads = location.breakpoints.iter().any(|b| match b { BreakpointRef::Step(_) => false, BreakpointRef::Id{..} => true });
            let thread_specific = match &self.stepping {
                Some(s) if !all_threads => Some(s.tid),
                _ => None,
            };

            self.hardware_breakpoints[hw_idx] = HardwareBreakpoint {active: true, thread_specific, addr};
            let tids: Vec<pid_t> = self.threads.keys().copied().collect();
            for tid in tids {
                self.set_debug_registers_for_thread(tid)?;
            }
        } else {
            let byte_idx = addr % 8;
            let bit_idx = byte_idx * 8;
            // Note that some threads might be running right now, so this is a bit precarious, but should still be correct.
            let word = self.memory.read_u64(addr - byte_idx)?;
            self.breakpoint_locations[idx].original_byte = ((word >> bit_idx) & 0xff) as u8;
            let word = word & !(0xff << bit_idx) | (0xcc << bit_idx);
            // PTRACE_POKETEXT is dumb. It requires the provided thread to be suspended, but doesn't care if other threads are running.
            // Presumably this requirement was added just in case, back when threads didn't exist.
            // So we need to semi-artificially propagate a TID of any suspended thread into here, and we can't add/remove breakpoints
            // while all threads are running. I wish process_vm_writev() had a flag to allow writing to read-only memory (.text is usually mapped as read-only).
            unsafe { ptrace(libc::PTRACE_POKETEXT, any_suspended_tid, (addr - byte_idx) as u64, word, &mut self.prof.bucket)?; }
        }
        self.breakpoint_locations[idx].active = true;
        Ok(())
    }

    fn deactivate_breakpoint_location(&mut self, idx: usize, any_suspended_tid: pid_t) -> Result<()> {
        let location = &mut self.breakpoint_locations[idx];
        if !location.active { return Ok(()); }
        if location.hardware {
            for h in &mut self.hardware_breakpoints {
                if h.addr == location.addr {
                    h.active = false;
                    h.addr = 0;
                }
            }
            // Don't actively update threads' debug registers. We'll update them if the stale breakpoint gets hit.
        } else {
            let byte_idx = location.addr % 8;
            let bit_idx = byte_idx * 8;
            // Other threads may be running, but it's fine.
            let word = self.memory.read_u64(location.addr - byte_idx)?;
            let word = word & !(0xff << bit_idx) | ((location.original_byte as u64) << bit_idx);
            unsafe { ptrace(libc::PTRACE_POKETEXT, any_suspended_tid, (location.addr - byte_idx) as u64, word, &mut self.prof.bucket)?; }
        }
        location.active = false;
        Ok(())
    }

    fn find_breakpoint_location(&self, addr: usize) -> Option<usize> {
        let idx = self.breakpoint_locations.partition_point(|b| b.addr < addr);
        if idx < self.breakpoint_locations.len() && self.breakpoint_locations[idx].addr == addr {
            Some(idx)
        } else {
            None
        }
    }

    // Either calls handle_breakpoints() or makes sure it'll be called as soon as all threads are suspended.
    // Caller must ensure all ThreadInfo-s are up-to-date (i.e. just don't call this from the middle of process_events()).
    fn arrange_handle_breakpoints(&mut self) -> Result<()> {
        if !self.stopping_to_handle_breakpoints {
            if self.ptrace_interrupt_all_running_threads()? > 0 {
                self.stopping_to_handle_breakpoints = true;
            } else {
                self.handle_breakpoints()?;
            }
        }
        Ok(())
    }

    // All threads must be suspended.
    fn handle_breakpoints(&mut self) -> Result<()> {
        // Deactivate lingering locations from removed breakpoints.
        let mut res_idx = 0usize;
        for idx in 0..self.breakpoint_locations.len() {
            if self.breakpoint_locations[idx].breakpoints.is_empty() {
                self.deactivate_breakpoint_location(idx, self.pid)?;
            } else {
                self.breakpoint_locations.swap(res_idx, idx);
                res_idx += 1;
            }
        }
        self.breakpoint_locations.truncate(res_idx);

        // Convert between hardware and software breakpoints as needed:
        // if any thread is standing at a breakpoint, make it hardware, otherwise make it software.

        let mut thread_addresses: HashMap<usize, pid_t> = HashMap::new();
        for (tid, t) in self.threads.iter() {
            if t.info.regs.has(RegisterIdx::Rip) {
                let addr = t.info.regs.get_int(RegisterIdx::Rip)?.0 as usize;
                thread_addresses.insert(addr, *tid);
            }
        }

        for idx in 0..self.breakpoint_locations.len() {
            let loc = &self.breakpoint_locations[idx];
            if loc.hardware && !thread_addresses.contains_key(&loc.addr) {
                self.deactivate_breakpoint_location(idx, self.pid)?;
                self.breakpoint_locations[idx].hardware = false;
            }
        }
        for idx in 0..self.breakpoint_locations.len() {
            let loc = &self.breakpoint_locations[idx];
            let addr = loc.addr;
            let tid = thread_addresses.get(&loc.addr);
            if !loc.hardware && tid.is_some() {
                self.deactivate_breakpoint_location(idx, self.pid)?;
                self.breakpoint_locations[idx].hardware = true;
                self.threads.get_mut(tid.unwrap()).unwrap().ignore_next_hw_breakpoint_hit_at_addr = Some(addr);
            }
        }

        for idx in 0..self.breakpoint_locations.len() {
            match self.activate_breakpoint_location(idx, self.pid) {
                Ok(()) => self.breakpoint_locations[idx].error = None,
                Err(e) => {
                    self.breakpoint_locations[idx].error = Some(e.clone());
                    eprintln!("breakpoint error: {}", e);
                    if e.is_out_of_hardware_breakpoints() {
                        log!(self.log, "out of hw breakpoints! some breakpoints deactivated");
                    } else {
                        log!(self.log, "breakpoint error: {}", e);
                    }
                }
            }
        }

        Ok(())
    }

    fn set_debug_registers_for_thread(&mut self, tid: pid_t) -> Result<()> {
        let mut dr7 = 1u64 << 10;
        for i in 0..4 {
            let b = &self.hardware_breakpoints[i];
            if !b.active || b.thread_specific.is_some_and(|x| x != tid) {
                continue;
            }
            unsafe { ptrace(libc::PTRACE_POKEUSER, tid, (offsetof!(libc::user, u_debugreg) + i * 8) as u64, b.addr as u64, &mut self.prof.bucket)? };
            dr7 |= 1 << (i*2);
        }
        unsafe { ptrace(libc::PTRACE_POKEUSER, tid, (offsetof!(libc::user, u_debugreg) + 7*8) as u64, dr7, &mut self.prof.bucket)? };
        Ok(())
    }

    fn handle_step_breakpoint_hit(step: &StepState, type_: StepBreakpointType, request_single_step: &mut bool) {
        match type_ {
            StepBreakpointType::Call | StepBreakpointType::JumpOut => *request_single_step = true,
            StepBreakpointType::AfterRange | StepBreakpointType::AfterRet | StepBreakpointType::Catch | StepBreakpointType::Cursor(_) => (),
        }
    }

    // Returns whether the step completed.
    fn handle_step_stop(&mut self, spurious_stop: bool, hit_step_breakpoint: bool, regs: &Registers) -> bool {
        let step = self.stepping.as_ref().unwrap();
        if step.internal_kind == StepKind::Cursor {
            return hit_step_breakpoint;
        }
        let addr = regs.get_int(RegisterIdx::Rip).unwrap().0 as usize;
        let i = step.addr_ranges.partition_point(|r| r.end <= addr);
        let in_ranges = i < step.addr_ranges.len() && step.addr_ranges[i].start <= addr;
        if step.internal_kind == StepKind::Into && step.by_instructions {
            if step.addr_ranges.is_empty() && spurious_stop {
                if self.context.settings.trace_logging { eprintln!("trace: ignoring spurious stop on hw breakpoint {:x} (stepping)", addr); }
                return false;
            }
            return !in_ranges;
        }
        let step = self.stepping.as_ref().unwrap();
        let cfa = Self::get_cfa_for_step(&self.info, &self.symbols, &mut self.log, &self.memory, addr, regs);
        let cfa = match cfa {
            None => return step.internal_kind == StepKind::Into,
            Some(c) => c };
        match step.internal_kind {
            StepKind::Into => cfa != step.cfa || !in_ranges,
            StepKind::Over => cfa > step.cfa || (cfa == step.cfa && !in_ranges),
            StepKind::Out => cfa > step.cfa,
            StepKind::Cursor => panic!("huh"),
        }
    }

    fn determine_subframe_to_select(stack: &StackTrace, stack_digest: &Vec<usize>, is_step_into: bool, subfunction_level: u16) -> Option<usize> {
        if stack.frames.is_empty() {
            return None;
        }
        if subfunction_level != u16::MAX {
            return Some(stack.frames[0].subframes.end.saturating_sub(subfunction_level as usize + 1));
        }
        if stack_digest.is_empty() {
            return None;
        }
        let mut suf = 0;
        while suf < stack_digest.len() && suf < stack.subframes.len() && stack_digest[stack_digest.len() - 1 - suf] == stack.subframe_identity(stack.subframes.len() - 1 - suf) {
            suf += 1;
        }
        if suf == 0 {
            return None;
        }
        if is_step_into && suf == stack_digest.len() && suf < stack.subframes.len() {
            suf += 1;
        }
        Some(stack.subframes.len() - suf)
    }

    fn get_cfa_for_step(info: &ProcessInfo, symbols_registry: &SymbolsRegistry, log: &mut Log, memory: &MemReader, addr: usize, regs: &Registers) -> Option<usize> {
        // This is called while handling SIGTRAP, when `info` is not necessarily up-to-date, so this
        // in theory may incorrectly fail if a dynamic library was loaded during a step, and the step ended up hitting it (not sure how).
        let map = match info.maps.addr_to_map(addr) {
            None => {
                log!(log, "address 0x{:x} not mapped", addr);
                eprintln!("warning: address 0x{:x} not mapped (when determining cfa for step)", addr);
                return None;
            }
            Some(m) => m };
        let binary_id = match map.binary_id.clone() {
            None => {
                log!(log, "address 0x{:x} not mapped to a binary", addr);
                eprintln!("warning: address 0x{:x} not mapped to a binary (when determining cfa for step)", addr);
                return None;
            }
            Some(b) => b };
        let binary = symbols_registry.get(binary_id).unwrap();
        let unwind = match &binary.unwind {
            Err(e) => {
                log!(log, "no unwind: {}", e);
                eprintln!("warning: no unwind for address 0x{:x} (when determining cfa for step)", addr);
                return None;
            }
            Ok(u) => u };
        let mut scratch = UnwindScratchBuffer::default();
        let mut memory = CachedMemReader::new(memory.clone());
        match unwind.find_row_and_eval_cfa(&mut memory, &binary.addr_map, &mut scratch, addr, regs) {
            Err(e) => {
                log!(log, "no frame for addr 0x{:x}: {}", addr, e);
                eprintln!("warning: no frame for addr 0x{:x} (when determining cfa for step): {}", addr, e);
                return None;
            }
            Ok((_, _, cfa, _, _)) => Some(cfa),
        }
    }
    
    // Returns true if any breakpoint was actually hit, so we should switch to ProcessState::Suspended.
    // May also set stopping_to_handle_breakpoints to true, in which case the caller should stop all threads.
    // Otherwise treat it as a spurious wakeup and continue (e.g. breakpoint is for a different thread, or conditional breakpoint's condition evaluated to false, or something).
    fn handle_breakpoint_trap(&mut self, tid: pid_t, single_stepping: bool, ignore_next_hw_breakpoint_hit_at_addr: Option<usize>) -> Result<(/*hit*/ bool, Registers, Option<(Vec<usize>, bool, u16)>)> {
        let mut regs = ptrace_getregs(tid, &mut self.prof.bucket)?;
        let mut addr = regs.get_int(RegisterIdx::Rip).unwrap().0 as usize;

        // There's a very unfortunate detail in how the 0xcc (INT 3) instruction is handled (at least in Linux). After hitting 0xcc at address X,
        // the thread is stopped with its RIP = X+1, not X. When we see a SIGTRAP and RIP = X+1, it can mean two things:
        //  (a) The 0xcc instruction was hit. We're stopped at breakpoint X. When resuming the thread, we must remove the breakpoint *and decrement RIP*.
        //  (b) The thread jumped to X+1, then got a SIGTRAP unrelated to our breakpoint. When resuming the thread we must *leave RIP unchanged*.
        // (In contrast, if 0xcc suspended with RIP = X, there would be no such ambiguity. There also wouldn't be any of the "Interaction between
        // SINGLESTEP and breakpoints" nonsense. Ugh.)
        //
        // So we have to do some guesswork to distinguish (a) and (b). We do it by elimination. A thread may receive SIGTRAP (with no PTRACE_EVENT_*) if:
        //  (1) It did a PTRACE_SINGLESTEP. We check for this by keeping track of our own calls to ptrace(PTRACE_SINGLESTEP).
        //      But see "Interaction between SINGLESTEP and breakpoints" about extra difficulties with this.
        //  (2) It hit a hardware breakpoint. We check for this by inspecting the debug register.
        //  (3) It hit a software breakpoint. We assume this if none of the above are the case.
        //  (4) Someone sent a SIGTRAP manually at just the wrong moment. This will break things, there's not much we can do about it, AFAICT.

        let dr6 = unsafe { ptrace(libc::PTRACE_PEEKUSER, tid, offsetof!(libc::user, u_debugreg) as u64 + 6*8, 0, &mut self.prof.bucket)? };
        let stopped_on_hw_breakpoint = dr6 & 15 != 0;
        if stopped_on_hw_breakpoint {
            // In case it's a stale breakpoint.
            self.set_debug_registers_for_thread(tid)?;
            // Clear the 'breakpoint was hit' bits because neither the CPU nor Linux will do it for us.
            unsafe { ptrace(libc::PTRACE_POKEUSER, tid, (offsetof!(libc::user, u_debugreg) + 6 * 8) as u64, (dr6 & !15) as u64, &mut self.prof.bucket)? };
        }

        let mut stopped_on_sw_breakpoint = false;
        if !single_stepping && !stopped_on_hw_breakpoint {
            // Supposedly, we can only get here by hitting a software breakpoint (INT3 instruction) at addr-1 (or if someone sent a SIGTRAP manually).
            // But this is so precarious that who knows.
            // Should we decrement addr unconditionally or should we check that there's INT3 at addr-1?
            // Currently we do it unconditionally because it's in principle possible to get a delayed SIGTRAP after we already removed the INT3 (and the corresponding breakpoint location).
            // But we also print a warning (below) in this case, so hopefully we'll be able to hunt down all cases where this breaks.
            stopped_on_sw_breakpoint = true;
            addr -= 1;
            regs.set_int(RegisterIdx::Rip, addr as u64, false);
            unsafe { ptrace(libc::PTRACE_POKEUSER, tid, offsetof!(libc::user, regs.rip) as u64, addr as u64, &mut self.prof.bucket)? };
        }

        let spurious_stop = stopped_on_hw_breakpoint && ignore_next_hw_breakpoint_hit_at_addr == Some(addr);

        let mut hit = false;
        let mut request_single_step = false;
        let mut stop_reasons: Vec<StopReason> = Vec::new();
        let mut stack_digest_to_select: Option<(Vec<usize>, bool, u16)> = None;
        let mut hit_step_breakpoint: Option<StepBreakpointType> = None;

        if let Some(idx) = self.find_breakpoint_location(addr) {
            let location = &mut self.breakpoint_locations[idx];

            if stopped_on_sw_breakpoint && location.hardware {
                eprintln!("warning: got unexpected SIGTRAP in thread {} at {:x} (just after a hw breakpoint)", tid, addr + 1);
            }

            if location.breakpoints.is_empty() {
                // Lazily deactivate obsolete breakpoint location if we hit it. This is just for performance, to avoid repeatedly hitting+ignoring a deleted hot breakpoint.
                self.deactivate_breakpoint_location(idx, tid)?;
            }

            for bp_i in 0..self.breakpoint_locations[idx].breakpoints.len() {
                let b = &self.breakpoint_locations[idx].breakpoints[bp_i];
                match b {
                    BreakpointRef::Step(t) => {
                        let step = self.stepping.as_ref().unwrap();
                        if tid == step.tid {
                            Self::handle_step_breakpoint_hit(step, *t, &mut request_single_step);

                            hit_step_breakpoint = Some(*t);
                            if let &StepBreakpointType::Cursor(subfunction_level) = t {
                                if subfunction_level != u16::MAX {
                                    stack_digest_to_select = Some((Vec::new(), false, subfunction_level));
                                }
                            }
                        }
                    }
                    &BreakpointRef::Id {id, subfunction_level} => {
                        let bp = self.breakpoints.get_mut(id);
                        bp.hits += 1;

                        if spurious_stop {
                            // Spurious stop after converting breakpoint from software to hardware, or initial hit after adding a breakpoint on current line.
                            if self.context.settings.trace_logging { eprintln!("trace: ignoring spurious stop on hw breakpoint {:x}", addr); }
                            continue;
                        }
                        if let Some(step) = &self.stepping {
                            if step.disable_breakpoints {
                                // Ignore regular breakpoints when stepping.
                                // (It would be better for performance to also deactivate them as we go, then reactivate after the step completes.)
                                continue;
                            }
                        }
                        if self.pending_step.is_some() {
                            continue;
                        }
                        if self.target_state == ProcessState::Suspended {
                            // Solves this race condition:
                            //  1. A step completes. It's added to thread's stop_reasons. Other threads are requested to suspend.
                            //  2. The UI sees the stepped thread's stop_reasons.
                            //  3. Just before suspending, some other thread hits a breakpoint. It's added to stop_reasons (because self.stepping is already unset).
                            //  4. The UI sees the breakpoint hit in stop_reasons and switches to that thread.
                            //     Very confusing because breakpoints are supposed to be disabled when stepping.
                            //
                            // As a side effect, this check also prevents reporting simultaneous breakpoint hits by multiple threads.
                            // If this turns out to be a problem, replace this with a different mechanism (maybe a flag in Thread saying "ignore breakpoints in this thread until it's suspended").
                            continue;
                        }
                        if let Some((_, Ok(_), _)) = &bp.condition {
                            let r = self.eval_breakpoint_condition(tid, id, subfunction_level);
                            let bp = self.breakpoints.get_mut(id);
                            let cond = &mut bp.condition.as_mut().unwrap();
                            match r {
                                Ok(hit) => {
                                    cond.2 = None;
                                    if !hit {
                                        continue;
                                    }
                                }
                                Err(e) => cond.2 = Some(e), // put error into the breakpoint to be shown in UI, and stop
                            }
                        }

                        stop_reasons.push(StopReason::Breakpoint(id));
                        if subfunction_level != u16::MAX {
                            stack_digest_to_select = Some((Vec::new(), false, subfunction_level));
                        }
                        hit = true;
                    }
                }
            }
            let location = &mut self.breakpoint_locations[idx];

            if !location.hardware {
                // Stop all threads so that we can convert the breakpoint into hardware breakpoint (or single-step past it).
                // If this turns out too slow, we could hook the current instruction instead (maybe won't work for all instructions).
                self.stopping_to_handle_breakpoints = true;
            }

            if request_single_step {
                self.threads.get_mut(&tid).unwrap().single_stepping = true;
            }
        } else if stopped_on_sw_breakpoint {
            eprintln!("warning: got unexpected SIGTRAP in thread {} at {:x}", tid, addr + 1);
        }

        if let Some(step) = &self.stepping {
            if hit {
                self.cancel_stepping();
            } else if tid == step.tid && self.handle_step_stop(spurious_stop, hit_step_breakpoint.is_some(), &regs) {
                let step = self.stepping.as_mut().unwrap();
                if step.internal_kind != StepKind::Cursor {
                    stack_digest_to_select = Some((mem::take(&mut step.stack_digest), step.internal_kind == StepKind::Into, u16::MAX));
                }
                let stop_reason = if hit_step_breakpoint.is_some_and(|t| t == StepBreakpointType::Catch) {StopReason::Exception} else {StopReason::Step};
                stop_reasons.push(stop_reason);
                self.cancel_stepping();
                hit = true;
            }
        }

        if !stop_reasons.is_empty() {
            self.threads.get_mut(&tid).unwrap().stop_reasons.append(&mut stop_reasons);
        }

        Ok((hit, regs, stack_digest_to_select))
    }

    fn eval_breakpoint_condition(&mut self, tid: pid_t, id: BreakpointId, subfunction_level: u16) -> Result<bool> {
        // All of this is slow.
        let bp = self.breakpoints.get(id);
        let expr = bp.condition.as_ref().unwrap().1.as_ref().unwrap();
        if expr.is_trivial_false() {
            // Fast path for profiling (to measure how slow is the expression evaluation vs everything else.
            return Ok(false);
        }
        let need_full_stack = does_expression_need_full_stack(expr);
        self.threads.get_mut(&tid).unwrap().info.regs = ptrace_getregs(tid, &mut self.prof.bucket)?;
        let stack = self.get_stack_trace(tid, /*partial*/ !need_full_stack);
        let selected_subframe = if subfunction_level != u16::MAX && !stack.frames.is_empty() {
            stack.frames[0].subframes.end.saturating_sub(subfunction_level as usize + 1)
        } else {
            0
        };
        let bp = self.breakpoints.get(id);
        let expr = bp.condition.as_ref().unwrap().1.as_ref().unwrap();
        let mut eval_state = EvalState::new();
        let mut eval_context = self.make_eval_context(&stack, selected_subframe);
        let (val, _dubious) = eval_parsed_expression(expr, &mut eval_state, &mut eval_context)?;
        Ok(is_value_truthy(&val, &mut eval_context.memory)?)
    }
}

// Make a best effort to detach from the process, i.e. remove all breakpoints and detach from all threads.
// Called just before exiting the process. Leaves the Debugger in potentially unusable state.
// May be called from a panic handler in main thread, without unwinding the stack! The Debugger may be in inconsistent state,
// so this function should make as few assumptions as possible about that.
//
// We can't guarantee that this semi-graceful detaching always happens (e.g. we may be SIGKILLed), but we at least do it on normal exit and on
// panics in main thread. (Currently not on panics in other threads, though they should be rare; and not on things like segfaults.)
//
// (The PTRACE_DETACH part is probably not necessary, `man ptrace` says:
//  "If the tracer dies, all tracees are automatically detached and restarted, unless they were in group-stop".
//  We do it along the way anyway because it's easy, we have to stop all threads to unset debug registers anyway.)
impl Drop for Debugger {
    fn drop(&mut self) {
        if self.mode != RunMode::Attach || self.target_state == ProcessState::NoProcess {
            return;
        }
        self.target_state = ProcessState::NoProcess;
        eprintln!("info: detaching");

        let memory = self.memory.clone();
        let mut memory_bytes_to_restore: Vec<(usize, u8)> = Vec::new();
        for location in &self.breakpoint_locations {
            if !location.hardware && location.active {
                memory_bytes_to_restore.push((location.addr, location.original_byte));
            }
        }
        let mut detach_thread = |tid: pid_t| {
            let mut prof = ProfileBucket::invalid();
            // Remove software breakpoints when we see the first stopped thread (which is required for PTRACE_POKETEXT).
            for (addr, byte) in mem::take(&mut memory_bytes_to_restore) {
                let byte_idx = addr % 8;
                let bit_idx = byte_idx * 8;
                let word = match memory.read_u64(addr - byte_idx) {
                    Ok(w) => w,
                    Err(e) => {
                        eprintln!("warning: detach failed to remove breakpoint at 0x{:x}: read failed: {}", addr, e);
                        continue;
                    } };
                let word = word & !(0xff << bit_idx) | ((byte as u64) << bit_idx);
                if let Err(e) = unsafe { ptrace(libc::PTRACE_POKETEXT, tid, (addr - byte_idx) as u64, word, &mut prof) } {
                    eprintln!("warning: detach failed to remove breakpoint at 0x{:x}: PTRACE_POKETEXT failed: {}", addr, e);
                }
            }

            // Disable hardware breakpoints for this thread. (Do this unconditionally because threads may have leftover breakpoints that are not in self.hardware_breakpoints or self.breakpoint_locations anymore.)
            if let Err(e) = unsafe { ptrace(libc::PTRACE_POKEUSER, tid, (offsetof!(libc::user, u_debugreg) + 7*8) as u64, 1u64 << 10, &mut prof) } {
                eprintln!("warning: detach failed to clear hardware breakpoints for thread {}: {}", tid, e);
            }

            if let Err(e) = unsafe { ptrace(libc::PTRACE_DETACH, tid, 0, 0, &mut prof) } {
                eprintln!("warning: detach failed for thread {}: {}", tid, e);
            }
        };
        let mut running_threads: HashSet<pid_t> = HashSet::new();
        let mut prof = ProfileBucket::invalid();
        for (tid, thread) in &self.threads {
            if thread.state == ThreadState::Suspended {
                detach_thread(*tid);
            } else if let Err(e) = unsafe {ptrace(libc::PTRACE_INTERRUPT, *tid, 0, 0, &mut prof)} {
                eprintln!("warning: detach failed to stop thread {}: {}", tid, e);
            } else {
                running_threads.insert(*tid);
            }
        }
        while !running_threads.is_empty() {
            let (tid, wstatus) = if let Some(x) = self.pending_wait_events.pop_front() {
                x
            } else {
                let mut wstatus = 0i32;
                let tid = unsafe {libc::waitpid(-1, &mut wstatus, 0)};
                if tid < 0 {
                    let err = io::Error::last_os_error();
                    if err.kind() == io::ErrorKind::Interrupted {
                        continue;
                    }
                    eprintln!("warning: waitpid() failed during detach: {}", err);
                    break;
                }
                (tid, wstatus)
            };
            if !running_threads.contains(&tid) {
                eprintln!("info: got event {} for unknown thread {} during detach", wstatus, tid);
                continue;
            }

            if !libc::WIFEXITED(wstatus) && !libc::WIFSIGNALED(wstatus) {
                detach_thread(tid);
            }

            running_threads.remove(&tid);
        }
    }
}
