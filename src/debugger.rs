use crate::{*, elf::*, error::*, util::*, log::*, symbols::*, process_info::*, symbols_registry::*, unwind::*, procfs::*, registers::*, disassembly::*, pool::*, settings::*, context::*, disassembly::*, expr::*, persistent::*, interp::*, os::*};
use libc::{pid_t, c_char, c_void};
use iced_x86::FlowControl;
use std::{io, ptr, rc::Rc, collections::{HashMap, VecDeque, HashSet, hash_map::Entry}, mem, path::{Path, PathBuf}, sync::Arc, ffi::CStr, ops::Range, os::fd::AsRawFd, fs, time::{Instant, Duration}};

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum RunMode {
    Run, // start the program inside the debugger
    Attach, // attach to a running process
    CoreDump,
}
impl RunMode {
    pub fn human_string(self) -> &'static str { match self {RunMode::Run => "run", RunMode::Attach => "attach", RunMode::CoreDump => "coredump"} }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ProcessState {
    NoProcess,
    Starting,
    Exiting,

    Running,
    Suspended,

    CoreDump, // something between NoProcess and Suspended

    Stepping,
}
impl ProcessState {
    pub fn process_ready(self) -> bool {
        match self {
            Self::NoProcess | Self::Starting | Self::Exiting | Self::CoreDump => false,
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
    // We often want to do things when this changes, so keep the number of code sites that change it to a minimum.
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
    // See singlestep_vs_group_stop.cpp for repro.
    //
    // We prevent this scenario by preventing part (3). After doing one SINGLESTEP, we keep doing SINGLESTEP until we get a SIGTRAP.
    // This way the spurious SIGTRAP gets correctly interpreted as relating to a SINGLESTEP, with no ambiguity.
    // To this end, the single_stepping flag is unset only when we get SIGTRAP, and while it's set we always do SINGLESTEP instead of CONT.
    single_stepping: bool,

    // If true, we're standing just after an int3 instruction in the program (not injected by the debugger).
    // For UI and stepping, we should pretend that we're standing on the int3 instead, i.e. that the thread's RIP is 1 less than info.regs says.
    is_after_user_debug_trap_instruction: bool,

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
    // `man ptrace` says:
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
    initial_exec_failed: bool,

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

    // Start this step when we're ready: on PTRACE_EVENT_EXEC and/or after symbols are loaded. Can't be a data breakpoint.
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
    //  * Into: cfa != step.cfa || addr not in step.addr_ranges  [+ additional logic if stop_only_on_statements]
    //  * Over: cfa > step.cfa || (cfa == step.cfa && addr not in step.addr_ranges)  [+ additional logic if stop_only_on_statements]
    //  * Out: cfa > step.cfa
    // `internal_kind` may be different from the user-level step kind. E.g. step-out-of-inlined-function is turned into step-over.
    pub internal_kind: StepKind,
    pub by_instructions: bool,
    pub addr_ranges: Vec<Range<usize>>,
    // Do repeated PTRACE_SINGLESTEP instead of using internal breakpoints.
    pub single_steps: bool,

    // Canonical frame address, i.e. something like the RBP register - identifies the current call frame.
    pub cfa: usize,

    pub stop_only_on_statements: bool,
    // These are used only if stop_only_on_statements is true.
    pub binary_id: usize,
    pub start_line: Option<LineInfo>,
    pub use_line_number_with_column: bool,

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
impl Default for StepState { fn default() -> Self { Self {tid: 0, keep_other_threads_suspended: false, disable_breakpoints: true, internal_kind: StepKind::Into, by_instructions: false, addr_ranges: Vec::new(), single_steps: false, cfa: 0, stop_only_on_statements: false, binary_id: 0, start_line: None, use_line_number_with_column: false, stack_digest: Vec::new()} } }

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
    pub no_retry: bool, // got an ~unretriable error, don't try activating this location in handle_breakpoints()
}

#[derive(Clone, Debug, Default)]
pub struct HardwareBreakpoint {
    pub active: bool,
    // We allocate hardware breakpoint slots as if no breakpoints are thread-specific. This is fine currently since only steps use thread-specific breakpoints, but
    // if we add support for user-provided thread-specific breakpoints we may want to make thread-specific hw breakpoint allocation be per thread.
    pub thread_specific: Option<pid_t>,
    pub addr: usize,

    pub data_breakpoint_id: Option<BreakpointId>, // iff it's a data breakpoint
    pub stop_on_read: bool,
    pub data_size: u8, // 1, 2, 4, or 8

    pub pushed_to_threads: bool,
}

#[derive(Debug, Clone)]
pub struct LineBreakpoint {
    pub path: PathBuf,
    pub line: usize,
    // If the `line` corresponds to no machine instructions (e.g. it points to a comment or it's optimized out), we put the breakpoint on the next line that has code and point `adjusted_line` to that line, and the UI shows different breakpoint markers on both lines.
    // We don't modify `line` because that would be confusing in the UI in case when breakpoint is set before symbols are loaded (e.g. in a dynamic library), and we can't adjust the line right away.
    pub adjusted_line: Option<usize>,
}

#[derive(Debug, Clone)]
pub struct InstructionBreakpoint {
    // We remember the address relative to its function to make the breakpoint survive changes to the executable.
    pub function: Option<(FunctionLocator, /*offset*/ usize)>,
    pub addr: usize, // in case `function` is None or not found
    pub subfunction_level: u16,
}

#[derive(Debug, Clone)]
pub struct DataBreakpoint {
    pub addr: usize,
    pub size: u8, // 1, 2, 4, or 8 bytes
    pub stop_on_read: bool, // we always stop on write regardless of this
}

#[derive(Debug, Clone)]
pub enum BreakpointOn {
    Line(LineBreakpoint),
    Instruction(InstructionBreakpoint),
    InitialExec, // right after initial exec (PTRACE_EVENT_EXEC)
    PointOfInterest(PointOfInterest),
    Data(DataBreakpoint),
    // Could add syscall, signal, etc.
}
impl BreakpointOn {
    pub fn is_data(&self) -> bool { match self { Self::Data(_) => true, _ => false } }
    pub fn as_point_of_interest(&self) -> Option<&PointOfInterest> { match self { Self::PointOfInterest(x) => Some(x), _ => None } }

    pub fn should_wait_for_symbols(&self) -> bool {
        match self {
            Self::Data(_) | Self::InitialExec => false,
            // Hack: exempt Panic breakpoint from waiting for symbols to load.
            // This means panic will be missed if it happens early enough in the program execution.
            // Without this, we'd always wait for symbols to load before running
            // (because panic breakpoint is active on startup by default), which seems worse.
            // Ideally we should make symbols loading find the panic handler early on, so we can
            // activate panic breakpoint without waiting for the whole loading.
            Self::PointOfInterest(PointOfInterest::Panic) => false,
            _ => true,
        }
    }
}

pub struct Breakpoint {
    pub on: BreakpointOn,
    pub condition: Option<(String, Result<Expression>, Option<Error>)>,
    pub hits: usize, // including spurious stops of all kinds
    // Cached list of instruction addresses, determined using the BreakpointOn and debug symbols. NotCalculated if we didn't resolve this yet.
    // (We don't put data breakpoint addresses here because that would invite bugs.)
    // These are dynamic addresses, so we clear this list when restarting the debuggee as runtime addresses may have changed.
    // If the breakpoint is on a line that has inlined function call, subfunction_level is the depth of that inlined call.
    // When the breakpoint is hit we should select the stack subframe at that inline depth, not the top subframe that shows the insides
    // of the inlined function (it's very confusing otherwise). If SUBFUNCTION_LEVEL_MAX, no subframe selection is made (so ui probably selects the top subframe).
    pub addrs: Result<Vec<(usize, /*subfunction_level*/ u16)>>,
    // Directly controlled by the user, may be true even if we failed to activate the breakpoint.
    pub enabled: bool,
    // True if this breakpoint's addresses are added to breakpoint_locations (even if these locations failed to activate).
    pub active: bool,

    // Internal breakpoint. Don't show in UI, don't delete. We create such breakpoints once and rely that no code site will accidentally remove or disable them after that.
    pub hidden: bool,
    // Special convenience breakpoints automatically created on startup. E.g. for exceptions and panics.
    // We have a bunch of special behavior for them: don't allow deleting them in ui, don't show highlight errors in red (e.g. if panic breakpoint failed to activate because the program is not in Rust), place cursor after them on startup, etc.
    pub builtin: bool,
}
impl Breakpoint {
    fn save_state(&self, out: &mut Vec<u8>) -> Result<()> {
        match &self.on {
            BreakpointOn::Line(b) => {
                out.write_u8(0)?;
                out.write_path(&b.path)?;
                out.write_usize(b.line)?;
            }
            BreakpointOn::Instruction(b) => {
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
            BreakpointOn::Data(b) => {
                out.write_u8(4)?;
                out.write_usize(b.addr)?;
                out.write_u8(b.size)?;
                out.write_bool(b.stop_on_read)?;
            }
        }
        if let Some((s, _, _)) = &self.condition {
            out.write_u8(1)?;
            out.write_str(s)?;
        } else {
            out.write_u8(0)?;
        }
        out.write_bool(self.enabled)?;
        Ok(())
    }

    fn load_state(inp: &mut &[u8]) -> Result<Breakpoint> {
        let on = match inp.read_u8()? {
            0 => BreakpointOn::Line(LineBreakpoint {path: inp.read_path()?, line: inp.read_usize()?, adjusted_line: None}),
            1 => {
                let function = if inp.read_bool()? {
                    Some((FunctionLocator::load_state(inp)?, inp.read_usize()?))
                } else {
                    None
                };
                BreakpointOn::Instruction(InstructionBreakpoint {function, addr: inp.read_usize()?, subfunction_level: inp.read_u16()?})
            }
            2 => BreakpointOn::InitialExec,
            3 => BreakpointOn::PointOfInterest(PointOfInterest::load_state(inp)?),
            4 => BreakpointOn::Data(DataBreakpoint {addr: inp.read_usize()?, size: inp.read_u8()?, stop_on_read: inp.read_bool()?}),
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
        let enabled = inp.read_bool()?;
        Ok(Breakpoint {on, condition, hits: 0, addrs: err!(NotCalculated, ""), enabled, active: false, hidden: false, builtin: false})
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum StopReason {
    Breakpoint(BreakpointId),
    DebugTrap, // int3 instruction in the program, e.g. __builtin_debugtrap()
    Step,
    Signal(i32),
    Exception,
}
impl StopReason {
    // If different threads simultaneously stopped for different reasons, the ui should switch to the one with highest-priority reason.
    // (Currently this probably never comes into play because we don't report simultaneous breakpoint hits, see ignore_breakpoints in handle_breakpoint_trap.)
    pub fn priority(&self) -> isize /* >= 0 */ {
        match self {
            Self::DebugTrap => 0,
            Self::Breakpoint(_) => 1,
            Self::Step => 2,
            Self::Exception => 3,
            Self::Signal(_) => 4,
        }
    }
}

impl Thread {
    fn new(idx: usize, tid: pid_t, state: ThreadState) -> Self {
        Thread {idx: idx, tid: tid, state: state, single_stepping: false, ignore_next_hw_breakpoint_hit_at_addr: None, stop_reasons: Vec::new(), info: ThreadInfo::default(), pending_signal: None, waiting_for_initial_stop: true, sent_interrupt: false, stop_count: 0, attached_late: false, exiting: false, subframe_to_select: None, is_after_user_debug_trap_instruction: false}
    }
}

impl Debugger {
    fn new(mode: RunMode, command_line: Vec<String>, context: Arc<Context>, symbols: SymbolsRegistry, mut breakpoints: Pool<Breakpoint>, persistent: PersistentState, my_resource_stats: ResourceStats, prof: Profiling) -> Self {
        if breakpoints.is_empty() {
            // Add default breakpoints.

            // Hidden non-stopping breakpoint on library load to activate breakpoints on dlopen.
            breakpoints.add(Breakpoint {on: BreakpointOn::PointOfInterest(PointOfInterest::LibraryLoad), condition: None, hits: 0, addrs: err!(NotCalculated, ""), enabled: true, active: false, hidden: true, builtin: true});
            // Regular breakpoints on panics (on by default) and exceptions (off by default).
            breakpoints.add(Breakpoint {on: BreakpointOn::PointOfInterest(PointOfInterest::Panic), condition: None, hits: 0, addrs: err!(NotCalculated, ""), enabled: true, active: false, hidden: false, builtin: true});
            breakpoints.add(Breakpoint {on: BreakpointOn::PointOfInterest(PointOfInterest::Exception), condition: None, hits: 0, addrs: err!(NotCalculated, ""), enabled: false, active: false, hidden: false, builtin: true});
        } else {
            assert!(breakpoints.iter().filter(|(_, b)| b.hidden).count() == 1);
        }

        Debugger {mode, command_line, context, pid: 0, target_state: ProcessState::NoProcess, log: Log::new(), prof, threads: HashMap::new(), pending_wait_events: VecDeque::new(), next_thread_idx: 1, info: ProcessInfo::default(), my_resource_stats, symbols, memory: MemReader::Invalid, waiting_for_initial_sigstop: false, initial_exec_failed: false, stepping: None, pending_step: None, breakpoint_locations: Vec::new(), breakpoints, stopping_to_handle_breakpoints: false, stopped_until_symbols_are_loaded: None, hardware_breakpoints: std::array::from_fn(|_| HardwareBreakpoint::default()), persistent}
    }

    pub fn save_state(&self, out: &mut Vec<u8>) -> Result<()> {
        // Don't save data breakpoints because their addresses usually become obsolete on program restart or recompilation.
        let mut ids: Vec<BreakpointId> = self.breakpoints.iter().filter(|(_, b)| !b.hidden && !b.on.is_data()).map(|p| p.0).collect();
        ids.sort_by_key(|id| id.seqno); // preserve order as seen in UI
        for id in ids {
            let bp = self.breakpoints.get(id);
            if !bp.hidden && !bp.on.is_data() {
                out.write_u8(1)?;
                bp.save_state(out)?;
            }
        }
        out.write_u8(0)?;
        Ok(())
    }

    pub fn load_state(&mut self, inp: &mut &[u8]) -> Result<()> {
        // Possibly overcomplicated management of default breakpoints (currently: Panic and Exception).
        // Add them on startup before loading state, but allow the user to make them conditional.
        // If a breakpoint is found in save file, it replaces the default breakpoint (to preserve the condition, if any).
        let mut builtin_breakpoints: HashMap<PointOfInterest, BreakpointId> = HashMap::new();
        for (id, bp) in self.breakpoints.iter() {
            if let &BreakpointOn::PointOfInterest(p) = &bp.on {
                if bp.builtin {
                    builtin_breakpoints.insert(p, id);
                }
            }
        }

        loop {
            if !inp.read_bool()? {
                break;
            }
            let mut b = Breakpoint::load_state(inp)?;

            if let &BreakpointOn::PointOfInterest(p) = &b.on {
                if let Entry::Occupied(o) = builtin_breakpoints.entry(p) {
                    b.builtin = true;
                    self.breakpoints.remove(*o.get());
                    o.remove();
                }
            }

            if !b.builtin {
                // Disable regular breakpoints on startup to allow running the program without waiting for symbols to load.
                // For Panic and Exception, keep enabledness on restart.
                // Kind of inconsistent behavior, but seems convenient. Maybe UI should show regular vs special breakpoints separately to make this more clear.
                b.enabled = false;
            }

            self.breakpoints.add(b);
        }
        Ok(())
    }

    pub fn from_command_line(args: &[String], context: Arc<Context>, persistent: PersistentState, supp: SupplementaryBinaries) -> Self {
        Self::new(RunMode::Run, args.into(), context.clone(), SymbolsRegistry::new(context, supp), Pool::new(), persistent, ResourceStats::default(), Profiling::new())
    }

    pub fn attach(pid: pid_t, context: Arc<Context>, persistent: PersistentState, supp: SupplementaryBinaries) -> Result<Self> {
        let mut r = Self::new(RunMode::Attach, Vec::new(), context.clone(), SymbolsRegistry::new(context, supp), Pool::new(), persistent, ResourceStats::default(), Profiling::new());
        r.pid = pid;
        r.target_state = ProcessState::Running;
        r.memory = MemReader::Pid(PidMemReader::new(pid));

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
                match unsafe {ptrace(PTRACE_SEIZE, tid, 0, (PTRACE_O_TRACECLONE | PTRACE_O_TRACEEXEC | PTRACE_O_TRACEEXIT | PTRACE_O_TRACESYSGOOD) as u64)} {
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

    pub fn open_core_dump(core_dump_path: &str, context: Arc<Context>, persistent: PersistentState, supp: SupplementaryBinaries) -> Result<Self> {
        let file = fs::File::open(core_dump_path)?;
        let metadata = file.metadata()?;
        let elf = ElfFile::from_file(core_dump_path.to_string(), &file, metadata.len())?;
        let (memory, threads, maps) = parse_core_dump(Arc::new(elf))?;
        let mut r = Self::new(RunMode::CoreDump, Vec::new(), context.clone(), SymbolsRegistry::new(context, supp), Pool::new(), persistent, ResourceStats::default(), Profiling::new());
        r.pid = 0; // (we could use pid from core dump, but that would just be inviting bugs; if we ever want to show it in ui, we should put it somewhere other than this field and and special-case it in ui)
        r.target_state = ProcessState::CoreDump;
        r.info.maps = maps;
        r.memory = MemReader::CoreDump(Arc::new(memory));
        for (tid, info, signal) in threads {
            let mut t = Thread::new(r.next_thread_idx, tid, ThreadState::Suspended);
            r.next_thread_idx += 1;
            t.info = info;
            if let Some(s) = signal {
                t.stop_reasons.push(StopReason::Signal(s));
            }
            r.threads.insert(tid, t);
        }
        refresh_maps_and_binaries_info(&mut r);
        Ok(r)
    }

    pub fn start_child(&mut self, initial_step: Option<BreakpointOn>) -> Result<()> {
        if self.mode != RunMode::Run { return err!(Usage, "can't start new process in {} mode", self.mode.human_string()); }
        if self.target_state != ProcessState::NoProcess { return err!(Usage, "already debugging, can't start"); }
        eprintln!("info: starting child");

        {
            // Clear all fields but a few. I guess this suggests that these fields should be grouped into a struct (or a few). Would probably
            // make sense to split things up somewhat (in particular, probably separate breakpoints from threads), but not go overboard and nest everything 10 layers deep.
            let mode = self.mode;
            let command_line = mem::take(&mut self.command_line);
            let context = mem::replace(&mut self.context, Context::invalid());
            let symbols = mem::replace(&mut self.symbols, SymbolsRegistry::new(Context::invalid(), SupplementaryBinaries::default()));
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
                None => self.persistent.open_or_create_file("stdout")?,
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
                None => self.persistent.open_or_create_file("stderr")?,
                Some(path) => match fs::File::create(path) {
                    Ok(x) => x,
                    Err(e) => {
                        log!(self.log, "stderr failed: {}", e);
                        eprintln!("failed to create stderr file '{}': {}", path, e);
                        open_dev_null()?
                    }
                }
            };
            let disable_aslr = self.context.settings.disable_aslr;

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
                    if disable_aslr && libc::personality(libc::ADDR_NO_RANDOMIZE as u64) == -1 {
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

            ptrace(PTRACE_SEIZE, pid, 0, (PTRACE_O_EXITKILL | PTRACE_O_TRACECLONE | PTRACE_O_TRACEEXEC | PTRACE_O_TRACEEXIT | PTRACE_O_TRACESYSGOOD) as u64)?;
        }

        self.pid = pid;
        self.target_state = ProcessState::Starting;
        self.pending_step = initial_step.map(|on| (pid, on));
        self.waiting_for_initial_sigstop = true;
        self.memory = MemReader::Pid(PidMemReader::new(pid));
        let thread = Thread::new(self.next_thread_idx, pid, ThreadState::Running);
        self.threads.insert(pid, thread);
        self.next_thread_idx += 1;

        Ok(())
    }

    pub fn process_events(&mut self) -> Result<(/*have_more_events_to_process*/ bool, /*drop_caches*/ bool)> {
        if self.mode == RunMode::CoreDump {
            return Ok((false, false));
        }

        // true if we should refresh process info or consider calling handle_breakpoints or something like that.
        // false if it's a "spurious" stop, e.g. conditional breakpoint hit with condition not satisfied.
        let mut nontrivial_stop = false;
        
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
                    tid = profile_syscall!(libc::waitpid(-1, &mut wstatus, libc::WNOHANG));
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

                // Process an event returned by waitpid().
                // Warning: the code path between here and the call to handle_breakpoint_trap() should be kept simple and safe;
                // if we fail to handle a SIGTRAP, the debuggee thread may be left in a broken state after we detach; see shutdown().

                self.prof.bucket.debugger_count += 1;
                let thread = thread.unwrap();
                thread.sent_interrupt = false;

                if thread.state != ThreadState::Running && !(libc::WIFSTOPPED(wstatus) && libc::WSTOPSIG(wstatus) == libc::SIGTRAP && wstatus >> 16 == PTRACE_EVENT_EXIT) {
                    eprintln!("warning: got event {:x} for thread {} that is already stopped", wstatus, tid);
                }

                let mut trivial_stop = false;

                if libc::WIFEXITED(wstatus) || libc::WIFSIGNALED(wstatus) {
                    let stepping_this_thread = self.stepping.as_ref().is_some_and(|s| s.tid == tid);
                    if libc::WIFEXITED(wstatus) {
                        let exit_code = libc::WEXITSTATUS(wstatus);
                        eprintln!("info: thread {} exited with status {}", tid, exit_code);
                        if tid == self.pid && self.initial_exec_failed {
                            // Exited before initial execve(). Probably the user made a typo in the executable path.
                            // Maybe we should quit the whole debugger in this case, if this is the first attempt to start the process?
                            log!(self.log, "exec failed (incorrect executable path?)");
                        } else if tid == self.pid || exit_code != 0 || stepping_this_thread {
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
                        self.symbols.mark_all_as_unmapped();
                        self.memory = MemReader::Invalid;
                    } else if stepping_this_thread {
                        self.suspend()?;
                    }
                } else if libc::WIFSTOPPED(wstatus) {
                    let signal = libc::WSTOPSIG(wstatus);

                    let thread_prev_state = mem::replace(&mut thread.state, ThreadState::Suspended);
                    let mut thread_initial_stop = false;
                    thread.subframe_to_select = None;
                    thread.info.invalidate(self.mode);
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
                    } else if wstatus>>16 == PTRACE_EVENT_STOP { // group-stop, PTRACE_INTERRUPT, or newly created thread
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
                            PTRACE_EVENT_EXEC => {
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
                            PTRACE_EVENT_CLONE => {
                                let new_tid;
                                {
                                    let mut t: pid_t = 0;
                                    ptrace(PTRACE_GETEVENTMSG, tid, 0, &mut t as *mut pid_t as u64)?;
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
                            PTRACE_EVENT_EXIT => {
                                eprintln!("info: thread {} exiting", tid);
                                if thread.exiting {
                                    eprintln!("warning: got multiple PTRACE_EVENT_EXIT for tid {}", tid);
                                }
                                thread.exiting = true;
                                force_resume = true;
                                if self.threads.iter().all(|(_, t)| t.exiting) {
                                    eprintln!("info: process exiting");
                                    if self.target_state == ProcessState::Starting {
                                        // Exited before PTRACE_EVENT_EXEC.
                                        self.initial_exec_failed = true;
                                    }
                                    // Make sure we don't try to read things like /proc/<pid>/maps when the pid may not exist anymore.
                                    self.target_state = ProcessState::Exiting;
                                    self.stepping = None;
                                }
                            }
                            _ => return err!(Internal, "unexpected ptrace event: {}", wstatus >> 16),
                        }
                    } else if signal == libc::SIGTRAP { // hit a breakpoint
                        let mut si: libc::siginfo_t;
                        si = mem::zeroed();
                        ptrace(PTRACE_GETSIGINFO, tid, 0, &mut si as *mut _ as u64)?;

                        if self.context.settings.trace_logging { eprintln!("trace: thread {} got SIGTRAP ({}) at 0x{:x}", tid, trap_si_code_name(si.si_code), si.si_addr() as usize); }

                        let thread_single_stepping = mem::take(&mut thread.single_stepping);
                        let thread_ignore_next_hw_breakpoint_hit_at_addr = mem::take(&mut thread.ignore_next_hw_breakpoint_hit_at_addr);

                        let (hit, refresh_process_info, _regs, stack_digest_to_select) = self.handle_breakpoint_trap(tid, si.si_code, thread_single_stepping, thread_ignore_next_hw_breakpoint_hit_at_addr)?;

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
                            trivial_stop = !refresh_process_info;
                        }
                    } else { // other signals, with no special meaning for the debugger
                        if self.context.settings.trace_logging { eprintln!("trace: thread {} stopped by signal {} {}", tid, signal, signal_name(signal)); }
                        thread.pending_signal = Some(signal);

                        if [libc::SIGSEGV, libc::SIGABRT, libc::SIGILL, libc::SIGFPE].contains(&signal) {
                            let mut si: libc::siginfo_t;
                            si = mem::zeroed();
                            ptrace(PTRACE_GETSIGINFO, tid, 0, &mut si as *mut _ as u64)?;

                            thread.stop_reasons.push(StopReason::Signal(signal));
                            log!(self.log, "thread {} got {} at 0x{:x}", tid, signal_name(signal), si.si_addr() as usize);
                            self.target_state = ProcessState::Suspended;
                            self.cancel_stepping();
                            self.ptrace_interrupt_all_running_threads()?;
                        } else {
                            force_resume = true;
                            trivial_stop = true;
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

                if !trivial_stop {
                    nontrivial_stop = true;
                }
            }
        }

        // Don't load process information if any of:
        //  * There is no process.
        //  * The forked child process didn't do the initial exec() yet. In particular, don't kick off loading symbols because that would uselessly load symbols for the debugger itself.
        //  * All we did was skip conditional breakpoints. This path must be kept fast, otherwise conditional breakpoints will be slow.
        let mut drop_caches = false;
        if nontrivial_stop && self.target_state.process_ready() {
            // Re-read /proc/<pid>/maps to see what dynamic libraries are loaded. Re-resolve breakpoints if there are any new libraries.
            // For simplicity we do it on every user-visible stop. If this turns out to be slow, we can be more careful and only do it on _dl_debug_state hit and maybe on periodic timer.
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
            ProcessState::Suspended | ProcessState::CoreDump => ThreadState::Suspended,
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
        self.info.drop_caches();
        if self.target_state.process_ready() {
            refresh_maps_and_binaries_info(self);
            for t in self.threads.values_mut() {
                t.info.invalidate(self.mode);
                refresh_thread_info(self.pid, t, &mut self.prof.bucket, &self.context.settings);
            }
            self.try_pending_step_and_activate_breakpoints()?;
        } else if self.mode == RunMode::CoreDump {
            refresh_maps_and_binaries_info(self);
            for t in self.threads.values_mut() {
                t.info.invalidate(self.mode);
            }            
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
                    unsafe {ptrace(PTRACE_INTERRUPT, *tid, 0, 0)?};
                    t.sent_interrupt = true;
                }
                n += 1;
            }
        }
        Ok(n)
    }

    pub fn murder(&mut self, signal: i32) -> Result<()> {
        if self.mode == RunMode::Attach { return err!(Usage, "not killing attached process"); }
        if !self.target_state.process_ready() { return err!(Usage, "no process"); }
        eprintln!("info: kill");
        unsafe {
            let r = libc::kill(self.pid, signal);
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
            if !self.breakpoints.iter().any(|(_, b)| b.enabled && b.addrs.as_ref().is_err_and(|e| e.is_loading()) && b.on.should_wait_for_symbols()) {
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
                let mut breakpoint = Breakpoint {on: on.clone(), condition: None, hits: 0, addrs: err!(NotCalculated, ""), enabled: true, active: false, hidden: true, builtin: true};
                Self::determine_locations_for_breakpoint(&self.symbols, &mut breakpoint);
                match breakpoint.addrs {
                    Err(e) if e.is_loading() => (),
                    Err(e) => {
                        log!(self.log, "{}", e);
                        self.target_state = ProcessState::Suspended;
                        self.pending_step = None;
                    }
                    Ok(addrs) => {
                        assert!(!addrs.is_empty());
                        eprintln!("info: step to cursor thread {} cursor {:?}", tid, breakpoint.on);

                        let step = StepState {tid, keep_other_threads_suspended: false, disable_breakpoints: true, internal_kind: StepKind::Cursor, by_instructions: false, single_steps: false, ..StepState::default()};
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

    fn jump_target_may_be_outside_ranges(instruction: &iced_x86::Instruction, ranges: &[Range<usize>]) -> bool {
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
        let mut step = StepState {tid, keep_other_threads_suspended: true, disable_breakpoints: true, internal_kind: kind, by_instructions, ..StepState::default()};
        let mut breakpoint_types: Vec<StepBreakpointType> = Vec::new();
        let mut unwind: Option<(Arc<UnwindInfo>, AddrMap)> = None;
        let thread_is_after_user_debug_trap_instruction = thread.is_after_user_debug_trap_instruction;

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

            let mut addr = frame.addr;
            if thread_is_after_user_debug_trap_instruction {
                // Pretend to step over the int3 instruction.
                addr = frame.pseudo_addr;
            }
            
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
            // Source-code-based step Into or Over. Require line numbers and inlined functions information from debug symbols.

            assert!(!by_instructions);

            // (Disabling stop_only_on_statements if use_line_number_with_column because the .debug_line is_stmt flag is particularly unreliable when
            //  there are multiple statements on one line. Often there are even function calls in a range of instructions not marked as statement.
            //  Alternatively, we could make stop_only_on_statements detect call instructions and consider them "statements"
            //  even if is_stmt flag is not set.)
            if self.context.settings.steps_stop_only_on_statements && !use_line_number_with_column {
                step.stop_only_on_statements = true;
                step.binary_id = frame.binary_id.clone()?;
                step.start_line = match &subframe.line {
                    Some(l) => Some(l.line),
                    None => None,
                };
                step.use_line_number_with_column = use_line_number_with_column;
            }

            let function_idx = stack.subframes[frame.subframes.end - 1].function_idx.clone()?;
            let binary = match self.symbols.get(frame.binary_id.clone()?) {
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
                        if l.equals(start_line.line, use_line_number_with_column) {
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
                            if !l.equals(start_line.line, use_line_number_with_column) {
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

            step.cfa = frame.regs.get(RegisterIdx::Cfa)?.0 as usize;

            if step.internal_kind == StepKind::Out {
                // Check if caller frame's cfa is equal to this frame's cfa. Such nonsense happens in .plt for some reason, and it breaks step-out.
                if let Some(caller_frame) = stack.frames.get(subframe.frame_idx + 1) {
                    if let Some((caller_cfa, _)) = caller_frame.regs.get_option(RegisterIdx::Cfa) {
                        if caller_cfa as usize == step.cfa {
                            eprintln!("warning: two stack frames have equal cfa; step-out may be janky");
                            // Make step-out complete on next stop. Normally that's the stop at return address, as desired.
                            // But if there's a spurious stop before that, the step will finish early.
                            step.cfa -= 1;
                        }
                    }
                }
            }
        }

        if breakpoint_types.contains(&StepBreakpointType::AfterRet) {
            let return_addr = match frame.regs.get_option(RegisterIdx::Ret) {
                Some((x, _)) => Some(x),
                None => match stack.frames.get(subframe.frame_idx + 1) {
                    Some(caller_frame) => match caller_frame.regs.get_option(RegisterIdx::Rip) {
                        Some((x, _)) => Some(x),
                        None => None,
                    }
                    None => None,
                }
            };
            match return_addr {
                Some(addr) => breakpoints_to_add.push((StepBreakpointType::AfterRet, addr as usize)),
                None if step.internal_kind == StepKind::Out => return err!(ProcessState, "no return address"),
                None => (),
            }
        }

        let mut may_do_syscalls = false;
        for range in &step.addr_ranges {
            self.determine_some_step_breakpoint_locations(&breakpoint_types, range.clone(), &step.addr_ranges, /*skip_first_instruction*/ false, &mut breakpoints_to_add, &mut may_do_syscalls, &mut buf)?;
        }
        step.keep_other_threads_suspended &= !may_do_syscalls;

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
            if thread_is_after_user_debug_trap_instruction {
                // Weird special case: we're pretending to stand on an int3 instruction (e.g. __builtin_debugtrap in the program),
                // but actually we're on the next instruction.
                // So if we proceed it'll appear that we stepped through 2 instructions: int3 and the next one.
                // Instead, we'd like the thread to stop after resume_thread() increments RIP but before any instructions execute.
                // So we add a hardware breakpoint that will be hit immediately after PTRACE_SINGLESTEP, before RIP advances.
                if !step.addr_ranges.is_empty() {
                    breakpoints_to_add.push((StepBreakpointType::AfterRange, step.addr_ranges[0].end));
                }
            } else if step.keep_other_threads_suspended {
                // For single-instruction-step, stop after one PTRACE_SINGLESTEP, even if instruction pointer doesn't change.
                // Useful in case of recursive `call` immediately followed by `ret`.
                step.addr_ranges.clear();
            } else {
                // PTRACE_SINGLESTEP produces incorrect TRAP_BRKPT instead of TRAP_TRACE after stepping from syscall instruction.
                // Leave addr_ranges nonempty to not rely on trap type. This doesn't interfere with the case of recursive call followed by ret (above).
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
            self.add_step_breakpoint_locations(&breakpoints_to_add, tid, stack.frames[0].addr);
            self.arrange_handle_breakpoints()?;
        } else if self.stepping.as_ref().unwrap().single_steps {
            // Interaction between SINGLESTEP and breakpoints.
            //
            // We need to be careful to avoid single-stepping while standing on a software breakpoint.
            // Otherwise on SIGTRAP we won't be able to tell whether we single-stepped from the breakpoint
            // or from some different instruction that *jumped* to the address just after the breakpoint.
            // So when single-stepping from a software breakpoint, we make sure handle_breakpoints() is called first, which will convert it to a hardware breakpoint.
            //
            // There's a corresponding problem when adding a breakpoint while single-stepping. We solve it the same way: by making sure handle_breakpoints() happens
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

    // Decode instructions in given address ranges and find things like calls, jump, and syscalls. Based on that, make a list of addresses for internal breakpoints needed for a step.
    // Annoyingly, this sometimes needs to be re-done in the middle of a step (see comment at one of the call sites), so it's extracted into a function.
    // Only some StepBreakpointType-s are handled here, others only need to be handled when starting a step.
    fn determine_some_step_breakpoint_locations(&self, breakpoint_types: &[StepBreakpointType], addr_range: Range<usize>, all_addr_ranges: &[Range<usize>], mut skip_first_instruction: bool, breakpoints_to_add: &mut Vec<(StepBreakpointType, /*addr*/ usize)>, out_may_do_syscalls: &mut bool, buf: &mut Vec<u8>) -> Result<()> {
        if breakpoint_types.contains(&StepBreakpointType::AfterRange) {
            breakpoints_to_add.push((StepBreakpointType::AfterRange, addr_range.end));
        }
        let bp_on_call = breakpoint_types.contains(&StepBreakpointType::Call);
        let bp_on_jump_out = breakpoint_types.contains(&StepBreakpointType::JumpOut);
        if bp_on_call || bp_on_jump_out {
            let mut decoder = self.make_instruction_decoder(addr_range.clone(), buf)?;
            let mut instruction = iced_x86::Instruction::default();
            while decoder.can_decode() {
                decoder.decode_out(&mut instruction);
                if skip_first_instruction {
                    skip_first_instruction = false;
                    continue;
                }
                match instruction.flow_control() {
                    FlowControl::Call if instruction.code() == iced_x86::Code::Syscall => *out_may_do_syscalls = true,
                    FlowControl::Call | FlowControl::IndirectCall if bp_on_call => breakpoints_to_add.push((StepBreakpointType::Call, instruction.ip() as usize)),
                    FlowControl::Call | FlowControl::IndirectCall => *out_may_do_syscalls = true,
                    FlowControl::UnconditionalBranch | FlowControl::ConditionalBranch | FlowControl::IndirectBranch => {
                        if bp_on_jump_out && Self::jump_target_may_be_outside_ranges(&instruction, all_addr_ranges) {
                            breakpoints_to_add.push((StepBreakpointType::JumpOut, instruction.ip() as usize));
                        }
                    }
                    FlowControl::Return | FlowControl::Next | FlowControl::XbeginXabortXend | FlowControl::Exception | FlowControl::Interrupt => (),
                }
            }
        }
        Ok(())
    }

    fn add_step_breakpoint_locations(&mut self, breakpoints_to_add: &[(StepBreakpointType, /*addr*/ usize)], tid: pid_t, addr: usize) {
        for &(type_, breakpoint_addr) in breakpoints_to_add {
            self.add_breakpoint_location(BreakpointRef::Step(type_), breakpoint_addr);
        }

        // If we're already standing on one of the breakpoints we're adding, handle it the same way as if breakpoint was hit.
        // In addition to this, the breakpoint may or may not get actually hit immediately after we resume the thread.
        // There's no good way to guarantee that it will get hit (if the thread is currently stopped by hardware breakpoint),
        // so we have to do this handling manually here.
        for &(type_, breakpoint_addr) in breakpoints_to_add {
            if breakpoint_addr == addr {
                let mut request_single_step = false;
                Self::handle_step_breakpoint_hit(self.stepping.as_mut().unwrap(), type_, &mut request_single_step);
                if request_single_step {
                    self.threads.get_mut(&tid).unwrap().single_stepping = true;
                }
            }
        }
    }

    pub fn step_to_cursor(&mut self, tid: pid_t, cursor: BreakpointOn) -> Result<()> {
        assert!(!cursor.is_data());
        match self.target_state {
            ProcessState::Suspended | ProcessState::Running | ProcessState::Stepping => (),
            ProcessState::NoProcess => return self.start_child(Some(cursor)),
            ProcessState::Starting | ProcessState::Exiting | ProcessState::CoreDump => return err!(Usage, "not ready"),
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
        let op = if thread.single_stepping {PTRACE_SINGLESTEP} else {PTRACE_CONT};
        let sig = thread.pending_signal.take().unwrap_or(0);
        unsafe {ptrace(op, tid, 0, sig as u64)?};
        thread.state = ThreadState::Running;
        thread.stop_reasons.clear();
        thread.is_after_user_debug_trap_instruction = false;

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
        let mut pseudo_addr = regs.get(RegisterIdx::Rip)?.0 as usize;
        let mut memory = CachedMemReader::new(self.memory.clone());

        if thread.is_after_user_debug_trap_instruction {
            pseudo_addr -= 1;
        }

        loop {
            let idx = stack.frames.len();

            if idx > 1000 {
                return err!(ProcessState, "stack too deep");
            }

            let addr = regs.get(RegisterIdx::Rip).unwrap().0 as usize;
            stack.subframes.push(StackSubframe {frame_idx: stack.frames.len(), function_idx: err!(MissingSymbols, "unwind failed"), ..Default::default()});
            stack.frames.push(StackFrame {addr, pseudo_addr, regs: regs.clone(), subframes: stack.subframes.len()-1..stack.subframes.len(), .. Default::default()});
            let frame = &mut stack.frames.last_mut().unwrap();

            // Cases:
            //  * Address is mapped to a binary. Normal case. Unwind using the binary's UnwindInfo.
            //  * Address is mapped but not to a binary. Probably JIT-generated code. Unwind using frame pointer.
            //  * Address is not mapped, we're at the top of the stack. Probably the program called a bad function pointer and is about to crash with SIGSEGV. Take return address from the top of the stack.
            //  * Address is not mapped, we're in the middle of the stack. Probably we got a garbage address when unwinding from previous frame. Stop the unwind.
            let (addr_is_mapped, binary) = match self.info.maps.addr_to_map(pseudo_addr) {
                Some(&MemMapInfo {binary_id: Some(binary_id), ..}) => (true, Ok(self.symbols.get(binary_id).unwrap())),
                Some(map) if !map.perms.contains(MemMapPermissions::EXECUTE) => (false, err!(ProcessState, "address in non-executable memory")),
                Some(_) => (true, err!(ProcessState, "address not mapped to a binary")),
                None => (false, err!(ProcessState, "address not mapped")),
            };

            let step_result = match &binary {
                &Ok(binary) => {
                    frame.binary_id = Ok(binary.id);
                    frame.addr_static_to_dynamic = pseudo_addr.wrapping_sub(binary.addr_map.dynamic_to_static(pseudo_addr));
                    // This populates CFA "register", so needs to happen before symbolizing the frame (because frame_base expression might use CFA).
                    UnwindInfo::step(&mut memory, Some(binary), &mut scratch, pseudo_addr, frame)
                }
                Err(e) => {
                    frame.binary_id = Err(e.clone());
                    if addr_is_mapped {
                        UnwindInfo::step(&mut memory, /*binary*/ None, &mut scratch, pseudo_addr, frame)
                    } else if idx == 0 {
                        UnwindInfo::step_from_bad_function_call(&mut memory, frame)
                    } else {
                        return err!(Dwarf, "address not mapped")
                    }
                }
            };

            if let &Ok((_, /*is_signal_trampoline*/ true)) = &step_result {
                // Un-decrement the instruction pointer, there's no `call` in signal trampoline.
                frame.pseudo_addr = frame.regs.get(RegisterIdx::Rip).unwrap().0 as usize;
            }

            // (This has to be after updating pseudo_addr above.)
            if let Ok(ref binary) = binary {
                self.symbolize_stack_frame(binary, frame, &mut stack.subframes, &mut memory);
            }

            if partial {
                return Ok(());
            }

            let (next_regs, is_signal_trampoline) = step_result?;
            if !next_regs.has(RegisterIdx::Rip) {
                // This is how stacks usually end.
                return Ok(());
            }
            let next_addr = next_regs.get(RegisterIdx::Rip).unwrap().0 as usize;
            if next_addr == 0 {
                // I've seen this in MUSL's clone.s, which has bad unwind info.
                return err!(Dwarf, "zero return address");
            }
            if next_addr == addr && next_regs.has(RegisterIdx::Rsp) && regs.has(RegisterIdx::Rsp) && next_regs.get(RegisterIdx::Rsp).unwrap().0 == regs.get(RegisterIdx::Rsp).unwrap().0 {
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
        let mut context = DwarfEvalContext {memory, symbols: Some(symbols), addr_map: &binary.addr_map, encoding: unit.unit.header.encoding(), unit: Some(unit), regs: Some(&frame.regs), extra_regs: None, frame_base: None, local_variables: &[], fs_base: frame.regs.get_option(RegisterIdx::FsBase).map(|(x, _)| x), tls_offset: &binary.tls_offset};
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
    
    fn symbolize_stack_frame(&self, binary: &Binary, frame: &mut StackFrame, subframes: &mut Vec<StackSubframe>, memory: &mut CachedMemReader) {
        assert!(frame.subframes.len() == 1 && frame.subframes.start + 1 == subframes.len());
        let static_addr = binary.addr_map.dynamic_to_static(frame.pseudo_addr);
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

    pub fn make_eval_context<'a>(&'a self, stack: &'a StackTrace, selected_subframe: usize, tid: pid_t) -> EvalContext<'a> {
        let (extra_regs, fs_base) = match self.threads.get(&tid) {
            Some(t) => (Some(&t.info.extra_regs), if t.info.regs.has(RegisterIdx::FsBase) {Some(t.info.regs.get(RegisterIdx::FsBase).unwrap().0)} else {None}),
            None => (None, None),
        };
        EvalContext {memory: CachedMemReader::new(self.memory.clone()), process_info: &self.info, symbols_registry: &self.symbols, stack, selected_subframe, extra_regs, fs_base}
    }

    pub fn add_breakpoint(&mut self, on: BreakpointOn) -> Result<BreakpointId> {
        if let BreakpointOn::Data(d) = &on {
            if ![1, 2, 4, 8].contains(&d.size) {
                return err!(Internal, "unsupported size for data breakpoint size: {}", d.size);
            }
        }
        
        let breakpoint = Breakpoint {on, condition: None, hits: 0, addrs: err!(NotCalculated, ""), enabled: true, active: false, hidden: false, builtin: false};
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

    pub fn set_data_breakpoint_stop_on_read(&mut self, id: BreakpointId, stop_on_read: bool) -> Result<bool> {
        let b = match self.breakpoints.try_get_mut(id) {
            None => return Ok(false),
            Some(x) => x };
        let d = match &mut b.on {
            BreakpointOn::Data(x) => x,
            _ => panic!("unexpected non-data breakpoint") };
        if d.stop_on_read == stop_on_read {
            return Ok(false);
        }
        d.stop_on_read = stop_on_read;

        // Reactivate to update debug register in all threads.
        self.deactivate_breakpoint(id);
        if self.target_state.process_ready() {
            self.activate_breakpoints(vec![id])?;
        }
        Ok(true)
    }

    pub fn find_line_breakpoint_fuzzy(&self, lb: &LineBreakpoint) -> Option<BreakpointId> {
        for (id, breakpoint) in self.breakpoints.iter() {
            match &breakpoint.on {
                BreakpointOn::Line(bp) if bp.path == lb.path && (bp.line == lb.line || bp.adjusted_line == Some(lb.line)) => return Some(id.clone()),
                _ => (),
            }
        }
        None
    }

    fn activate_breakpoints(&mut self, ids: Vec<BreakpointId>) -> Result<()> {
        assert!(self.target_state.process_ready());
        let mut should_handle_breakpoints = false;
        let mut wait_for_symbols = false;
        for id in ids {
            let b = self.breakpoints.get_mut(id);
            if !b.enabled || b.active {
                continue;
            }
            if let BreakpointOn::Data(d) = &b.on {
                // Allocate a hardware breakpoint slot right here.
                let mut found = false;
                for h in &mut self.hardware_breakpoints {
                    if !h.active {
                        *h = HardwareBreakpoint {active: true, addr: d.addr, data_breakpoint_id: Some(id), stop_on_read: d.stop_on_read, data_size: d.size, ..Default::default()};
                        found = true;
                        break;
                    }
                }
                if found {
                    b.active = true;
                    b.addrs = err!(NotCalculated, "");
                    should_handle_breakpoints = true; // to set debug registers in all threads
                } else {
                    b.enabled = false; // auto-disable, seems convenient
                    b.addrs = err!(OutOfHardwareBreakpoints, "out of hardware breakpoints (max: 4)");
                    log!(self.log, "out of hw breakpoints (max: 4)");
                }
            } else {
                if let Err(e) = &b.addrs {
                    Self::determine_locations_for_breakpoint(&self.symbols, b);
                }
                match &b.addrs {
                    Ok(addrs) => {
                        assert!(!addrs.is_empty());
                        should_handle_breakpoints = true;
                        b.active = true;
                        for (addr, subfunction_level) in addrs.clone() {
                            self.add_breakpoint_location(BreakpointRef::Id {id, subfunction_level}, addr);
                        }
                    }
                    Err(e) if e.is_loading() && b.on.should_wait_for_symbols() => wait_for_symbols = true,
                    Err(_) => (),
                }
            }
        }
        if should_handle_breakpoints {
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
        for h in &mut self.hardware_breakpoints {
            if h.active && h.data_breakpoint_id == Some(id) {
                *h = HardwareBreakpoint::default();
            }
        }
    }

    fn determine_locations_for_breakpoint(symbols_registry: &SymbolsRegistry, breakpoint: &mut Breakpoint) {
        assert!(breakpoint.addrs.is_err());
        match &mut breakpoint.on {
            BreakpointOn::Line(bp) => {
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
                    if addrs[0].line() > res.0 {
                        continue;
                    }
                    if addrs[0].line() < res.0 {
                        res = (addrs[0].line(), Vec::new());
                    }

                    // There are often multiple nearby addresses for the same line, usually with different column numbers.
                    // E.g. if the line contains a function call where some arguments are function calls too, there would usually be an address for each of the arguments and a location for the outer function call.
                    // We want to set breakpoint on only the first of those addresses. Otherwise continuing from such breakpoint is very confusing: you continue and immediately stop without leaving the line.
                    // On the other hand, a line can have multiple addresses corresponding to different inlining sites of the containing function; we don't want to deduplicate those.
                    // So we group addresses by the containing (sub)function and keep the lowest address in each.
                    let mut subfuncs_and_addrs: Vec<(/*function_idx*/ usize, /*subfunction_idx*/ usize, /*addr*/ usize, u16)> = addrs.iter().map(|line| {
                        let addr = line.addr();
                        if let Ok((function, function_idx)) = symbols.addr_to_function(addr) {
                            if let Some((sf, l)) = symbols.containing_subfunction_at_level(addr, line.subfunction_level(), function) {
                                return (function_idx, sf, addr, l);
                            }
                        }
                        (usize::MAX, addr, addr, line.subfunction_level())
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
            BreakpointOn::Instruction(bp) => {
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
                            addrs.push((addr, SUBFUNCTION_LEVEL_MAX));
                        }
                    }
                }
                breakpoint.addrs = if !addrs.is_empty() {
                    Ok(addrs)
                } else if loading {
                    err!(Loading, "symbols are not loaded yet")
                } else {
                    err!(NoFunction, "no locations found for {}", point.name_for_ui())
                };
            }
            b => breakpoint.addrs = err!(Internal, "unexpected breakpoint kind: {:?}", b),
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
            // Read a byte of machine code at the breakpoint address to make it easier to check whether it's int3 (e.g. a __builtin_debugtrap() in user's code).
            let original_byte = match self.memory.read_u8(addr) {
                Ok(x) => x,
                Err(e) => {
                    eprintln!("warning: failed to read original byte for breakpoint at 0x{:x}: {}", addr, e);
                    0
                }
            };

            self.breakpoint_locations.insert(idx, BreakpointLocation {addr, original_byte, hardware: false, active: false, breakpoints: vec![breakpoint], error: None, no_retry: false});
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

            self.hardware_breakpoints[hw_idx] = HardwareBreakpoint {active: true, thread_specific, addr, ..Default::default()};
        } else {
            let byte_idx = addr % 8;
            let bit_idx = byte_idx * 8;
            let word = self.memory.read_u64(addr - byte_idx)?;

            let original_byte = ((word >> bit_idx) & 0xff) as u8;
            let orig = &mut self.breakpoint_locations[idx].original_byte;
            if *orig != original_byte {
                eprintln!("warning: original byte for breakpoint at 0x{:x} changed from 0x{:x} to 0x{:x}", addr, orig, original_byte);
                *orig = original_byte;
            }

            let word = word & !(0xff << bit_idx) | (0xcc << bit_idx);
            // PTRACE_POKETEXT is dumb. It requires the provided thread to be suspended, but doesn't care if other threads are running.
            // Presumably this requirement was added just in case, back when threads didn't exist.
            // So we need to semi-artificially propagate a TID of any suspended thread into here, and we can't add/remove breakpoints
            // while all threads are running. I wish process_vm_writev() had a flag to allow writing to read-only memory (.text is usually mapped as read-only).
            unsafe { ptrace(PTRACE_POKETEXT, any_suspended_tid, (addr - byte_idx) as u64, word)?; }
        }
        self.breakpoint_locations[idx].active = true;
        Ok(())
    }

    fn deactivate_breakpoint_location(&mut self, idx: usize, any_suspended_tid: pid_t) -> Result<()> {
        let location = &mut self.breakpoint_locations[idx];
        if !location.active { return Ok(()); }
        if location.hardware {
            for h in &mut self.hardware_breakpoints {
                if h.active && h.addr == location.addr {
                    *h = HardwareBreakpoint::default();
                }
            }
            // Don't actively update threads' debug registers. We'll update them if the stale breakpoint gets hit.
        } else {
            let byte_idx = location.addr % 8;
            let bit_idx = byte_idx * 8;
            // Other threads may be running, but it's fine.
            let word = self.memory.read_u64(location.addr - byte_idx)?;
            let word = word & !(0xff << bit_idx) | ((location.original_byte as u64) << bit_idx);
            unsafe { ptrace(PTRACE_POKETEXT, any_suspended_tid, (location.addr - byte_idx) as u64, word)?; }
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

        let mut thread_addresses: HashMap<usize, Vec<pid_t>> = HashMap::new();
        for (tid, t) in self.threads.iter() {
            if t.info.regs.has(RegisterIdx::Rip) {
                let addr = t.info.regs.get(RegisterIdx::Rip).unwrap().0 as usize;
                let tids = thread_addresses.entry(addr).or_default();
                if !t.is_after_user_debug_trap_instruction {
                    tids.push(*tid);
                } else {
                    // Don't set ignore_next_hw_breakpoint_hit_at_addr in this case.
                    // When single-instruction-stepping from is_after_user_debug_trap_instruction state,
                    // we want the new hw breakpoint to be immediately hit without making progress.
                }
            }
        }

        for idx in 0..self.breakpoint_locations.len() {
            let loc = &self.breakpoint_locations[idx];
            let addr = loc.addr;
            let tids = thread_addresses.get(&loc.addr);
            if loc.hardware {
                if tids.is_none() {
                    self.deactivate_breakpoint_location(idx, self.pid)?;
                    self.breakpoint_locations[idx].hardware = false;
                }
            } else {
                if let Some(tids) = tids {
                    self.deactivate_breakpoint_location(idx, self.pid)?;
                    self.breakpoint_locations[idx].hardware = true;

                    for tid in tids {
                        // The thread is stopped at a sw breakpoint address. After we convert it to hw breakpoint,
                        // the thread may immediately hit it. Ignore such hit. Possible situations:
                        //  * We've already handled this sw breakpoint hit. Don't want to handle it again.
                        //  * This breakpoint was added when this thread was already stopped. I.e. the user added a breakpoint on the current line ("current" for some thread).
                        //    We shouldn't report a breakpoint hit before the thread even starts moving.
                        //  * Race condition: the thread happened to stop at the breakpoint address, but not because of the breakpoint.
                        //    We currently don't handle this correctly. It's probably possible for a breakpoint hit to be missed.
                        //    E.g. scenario: one thread hit a conditional breakpoint; the condition evaluated to false; we did PTRACE_INTERRUPT of all other threads (to call handle_breakpoints());
                        //    one of those threads happened to be interrupted at the same breakpoint address (just *before* executing the int3 instruction, so no SIGTRAP);
                        //    that thread then incorrectly ignores the breakpoint hit.
                        //    Maybe we should check for breakpoint hits when thread stops for any reason. Or maybe we should assign ignore_next_hw_breakpoint_hit_at_addr only on SIGTRAP and when adding breakpoint. TODO: Probably the latter.
                        self.threads.get_mut(tid).unwrap().ignore_next_hw_breakpoint_hit_at_addr = Some(addr);
                    }
                }
            }
        }

        for idx in 0..self.breakpoint_locations.len() {
            if self.breakpoint_locations[idx].no_retry {
                continue;
            }
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

        if self.hardware_breakpoints.iter().any(|b| b.active && !b.pushed_to_threads) {
            let tids: Vec<pid_t> = self.threads.keys().copied().collect();
            for tid in tids {
                self.set_debug_registers_for_thread(tid)?;
            }
            for b in &mut self.hardware_breakpoints {
                b.pushed_to_threads = true;
            }
        }

        Ok(())
    }

    fn get_debug_register_values_for_hardware_breakpoint(b: &HardwareBreakpoint, i: usize, tid: pid_t) -> Option<(/*addr*/ u64, /*dr7*/ u64)> {
        if !b.active || b.thread_specific.is_some_and(|x| x != tid) {
            return None;
        }
        let mut dr7 = 1 << (i*2);
        if b.data_breakpoint_id.is_some() {
            dr7 |= (if b.stop_on_read {3} else {1}) << (16 + i*4);
            let size_code: u64 = match b.data_size {
                1 => 0,
                2 => 1,
                4 => 3,
                8 => 2,
                _ => panic!("unexpected data breakpoint size"),
            };
            dr7 |= size_code << (18 + i*4);
        }
        Some((b.addr as u64, dr7))
    }

    fn set_debug_registers_for_thread(&mut self, tid: pid_t) -> Result<()> {
        // TODO: Remember last assigned values if dr0-3 and dr7 to avoid doing these syscalls again if nothing changed.
        //       Then also clear dr6 when changing hw breakpoints, to not report incorrect hits based on stale bp indices.

        let dr7_common_bits = 1u64 << 10;
        let mut dr7 = dr7_common_bits;

        // Disable all breakpoints (clear dr7) before modifying their addresses.
        // Because ptrace_set_debugreg is weird about validating inputs, in a way I don't fully understand. E.g. scenario:
        //  1. Set dr0 to unmapped address, then dr1 to valid executable address, then dr7 to enable data breakpoint 0 and exec breakpoint 1. Success
        //  2. Possibly repeat step 1, it keeps succeeding.
        //  3. [The data breakpoint was removed, we shifted the exec breakpoint from hw bp 1 to 0, and are going to set dr0 = valid executable address, then dr7 to enable only bp 0. So we...]
        //     Set dr0 to a valid executable address (same as dr1 in step 1) - and ptrace returns EINVAL. What?
        //     (Is it because the previous dr0 address was unmapped or because the new dr0 == dr1? I didn't check. Either way the solution to clear dr7.)
        unsafe {ptrace(PTRACE_POKEUSER, tid, (mem::offset_of!(libc::user, u_debugreg) + 7*8) as u64, dr7)? };
        let mut assigned_dr7 = dr7; // last successfully written dr7 value

        for i in 0..4 {
            if let Some((addr, d7)) = Self::get_debug_register_values_for_hardware_breakpoint(&self.hardware_breakpoints[i], i, tid) {
                unsafe { ptrace(PTRACE_POKEUSER, tid, (mem::offset_of!(libc::user, u_debugreg) + i * 8) as u64, addr)? };
                dr7 |= d7;
            }
        }

        // Now we just need to do PTRACE_POKEUSER to write `dr7`.
        // But we had to wrap it in a retry loop to work around the following inconvent ptrace behavior.
        //
        // Writes to dr7 may fail with EINVAL if one of the breakpoints has invalid address.
        // The error doesn't say which of the breakpoints is the culprit, so we try to activate breakpoints one by one and disable the ones that fail.
        // Other threads may be running during this, so more addresses may get mapped or unmapped during this, so we do a few retries juuust in case.
        // (Although I've seen this only with addresses below 4096 or above (1<<56); unmapped addresses seem fine.)
        // (Alternatively, we could validate addresses ourselves, but I don't want to rely on exactly matching ptrace's validation logic.)
        let mut attempts = 0;
        loop {
            attempts += 1;

            if dr7 == assigned_dr7 {
                // The desired dr7 value was already written.
                // This happend is there are no active hw breakpoints, or if we activated the only active breakpoint on previous iteration of the loop.
                return Ok(());
            }

            // Try to activate all enabled breakpoints.
            let mut error: Option<Error>;
            match unsafe { ptrace(PTRACE_POKEUSER, tid, (mem::offset_of!(libc::user, u_debugreg) + 7*8) as u64, dr7) } {
                Ok(_) => return Ok(()),
                Err(e) if e.is_io_invalid_input() && attempts < 6 => error = Some(e),
                Err(e) => return Err(e),
            }
            // Failed with EINVAL.

            // Try to activate breakpoints one at a time.
            let mut new_dr7 = dr7_common_bits;
            for i in 0..4 {
                if let Some((_, d7)) = Self::get_debug_register_values_for_hardware_breakpoint(&self.hardware_breakpoints[i], i, tid) {
                    let single_dr7 = d7 | dr7_common_bits;
                    if single_dr7 == dr7 {
                        // There's only one enabled breakpoint, we already tried to activate it above and got EINVAL, no need to try again.
                    } else {
                        match unsafe { ptrace(PTRACE_POKEUSER, tid, (mem::offset_of!(libc::user, u_debugreg) + 7*8) as u64, single_dr7) } {
                            Ok(_) => {
                                assigned_dr7 = single_dr7;
                                new_dr7 |= d7;
                                continue;
                            }
                            Err(e) if e.is_io_invalid_input() => error = Some(e),
                            Err(e) => return Err(e),
                        }
                    }
                    assert!(error.is_some());

                    // Got EINVAL when activating this breakpoint alone. Disable the breakpoint and store error such that it's visible in the UI.
                    if let &Some(id) = &self.hardware_breakpoints[i].data_breakpoint_id {
                        self.deactivate_breakpoint(id);
                        self.breakpoints.get_mut(id).addrs = Err(mem::take(&mut error).unwrap());
                    } else {
                        let addr = self.hardware_breakpoints[i].addr;
                        let location_idx = self.find_breakpoint_location(addr).unwrap();
                        assert!(self.breakpoint_locations[location_idx].hardware);
                        self.deactivate_breakpoint_location(location_idx, tid).unwrap();
                        let location = &mut self.breakpoint_locations[location_idx];
                        location.error = mem::take(&mut error);
                        location.no_retry = true;
                    }
                    assert!(!self.hardware_breakpoints[i].active);
                }
            }
            // All remaining active breakpoints.
            dr7=new_dr7;
        }
    }

    fn handle_step_breakpoint_hit(step: &StepState, type_: StepBreakpointType, request_single_step: &mut bool) {
        match type_ {
            StepBreakpointType::Call | StepBreakpointType::JumpOut => *request_single_step = true,
            StepBreakpointType::AfterRange | StepBreakpointType::AfterRet | StepBreakpointType::Catch | StepBreakpointType::Cursor(_) => (),
        }
    }

    // Returns whether the step completed.
    fn handle_step_stop(&mut self, hit_step_breakpoint: bool, single_stepped: bool, regs: &Registers) -> bool {
        let step = self.stepping.as_ref().unwrap();
        if step.internal_kind == StepKind::Cursor {
            return hit_step_breakpoint;
        }
        let addr = regs.get(RegisterIdx::Rip).unwrap().0 as usize;
        let i = step.addr_ranges.partition_point(|r| r.end <= addr);
        let in_ranges = i < step.addr_ranges.len() && step.addr_ranges[i].start <= addr;
        if step.internal_kind == StepKind::Into && step.by_instructions {
            if step.addr_ranges.is_empty() && !single_stepped {
                return false;
            }
            return !in_ranges;
        }
        let step = self.stepping.as_mut().unwrap();
        let cfa = Self::get_cfa_for_step(&self.info, &self.symbols, &mut self.log, &self.memory, addr, regs);
        let cfa = match cfa {
            None => return step.internal_kind == StepKind::Into,
            Some(c) => c };
        let (cfa_done, ranges_done) = match step.internal_kind {
            StepKind::Into => (cfa != step.cfa, !in_ranges),
            StepKind::Over => (cfa > step.cfa, cfa == step.cfa && !in_ranges),
            StepKind::Out => (cfa > step.cfa, false),
            StepKind::Cursor => panic!("huh"),
        };
        if cfa_done {
            // Stepped in or out.
            return true;
        }
        if !ranges_done {
            // Still on the initial line or inlined function.
            return false;
        }
        if !step.stop_only_on_statements {
            // Left the initial line or inlined function.
            return true;
        }

        // The step is kind of done, except for the "stop only on statements" part. Unfortunately, it's a big part.

        // Check if we're on a statement. If anything goes wrong, just finish the step here, as if stop_only_on_statements is false.
        let Some(binary) = self.symbols.get(step.binary_id) else {return true};
        let Ok(symbols) = binary.symbols.as_ref() else {return true};
        let static_addr = binary.addr_map.dynamic_to_static(addr);
        let mut line_iter = symbols.addr_to_line_iter(static_addr);
        let line = match line_iter.next() {
            None => return true, // hole in line number info, unusual
            Some(line) if line.addr() > static_addr || line.file_idx().is_none() => return true, // ditto
            Some(x) => x,
        };
        let mut stop = line.flags().contains(LineFlags::STATEMENT) && line.addr() == static_addr;
        // Check if we're somehow still on the same line on which the step started.
        // That would be unusual, normally the start_line is covered by step.addr_ranges, which we already checked.
        // But it's currently possible because step() doesn't search for all ranges for start_line, only the range that contains current address.
        // So we do this additional check here along the way, because it's easy.
        // (Maybe we should make step() search for all ranges instead. I avoided it for performance, to avoid scanning addr_to_line for the whole function, but it would probably be fine.)
        if let Some(start_line) = step.start_line.clone() {
            stop &= !line.equals(start_line, step.use_line_number_with_column);
        }
        if stop {
            return true;
        }

        // We're on an address on which we shouldn't stop. So from now on, this step should handle this address as if it were in step.addr_ranges.
        // We do it by actually adding it to step.addr_ranges, as well as adding the corresponding internal breakpoints, same way as when starting a step.
        // (Can we get away with something simpler, like doing single-steps until we reach a statement? AFAICT, no. I've seen this code hit non-statement `call` instructions,
        //  which means we'd need to single-step through the whole function call subtree, which may be very slow, and also may get stuck on a syscall if step.keep_other_threads_suspended is true.)
        // (Alternatively, when starting a step, we could populate addr_ranges with all non-statement instruction ranges in the whole function, as well as add corresponding internal breakpoints
        //  for all jumps/calls/syscalls in the function as needed. But this sounds slow, especially adding lots of internal breakpoints.)
        // (I wish compilers would just always emit accurate line number information for all instructions. Then we wouldn't need stop_only_on_statements.)

        // Instead of adding just `addr` to step.addr_ranges, extend it to a range based on neighboring LineInfo-s.
        let mut new_range: Option<Range<usize>> = None;
        while let Some(next_line) = line_iter.next() {
            if next_line.file_idx().is_none() || (next_line.flags().contains(LineFlags::STATEMENT) && !step.start_line.is_some_and(|start_line| next_line.equals(start_line, step.use_line_number_with_column))) {
                new_range = Some(binary.addr_map.static_to_dynamic(line.addr())..binary.addr_map.static_to_dynamic(next_line.addr()));
                break;
            }
        }
        mem::drop(line_iter);
        let Some(new_range) = new_range else {return true};
        let skip_first_instruction = line.flags().contains(LineFlags::STATEMENT);

        let mut addr_ranges = mem::take(&mut step.addr_ranges);
        // new_range must start at instruction boundary for determine_some_step_breakpoint_locations() to work,
        // but step.addr_ranges is ok with range start shifted by one byte to skip first instruction (which may be longer than one byte).
        addr_ranges.push(new_range.start + (skip_first_instruction as usize)..new_range.end);

        let mut breakpoint_types = vec![StepBreakpointType::AfterRange, StepBreakpointType::JumpOut];
        if step.internal_kind == StepKind::Into {
            breakpoint_types.push(StepBreakpointType::Call);
        }
        let mut breakpoints_to_add: Vec<(StepBreakpointType, usize)> = Vec::new();
        let mut may_do_syscalls = false;
        // (It may be possible for the new range to intersect some existing ranges. This shouldn't break anything.)
        match self.determine_some_step_breakpoint_locations(&breakpoint_types, new_range.clone(), &addr_ranges, skip_first_instruction, &mut breakpoints_to_add, &mut may_do_syscalls, &mut Vec::new()) {
            Err(_) => return true,
            Ok(()) => (),
        }
        let step = self.stepping.as_mut().unwrap();
        let mut need_to_resume_threads = may_do_syscalls && step.keep_other_threads_suspended;
        step.keep_other_threads_suspended &= !may_do_syscalls;
        step.addr_ranges = addr_ranges;
        let step_tid = step.tid;
        if !breakpoints_to_add.is_empty() {
            self.add_step_breakpoint_locations(&breakpoints_to_add, step_tid, addr);
            self.stopping_to_handle_breakpoints = true;
            need_to_resume_threads = false;
        }

        if need_to_resume_threads {
            // When starting the step, it seemed that it can'd hit syscalls, so we can keep other threads stopped as an optimization.
            // But now it turned out that the step may hit syscall (when running through non-statement instructions), so we have
            // to start other threads to avoid getting stuck if the syscall e.g. waits for a lock held by another thread.
            let tids_to_resume: Vec<pid_t> = self.threads.keys().filter(|tid| **tid != step_tid && self.target_state_for_thread(**tid) == ThreadState::Running).copied().collect();
            for t in tids_to_resume {
                match self.resume_thread(t, /*refresh_info*/ true) {
                    Err(_) => return true,
                    Ok(()) => (),
                }
            }
        }

        false
    }

    fn determine_subframe_to_select(stack: &StackTrace, stack_digest: &Vec<usize>, is_step_into: bool, subfunction_level: u16) -> Option<usize> {
        if stack.frames.is_empty() {
            return None;
        }
        if subfunction_level < SUBFUNCTION_LEVEL_MAX {
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
        match unwind.find_row_and_eval_cfa(&mut memory, binary, &mut scratch, addr, regs) {
            Err(e) => {
                log!(log, "no frame for addr 0x{:x}: {}", addr, e);
                eprintln!("warning: no frame for addr 0x{:x} (when determining cfa for step): {}", addr, e);
                return None;
            }
            Ok(None) => {
                if let Some((x, _)) = regs.get_option(RegisterIdx::Rbp) {
                    Some(x as usize)
                } else {
                    log!(log, "no frame for addr 0x{:x}: no unwind info and no rbp", addr);
                    eprintln!("warning: no frame for addr 0x{:x} (when determining cfa for step): no unwind info and no rbp", addr);
                    return None;
                }
            }
            Ok(Some((_, _, cfa, _, _, _))) => Some(cfa),
        }
    }

    fn process_breakpoint_hit(&mut self, id: BreakpointId, tid: pid_t, ignore_breakpoints: bool, subfunction_level: u16, stop_reasons: &mut Vec<StopReason>) -> bool {
        let bp = self.breakpoints.get_mut(id);
        bp.hits += 1;

        if ignore_breakpoints {
            return false;
        }
        if let Some((_, Ok(_), _)) = &bp.condition {
            let r = self.eval_breakpoint_condition(tid, id, subfunction_level);
            let bp = self.breakpoints.get_mut(id);
            let cond = &mut bp.condition.as_mut().unwrap();
            match r {
                Ok(hit) => {
                    cond.2 = None;
                    if !hit {
                        return false;
                    }
                }
                Err(e) => cond.2 = Some(e), // put error into the breakpoint to be shown in UI, and stop
            }
        }

        stop_reasons.push(StopReason::Breakpoint(id));
        true
    }
    
    // Returns true if any breakpoint was actually hit, so we should switch to ProcessState::Suspended.
    // May also set stopping_to_handle_breakpoints to true, in which case the caller should stop all threads.
    // Otherwise treat it as a spurious wakeup and continue (e.g. breakpoint is for a different thread, or conditional breakpoint's condition evaluated to false, or something).
    fn handle_breakpoint_trap(&mut self, tid: pid_t, si_code: i32, single_stepping: bool, ignore_next_hw_breakpoint_hit_at_addr: Option<usize>) -> Result<(/*hit*/ bool, /*refresh_process_info*/ bool, Registers, Option<(Vec<usize>, bool, u16)>)> {
        let mut regs = ptrace_getregs(tid)?;
        let mut addr = regs.get(RegisterIdx::Rip).unwrap().0 as usize;

        // Some weird nonsense is needed to interpret SIGTRAPs correctly.
        // Suppose there's a software breakpoint (int3 instruction, 0xcc) at addrss X. When we see a SIGTRAP and RIP = X+1, it can mean two things:
        //  (a) The 0xcc instruction was hit. We're stopped at breakpoint X. When resuming the thread, we must remove the breakpoint *and decrement RIP*.
        //  (b) The thread jumped to X+1, then got a SIGTRAP unrelated to our breakpoint. When resuming the thread we must *leave RIP unchanged*.
        //
        // It sure would make sense if the kernel just told us what caused SIGTRAP. It has that information. There's even already an API for reporting it:
        // siginfo.si_code == TRAP_BRKPT for int3 hit, TRAP_TRACE for PTRACE_SINGLESTEP.
        // But ptrace intentionally (?) often doesn't use these values and instead reports si_code == SI_KERNEL. I'm not sure what the idea is.
        // To add insult to injury, sometimes TRAP_BRKPT is reported after PTRACE_SINGLESTEP, with no int3 in sight. So we should mostly ignore TRAP_BRKPT and TRAP_TRACE even when they're present.
        //
        // So we have to do some guesswork to distinguish (a) and (b). We do it by elimination. A thread may receive SIGTRAP (with no PTRACE_EVENT_*) if:
        //  (1) It did a PTRACE_SINGLESTEP. We check for this by keeping track of our own calls to ptrace(PTRACE_SINGLESTEP).
        //      But see "Interaction between SINGLESTEP and breakpoints" about extra difficulties with this.
        //  (2) It hit a hardware breakpoint. We check for this by inspecting the debug register.
        //  (3) Someone sent a SIGTRAP manually using kill/tgkill/etc or using a timer. Then si_code != SI_KERNEL.
        //  (4) It hit a software breakpoint. We assume this if none of the above are the case.
        //  (5) Some other kernel-generated SIGTRAP. We would incorrectly treat it as int3 hit, and it would break things.
        //
        // We could also check whether the byte at RIP-1 is actually 0xcc or contains a breakpoint, but we'd need to be extra careful to avoid race condition with activating/deactivating breakpoint locations.
        // E.g. suppose two threads hit the same breakpoint at the same time, and when handling the first SIGTRAP we deactivate the breakpoint (e.g. because it's obsolete) and revert the 0xcc byte to its original value;
        // then the second thread's SIGTRAP won't see 0xcc at RIP-1, incorrectly won't decrement RIP, and debuggee will break.
        // So currently we don't check for 0xcc here. If it turns out that we have to do it, we'll have to ensure that the original_byte <-> 0xcc memory writes only happen when all threads are stopped (likely in handle_breakpoints()).
        // Possibly even that would be insufficient because maybe a SIGTRAP may be queued behind another type of stop, then get delivered after we resume threads; or maybe that's impossible, I haven't checked.

        let dr6 = unsafe { ptrace(PTRACE_PEEKUSER, tid, mem::offset_of!(libc::user, u_debugreg) as u64 + 6*8, 0)? };
        let stopped_on_hw_breakpoint = dr6 & 15 != 0; // may be a data breakpoint
        if stopped_on_hw_breakpoint {
            // In case it's a stale breakpoint.
            self.set_debug_registers_for_thread(tid)?;
            // Clear the 'breakpoint was hit' bits because neither the CPU nor Linux will do it for us.
            unsafe { ptrace(PTRACE_POKEUSER, tid, (mem::offset_of!(libc::user, u_debugreg) + 6 * 8) as u64, (dr6 & !15) as u64)? };
        }

        // Need to be careful to correctly handle being stopped for multiple reasons at once:
        //  * Data breakpoint and instruction breakpoint (e.g. breakpoint on a `mov` that writes to memory address with data breakpoint).
        //    In this case, the code below will just run both the instruction-related and data-related code paths,
        //    combining the results the same way as multiple instruction breakpoints at the same address.
        //  * Software breakpoint and hardware breakpoint. We assume this can't happen, see below.

        // (This doesn't apply to data breakpoint hit, if any.)
        let spurious_stop = stopped_on_hw_breakpoint && ignore_next_hw_breakpoint_hit_at_addr == Some(addr);

        // True if the stop was caused by a software breakpoint.
        // Why can't stopped_on_hw_breakpoint and single_stepping be true for a stop caused by a software breakpoint? E.g. if there's a hw breakpoint on the same spot.
        //  * single_stepping can't be true because we never single-step from an address with sw breakpoint (we convert it to hw first).
        //  * Can't be stopped on hw data breakpoint because int3 doesn't write to memory.
        //    (... Or maybe kernel's interrupt handler can write to userspace memory and trip our data breakpoint?
        //     Welp, then we'll use incorrect value of stopped_on_sw_breakpoint, which means the debuggee will likely execute illegal instruction and die.
        //     I don't know how to distinguish that case.)
        //  * If stopped on hw bp with the same address as sw bp (maybe possible for stale hw bp), that shouldn't be considered sw bp hit as we shouldn't decrement rip.
        //  * If there's a hw bp just after int3, presumably such hw bp hit is not reported on int3 trap, but I haven't checked.
        // So, this assumption may not be fully sound, but I don't know how to do better. (I feel this should be the job of si_code, and it has failed at this job.)
        let stopped_on_sw_breakpoint = (si_code == libc::TRAP_BRKPT || si_code == libc::SI_KERNEL) && !stopped_on_hw_breakpoint && !single_stepping;
        if stopped_on_sw_breakpoint {
            addr -= 1;
        }

        // More ptrace jank: after PTRACE_SINGLESTEP we may get a TRAP_BRKPT (!) before the single-step step happens (i.e. still at original address).
        // We ignore it and do another PTRACE_SINGLESTEP, which then actually steps and generates a TRAP_TRACE.
        let single_stepped = (si_code == libc::TRAP_TRACE || si_code == libc::SI_KERNEL) && single_stepping && !spurious_stop;

        let mut hit = false;
        let mut refresh_process_info = false;
        let mut request_single_step = false;
        let mut is_active_breakpoint_location = false;
        let mut stop_reasons: Vec<StopReason> = Vec::new();
        let mut stack_digest_to_select: Option<(Vec<usize>, bool, u16)> = None;
        let mut hit_step_breakpoint: Option<StepBreakpointType> = None;

        let breakpoint_location_idx = self.find_breakpoint_location(addr);

        // Check if there's int3 instruction in the actual program, i.e. not injected by the debugger.
        let original_instruction_byte = match &breakpoint_location_idx {
            &Some(idx) => self.breakpoint_locations[idx].original_byte,
            None => match self.memory.read_u8(addr) {
                Ok(x) => x,
                Err(e) => {
                    eprintln!("warning: failed to read instruction byte at 0x{:x}: {}", addr, e);
                    0
                }
            }
        };
        let is_debug_trap = original_instruction_byte == 0xcc; // even if we stopped for a different reason

        if stopped_on_sw_breakpoint && !is_debug_trap {
            // Revert RIP to the start of the instruction that we overwrote with 0xcc.
            regs.set(RegisterIdx::Rip, addr as u64, false);
            unsafe { ptrace(PTRACE_POKEUSER, tid, mem::offset_of!(libc::user, regs.rip) as u64, addr as u64)? };
        }

        let is_user_signal = si_code <= 0;

        let ignore_breakpoints =
            // Ignore regular breakpoints when stepping.
            // (It would be better for performance to also deactivate them as we go, then reactivate after the step completes.)
            self.stepping.as_ref().is_some_and(|s| s.disable_breakpoints) ||
            self.pending_step.is_some() ||
            // Solves this race condition:
            //  1. A step completes. It's added to thread's stop_reasons. Other threads are requested to suspend.
            //  2. The UI sees the stepped thread's stop_reasons.
            //  3. Just before suspending, some other thread hits a breakpoint. It's added to stop_reasons (because self.stepping is already unset).
            //  4. The UI sees the breakpoint hit in stop_reasons and switches to that thread.
            //     Very confusing because breakpoints are supposed to be disabled when stepping.
            //
            // As an undesired side effect, this check also prevents reporting simultaneous breakpoint hits by multiple threads.
            // If this turns out to be a problem, replace this with a different mechanism (maybe a flag in Thread saying "ignore breakpoints in this thread until it's suspended").
            self.target_state == ProcessState::Suspended;

        if (!stopped_on_sw_breakpoint && !stopped_on_hw_breakpoint && !single_stepping && !is_debug_trap && !is_user_signal) ||
            (stopped_on_sw_breakpoint && breakpoint_location_idx.is_none() && !is_debug_trap) {
            eprintln!("warning: unexpected SIGTRAP ({}) in thread {} at 0x{:x}", trap_si_code_name(si_code), tid, addr);
        }

        // Instruction breakpoints/stepping.
        if let Some(idx) = breakpoint_location_idx {
            let location = &mut self.breakpoint_locations[idx];

            if stopped_on_sw_breakpoint && location.hardware && !is_debug_trap {
                // Maybe this is normal, if the sw breakpoint was recently converted to hw, and this SIGTRAP was queued up before that.
                eprintln!("warning: unexpected sw breakpoint SIGTRAP on hw breakpoint in thread {} at {:x}", tid, addr);
            }

            if location.breakpoints.is_empty() {
                // Lazily deactivate obsolete breakpoint location if we hit it. This is just for performance, to avoid repeatedly hitting+ignoring a deleted hot breakpoint.
                self.deactivate_breakpoint_location(idx, tid)?;
            } else {
                is_active_breakpoint_location = true;
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
                                if subfunction_level < SUBFUNCTION_LEVEL_MAX {
                                    stack_digest_to_select = Some((Vec::new(), false, subfunction_level));
                                }
                            }
                        }
                    }
                    &BreakpointRef::Id {id, subfunction_level} => {
                        if spurious_stop {
                            // Spurious stop after converting breakpoint from software to hardware, or initial hit after adding a breakpoint on current line.
                            if self.context.settings.trace_logging { eprintln!("trace: ignoring spurious stop on hw breakpoint {:x}", addr); }
                            // But still increment hit counter to make it easier to notice and debug if we get unexpectedly many spurious stops.
                            self.breakpoints.get_mut(id).hits += 1;
                        } else {
                            let bp = self.breakpoints.get(id);
                            if bp.hidden {
                                match &bp.on {
                                    BreakpointOn::PointOfInterest(PointOfInterest::LibraryLoad) => refresh_process_info = true,
                                    // (Hardcoded behavior for this breakpoint, for now. We should make it a normal user-visible breakpoint instead, allowing attaching condition to it etc.)
                                    BreakpointOn::PointOfInterest(PointOfInterest::Panic) => hit = true,
                                    _ => panic!("unexpected hidden breakpoint"),
                                }
                            } else if self.process_breakpoint_hit(id, tid, ignore_breakpoints, subfunction_level, &mut stop_reasons) {
                                hit = true;
                                if subfunction_level < SUBFUNCTION_LEVEL_MAX {
                                    stack_digest_to_select = Some((Vec::new(), false, subfunction_level));
                                }
                            }
                        }
                    }
                }
            }
            let location = &mut self.breakpoint_locations[idx];

            if !location.hardware {
                // Stop all threads so that we can convert the breakpoint into hardware breakpoint (or single-step past it).
                // If this turns out too slow, we could hook the current instruction instead (maybe won't work for all instructions).
                self.stopping_to_handle_breakpoints = true;
            }
        }

        // Data breakpoints.
        if stopped_on_hw_breakpoint {
            for i in 0..4 {
                if (dr6 & (1 << i)) != 0 {
                    let bp = &self.hardware_breakpoints[i];
                    if bp.active {
                        if let &Some(id) = &bp.data_breakpoint_id {
                            hit |= self.process_breakpoint_hit(id, tid, ignore_breakpoints, /*subfunction_level*/ SUBFUNCTION_LEVEL_MAX, &mut stop_reasons);
                        }
                    }
                }
            }
        }

        if (is_debug_trap || is_user_signal) && !is_active_breakpoint_location && !ignore_breakpoints {
            // Hit something like __builtin_debugtrap or raise(SIGTRAP), and there's no debugger breakpoint at the same location.
            // The !is_active_breakpoint_location condition makes debugger breakpoints override __builtin_debugtrap,
            // which allows e.g. using a conditional breakpoint to make the trap conditional.
            hit = true;
            stop_reasons.push(StopReason::DebugTrap);
        }

        if let Some(step) = &self.stepping {
            if hit {
                self.cancel_stepping();
            } else if tid == step.tid && self.handle_step_stop(hit_step_breakpoint.is_some(), single_stepped, &regs) {
                let step = self.stepping.as_mut().unwrap();
                if step.internal_kind != StepKind::Cursor {
                    stack_digest_to_select = Some((mem::take(&mut step.stack_digest), step.internal_kind == StepKind::Into, SUBFUNCTION_LEVEL_MAX));
                }
                let stop_reason = if hit_step_breakpoint.is_some_and(|t| t == StepBreakpointType::Catch) {StopReason::Exception} else {StopReason::Step};
                stop_reasons.push(stop_reason);
                self.cancel_stepping();
                hit = true;
            }
        }

        if request_single_step {
            self.threads.get_mut(&tid).unwrap().single_stepping = true;
        }

        if !stop_reasons.is_empty() {
            self.threads.get_mut(&tid).unwrap().stop_reasons.append(&mut stop_reasons);
        }

        if is_debug_trap {
            self.threads.get_mut(&tid).unwrap().is_after_user_debug_trap_instruction = true;
        }

        Ok((hit, refresh_process_info, regs, stack_digest_to_select))
    }

    fn eval_breakpoint_condition(&mut self, tid: pid_t, id: BreakpointId, subfunction_level: u16) -> Result<bool> {
        // All of this looks slow.
        let bp = self.breakpoints.get(id);
        let expr = bp.condition.as_ref().unwrap().1.as_ref().unwrap();
        if expr.is_trivial_false() {
            // Fast path for profiling (to measure how slow is the expression evaluation vs everything else.
            return Ok(false);
        }
        let need_full_stack = does_expression_need_full_stack(expr);

        let t = self.threads.get_mut(&tid).unwrap();
        t.info.regs = ptrace_getregs(tid)?;
        t.info.extra_regs.reset_with_tid(tid);

        let stack = self.get_stack_trace(tid, /*partial*/ !need_full_stack);
        let selected_subframe = if subfunction_level < SUBFUNCTION_LEVEL_MAX && !stack.frames.is_empty() {
            stack.frames[0].subframes.end.saturating_sub(subfunction_level as usize + 1)
        } else {
            0
        };
        let bp = self.breakpoints.get(id);
        let expr = bp.condition.as_ref().unwrap().1.as_ref().unwrap();
        let mut eval_state = EvalState::new();
        let mut eval_context = self.make_eval_context(&stack, selected_subframe, tid);
        let (val, _dubious) = eval_parsed_expression(expr, &mut eval_state, &mut eval_context)?;
        Ok(is_value_truthy(&val, &mut eval_context.memory)?)
    }

    // Do cleanup just before exit. The Debugger is not usable after this.
    //
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
    pub fn shutdown(&mut self) {
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
                if let Err(e) = unsafe { ptrace(PTRACE_POKETEXT, tid, (addr - byte_idx) as u64, word) } {
                    eprintln!("warning: detach failed to remove breakpoint at 0x{:x}: PTRACE_POKETEXT failed: {}", addr, e);
                }
            }

            // Disable hardware breakpoints for this thread. (Do this unconditionally because threads may have leftover breakpoints that are not in self.hardware_breakpoints or self.breakpoint_locations anymore.)
            if let Err(e) = unsafe { ptrace(PTRACE_POKEUSER, tid, (mem::offset_of!(libc::user, u_debugreg) + 7*8) as u64, 1u64 << 10) } {
                eprintln!("warning: detach failed to clear hardware breakpoints for thread {}: {}", tid, e);
            }

            if let Err(e) = unsafe { ptrace(PTRACE_DETACH, tid, 0, 0) } {
                eprintln!("warning: detach failed for thread {}: {}", tid, e);
            }
        };
        let mut running_threads: HashSet<pid_t> = HashSet::new();
        for (tid, thread) in &self.threads {
            if thread.state == ThreadState::Suspended {
                detach_thread(*tid);
            } else if let Err(e) = unsafe {ptrace(PTRACE_INTERRUPT, *tid, 0, 0)} {
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

            // TODO: Do a subset of handle_breakpoint_trap() logic here, to decrement RIP after hitting our breakpoint instruction.

            if !libc::WIFEXITED(wstatus) && !libc::WIFSIGNALED(wstatus) {
                detach_thread(tid);
            }

            running_threads.remove(&tid);
        }
    }
}

impl Drop for Debugger {
    fn drop(&mut self) {
        self.shutdown();
    }
}
