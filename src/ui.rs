use crate::{*, debugger::*, error::*, log::*, symbols::*, symbols_registry::*, util::*, registers::*, procfs::*, unwind::*, disassembly::*, pool::*, layout::*, settings::*, context::*, types::*, expr::*, widgets::*, search::*, arena::*, interp::*, imgui::*, common_ui::*, terminal::*, doc::*, os::*};
use std::{io::{self, Write, BufRead, BufReader, Read}, mem::{self, take}, collections::{HashSet, HashMap, hash_map::Entry}, os::fd::AsRawFd, path, path::{Path, PathBuf}, fs::File, fmt::Write as FmtWrite, borrow::Cow, ops::Range, str, os::unix::ffi::OsStrExt, sync::{Arc}, time::Duration};
use libc::{self, pid_t};
use rand::random;

pub struct DebuggerUI {
    pub terminal: Terminal,
    pub ui: UI,
    input: InputReader,
    state: UIState,
    layout: Layout,
    loaded_layout: bool,

    // These are assigned by build(), to be checked and acted on by the caller.
    pub should_quit: bool,
    pub should_drop_caches: bool,

    help_dialog: HelpDialog,
}

#[derive(Default)]
pub struct UIState {
    last_error: String, // reset on next key press
    key_hints: Vec<KeyHint>,
    profiler_enabled: bool,

    selected_thread: pid_t,
    selected_frame: usize,
    selected_subframe: usize,

    // Selected in disassembly window.
    selected_addr: Option<(/*binary_id*/ usize, /*function_idx*/ usize, /*addr*/ usize)>,

    // Redundant copies of information from Debugger. Updated on every frame. Used for convenience and for consistent ordering.
    stack: StackTrace, // assigned by StackWindow
    hit_breakpoints: Vec<BreakpointId>,

    // Communication between windows, for interactions like:
    //  * when switching stack frames (for any of a number of reasons, including the above), scroll to the corresponding source file+line and disassembly instruction,
    //  * when selecting a breakpoint in the breakpoints window, scroll to the corresponding line in source and instruction and disassembly.
    // The only_if_error_tab solves the following; typically the should_scroll_* are first requested before symbols are loaded; that makes source and disassembly windows initially show errors;
    // when symbols are loaded, we want to try again and stop showing errors; but maybe the user already opened some non-error file and is looking at it - then we shouldn't forcefully switch to current file;
    // so we set this flag, which tells the windows to scroll only if the error tab is selected.
    should_scroll_source: Option<(Option<SourceScrollTarget>, /*only_if_on_error_tab*/ bool)>,
    should_scroll_disassembly: Option<(Result<DisassemblyScrollTarget>, /*only_if_on_error_tab*/ bool)>,
    should_edit_breakpoint_condition: Option<BreakpointId>,
}

#[derive(Default, Clone)]
pub struct KeyHint {
    pub key_ranges: Vec<[KeyAction; 2]>,
    pub hint: &'static str,
    pub condition: &'static str, // hint applicable only if this case, e.g. "if the process is running"
    pub window: Option<WindowType>,
    // Show only in the big help window, not in the hints corner pane.
    pub hidden: bool,
    pub if_not_core_dump: bool, // not applicable if debugging a core dump
}
impl KeyHint {
    fn key(key: KeyAction, hint: &'static str) -> Self { Self {key_ranges: vec![[key, key]], hint, ..Self::default()} }
    fn keys(keys: &[KeyAction], hint: &'static str) -> Self { Self {key_ranges: keys.iter().map(|k| [*k, *k]).collect(), hint, ..Self::default()} }
    fn ranges(ranges: &[[KeyAction; 2]], hint: &'static str) -> Self { Self {key_ranges: ranges.iter().cloned().collect(), hint, ..Self::default()} }
    fn hide(mut self) -> Self { self.hidden = true; self }
    fn conditional(mut self, show: bool, cond: &'static str) -> Self { self.hidden = !show; self.condition = cond; self }
    fn if_not_core_dump(mut self) -> Self { self.if_not_core_dump = true; self }
}

struct SourceScrollTarget {
    path: PathBuf,
    version: FileVersionInfo,
    line: usize,
    cascade: bool, // scroll disassembly as well
}

struct DisassemblyScrollTarget {
    binary_id: usize,
    function_idx: usize,
    static_pseudo_addr: usize,
    subfunction_level: u16,
    cascade: bool, // scroll source as well
}

pub trait WindowContent {
    fn build(&mut self, state: &mut UIState, debugger: &mut Debugger, ui: &mut UI);

    // Called after some symbols finished loading, or if the user requested a redraw.
    fn drop_caches(&mut self) {}

    fn get_key_hints(&self, out: &mut Vec<KeyHint>, debugger: &Debugger) {}

    fn save_state(&self, out: &mut Vec<u8>) -> Result<()> {Ok(())}
    fn load_state(&mut self, inp: &mut &[u8]) -> Result<()> {Ok(())}
}

#[derive(Ord, PartialOrd, Eq, PartialEq, Debug, Clone, Copy, Hash)]
#[repr(u8)]
pub enum WindowType {
    // Some windows must be updated in a specific order. E.g. threads window may change ui.selected_thread and therefore must be rendered before any windows that depend on current thread.
    // This enum defines the order in which windows should be rendered.
    // If there are circular dependencies (e.g. breakpoints window wants to scroll the code window, and the code window may add breakpoints), the later window can set should_redraw = true to ask an earlier window to refresh.
    Binaries = 0,
    Breakpoints = 1,
    Threads = 2,
    Stack = 3,

    Code = 4,
    Disassembly = 5,

    Locations = 6,
    Watches = 7,
    Hints = 8,

    Status = 9,
}
impl WindowType {
    pub fn title(self) -> &'static str {
        match self {
            Self::Binaries => "binaries",
            Self::Breakpoints => "breakpoints",
            Self::Threads => "threads",
            Self::Stack => "stack",
            Self::Code => "code",
            Self::Disassembly => "disassembly",
            Self::Locations => "locations",
            Self::Watches => "watches",
            Self::Hints => "controls",
            Self::Status => "status",
        }
    }

    pub fn serialize(self) -> u8 {
        self as u8
    }

    pub fn deserialize(x: u8) -> Result<Self> {
        if x <= Self::Status as u8 {
            Ok(unsafe {mem::transmute(x)})
        } else {
            err!(Environment, "bad WindowType")
        }
    }

    pub fn create_window(self) -> Box<dyn WindowContent> {
        match self {
            WindowType::Hints => Box::new(HintsWindow::default()),
            WindowType::Status => Box::new(StatusWindow::default()),
            WindowType::Watches => Box::new(WatchesWindow::default()),
            WindowType::Locations => Box::new(LocationsWindow::default()),
            WindowType::Disassembly => Box::new(DisassemblyWindow::default()),
            WindowType::Code => Box::new(CodeWindow::default()),
            WindowType::Binaries => Box::new(BinariesWindow::default()),
            WindowType::Breakpoints => Box::new(BreakpointsWindow::default()),
            WindowType::Stack => Box::new(StackWindow::default()),
            WindowType::Threads => Box::new(ThreadsWindow::default()),
        }
    }
}

pub struct RequiredWindowInfo {
    pub type_: WindowType,
    pub hotkey_number: Option<usize>,
    pub fixed_height: Option<usize>,
}

pub const REQUIRED_WINDOWS: &'static [RequiredWindowInfo] = &[
    RequiredWindowInfo {type_: WindowType::Hints, hotkey_number: None, fixed_height: None},
    RequiredWindowInfo {type_: WindowType::Status, hotkey_number: None, fixed_height: Some(7)},
    RequiredWindowInfo {type_: WindowType::Watches, hotkey_number: Some(1), fixed_height: None},
    RequiredWindowInfo {type_: WindowType::Locations, hotkey_number: None, fixed_height: None},
    RequiredWindowInfo {type_: WindowType::Disassembly, hotkey_number: Some(2), fixed_height: None},
    RequiredWindowInfo {type_: WindowType::Code, hotkey_number: Some(3), fixed_height: None},
    RequiredWindowInfo {type_: WindowType::Binaries, hotkey_number: None, fixed_height: None},
    RequiredWindowInfo {type_: WindowType::Breakpoints, hotkey_number: Some(4), fixed_height: None},
    RequiredWindowInfo {type_: WindowType::Stack, hotkey_number: Some(5), fixed_height: None},
    RequiredWindowInfo {type_: WindowType::Threads, hotkey_number: Some(6), fixed_height: None},
];

impl DebuggerUI {
    pub fn new() -> Self {
        let ui = UI::default();
        let state = UIState::default();
        Self {terminal: Terminal::new(), input: InputReader::new(), layout: Layout::new(), loaded_layout: false, ui, state, help_dialog: Default::default(), should_drop_caches: false, should_quit: false}
    }

    pub fn save_state(&self, out: &mut Vec<u8>) -> Result<()> {
        self.layout.save_state(out)?;
        Ok(())
    }

    pub fn load_state(&mut self, inp: &mut &[u8]) -> Result<()> {
        self.layout.load_state(inp)?;

        let mut windows_by_type: HashMap<WindowType, usize> = HashMap::new();
        for (_, window) in self.layout.sorted_windows() {
            *windows_by_type.entry(window.type_).or_default() += 1;
        }
        for info in REQUIRED_WINDOWS {
            if windows_by_type.get(&info.type_) != Some(&1) {
                return err!(Environment, "missing or duplicate windows");
            }
        }

        self.loaded_layout = true;
        Ok(())
    }

    fn default_layout() -> Layout {
        // +---------+-------+-------------+
        // |  hints  |       |  binaries   |
        // |         |       | breakpoints |
        // +---------+ disas +-------------+
        // | status  |       |             |
        // +---------+-------+    stack    |
        // |         |       |             |
        // | watches | code  +-------------+
        // |  locs   |       |   threads   |
        // |         |       |             |
        // +---------+-------+-------------+
        //
        // Other windows we could add: terminal, memory, detached watch.

        let mut layout = Layout::new();
        let cols = layout.split(layout.root, Axis::X, vec![0.3, 0.75], 0);

        let rows = layout.split(cols[0], Axis::Y, vec![0.3, 0.4], 0);
        let hints_window = layout.new_window(Some(rows[0]), WindowType::Hints);
        let status_window = layout.new_window(Some(rows[1]), WindowType::Status);
        let watches_window = layout.new_window(Some(rows[2]), WindowType::Watches);
        layout.new_window(Some(rows[2]), WindowType::Locations);

        let rows = layout.split(cols[1], Axis::Y, vec![0.4], 0);
        let disassembly_window = layout.new_window(Some(rows[0]), WindowType::Disassembly);
        let code_window = layout.new_window(Some(rows[1]), WindowType::Code);

        let rows = layout.split(cols[2], Axis::Y, vec![0.25, 0.75], 0);
        layout.new_window(Some(rows[0]), WindowType::Binaries);
        let breakpoints_window = layout.new_window(Some(rows[0]), WindowType::Breakpoints);
        let stack_window = layout.new_window(Some(rows[1]), WindowType::Stack);
        let threads_window = layout.new_window(Some(rows[2]), WindowType::Threads);

        layout.active_window = Some(threads_window);

        layout
    }

    pub fn buffer_input(&mut self, prof: &mut ProfileBucket) -> Result<bool> {
        let mut evs: Vec<Event> = Vec::new();
        let bytes = self.input.read(&mut evs, prof, None)?;
        prof.ui_input_bytes += bytes;

        let mut significant = false;
        for e in &evs {
            match e {
                Event::Key(_) => significant = true,
                Event::Mouse(m) if m.event == MouseEvent::Press => significant = true,
                _ => (),
            }
        }
        if significant {
            self.state.last_error = String::new();
        }

        Ok(self.ui.buffer_input(&evs))
    }

    pub fn update_and_render(&mut self, debugger: &mut Debugger) -> Result<()> {
        let mut timer = TscScopeExcludingSyscalls::new(&debugger.prof.bucket);
        let mut buffer = self.terminal.start_frame(self.ui.palette.default, &mut debugger.prof.bucket)?;
        let fill_tsc = timer.restart(&debugger.prof.bucket);

        self.ui.start_build(buffer.width, buffer.height);

        self.build(debugger)?;

        if self.should_quit {
            return Ok(());
        }

        self.ui.end_build(&mut buffer);
        let build_tsc = timer.restart(&debugger.prof.bucket) - self.ui.prof_render_tsc;

        let commands = self.terminal.prepare_command_buffer(&buffer, self.ui.should_show_cursor.clone());
        debugger.prof.bucket.ui_output_bytes += commands.len();
        self.terminal.present(buffer, commands, &mut debugger.prof.bucket)?;
        let fill_tsc = fill_tsc + timer.finish(&debugger.prof.bucket);

        debugger.prof.bucket.ui_build_max_tsc.set_max(build_tsc);
        debugger.prof.bucket.ui_render_max_tsc.set_max(self.ui.prof_render_tsc);
        debugger.prof.bucket.ui_fill_max_tsc.set_max(fill_tsc);
        debugger.prof.bucket.ui_max_tsc.set_max(build_tsc + self.ui.prof_render_tsc + fill_tsc);

        Ok(())
    }

    fn build(&mut self, debugger: &mut Debugger) -> Result<()> {
        if !self.loaded_layout {
            self.layout = Self::default_layout();
            self.loaded_layout = true;
        }
        
        self.should_drop_caches = false;

        let w = self.ui.get_mut(self.ui.content_root);
        w.flags.insert(WidgetFlags::CAPTURE_ALL_KEYS);
        let keys = w.keys.clone();

        // Handle some of the global hotkeys. Windows may also handle their global hotkeys by attaching them to the content_root widget, e.g. threads window handling global hotkeys for switching threads.
        let mut open_help = false;
        for key in &keys {
            match self.ui.key_binds.normal.key_to_action.get(key) {
                Some(KeyAction::Quit) => {
                    LogTimestampInDestructor("shutdown requested");
                    self.should_quit = true;
                    return Ok(());
                }
                Some(KeyAction::Run) => {
                    let r = debugger.start_child(None);
                    report_result(&mut self.state, &r);
                }
                Some(KeyAction::Continue) => {
                    let r = debugger.resume();
                    report_result(&mut self.state, &r);
                }
                Some(KeyAction::Suspend) => {
                    let r = debugger.suspend();
                    report_result(&mut self.state, &r);
                }
                Some(KeyAction::Kill) => {
                    let r = debugger.murder(libc::SIGKILL);
                    report_result(&mut self.state, &r);
                }
                Some(KeyAction::SendSigint) => {
                    let r = debugger.murder(libc::SIGINT);
                    if r.is_ok() {
                        log!(debugger.log, "sent SIGINT");
                    } else {
                        report_result(&mut self.state, &r);
                    }
                }
                Some(KeyAction::Help) => open_help = true,

                Some(KeyAction::DropCaches) => {
                    self.terminal.clear()?; // do this only on hotkey, not when drop_caches is initiated by e.g. symbols loading
                    self.should_drop_caches = true;
                }

                Some(KeyAction::ToggleProfiler) => self.state.profiler_enabled ^= true,

                _ => (),
            }
        }

        // Special treatment for hints/profiler window. Maybe we should just make them different windows instead.
        if let Some(id) = self.layout.any_window_by_type(WindowType::Hints) {
            let w = self.layout.windows.get_mut(id);
            if self.state.profiler_enabled {
                w.fixed_size[Axis::Y] = None;
                w.title = "profiler".to_string();
            } else {
                w.fixed_size[Axis::Y] = Some(HintsWindow::NORMAL_HEIGHT);
                w.title = "controls".to_string();
            }
        }

        if self.state.should_edit_breakpoint_condition.is_some() {
            match self.layout.any_window_by_type(WindowType::Breakpoints) {
                Some(id) => self.layout.active_window = Some(id),
                None => {
                    log!(debugger.log, "no breakpoints window");
                    self.state.should_edit_breakpoint_condition = None;
                }
            }
        }

        // Draw lines around windows, determine which window is active.
        self.layout.build(&mut self.ui);

        // Hints for all key binds. Used for both hints window and help dialog.
        // Keep it brief, there's not much space.
        let mut hints = Vec::new();
        hints.push(KeyHint::key(KeyAction::Quit, match debugger.mode {
            RunMode::CoreDump => "quit",
            _ if debugger.target_state == ProcessState::NoProcess => "quit",
            RunMode::Run => "kill and quit",
            RunMode::Attach => "detach and quit",
        }));
        hints.push(KeyHint::key(KeyAction::Help, "help"));
        hints.push(KeyHint::key(KeyAction::Cancel, "close dialog (like this one) or search bar").conditional(false, "if any"));
        hints.push(KeyHint::ranges(&[[KeyAction::Window0, KeyAction::Window9], [KeyAction::WindowLeft, KeyAction::WindowDown]], "switch window"));
        hints.push(KeyHint::keys(&[KeyAction::NextTab, KeyAction::PreviousTab], "switch tab").conditional(true, "if there are tabs"));
        hints.push(KeyHint::keys(&[KeyAction::PreviousStackFrame, KeyAction::NextStackFrame, KeyAction::PreviousThread, KeyAction::NextThread], "switch frame/thread"));
        hints.push(KeyHint::key(KeyAction::ToggleProfiler, "profiler").hide());
        hints.push(KeyHint::key(KeyAction::DropCaches, "drop caches and redraw").hide());
        let state = debugger.target_state;
        hints.push(KeyHint::key(KeyAction::Suspend, "suspend").conditional(state == ProcessState::Running || state == ProcessState::Stepping, "if running or stepping"));
        hints.push(KeyHint::key(KeyAction::Continue, "continue").conditional(state == ProcessState::Suspended || state == ProcessState::Stepping, "if suspended or stepping"));
        hints.push(KeyHint::keys(&[KeyAction::StepIntoLine, KeyAction::StepOverLine, KeyAction::StepOut, KeyAction::StepOverColumn], "step into/over/out/column").conditional(state == ProcessState::Suspended, "if suspended"));
        hints.push(KeyHint::keys(&[KeyAction::StepIntoInstruction, KeyAction::StepOverInstruction], "step into/over instruction").conditional(state == ProcessState::Suspended, "if suspended"));
        let startable = state == ProcessState::NoProcess && debugger.mode == RunMode::Run;
        let startable_text = "if no process";
        hints.push(KeyHint::key(KeyAction::Run, "start").conditional(startable, startable_text));
        hints.push(KeyHint::key(KeyAction::StepIntoLine, "run to main()").conditional(startable, startable_text));
        hints.push(KeyHint::key(KeyAction::StepIntoInstruction, "run to early start").conditional(startable, startable_text));
        hints.push(KeyHint::keys(&[KeyAction::Kill, KeyAction::SendSigint], "kill/sigint").conditional(debugger.mode == RunMode::Run && debugger.target_state.process_ready(), "if child exists"));
        for (id, win) in self.layout.sorted_windows() {
            let start = hints.len();
            win.content.get_key_hints(&mut hints, debugger);
            for h in &mut hints[start..] {
                h.window = Some(win.type_);
                if &Some(id) != &self.layout.active_window {
                    h.hidden = true;
                }
            }
        }
        self.state.key_hints = hints;

        // Build windows.
        for (_, win) in self.layout.sorted_windows_mut() {
            with_parent!(self.ui, win.widget, {
                win.content.build(&mut self.state, debugger, &mut self.ui);
            });
        }

        if let Some(widget_idx) = make_dialog_frame(open_help, AutoSize::Remainder(0.75), AutoSize::Remainder(0.83), self.ui.palette.dialog, self.ui.palette.default, "halp!", &mut self.ui) {
            with_parent!(self.ui, widget_idx, {
                if !self.ui.check_keys(&[KeyAction::Help, KeyAction::Cancel]).is_empty() {
                    self.ui.close_dialog();
                } else {
                    self.help_dialog.build(&mut self.state, &mut self.ui);
                }
            });
        }

        // Stepping has to be handled after updating windows because selected_subframe is assigned by StackWindow.
        for key in &keys {
            let (kind, by_instructions, use_line_number_with_column) = match self.ui.key_binds.normal.key_to_action.get(key) {
                Some(KeyAction::StepIntoLine) => (StepKind::Into, false, false),
                Some(KeyAction::StepIntoInstruction) => (StepKind::Into, true, false),
                Some(KeyAction::StepOverLine) => (StepKind::Over, false, false),
                Some(KeyAction::StepOverColumn) => (StepKind::Over, false, true),
                Some(KeyAction::StepOverInstruction) => (StepKind::Over, true, false),
                Some(KeyAction::StepOut) => (StepKind::Out, false, false),
                Some(KeyAction::StepOutNoInline) => (StepKind::Out, true, false),
                _ => continue,
            };
            let r = if debugger.target_state == ProcessState::NoProcess {
                // If the program is not running, start it and step to start of main() or to initial exec.
                let initial_step = if by_instructions {
                    BreakpointOn::InitialExec
                } else {
                    BreakpointOn::PointOfInterest(PointOfInterest::MainFunction)
                };
                debugger.start_child(Some(initial_step))
            } else {
                debugger.step(self.state.selected_thread, self.state.selected_subframe, kind, by_instructions, use_line_number_with_column)
            };
            report_result(&mut self.state, &r);
            self.ui.should_redraw = true;
        }

        Ok(())
    }

    pub fn drop_caches(&mut self) {
        for (win_id, win) in self.layout.windows.iter_mut() {
            win.content.drop_caches();
        }
        self.help_dialog.drop_caches();
    }
}

fn report_result<R>(state: &mut UIState, r: &Result<R>) {
    if let Err(e) = r {
        state.last_error = format!("{}", e);
        if !e.is_usage() {
            eprintln!("warning: {}", e);
        }
    }
}

fn get_breakpoint_icon(enabled: bool, active: bool, secondary: bool, conditional: bool, data: bool, stop_on_read: bool, palette: &Palette) -> (&'static str, Style) {
    if data {
        if stop_on_read {
            if conditional {
                if active {
                    ("★ᶜ", palette.breakpoint)
                } else {
                    ("☆ᶜ", palette.secondary_breakpoint)
                }
            } else {
                if active {
                    ("★ ", palette.breakpoint)
                } else {
                    ("☆ ", palette.secondary_breakpoint)
                }
            }
        } else {
            if conditional {
                if active {
                    ("◆ᶜ", palette.breakpoint)
                } else {
                    ("◇ᶜ", palette.secondary_breakpoint)
                }
            } else {
                if active {
                    ("◆ ", palette.breakpoint)
                } else {
                    ("◇ ", palette.secondary_breakpoint)
                }
            }
        }
    } else if !enabled {
        if conditional {
            ("© ", palette.secondary_breakpoint)
        } else {
            ("○ ", palette.secondary_breakpoint)
        }
    } else if !active {
        if conditional {
            ("© ", palette.breakpoint)
        } else {
            ("○ ", palette.breakpoint)
        }
    } else {
        if secondary {
            if conditional {
                ("Ⓒ ", palette.secondary_breakpoint)
            } else {
                ("● ", palette.secondary_breakpoint)
            }
        } else {
            if conditional {
                ("Ⓒ ", palette.breakpoint)
            } else {
                ("● ", palette.breakpoint)
            }
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum SpecialWatch {
    Locals,
    Registers,
    RegistersGroup,
    AddWatch,
}

#[derive(Clone, Copy, Eq, PartialEq)]
struct ValueTreeNodeIdx(usize);
impl ValueTreeNodeIdx {
    fn invalid() -> Self { Self(usize::MAX) }
    fn is_valid(self) -> bool { self.0 != usize::MAX }
}

struct ValueTreeNode {
    name: Range<usize>, // lines in ValueTree's `text`
    line_wrapped_name: Option<Range<usize>>,
    value: Result<Value>,
    dubious: bool,
    special: Option<SpecialWatch>,
    registers_group: &'static [ExtraRegisterIdx],

    child_kind: ValueChildKind,
    deref: usize,
    click_action: ValueClickAction,

    // Unique identifier of this node. Hash of identities (field names or array indices or similar) of nodes on the path from the root to here.
    // For remembering which subtrtees were expanded and where the cursor was, in a way that survives recalculation or partial change of the values.
    identity: usize,

    depth: usize,
    parent: ValueTreeNodeIdx,

    // These are populated lazily.
    formatted_value: [Option<Range<usize>>; 3], // collapsed, expanded, line-wrapped; ranges in ValueTree's `text`; if value is Err, the error message is formatted into here
    has_children: bool, // populated together with either element of formatted_value
    children: Range<usize>, // indices in `nodes`; populated together with formatted_value[1]

    // Layout information, recalculated every frame, valid only for reachable nodes.
    start_y: isize,
    node_end_y: isize,
    subtree_end_y: isize,
    expanded: bool,
    is_text_input: bool,
    // These are just for asserts.
    layout_frame_idx: usize, // when this node's layout information was updated
    name_line_wrap_width: usize, // what width was used for line_wrapped_name
}
impl Default for ValueTreeNode { fn default() -> Self { Self {name: 0..0, line_wrapped_name: None, value: err!(Internal, ""), dubious: false, special: None, child_kind: ValueChildKind::Other, deref: 0, click_action: ValueClickAction::None, identity: 0, depth: 0, parent: ValueTreeNodeIdx::invalid(), formatted_value: [None, None, None], has_children: false, children: 0..0, start_y: 0, node_end_y: 0, subtree_end_y: 0, expanded: false, is_text_input: false, layout_frame_idx: 0, name_line_wrap_width: 0, registers_group: &[]} } }

#[derive(Default)]
struct ValueTree {
    nodes: Vec<ValueTreeNode>,
    roots: Vec<ValueTreeNodeIdx>, // (so it's technically a forest, but ValueTree sounds nicer, and you can always imagine an implicit root node that has these "root" nodes as children)
    // An element of depth-first traversal of tree nodes, descending only into expanded ones. The cursor stands on one of these.
    rows: Vec<ValueTreeNodeIdx>,

    text: StyledText, // arena for various text
    temp_text: StyledText,
    arena: Arena,
}
impl ValueTree {
    fn clear(&mut self) { *self = Self::default(); }

    fn add(&mut self, mut node: ValueTreeNode) -> ValueTreeNodeIdx {
        assert!(node.depth == 0);
        if node.parent.is_valid() {
            let parent = &self.nodes[node.parent.0];
            node.identity = hash(&(parent.identity, node.identity));
            node.depth = parent.depth + 1;
        } else {
            self.roots.push(ValueTreeNodeIdx(self.nodes.len()));
        }
        self.nodes.push(node);
        ValueTreeNodeIdx(self.nodes.len() - 1)
    }
}

struct WatchExpression {
    identity: usize,
    text: String,
    special: Option<SpecialWatch>,
}
impl WatchExpression {
    fn is_editable(&self) -> bool { !self.special.is_some_and(|s| s != SpecialWatch::AddWatch) }
}

struct WatchesWindow {
    tree: ValueTree,
    expanded_nodes: HashSet<usize>,

    cursor_path: Vec<usize>,
    cursor_idx: usize,
    scroll: isize,
    scroll_to_cursor: bool,

    // Layout information. We do layout and line wrapping manually to avoid creating widgets for invisible rows.
    name_relative_width: f64,
    name_width: usize,
    value_width: usize,
    row_height_limit: usize,
    indent_width: usize,
    max_indent: usize,

    // When this changes, we recalculate everything.
    seen: (/*thread*/ pid_t, /*selected_subframe*/ usize, /*stop_count*/ usize, ProcessState),

    // Watches window can be in 3 states:
    //  * The debuggee is suspended, watches show up-to-date values.
    //  * The debuggee is not suspended (running or no process), watches window shows last seen values. have_good_cached_values = true
    //  * The debuggee is not suspended, watches window shows errors like "<no process>" or "<running>". have_good_cached_values = false.
    have_good_cached_values: bool,
    
    expressions: Vec<WatchExpression>, // watch expressions; parallel to tree.roots
    text_input: Option<(/*identity*/ usize, /*height*/ usize, TextInput)>, // if editing watch expression
    text_input_built: bool,

    eval_state: EvalState,

    data_breakpoints: HashMap<(/*addr*/ usize, /*size*/ u8), (/*enabled*/ bool, /*active*/ bool, /*stop_on_read*/ bool, /*conditional*/ bool, /*hit*/ bool)>,

    variable_search_dialog: Option<SearchDialog>,
    type_search_dialog: Option<SearchDialog>,
}
impl Default for WatchesWindow {
    fn default() -> Self {
        let mut r = Self {tree: ValueTree::default(), expanded_nodes: HashSet::new(), cursor_path: Vec::new(), cursor_idx: 0, scroll: 0, scroll_to_cursor: false, name_relative_width: 0.4, name_width: 0, value_width: 0, row_height_limit: 0, indent_width: 0, max_indent: 0, seen: (0, usize::MAX, usize::MAX, ProcessState::NoProcess), have_good_cached_values: false, expressions: Vec::new(), text_input: None, text_input_built: false, eval_state: EvalState::new(), data_breakpoints: HashMap::new(), variable_search_dialog: None, type_search_dialog: None };

        let locals_identity: usize = random();
        r.expanded_nodes.insert(locals_identity);
        r.expressions.push(WatchExpression {identity: locals_identity, text: "[locals]".to_string(), special: Some(SpecialWatch::Locals)});
        r.expressions.push(WatchExpression {identity: random(), text: "[registers]".to_string(), special: Some(SpecialWatch::Registers)});
        r
    }
}
impl WatchesWindow {
    const COLUMN_SPACING: usize = 3;
    
    fn eval_locals(&mut self, context: &mut EvalContext, parent: ValueTreeNodeIdx, palette: &Palette) {
        let selected_subframe = context.selected_subframe;
        let subframe = &context.stack.subframes[selected_subframe];
        let pseudo_addr = context.stack.frames[subframe.frame_idx].pseudo_addr;
        let (mut dwarf_context, _) = match context.make_local_dwarf_eval_context(selected_subframe) {
            Ok(x) => x,
            Err(e) => {
                self.tree.nodes[parent.0].value = Err(e);
                return;
            }
        };
        let symbols = dwarf_context.symbols.unwrap();
        let static_pseudo_addr = dwarf_context.addr_map.dynamic_to_static(pseudo_addr);

        let mut idxs_per_name: HashMap<&str, usize> = HashMap::new();
        for v in dwarf_context.local_variables {
            if !v.range().contains(&(static_pseudo_addr)) {
                continue;
            }
            if v.flags().contains(VariableFlags::FRAME_BASE) {
                // Pseudo-variable internal to eh_frame unwind mechanism. We don't list it here, but it's available as `#frame_base` in watch expressions.
                continue;
            }
            let (value, dubious) = match eval_variable(&v.location, &mut dwarf_context) {
                Ok((val, dub)) => (Ok(val), dub),
                Err(e) => (Err(e), false),
            };
            let name = unsafe {v.name()};
            let l = styled_writeln!(self.tree.text, palette.default, "{}", name);
            let idx_per_name = *idxs_per_name.entry(name).and_modify(|x| *x += 1).or_insert(1) - 1;
            self.tree.add(ValueTreeNode {name: l..l+1, value: value.map(|val| Value {val, type_: v.type_, flags: ValueFlags::empty()}), dubious, identity: hash(&(name, idx_per_name)), parent, ..Default::default()});
        }
    }

    fn eval_registers(&mut self, context: &mut EvalContext, parent: ValueTreeNodeIdx, palette: &Palette) {
        if let Some(sf) = context.stack.subframes.get(context.selected_subframe) {
            let regs = &context.stack.frames[sf.frame_idx].regs;
            for reg in RegisterIdx::all() {
                if let Ok((v, dubious)) = regs.get(*reg) {
                    let l = styled_writeln!(self.tree.text, palette.default, "{}", reg);
                    let value = Value {val: AddrOrValueBlob::Blob(ValueBlob::new(v as usize)), type_: self.eval_state.builtin_types.u64_, flags: ValueFlags::HEX};
                    self.tree.add(ValueTreeNode {name: l..l+1, value: Ok(value), dubious, identity: hash(&reg), parent, ..D!()});
                }
            }
            if let Some(extra_regs) = context.extra_regs.clone() {
                for (name, regs) in ExtraRegisterIdx::groups_for_ui() {
                    if name.is_empty() {
                        self.add_nodes_for_extra_registers(regs, context, parent, palette);
                    } else {
                        let l = styled_writeln!(self.tree.text, palette.default, "{}", name);
                        self.tree.add(ValueTreeNode {name: l..l+1, special: Some(SpecialWatch::RegistersGroup), registers_group: regs, parent, identity: hash(name), ..D!()});
                    }
                }
            }
        }
    }

    fn eval_registers_group(&mut self, context: &mut EvalContext, parent: ValueTreeNodeIdx, palette: &Palette) {
        let regs = self.tree.nodes[parent.0].registers_group;
        self.add_nodes_for_extra_registers(regs, context, parent, palette);
        if let &Some(extra_regs) = &context.extra_regs {
            if let Some(e) = &extra_regs.get().error {
                let l = styled_writeln!(self.tree.text, palette.error, "<{}>", e);
                self.tree.nodes[parent.0].formatted_value[1] = Some(l..l+1);
            }
        }
    }

    fn add_nodes_for_extra_registers(&mut self, regs: &[ExtraRegisterIdx], context: &mut EvalContext, parent: ValueTreeNodeIdx, palette: &Palette) {
        if let &Some(extra_regs) = &context.extra_regs {
            let all_dubious = match context.stack.subframes.get(context.selected_subframe) {
                Some(sf) => sf.frame_idx > 0,
                None => true,
            };
            let extra_regs = extra_regs.get();
            for &reg in regs {
                if let Ok((v, dubious)) = extra_regs.get(reg) {
                    let dubious = dubious || all_dubious;
                    let l = styled_writeln!(self.tree.text, palette.default, "{}", reg);
                    let value = self.eval_state.make_extra_register_value(v);
                    self.tree.add(ValueTreeNode {name: l..l+1, value: Ok(value), dubious, identity: hash(&reg), parent, ..D!()});
                }
            }
        }
    }

    fn eval_watches(&mut self, context: &mut EvalContext, palette: &Palette) {
        for i in 0..self.expressions.len() {
            let expr = &self.expressions[i];
            let style = if expr.special.is_some() {palette.default_dim} else {palette.default};
            let l = styled_writeln!(self.tree.text, style, "{}", expr.text);
            let name = self.tree.text.split_by_newline_character(l, None);
            let node_idx = self.tree.add(ValueTreeNode {name, identity: expr.identity, special: expr.special.clone(), ..D!()});
            let node = &mut self.tree.nodes[node_idx.0];

            if expr.special.is_some() {
                continue;
            }

            match eval_watch_expression(&expr.text, &mut self.eval_state, context) {
                Ok((val, dub)) => {
                    node.value = Ok(val);
                    node.dubious = dub;
                }
                Err(e) => node.value = Err(e),
            }
        }
    }

    // If !node.expanded: populates formatted_value[0], has_children.
    // If  node.expanded: populates formatted_value[1], has_children, children.
    // If already populated, does nothing.
    fn ensure_node_info(&mut self, node_idx: ValueTreeNodeIdx, context: &mut EvalContext, suspended: bool, palette: &Palette) {
        let node = &mut self.tree.nodes[node_idx.0];
        let i = node.expanded as usize;
        if node.formatted_value[i].is_some() {
            return;
        }
        match (&node.special, &node.value) {
            (&Some(SpecialWatch::AddWatch), _) => {
                node.formatted_value = [Some(0..0), Some(0..0), Some(0..0)];
            }
            (&Some(special), _) => {
                node.formatted_value[0] = Some(0..0);
                node.has_children = true;
                if node.expanded {
                    node.formatted_value[1] = Some(0..0);
                    if let Err(e) = context.check_has_stack() {
                        let l = styled_writeln!(self.tree.text, palette.default_dim, "<{}>", e);
                        node.formatted_value[1] = Some(l..l+1);
                    } else {
                        let start = self.tree.nodes.len();
                        let what = match special {
                            SpecialWatch::Locals => {
                                self.eval_locals(context, node_idx, palette);
                                "locals"
                            }
                            SpecialWatch::Registers => {
                                self.eval_registers(context, node_idx, palette);
                                "registers"
                            }
                            SpecialWatch::RegistersGroup => {
                                self.eval_registers_group(context, node_idx, palette);
                                "registers"
                            }
                            SpecialWatch::AddWatch => panic!("huh"),
                        };
                        let end = self.tree.nodes.len();
                        let node = &mut self.tree.nodes[node_idx.0];
                        node.children = start..end;
                        if node.children.is_empty() && node.formatted_value[1].is_none() {
                            let l = styled_writeln!(self.tree.text, palette.default_dim, "no {}", what);
                            node.formatted_value[1] = Some(l..l+1);
                        }
                    }
                }
            }
            (&None, Err(e)) => {
                let style = if !suspended {
                    palette.default_dim
                } else if e.is_too_long() {
                    palette.warning
                } else {
                    palette.error
                };
                let l = styled_writeln!(self.tree.text, style, "<{}>", e);
                node.formatted_value[0] = Some(l..l+1);
                node.formatted_value[1] = Some(l..l+1);
            }
            (&None, Ok(value)) => {
                let (has_children, children, click_action) = format_value(value, node.expanded, &mut self.eval_state, context, &mut self.tree.temp_text, &mut self.tree.text, palette);
                let l = self.tree.temp_text.close_line();
                let l = self.tree.text.import_lines(&self.tree.temp_text, l..l+1);
                node.formatted_value[i] = Some(l);
                node.has_children = has_children;
                node.click_action = click_action;

                if i == 1 {
                    let dubious = node.dubious;
                    let start = self.tree.nodes.len();
                    for c in children {
                        self.tree.add(ValueTreeNode {name: c.name_line..c.name_line+1, identity: c.identity, value: c.value, child_kind: c.kind, deref: c.deref, dubious, parent: node_idx, ..D!()});
                    }
                    let end = self.tree.nodes.len();
                    self.tree.nodes[node_idx.0].children = start..end;
                }
            }
        }
    }

    fn do_layout(&mut self, context: &mut EvalContext, suspended: bool, palette: &Palette, frame_idx: usize) -> usize {
        self.cursor_idx = 0;
        self.tree.rows.clear();
        let mut y = 0isize;
        let mut stack: Vec<(ValueTreeNodeIdx, u8)> = self.tree.roots.iter().map(|i| (*i, 0)).rev().collect();
        while let Some((node_idx, pass)) = stack.pop() {
            let node = &mut self.tree.nodes[node_idx.0];
            if pass == 1 {
                node.subtree_end_y = y;
                continue;
            }
            let row_idx = self.tree.rows.len();
            self.tree.rows.push(node_idx);
            node.layout_frame_idx = frame_idx;
            node.start_y = y;
            node.expanded = self.expanded_nodes.contains(&node.identity);
            node.is_text_input = self.text_input.as_ref().is_some_and(|(identity, _, _)| *identity == node.identity);
            if self.cursor_path.get(node.depth) == Some(&node.identity) {
                self.cursor_idx = row_idx;
            }

            // Calculate height. If expanded, this requires formatting the value and doing line wrap.
            let mut height = node.name.len().max(1);
            if node.is_text_input {
                height.set_max(self.text_input.as_ref().unwrap().1);
            }
            let mut pushed_children_to_stack = false;
            if node.expanded {
                let name_line_wrap_width = self.name_width.saturating_sub(node.depth.min(self.max_indent) * self.indent_width + 2);
                if node.line_wrapped_name.is_some() {
                    assert_eq!(node.name_line_wrap_width, name_line_wrap_width);
                } else {
                    node.name_line_wrap_width = name_line_wrap_width;
                    node.line_wrapped_name = Some(self.tree.text.line_wrap(node.name.clone(), name_line_wrap_width, self.row_height_limit, &palette.line_wrap_indicator, &palette.truncation_indicator, None));
                }
                if !node.is_text_input {
                    // (Note: we do line_wrapped_name calculation above even if is_text_input is true, because the name may be rendered for one frame when the text input loses focus.
                    //  In that case `height` may be incorrect for one frame, in theory causing visible artifact for one frame, but (1) meh, (2) I tried it and couldn't see it, maybe it's too fast or maybe it doesn't happen for some reason.)
                    height.set_max(node.line_wrapped_name.clone().unwrap().len());
                }

                self.ensure_node_info(node_idx, context, suspended, palette);
                let node = &mut self.tree.nodes[node_idx.0];

                if node.formatted_value[2].is_none() && node.formatted_value[1].is_some() {
                    node.formatted_value[2] = Some(self.tree.text.line_wrap(node.formatted_value[1].clone().unwrap(), self.value_width, self.row_height_limit, &palette.line_wrap_indicator, &palette.truncation_indicator, None));
                }
                if let Some(v) = &node.formatted_value[2] {
                    height.set_max(v.len());
                }

                if node.has_children && !node.children.is_empty() {
                    pushed_children_to_stack = true;
                    stack.push((node_idx, 1));
                    for idx in node.children.clone().rev() {
                        stack.push((ValueTreeNodeIdx(idx), 0));
                    }
                }
            }
            let node = &mut self.tree.nodes[node_idx.0];

            y += height as isize;
            node.node_end_y = y;
            if !pushed_children_to_stack {
                node.subtree_end_y = y;
            }
        }

        y as usize
    }

    fn build_widgets(&mut self, visible_y: Range<isize>, context: &mut EvalContext, suspended: bool, state: &mut UIState, ui: &mut UI) {
        self.text_input_built = false;
        let mut stack: Vec<ValueTreeNodeIdx> = self.tree.roots.iter().copied().rev().collect();
        let mut should_start_editing: Option<usize> = None;
        while let Some(node_idx) = stack.pop() {
            let node = &self.tree.nodes[node_idx.0];
            assert_eq!(node.layout_frame_idx, ui.frame_idx);
            if !node.is_text_input && (node.start_y >= visible_y.end || node.subtree_end_y <= visible_y.start) {
                continue;
            }

            if node.expanded {
                for idx in node.children.clone().rev() {
                    stack.push(ValueTreeNodeIdx(idx));
                }
            }

            let indent = node.depth.min(self.max_indent) * self.indent_width;

            // Order of operations:
            //  1. Format the value and determine whether the node has children.
            //  2. Create indentation arrow+line widget.
            //  3. Create the row widget. It may partially cover the indentation widget if indent width is > 2 cells in palette.
            //    3a. Create value widget.
            //    3b. Create name or text input widget. It may partially cover the value widget if it's a text input.

            let lines = if node.expanded {
                node.formatted_value[2].clone().unwrap()
            } else {
                self.ensure_node_info(node_idx, context, suspended, &ui.palette);
                self.tree.nodes[node_idx.0].formatted_value[0].clone().unwrap()
            };
            let node = &self.tree.nodes[node_idx.0];
            let value_start = ui.text.num_lines();
            ui.text.import_lines(&self.tree.text, lines);
            let value_end = ui.text.num_lines();

            // Draw vertical line showing indentation, and arrow showing whether the node is expanded or expandable.
            // This must be below the `node.has_children` assignment above (where we lazily format the value).
            with_parent!(ui, ui.add(widget!().identity(&('|', node.identity)).fixed_x(indent as isize).fixed_y(node.start_y).fixed_width(1).fixed_height(1).vstack().highlight_on_hover()), {
                if ui.check_mouse(MouseActions::CLICK) {
                    if node.expanded {
                        self.expanded_nodes.remove(&node.identity);
                    } else if &node.special != &Some(SpecialWatch::AddWatch) {
                        self.expanded_nodes.insert(node.identity);
                    }
                    ui.should_redraw = true;
                }

                let arrow = if node.expanded {
                    '▾'
                } else if node.has_children {
                    '▸'
                } else {
                    ' '
                };
                if node.has_children && node.expanded && node.depth < self.max_indent {
                    // Draw the line.
                    let w = ui.cur_mut();
                    w.axes[Axis::X].set_fixed_size(self.indent_width.max(1));
                    w.axes[Axis::Y].set_fixed_size((node.subtree_end_y - node.start_y) as usize);
                    ui.add(widget!().fixed_width(1).fixed_height(1).fill('▾', ui.palette.default));
                    let line = if node.depth + 1 < self.max_indent {
                        styled_writeln!(ui.text, ui.palette.tree_indent.1, "{}", ui.palette.tree_indent.0)
                    } else {
                        styled_writeln!(ui.text, ui.palette.tree_indent_limit_reached.1, "{}", ui.palette.tree_indent_limit_reached.0)
                    };
                    ui.add(widget!().text(line).flags(WidgetFlags::REPEAT_TEXT_VERTICALLY));
                } else {
                    let s = ui.palette.default;
                    ui.cur_mut().draw_fill = Some((arrow, s));
                }
            });

            if node.node_end_y > visible_y.start {
                let row_x = indent + 2;
                let row_widget = ui.add(widget!().identity(&node.identity).fixed_x(row_x as isize).fixed_width((self.name_width + self.value_width + Self::COLUMN_SPACING).saturating_sub(row_x)).fixed_height((node.node_end_y - node.start_y) as usize).fixed_y(node.start_y).fill(' ', ui.palette.default).highlight_on_hover());
                with_parent!(ui, row_widget, {
                    if self.cursor_path.last() == Some(&node.identity) {
                        let a = ui.palette.selected;
                        ui.cur_mut().style_adjustment.update(a);
                        ui.focus();

                        if let Some(tooltip) = ui.check_tooltip() {
                            if self.text_input.is_none() {
                                with_parent!(ui, tooltip, {
                                    ui.cur_mut().axes[Axis::Y].flags.insert(AxisFlags::STACK);

                                    let start = ui.text.num_lines();
                                    ui.text.import_lines(&self.tree.text, node.name.clone());
                                    ui_writeln!(ui, default_dim, "──────────");
                                    ui.text.import_lines(&self.tree.text, node.formatted_value[node.expanded as usize].clone().unwrap());

                                    let lines = start..ui.text.num_lines();
                                    let width = ui.text.widest_line(lines.clone());
                                    ui.add(widget!().height(AutoSize::Text).text_lines(lines).flags(WidgetFlags::LINE_WRAP));

                                    let max_width = ui.cur().axes[Axis::X].max_size;
                                    ui.cur_mut().axes[Axis::X].set_fixed_size(width.min(max_width));
                                });
                            }
                        }
                    }

                    let node = &self.tree.nodes[node_idx.0];

                    let name_effective_width = self.name_width.saturating_sub(row_x);

                    let mut w = widget!().fixed_x((name_effective_width + Self::COLUMN_SPACING) as isize).fixed_width(self.value_width).text_lines(value_start..value_end);
                    if node.dubious || !suspended {
                        w.style_adjustment.update(ui.palette.value_dubious);
                    }
                    ui.add(w);

                    if let Ok(Some((addr, size))) = Self::get_value_addr_and_size_for_data_breakpoint(&node.value, Ok(context)) {
                        if let Some(&(enabled, active, stop_on_read, conditional, hit)) = self.data_breakpoints.get(&(addr, size)) {
                            let l = if hit {
                                ui_writeln!(ui, instruction_pointer, "{}", "⮕ ")
                            } else {
                                let bp = get_breakpoint_icon(enabled, active, /*secondary*/ false, conditional, /*data*/ true, stop_on_read, &ui.palette);
                                styled_writeln!(ui.text, bp.1, "{}", bp.0)
                            };
                            ui.add(widget!().fixed_x(name_effective_width as isize + 1).fixed_width(2).text(l));
                        }
                    }

                    let mut clicked_name = false;
                    if node.is_text_input && ui.check_focus() {
                        let (identity, height, input) = self.text_input.as_mut().unwrap();
                        assert_eq!(*identity, node.identity);
                        let input_widget = ui.add(widget!().identity(&'i').width(AutoSize::Children).min_width(name_effective_width).max_width(name_effective_width + self.value_width + Self::COLUMN_SPACING).height(AutoSize::Children).max_height(self.row_height_limit));
                        with_parent!(ui, input_widget, {
                            ui.relative_focus(row_widget);
                            let changed = input.build(ui);
                            self.scroll_to_cursor |= changed && (visible_y.start > node.start_y || visible_y.end < node.node_end_y);
                            self.text_input_built = true;
                        });
                        let new_height = ui.calculate_size(input_widget, Axis::Y);
                        if new_height != *height {
                            *height = new_height;
                            self.scroll_to_cursor = true;
                            ui.should_redraw = true;
                        }
                    } else {
                        clicked_name = ui.check_mouse(MouseActions::CLICK);
                        let lines = if node.expanded {
                            assert_eq!(node.name_line_wrap_width, name_effective_width);
                            node.line_wrapped_name.clone().unwrap()
                        } else {
                            node.name.clone()
                        };
                        let lines = ui.text.import_lines(&self.tree.text, lines);
                        let mut w = widget!().text_lines(lines).fixed_width(name_effective_width);
                        // Dim the *name* if parent's value is dubious, i.e. the existence of this node is dubious.
                        if node.depth > 0 && (self.tree.nodes[node.parent.0].dubious || !suspended) {
                            w.style_adjustment.update(ui.palette.value_dubious);
                        }
                        ui.add(w);
                    }

                    if ui.check_mouse(MouseActions::CLICK_SUBTREE) {
                        let moved = Self::set_cursor_path_from_node(node_idx, &mut self.cursor_path, &self.tree);
                        if !node.click_action.is_none() {
                            Self::perform_click_action(&node.click_action, context.symbols_registry, state, ui);
                        } else if !moved && clicked_name && node.depth == 0 {
                            if let Some(expr_idx) = self.tree.roots.iter().position(|ix| *ix == node_idx) {
                                if self.expressions[expr_idx].is_editable() {
                                    // Can't assign self.text_input right here because a later iteration of this loop may incorrectly use it.
                                    should_start_editing = Some(expr_idx);
                                }
                            }
                        }
                        ui.should_redraw = true;
                    }
                });
            }
        }

        if let Some(expr_idx) = should_start_editing {
            let expr = &self.expressions[expr_idx];
            Self::start_editing_expression(&self.tree.nodes[self.tree.roots[expr_idx].0], expr, &mut self.text_input);
            self.text_input_built = true; // prevent the caller from closing the text input immediately
            ui.should_redraw = true;
        }
    }

    // Returns false if the cursor was already on this node.
    fn set_cursor_path_from_node(mut node_idx: ValueTreeNodeIdx, cursor_path: &mut Vec<usize>, tree: &ValueTree) -> bool {
        let mut new_path: Vec<usize> = Vec::new();
        while node_idx.is_valid() {
            let node = &tree.nodes[node_idx.0];
            new_path.push(node.identity);
            node_idx = node.parent;
        }
        new_path.reverse();
        if new_path == *cursor_path {
            return false;
        }
        *cursor_path = new_path;
        true
    }

    fn perform_click_action(action: &ValueClickAction, symbols_registry: &SymbolsRegistry, state: &mut UIState, ui: &mut UI) {
        match action {
            ValueClickAction::None => panic!("huh"),
            ValueClickAction::CodeLocation(line) => {
                let target = SourceScrollTarget {path: line.path.clone(), version: line.version.clone(), line: line.line.line(), cascade: true};
                state.should_scroll_source = Some((Some(target), /*only_if_on_error_tab*/ false));
                ui.should_redraw = true;
            }
            &ValueClickAction::Function {binary_id, function_idx, static_addr} => {
                let target = DisassemblyScrollTarget {binary_id, function_idx, static_pseudo_addr: static_addr, subfunction_level: 0, cascade: true};
                state.should_scroll_disassembly = Some((Ok(target), /*only_if_on_error_tab*/ false));
                ui.should_redraw = true;
            }
        }
    }

    fn start_editing_expression(node: &ValueTreeNode, expr: &WatchExpression, text_input: &mut Option<(usize, usize, TextInput)>) {
        let height_estimate = (node.node_end_y - node.start_y).max(1) as usize;
        let text = if expr.special.is_some() {String::new()} else {expr.text.clone()};
        *text_input = Some((node.identity, height_estimate, TextInput::new_multiline(text)));
    }

    fn make_expression_for_tree_node(&self, mut node_idx: ValueTreeNodeIdx) -> Option<String> {
        let mut components: Vec<(/*deref*/ usize, /*suffix*/ String)> = Vec::new();
        loop {
            let node = &self.tree.nodes[node_idx.0];
            if node.name.is_empty() {
                return None;
            }
            let name = self.tree.text.get_line_str(node.name.start);
            if node.depth == 0 {
                if node.special.is_some() {
                    return None;
                }
                match adjust_expression_for_appending_child_path(name) {
                    Err(_) => return None,
                    Ok(s) => components.push((0, s)),
                }
                break;
            }
            let parent = &self.tree.nodes[node.parent.0];
            match &parent.special {
                Some(SpecialWatch::Locals) => {
                    components.push((0, make_expression_for_variable(name)));
                    break;
                }
                Some(SpecialWatch::Registers) | Some(SpecialWatch::RegistersGroup) => {
                    if node.special == Some(SpecialWatch::RegistersGroup) {
                        return None;
                    }
                    components.push((0, format!("{}.#x", name)));
                    break;
                }
                Some(SpecialWatch::AddWatch) => return None,
                None => (),
            }
            match node.child_kind {
                ValueChildKind::StructField => components.push((0, format!(".{}", name))),
                ValueChildKind::ArrayElement(i) => components.push((node.deref, format!("[{}]", i))),
                ValueChildKind::ArrayTail(i) => return None, // TODO: add [i..] syntax
                ValueChildKind::Other => return None,
            }

            node_idx = node.parent;
        }
        components.reverse();
        let mut res = components[0].1.clone();
        for (deref, suffix) in &components[1..] {
            if *deref != 0 {
                res = format!("({}{})", "*".to_string().repeat(*deref), res);
            }
            res.push_str(suffix);
        }
        Some(res)
    }

    fn make_value_ref_expression_for_tree_node(value: &Result<Value>, state: &mut UIState, debugger: &mut Debugger) -> Result<Option<String>> {
        let (addr, t) = match Self::get_value_addr_and_type(value, Err(debugger))? {
            Some(x) => x,
            None => return Ok(None) };
        let mut type_name = String::new();
        print_type_in_watch_language_syntax(t, &mut type_name, 0)?;
        let expr = format!("*(0x{:x} as *{})", addr, type_name);
        Ok(Some(expr))
    }

    fn add_watch(&mut self, s: String, refresh_data: &mut bool) {
        let mut i = self.expressions.len();
        if self.expressions.last().is_some_and(|e| &e.special == &Some(SpecialWatch::AddWatch)) {
            i -= 1;
        }
        let identity: usize = random();
        self.expressions.insert(i, WatchExpression {identity, text: s, special: None});
        self.cursor_path = vec![identity];
        *refresh_data = true;
    }

    // If the value shown for a node comes from dereferencing some memory address, returns that address and data type.
    fn get_value_addr_and_type(value: &Result<Value>, eval_context: std::result::Result<&mut EvalContext, &mut Debugger>) -> Result<Option<(usize, *const TypeInfo)>> {
        let value = match value {
            Ok(x) => x,
            Err(_) => return Ok(None), // error is already shown in UI
        };
        let mut addr = match &value.val {
            &AddrOrValueBlob::Addr(x) => x,
            AddrOrValueBlob::Blob(_) => return err!(Usage, "value is not in memory"),
        };
        let mut t = value.type_;
        match unsafe {&(*t).t} {
            Type::Pointer(p) if p.flags.contains(PointerFlags::REFERENCE) => {
                addr = match eval_context {
                    Ok(ctx) => ctx.memory.read_usize(addr)?,
                    // The call site that does at most one call per frame doesn't have EvalContext at hand (with CachedMemReader), so we fall back to uncached memory read.
                    Err(debugger) => debugger.memory.read_u64(addr)? as usize,
                };
                t = p.type_;
            }
            _ => () }

        Ok(Some((addr, t)))
    }

    fn get_value_addr_and_size_for_data_breakpoint(value: &Result<Value>, eval_context: std::result::Result<&mut EvalContext, &mut Debugger>) -> Result<Option<(usize, u8)>> {
        match Self::get_value_addr_and_type(value, eval_context) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some((addr, t))) => {
                let size = unsafe {(*t).calculate_size()};
                if [1, 2, 4, 8].contains(&size) {
                    Ok(Some((addr, size as u8)))
                } else {
                    return err!(Usage, "unsupported size: {} bytes (must be 1, 2, 4, or 8)", size);
                }
            }
        }
    }
    
    fn toggle_data_breakpoint(value: &Result<Value>, stop_on_read: bool, edit_condition: bool, state: &mut UIState, debugger: &mut Debugger, ui: &mut UI) -> Result<()> {
        let (addr, size) = match Self::get_value_addr_and_size_for_data_breakpoint(value, Err(debugger))? {
            Some(x) => x,
            None => return Ok(()) };

        ui.should_redraw = true;

        let mut existing = None;
        for (id, breakpoint) in debugger.breakpoints.iter() {
            if let BreakpointOn::Data(d) = &breakpoint.on {
                if d.addr == addr && d.size == size {
                    existing = Some((id, d.stop_on_read));
                    break;
                }
            }
        }
        let id = if let Some((id, existing_stop_on_read)) = existing {
            if stop_on_read != existing_stop_on_read {
                debugger.set_data_breakpoint_stop_on_read(id, stop_on_read)?;
            } else if !edit_condition {
                debugger.remove_breakpoint(id);
                return Ok(());
            }
            id
        } else {
            debugger.add_breakpoint(BreakpointOn::Data(DataBreakpoint {addr, size, stop_on_read}))?
        };
        if edit_condition {
            state.should_edit_breakpoint_condition = Some(id);
        }
        Ok(())
    }

    fn build_variable_search_dialog(&mut self, create: bool, refresh_data: &mut bool, state: &mut UIState, debugger: &mut Debugger, ui: &mut UI) {
        let dialog_widget = match make_dialog_frame(create, AutoSize::Remainder(0.75), AutoSize::Remainder(0.83), ui.palette.dialog, ui.palette.field_name, "find global variable", ui) {
            None => {
                self.variable_search_dialog = None;
                return;
            }
            Some(x) => x };

        let d = self.variable_search_dialog.get_or_insert_with(|| SearchDialog::new(Arc::new(GlobalVariableSearcher), debugger.context.clone()));
        with_parent!(ui, dialog_widget, {
            d.build(&debugger.symbols, ui);
        });

        if d.should_close_dialog {
            ui.close_dialog();
        }

        if let Some(res) = mem::take(&mut d.should_open_document) {
            self.add_watch(make_expression_for_variable(&format!("::{}", res.name)), refresh_data);
        }
    }

    fn build_type_search_dialog(&mut self, create: bool, refresh_data: &mut bool, state: &mut UIState, debugger: &mut Debugger, ui: &mut UI) {
        let dialog_widget = with_parent!(ui, ui.add(widget!().identity("ts").fixed_width(0).fixed_height(0)), { // the two potential dialogs must have different owner widgets
            make_dialog_frame(create, AutoSize::Remainder(0.75), AutoSize::Remainder(0.83), ui.palette.dialog, ui.palette.type_name, "find type", ui)
        });
        let dialog_widget = match dialog_widget {
            None => {
                self.type_search_dialog = None;
                return;
            }
            Some(x) => x };

        let d = self.type_search_dialog.get_or_insert_with(|| SearchDialog::new(Arc::new(TypeSearcher), debugger.context.clone()));
        with_parent!(ui, dialog_widget, {
            d.build(&debugger.symbols, ui);
        });

        if d.should_close_dialog {
            ui.close_dialog();
        }

        if let Some(res) = mem::take(&mut d.should_open_document) {
            self.add_watch(format!("type({})", make_expression_for_variable(&res.name)), refresh_data);
        }
    }
}

impl WindowContent for WatchesWindow {
    fn build(&mut self, state: &mut UIState, debugger: &mut Debugger, ui: &mut UI) {
        // Plan:
        //  1. Handle expand/collapse/edit-start/edit-stop inputs using last frame rows and tree.
        //  2. Recalculate the tree if needed.
        //  3. Recalculate layout and rows list if needed.
        //  4. Handle cursor movement and scrolling. Now we know which rows are visible.
        //  5. Build widgets for visible rows (and for selected row with text input, even if not visible).

        // Keyboard input.
        let mut refresh_data = self.tree.roots.is_empty();
        let (mut open_variable_search, mut open_type_search) = (false, false);
        for action in ui.check_keys(&[KeyAction::Cancel, KeyAction::CursorRight, KeyAction::CursorLeft, KeyAction::Enter, KeyAction::DeleteRow, KeyAction::DuplicateRow, KeyAction::AddValueRefWatch, KeyAction::ReorderRowUp, KeyAction::ReorderRowDown, KeyAction::Open, KeyAction::FindType, KeyAction::DataWriteBreakpoint, KeyAction::DataReadWriteBreakpoint, KeyAction::ConditionalDataWriteBreakpoint, KeyAction::ConditionalDataReadWriteBreakpoint]) {
            self.scroll_to_cursor = true;

            if action == KeyAction::Cancel {
                self.text_input = None;
                continue;
            }

            let node_idx = match self.tree.rows.get(self.cursor_idx) {
                None => continue,
                Some(x) => *x };
            let node = &self.tree.nodes[node_idx.0];
            let expr_idx = if node.depth == 0 {
                self.tree.roots.iter().position(|ix| *ix == node_idx)
            } else {
                None
            };
            match action {
                // We allow expanding even nodes without children, to enable line wrapping. Currently we have no indication of that, would be nice to check whether the text fits and allow expanding only if it doesn't.
                KeyAction::CursorRight if &node.special != &Some(SpecialWatch::AddWatch) => {self.expanded_nodes.insert(node.identity);}
                KeyAction::CursorLeft => {
                    self.expanded_nodes.remove(&node.identity);
                    if node.depth > 0 && !node.expanded {
                        self.expanded_nodes.remove(&self.tree.nodes[node.parent.0].identity);
                    }
                }
                KeyAction::Enter if expr_idx.is_some_and(|i| self.expressions[i].is_editable()) => {
                    let expr = &mut self.expressions[expr_idx.unwrap()];
                    if let Some((identity, _, input)) = &mut self.text_input {
                        if node.identity == *identity {
                            expr.text = input.text.clone();
                            let empty = expr.text.is_empty();
                            expr.special = None;
                            let i = expr_idx.unwrap();
                            if i + 1 < self.expressions.len() {
                                self.cursor_path = vec![self.expressions[i+1].identity];
                            }

                            if empty {
                                self.expressions.remove(i);
                                self.tree.roots.remove(i);
                            } else {
                                refresh_data = true;
                            }
                        }
                        self.text_input = None;
                    } else {
                        Self::start_editing_expression(node, &self.expressions[expr_idx.unwrap()], &mut self.text_input);
                    }
                }
                KeyAction::Enter if !node.click_action.is_none() => {
                    Self::perform_click_action(&node.click_action, &debugger.symbols, state, ui);
                }
                KeyAction::Enter | KeyAction::DuplicateRow | KeyAction::AddValueRefWatch => {
                    let s = if action == KeyAction::DuplicateRow && expr_idx.is_some() {
                        let e = &self.expressions[expr_idx.clone().unwrap()];
                        if e.special.is_none() {
                            Some(e.text.clone())
                        } else {
                            None
                        }
                    } else if action == KeyAction::AddValueRefWatch {
                        let r = Self::make_value_ref_expression_for_tree_node(&self.tree.nodes[node_idx.0].value, state, debugger);
                        report_result(state, &r);
                        r.ok().flatten()
                    } else {
                        self.make_expression_for_tree_node(node_idx)
                    };
                    if let Some(s) = s {
                        self.add_watch(s, &mut refresh_data);
                    }
                }
                KeyAction::ReorderRowUp | KeyAction::ReorderRowDown => if let &Some(i) = &expr_idx {
                    if self.expressions[i].special.is_none() {
                        let j = i as isize + if action == KeyAction::ReorderRowUp {-1} else {1};
                        if j >= 0 && j < self.expressions.len() as isize && self.expressions[j as usize].special.is_none() {
                            self.expressions.swap(i, j as usize);
                            refresh_data = true;
                        }
                    }
                }
                KeyAction::DeleteRow if expr_idx.is_some_and(|i| self.expressions[i].special.is_none()) => {
                    let i = expr_idx.unwrap();
                    self.expressions.remove(i);
                    self.tree.roots.remove(i); // this way we don't have to refresh_data
                    if !self.expressions.is_empty() {
                        self.cursor_path = vec![self.expressions[i.min(self.expressions.len()-1)].identity];
                    }
                }
                KeyAction::DataWriteBreakpoint | KeyAction::DataReadWriteBreakpoint | KeyAction::ConditionalDataWriteBreakpoint | KeyAction::ConditionalDataReadWriteBreakpoint => {
                    let stop_on_read = action == KeyAction::DataReadWriteBreakpoint || action == KeyAction::ConditionalDataReadWriteBreakpoint;
                    let conditional = action == KeyAction::ConditionalDataWriteBreakpoint || action == KeyAction::ConditionalDataReadWriteBreakpoint;
                    let r = Self::toggle_data_breakpoint(&node.value, stop_on_read, conditional, state, debugger, ui);
                    report_result(state, &r);
                }
                KeyAction::Open => open_variable_search = true,
                KeyAction::FindType => open_type_search = true,
                _ => (),
            }
        }

        open_type_search &= !open_variable_search;
        self.build_variable_search_dialog(open_variable_search, &mut refresh_data, state, debugger, ui);
        self.build_type_search_dialog(open_type_search, &mut refresh_data, state, debugger, ui);

        // Add the "<add watch>" placeholder watch.
        if self.expressions.iter().position(|e| &e.special == &Some(SpecialWatch::AddWatch)).is_none() {
            let identity: usize = random();
            self.expressions.push(WatchExpression {identity, text: "<add watch>".to_string(), special: Some(SpecialWatch::AddWatch)});
            self.cursor_path = vec![identity];
            refresh_data = true;
        }

        let mut suspended = false;
        let mut stop_count = 0usize;
        if let Some(thread) = debugger.threads.get(&state.selected_thread) {
            if thread.state == ThreadState::Suspended && !state.stack.frames.is_empty() {
                suspended = true;
                stop_count = thread.stop_count;
            }
        }
        let t = (state.selected_thread, state.selected_subframe, stop_count, debugger.target_state);
        if t != self.seen {
            self.seen = t;
            if suspended || !self.have_good_cached_values {
                refresh_data = true;
            }
        }
        let stack = state.stack.clone();
        let mut eval_context = debugger.make_eval_context(&stack, state.selected_subframe, state.selected_thread);

        // Recalculate everything if needed.
        if refresh_data {
            self.tree.clear();
            self.eval_state.clear();
            self.scroll_to_cursor = true;
            self.have_good_cached_values = suspended;

            self.eval_watches(&mut eval_context, &ui.palette);
        }

        // Get data breakpoints info.
        self.data_breakpoints.clear();
        for (id, bp) in debugger.breakpoints.iter() {
            if let BreakpointOn::Data(d) = &bp.on {
                let hit = state.hit_breakpoints.binary_search(&id).is_ok();
                self.data_breakpoints.insert((d.addr, d.size), (bp.enabled, bp.active, d.stop_on_read, bp.condition.is_some(), hit));
            }
        }

        // Create container widgets.
        ui.cur_mut().set_hstack();
        let header_and_viewport = ui.add(widget!().width(AutoSize::Remainder(1.0)).vstack());
        let scroll_bar = ui.add(widget!().fixed_width(1));
        ui.layout_children(Axis::X);
        let viewport_width = ui.calculate_size(header_and_viewport, Axis::X);
        let calculate_name_width = |viewport_width: usize, name_relative_width: f64| -> usize {
            (viewport_width as f64 * name_relative_width + 0.5) as usize
        };
        let mut name_width = calculate_name_width(viewport_width, self.name_relative_width);
        let value_width;
        let viewport;
        with_parent!(ui, header_and_viewport, {
            if !ui.check_focus() {
                self.text_input = None;
            }
            ui.focus();

            with_parent!(ui, ui.add(widget!().fixed_height(1)), {
                let l = ui_writeln!(ui, table_header, "  name");
                let name_header = ui.add(widget!().text(l).fixed_width(name_width));

                let l = ui_writeln!(ui, default_dim, "|");
                with_parent!(ui, ui.add(widget!().text(l).fixed_width(1).fixed_x(name_width as isize + 1)), {
                    ui.cur_mut().flags.insert(WidgetFlags::HIGHLIGHT_ON_HOVER);
                    if let Some(p) = ui.check_drag_out(DragWhat::NoDrop) {
                        // Update name_width and move widgets right here. Can't just use should_redraw
                        // as that would cause flicker because drag_out would use coordinates one frame out of date.
                        name_width = ((name_width as isize + p[Axis::X]).max(0) as usize).min(viewport_width.saturating_sub(Self::COLUMN_SPACING));
                        self.name_relative_width = name_width as f64 / viewport_width.max(1) as f64;
                        assert_eq!(calculate_name_width(viewport_width, self.name_relative_width), name_width as usize);

                        ui.cur_mut().axes[Axis::X].rel_pos = name_width as isize + 1;
                        ui.get_mut(name_header).axes[Axis::X].size = name_width;
                    }
                });

                value_width = viewport_width.saturating_sub(name_width + Self::COLUMN_SPACING);
                let l = ui_writeln!(ui, table_header, "value");
                ui.add(widget!().text(l).fixed_width(value_width).fixed_x((name_width + Self::COLUMN_SPACING) as isize));
            });

            viewport = ui.add(widget!().height(AutoSize::Remainder(1.0)));
            ui.layout_children(Axis::Y);
        });
        let indent_width = str_width(&ui.palette.tree_indent.0).max(1);
        let max_indent = name_width / 2 / indent_width;
        let row_height_limit = ui.calculate_size(viewport, Axis::Y);

        if (name_width, value_width, indent_width, max_indent, row_height_limit) != (self.name_width, self.value_width, self.indent_width, self.max_indent, self.row_height_limit) {
            (self.name_width, self.value_width, self.indent_width, self.max_indent, self.row_height_limit) = (name_width, value_width, indent_width, max_indent, row_height_limit);
            self.scroll_to_cursor = true;

            // Clear line wrapping cache.
            for node in &mut self.tree.nodes {
                node.line_wrapped_name = None;
                node.formatted_value[2] = None;
            }
        }

        // Determine positions and sizes of all nodes, do line wrapping (unless cached). Also assign cursor_idx.
        // We currently do this on each frame because determining if anything changed would be error-prone.
        let content_height = self.do_layout(&mut eval_context, suspended, &ui.palette, ui.frame_idx);

        // Do cursor movement and scrolling.
        let visible_y: Range<isize>;
        let content_widget;
        let root_widget = ui.cur_parent;
        with_parent!(ui, viewport, {
            content_widget = ui.add(widget!().fixed_height(content_height));

            ui.focus();
            self.scroll_to_cursor |= list_cursor_navigation_with_variable_row_height(&mut self.cursor_idx, self.tree.rows.len(), |i, ui| {
                let n = &self.tree.nodes[self.tree.rows[i].0];
                (n.node_end_y - n.start_y) as usize
            }, ui);

            let scroll_to = if mem::take(&mut self.scroll_to_cursor) && !self.tree.rows.is_empty() {
                let n = &self.tree.nodes[self.tree.rows[self.cursor_idx].0];
                Some(n.start_y..n.node_end_y)
            } else {
                None
            };
            visible_y = scrolling_navigation(&mut self.scroll, scroll_to, root_widget, scroll_bar, ui);
        });

        // Convert cursor_idx back to cursor_path.
        if !self.tree.rows.is_empty() {
            Self::set_cursor_path_from_node(self.tree.rows[self.cursor_idx], &mut self.cursor_path, &self.tree);
        }

        // Create widgets for visible nodes, handle mouse clicks.
        with_parent!(ui, content_widget, {
            self.build_widgets(visible_y, &mut eval_context, suspended, state, ui);
        });

        if let &Some((identity, _, _)) = &self.text_input {
            // (The second condition is not required because the text input will lose focus on next frame if cursor_path moved away from it. But it saves one frame of latency + one unnecessary redraw.)
            if !self.text_input_built || self.cursor_path.last() != Some(&identity) {
                self.text_input = None;
                ui.should_redraw = true;
            }
        }
        if self.scroll_to_cursor {
            ui.should_redraw = true;
        }
    }

    fn drop_caches(&mut self) {
        self.tree.clear();
        self.eval_state.clear();
        self.seen.2 = usize::MAX;
    }

    fn get_key_hints(&self, out: &mut Vec<KeyHint>, debugger: &Debugger) {
        out.extend([
            KeyHint::key(KeyAction::Enter, "edit/add"),
            KeyHint::keys(&[KeyAction::DuplicateRow, KeyAction::AddValueRefWatch], "copy/ref"),
            KeyHint::keys(&[KeyAction::ReorderRowUp, KeyAction::ReorderRowDown], "reorder"),
            KeyHint::key(KeyAction::DeleteRow, "delete"),
            KeyHint::keys(&[KeyAction::CursorRight, KeyAction::CursorLeft], "expand/collapse"),
            KeyHint::keys(&[KeyAction::Open, KeyAction::FindType], "find variable/type"),
            KeyHint::key(KeyAction::Tooltip, "tooltip"),
            KeyHint::keys(&[KeyAction::DataWriteBreakpoint, KeyAction::DataReadWriteBreakpoint, KeyAction::ConditionalDataWriteBreakpoint, KeyAction::ConditionalDataReadWriteBreakpoint], "data breakpoint w/rw/cond"),
        ]);
    }

    fn save_state(&self, out: &mut Vec<u8>) -> Result<()> {
        out.write_u32((self.name_relative_width.max(0.0).min(1.0) * 1e9) as u32)?;
        for expr in &self.expressions {
            if expr.special.is_none() {
                out.write_u8(1)?;
                out.write_str(&expr.text)?;
            }
        }
        out.write_u8(0)?;
        Ok(())
    }
    fn load_state(&mut self, inp: &mut &[u8]) -> Result<()> {
        self.name_relative_width = inp.read_u32()? as f64 / 1e9;
        while inp.read_u8()? != 0 {
            let text = inp.read_str()?;
            self.expressions.push(WatchExpression {identity: random(), text, special: None});
        }
        Ok(())
    }
}

#[derive(Default)]
struct LocationsWindow {
    table_state: TableState,
}
impl WindowContent for LocationsWindow {
    fn build(&mut self, state: &mut UIState, debugger: &mut Debugger, ui: &mut UI) {
        ui.cur_mut().set_vstack();
        let l = ui_writeln!(ui, default_dim, "(for address selected in disassembly window)");
        ui.add(widget!().text(l).height(AutoSize::Text));
        let table_widget = ui.add(widget!().height(AutoSize::Remainder(1.0)));
        ui.layout_children(Axis::Y);

        with_parent!(ui, table_widget, {
            let mut table = Table::new(mem::take(&mut self.table_state), ui, vec![
                Column::new("name", AutoSize::Remainder(0.25), false),
                Column::new("type", AutoSize::Remainder(0.3), false),
                Column::new("expression", AutoSize::Remainder(0.3), false),
                Column::new("die", AutoSize::Fixed(9), false),
            ]);
            if let Err(e) = self.fill_table(&mut table, state, debugger, ui) {
                table.start_row(hash(&'e'), ui);
                table.empty_cell(ui);
                table.empty_cell(ui);
                ui_writeln!(ui, error, "{}", e);
                table.text_cell(ui);
                table.empty_cell(ui);
            }
            self.table_state = table.finish(ui);
        });
    }

    fn get_key_hints(&self, out: &mut Vec<KeyHint>, debugger: &Debugger) {
        out.extend([
            KeyHint::key(KeyAction::Tooltip, "tooltip"),
        ]);
    }
}

impl LocationsWindow {
    fn fill_table(&mut self, table: &mut Table, state: &mut UIState, debugger: &Debugger, ui: &mut UI) -> Result<()> {
        let (binary_id, function_idx, addr) = match state.selected_addr.clone() { Some(x) => x, None => return Ok(()) };
        let binary = match debugger.symbols.get(binary_id) {
            Some(x) => x,
            None => return err!(ProcessState, "binary not mapped"),
        };
        let static_addr = binary.addr_map.dynamic_to_static(addr);
        let symbols = binary.symbols.as_ref_clone_error()?;
        let function = &symbols.functions[function_idx];
        let encoding = match function.debug_info_offset() {
            Some(off) => symbols.find_unit(off).map(|u| u.unit.header.encoding()),
            None => err!(Internal, "internal error: function has no debug info") /* should be no local variables in this case */ };

        let mut row_idx = 0;
        for level in 0..function.num_levels() {
            for sf in symbols.subfunctions_at_level(level, function) {
                for v in symbols.local_variables_in_subfunction(sf, function.shard_idx()) {
                    if !v.range().contains(&static_addr) {
                        continue;
                    }
                    let expr_str = match v.location.unpack() {
                        VariableLocation::Const(s) => Ok(hexdump(s, 100)),
                        VariableLocation::Unknown => Ok("unknown".to_string()),
                        VariableLocation::Expr(expr) => {
                            match &encoding {
                                Ok(e) => format_dwarf_expression(expr, *e),
                                Err(e) => Err(e.clone())
                            }
                        }
                    };

                    table.start_row(row_idx, ui);
                    row_idx += 1;

                    ui_writeln!(ui, default, "{}", unsafe {v.name()});
                    table.text_cell(ui);

                    print_type_name(v.type_, &mut ui.text, &ui.palette, 0);
                    ui.text.close_line();
                    table.text_cell(ui);

                    match expr_str {
                        Ok(s) => ui_writeln!(ui, default, "{}", s),
                        Err(e) => ui_writeln!(ui, error, "{}", e),
                    };
                    table.text_cell(ui);

                    if let Some(off) = v.debug_info_offset() {
                        ui_writeln!(ui, default, "{:x}", off.0);
                    } else {
                        ui_writeln!(ui, default, "");
                    }
                    table.text_cell(ui);
                }
            }
        }
        Ok(())
    }
}

#[derive(Default)]
struct DisassemblyTab {
    title: String,
    identity: usize,
    ephemeral: bool,

    // Cases:
    //  * locator is None, error is Some - couldn't find function for current address; this is a tab for the error message about that,
    //  * locator is Some, error is Some - couldn't find function, but may try again later (after drop_caches()),
    //  * locator is Some, error is None, cached_function_idx is None - didn't try finding the function yet (loaded from save file) or the Symbols was deloaded,
    //  * locator is Some, error is None, cached_function_idx is Some - found the function is Symbols.
    locator: Option<FunctionLocator>,
    error: Option<Error>,
    cached_function_idx: Option<(/*binary_id*/ usize, /*function_idx*/ usize)>,

    // When moving cursor through disassembly, we automatically scroll source code to the corresponding line.
    // But if the cursor is inside some inlined functions, which of them do we scroll to? This depth number determines that.
    // This indentation level is highlighted.
    selected_subfunction_level: u16,

    area_state: AreaState,
}

struct DisassemblyWindow {
    tabs: Vec<DisassemblyTab>,
    cache: HashMap<(/*binary_id*/ usize, /*function_idx*/ usize), Disassembly>,
    tabs_state: TabsState,
    search_dialog: Option<SearchDialog>,
    go_to_address_bar: SearchBar,
    go_to_address_error: Option<Error>,
    source_scrolled_to: Option<(/*binary_id*/ usize, /*function_idx*/ usize, /*disas_line*/ usize, /*selected_subfunction_level*/ u16)>,
}

impl Default for DisassemblyWindow { fn default() -> Self { Self {tabs: Vec::new(), cache: HashMap::new(), tabs_state: TabsState::default(), search_dialog: None, go_to_address_bar: SearchBar::default(), go_to_address_error: None, source_scrolled_to: None} } }

impl DisassemblyWindow {
    fn open_function(&mut self, target: Result<DisassemblyScrollTarget>, debugger: &Debugger) -> Result<()> {
        let target = match target {
            Ok(x) => x,
            // Ignore requests to open a "symbols are loading" error tab, because such tab would remain after symbols are loaded, and it'd be confusing.
            Err(e) if e.is_loading() => return Ok(()),
            Err(e) => {
                self.tabs.push(DisassemblyTab {identity: random(), error: Some(e), title: "[unknown]".to_string(), ephemeral: true, ..Default::default()});
                self.tabs_state.select(self.tabs.len() - 1);
                return Ok(());
            }
        };
        for i in 0..self.tabs.len() {
            if let Some((binary, function_idx)) = self.resolve_function_for_tab(i, debugger) {
                if binary.id == target.binary_id && function_idx == target.function_idx {
                    self.tabs_state.select(i);
                    return Ok(());
                }
            }
        }

        let binary = debugger.symbols.get(target.binary_id).unwrap();
        let symbols = binary.symbols.as_ref_clone_error()?;
        let function = &symbols.functions[target.function_idx];
        let demangled_name = function.demangle_name();
        let title = Self::make_title(&demangled_name);
        self.tabs.push(DisassemblyTab {
            identity: random(), locator: Some(FunctionLocator {binary_locator: binary.locator.clone(), mangled_name: function.mangled_name().to_owned(), addr: function.addr, demangled_name}),
            cached_function_idx: Some((target.binary_id, target.function_idx)), title, ephemeral: true, selected_subfunction_level: u16::MAX, ..Default::default()});
        self.tabs_state.select(self.tabs.len() - 1);

        Ok(())
    }

    fn find_address(&self, mut query: &str, debugger: &Debugger) -> Result<DisassemblyScrollTarget> {
        let relative = query.starts_with("+");
        if relative {
            query = &query[1..];
        }
        if query.starts_with("0x") { query = &query[2..]; }
        if query.ends_with("h") { query = &query[..query.len()-1]; }

        let addr = usize::from_str_radix(query, 16)?;

        if relative {
            let tab = match self.tabs.get(self.tabs_state.selected) {
                Some(x) => x,
                None => return err!(Usage, "no open tab"),
            };
            let (binary_id, function_idx) = match tab.cached_function_idx.clone() {
                Some(x) => x,
                None => return err!(Usage, "no open function"),
            };
            let function_locator = match &tab.locator {
                Some(x) => x,
                None => return err!(Usage, "no open function"),
            };
            Ok(DisassemblyScrollTarget {binary_id, function_idx, static_pseudo_addr: function_locator.addr.0.saturating_add(addr), subfunction_level: u16::MAX, cascade: true})
        } else {
            let (static_addr, binary) = match debugger.addr_to_binary(addr) {
                Ok((_, static_addr, binary, _)) => (static_addr, binary),
                Err(err) => {
                    // Search in unmapped binaries too, in particular if the program is not running.
                    let mut binary: Option<&Binary> = None;
                    for bin in debugger.symbols.iter() {
                        if bin.is_mapped {
                            continue;
                        }
                        let elves = match bin.elves.as_ref_clone_error() {
                            Ok(x) => x,
                            Err(e) if e.is_loading() => return Err(e),
                            Err(_) => continue,
                        };
                        if elves[0].addr_to_offset(addr).is_some() {
                            binary = Some(bin);
                            break;
                        }
                    }
                    let binary = binary.ok_or(err)?;
                    (addr, binary)
                }
            };
            let symbols = binary.symbols.as_ref_clone_error()?;
            let (function, function_idx) = symbols.addr_to_function(static_addr)?;
            Ok(DisassemblyScrollTarget {binary_id: binary.id, function_idx, static_pseudo_addr: static_addr, subfunction_level: u16::MAX, cascade: true})
        }
    }

    fn make_title(mut demangled_name: &str) -> String {
        rust_remove_function_name_hash_suffix(&mut demangled_name);
        // Some crude approximation of removing namespaces and parent classes.
        let mut res = demangled_name;
        let first_template = demangled_name.char_indices().find(|(_, c)| *c == '<');
        if let Some((last_ns, _)) = demangled_name.char_indices().rev().find(|(_, c)| *c == ':') {
            let last_template = demangled_name.char_indices().rev().find(|(_, c)| *c == '>');
            if !last_template.is_some_and(|(i, _)| i > last_ns) && last_ns + 1 < demangled_name.len() {
                // E.g. Foo<Bar>::doit  ->  doit
                res = &demangled_name[last_ns+1..];
            } else if let Some((first_template, _)) = first_template {
                if let Some((last_ns_before_templates, _)) = demangled_name[..first_template].char_indices().rev().skip(1).find(|(_, c)| *c == ':') {
                    // E.g. std::__1::nonsense::more_nonsense::bs<std::bs_traits<int> >::frob<std::bs_allocator>  ->  bs<std::bs_traits<int> >::frob<std::bs_allocator>
                    res = &demangled_name[last_ns_before_templates+1..];
                }
            }
        } else if let Some((first_template, _)) = first_template {
            // E.g. foo<Bar>  ->  foo
            if first_template > 0 {
                res = &demangled_name[..first_template];
            }
        }
        let mut i = res.len().min(30);
        while !res.is_char_boundary(i) {
            i += 1;
        }
        let mut r = res[..i].to_string();
        if i < res.len() {
            r += "…";
        }
        r
    }

    fn resolve_function_for_tab<'a>(&mut self, tab_idx: usize, debugger: &'a Debugger) -> Option<(&'a Binary, /*function_idx*/ usize)> {
        let tab = &mut self.tabs[tab_idx];
        if tab.error.is_some() {
            return None;
        }
        let locator = match &mut tab.locator {
            None => return None,
            Some(x) => x };

        let binary = match Debugger::find_binary_fuzzy(&debugger.symbols, &locator.binary_locator) {
            Err(e) => {
                tab.error = Some(e);
                return None;
            }
            Ok(x) => x };
        locator.binary_locator = binary.locator.clone();

        let symbols = match binary.symbols.as_ref() {
            Ok(x) => x,
            Err(e) => {
                tab.error = Some(e.clone());
                return None;
            }
        };

        if let &Some((binary_id, function_idx)) = &tab.cached_function_idx {
            if binary_id == binary.id {
                return Some((binary, function_idx));
            }
            tab.cached_function_idx = None;
        }

        let function_idx = match symbols.find_nearest_function(&locator.mangled_name, locator.addr) {
            Some(x) => x,
            None => {
                tab.error = Some(error!(NoFunction, "function not found: {}", locator.demangled_name));
                return None;
            }
        };

        let function = &symbols.functions[function_idx];
        locator.mangled_name = function.mangled_name().to_vec();
        locator.demangled_name = function.demangle_name();
        locator.addr = function.addr;

        Some((binary, function_idx))
    }

    fn find_or_disassemble_function<'a>(cache: &'a mut HashMap<(usize, usize), Disassembly>, binary: &Binary, function_idx: usize, palette: &Palette) -> &'a Disassembly {
        let indent_width = str_width(&palette.tree_indent.0);
        let e = cache.entry((binary.id, function_idx));
        match e {
            Entry::Occupied(o) if o.get().indent_width == indent_width => o.into_mut(),
            _ => {
                // Would be nice to also support disassembling arbitrary memory, regardless of functions or binaries. E.g. for JIT-generated code.
                let d = match Self::disassemble_function(binary, function_idx, palette) {
                    Ok(d) => d,
                    Err(e) => Disassembly::new().with_error(e, palette),
                };
                match e {
                    Entry::Occupied(mut o) => {
                        *o.get_mut() = d;
                        o.into_mut()
                    }
                    Entry::Vacant(v) => v.insert(d),
                }
            }
        }
    }

    // (Would be nice to also support disassembling arbitrary memory, regardless of functions or binaries. E.g. for JIT-generated code.)
    fn disassemble_function(binary: &Binary, function_idx: usize, palette: &Palette) -> Result<Disassembly> {
        let symbols = binary.symbols.as_ref().unwrap();
        let ranges = symbols.function_addr_ranges(function_idx);
        let function = &symbols.functions[function_idx];

        let mut prelude = StyledText::default();
        styled_write!(prelude, palette.default_dim, "{}", binary.locator.path);
        prelude.close_line();
        match function.debug_info_offset() {
            Some(off) => styled_write!(prelude, palette.default_dim, "dwarf offset: 0x{:x}", off.0),
            None => styled_write!(prelude, palette.default_dim, "function from symtab"),
        }
        prelude.close_line();
        prelude.close_line();
        // TODO: Print declaration site. Scroll code window to it when selected.
        // TODO: Print number of inlined call sites. Allow setting breakpoint on it.

        Ok(disassemble_function(function_idx, ranges, Some(symbols.as_ref()), None, prelude, palette))
    }

    fn close_error_tab(&mut self) -> Option<usize> {
        if self.tabs.is_empty() {
            return None;
        }
        if let Some(i) = self.tabs.iter().position(|t| t.locator.is_none()) {
            self.tabs.remove(i);
            if self.tabs_state.selected == i {
                return None;
            }
            self.tabs_state.closed(i);
        }
        Some(self.tabs_state.selected)
    }

    fn evict_cache(&mut self) {
        if self.cache.len().saturating_sub(self.tabs.len()) > 100 {
            let mut in_use: HashSet<(usize, usize)> = HashSet::new();
            for t in &self.tabs {
                if let Some(x) = t.cached_function_idx.clone() {
                    in_use.insert(x);
                }
            }
            let mut i = 0;
            self.cache.retain(|k, _| {
                if in_use.contains(k) {
                    true
                } else {
                    i += 1;
                    i % 2 == 0
                }
            });
        }
    }

    fn build_search_dialog(&mut self, create: bool, state: &mut UIState, debugger: &mut Debugger, ui: &mut UI) {
        let dialog_widget = match make_dialog_frame(create, AutoSize::Remainder(0.75), AutoSize::Remainder(0.83), ui.palette.dialog, ui.palette.function_name, "find function (by mangled name)", ui) {
            None => {
                self.search_dialog = None;
                return;
            }
            Some(x) => x };

        let d = self.search_dialog.get_or_insert_with(|| SearchDialog::new(Arc::new(FunctionSearcher), debugger.context.clone()));
        with_parent!(ui, dialog_widget, {
            d.build(&debugger.symbols, ui);
        });

        if d.should_close_dialog {
            ui.close_dialog();
        }

        if let Some(res) = mem::take(&mut d.should_open_document) {
            match self.open_function(Ok(DisassemblyScrollTarget {binary_id: res.binary_id, function_idx: res.id, static_pseudo_addr: 0, subfunction_level: u16::MAX, cascade: true}), debugger) {
                Ok(()) => self.tabs[self.tabs_state.selected].ephemeral = false,
                Err(e) => log!(debugger.log, "{}", e),
            }
        }
    }

    // Breakpoint addresses in Debugger may be outdated if the process is not running or if breakpoints weren't activated. This is a crutch to correct for that.
    fn fixup_breakpoint_address(bp: &InstructionBreakpoint, tab: &DisassemblyTab, addr_map: &AddrMap) -> usize {
        if let Some((bp_locator, offset)) = &bp.function {
            if let Some(tab_locator) = &tab.locator {
                if tab_locator.matches_incomplete(bp_locator) {
                    return addr_map.static_to_dynamic(tab_locator.addr.0 + offset);
                }
            }
        }
        bp.addr
    }

    fn toggle_breakpoint(new_breakpoint: InstructionBreakpoint, delete: bool, edit_condition: bool, tab: &DisassemblyTab, addr_map: &AddrMap, state: &mut UIState, debugger: &mut Debugger, ui: &mut UI) {
        ui.should_redraw = true;

        let mut existing_id = None;
        for (id, breakpoint) in debugger.breakpoints.iter() {
            if breakpoint.hidden {
                continue;
            }
            if let BreakpointOn::Instruction(bp) = &breakpoint.on {
                let addr = Self::fixup_breakpoint_address(bp, tab, addr_map);
                if addr == new_breakpoint.addr {
                    existing_id = Some(id);
                }
            } else if let Ok(addrs) = &breakpoint.addrs {
                if existing_id.is_none() && addrs.iter().position(|(a, _)| *a == new_breakpoint.addr).is_some() {
                    existing_id = Some(id);
                }
            }
        }
        if delete {
            if let Some(id) = existing_id {
                debugger.remove_breakpoint(id);
            } else {
                state.last_error = "no breakpoint".to_string();
            }
            return;
        }
        let id = if let Some(id) = existing_id {
            if !edit_condition {
                let enable = !debugger.breakpoints.get(id).enabled;
                let r = debugger.set_breakpoint_enabled(id, enable);
                report_result(state, &r);
            }
            id
        } else {
            let r = debugger.add_breakpoint(BreakpointOn::Instruction(new_breakpoint));
            report_result(state, &r);
            match r {
                Ok(id) => id,
                Err(_) => return,
            }
        };
        if edit_condition {
            state.should_edit_breakpoint_condition = Some(id);
        }
    }

    fn handle_tabs_action(&mut self, action: TabsAction) -> bool {
        if let &TabsAction::Close(idx) = &action {
            if let Some(tab) = self.tabs.get_mut(idx) {
                if tab.ephemeral && tab.locator.is_some() {
                    tab.ephemeral = false;
                    return true;
                }
            }
        }
        self.tabs_state.apply_action(action, &mut self.tabs)
    }

    fn build_tab_content(&mut self, content_root: WidgetIdx, scroll_to_addr: Option<(usize, u16)>, suppress_code_autoscroll: bool, state: &mut UIState, debugger: &mut Debugger, ui: &mut UI) {
        let tab = match self.tabs.get_mut(self.tabs_state.selected) {
            None => return,
            Some(x) => x };

        let start = ui.text.num_lines();
        if let Some(locator) = &tab.locator {
            ui_writeln!(ui, function_name, "{}", locator.demangled_name);
        }

        let r = self.resolve_function_for_tab(self.tabs_state.selected, debugger);
        let tab = self.tabs.get_mut(self.tabs_state.selected).unwrap();
        let (binary, function_idx) = match r {
            None => {
                ui_writeln!(ui, error, "{}", tab.error.as_ref().unwrap());
                let end = ui.text.num_lines();
                with_parent!(ui, content_root, {
                    // Horizontally scrollable error message.
                    build_biscrollable_area_with_header(None, start..end, [0, 0], &mut tab.area_state, ui);
                });
                return;
            }
            Some(x) => x };

        let disas = Self::find_or_disassemble_function(&mut self.cache, binary, function_idx, &ui.palette);

        if let Some((static_pseudo_addr, subfunction_level)) = scroll_to_addr {
            let line = disas.static_pseudo_addr_to_line(static_pseudo_addr).0;
            tab.selected_subfunction_level = subfunction_level;
            tab.area_state.select(line);
        }

        let rel_addr_digits = (((disas.max_abs_relative_addr as f64 + 1.0).log2() / 4.0).ceil() as usize).max(1); // how many hex digits to use in the "<+1abc>" things
        let prefix_width = 2 + 2 + 12+1 + rel_addr_digits+4 + 2 + 1; // ip, breakpoint, addr, rel_addr, jump_indicator, space

        let end = ui.text.num_lines();
        let (content, visible_y) = with_parent!(ui, content_root, {
            build_biscrollable_area_with_header(None, start..end, [prefix_width + disas.widest_line, disas.lines.len()], &mut tab.area_state, ui)
        });

        // Now the cursor position is final.

        let binary = binary.clone();
        let symbols = binary.symbols.as_ref().unwrap();
        let function = &symbols.functions[function_idx];
        assert_eq!(disas.symbols_shard, Some(function.shard_idx()));
        let symbols_shard = &symbols.shards[function.shard_idx()];

        let mut selected_subfunction_identity: Option<u32> = None;
        let mut source_line: Option<SourceScrollTarget> = None;

        if let Some(disas_line) = disas.lines.get(tab.area_state.cursor) {
            let mut cursor_static_addr = disas_line.static_addr;
            let mut source_line_info = disas_line.leaf_line.clone();
            if cursor_static_addr == 0 {
                // If the cursor is in the header, use first instruction address.
                (cursor_static_addr, source_line_info) = match disas.lines.iter().find(|l| l.static_addr != 0) {
                    None => (usize::MAX, None),
                    Some(line) => (line.static_addr, line.leaf_line.clone()),
                }
            }
            let mut cursor_addr = usize::MAX;
            if cursor_static_addr != usize::MAX {
                cursor_addr = binary.addr_map.static_to_dynamic(cursor_static_addr);
                state.selected_addr = Some((binary.id, function_idx, cursor_addr));
            }

            for action in ui.check_keys(&[KeyAction::Enter, KeyAction::DeleteRow, KeyAction::EditCondition, KeyAction::StepToCursor, KeyAction::PreviousLocation, KeyAction::NextLocation]) {
                match action {
                    KeyAction::Enter | KeyAction::DeleteRow | KeyAction::EditCondition | KeyAction::StepToCursor if cursor_addr != usize::MAX => {
                        let offset = cursor_static_addr - function.addr.0;
                        // TODO: For function entry breakpoints use entry_pc instead of start of first range. Figure out how to indicate it in the UI nicely.
                        let new_breakpoint = InstructionBreakpoint {function: Some((tab.locator.clone().unwrap(), offset)), addr: cursor_addr, subfunction_level: tab.selected_subfunction_level};
                        if action == KeyAction::StepToCursor {
                            ui.should_redraw = true;
                            let r = debugger.step_to_cursor(state.selected_thread, BreakpointOn::Instruction(new_breakpoint));
                            report_result(state, &r);
                        } else {
                            Self::toggle_breakpoint(new_breakpoint, action == KeyAction::DeleteRow, action == KeyAction::EditCondition, tab, &binary.addr_map, state, debugger, ui);
                        }
                    }
                    KeyAction::PreviousLocation => tab.selected_subfunction_level = tab.selected_subfunction_level.min(disas_line.subfunction_level).saturating_sub(1),
                    KeyAction::NextLocation => {
                        tab.selected_subfunction_level = tab.selected_subfunction_level.saturating_add(1);
                        if tab.selected_subfunction_level > disas_line.subfunction_level {
                            tab.selected_subfunction_level = u16::MAX;
                        }
                    }
                    _ => (),
                }
            }

            let selected_level = tab.selected_subfunction_level.min(disas_line.subfunction_level);
            if let &Some(mut sf_idx) = &disas_line.subfunction {
                let mut level = disas_line.subfunction_level;
                (sf_idx, level) = symbols.subfunction_ancestor_at_level(sf_idx, level, selected_level.saturating_add(1), function);
                if level == selected_level.saturating_add(1) {
                    source_line_info = Some(symbols_shard.subfunctions[sf_idx].call_line.clone());
                }

                (sf_idx, level) = symbols.subfunction_ancestor_at_level(sf_idx, level, selected_level, function);
                if level == selected_level {
                    selected_subfunction_identity = Some(symbols_shard.subfunctions[sf_idx].identity);
                }
            }
            if let Some(line) = source_line_info {
                let file = &symbols.files[line.file_idx().unwrap()];
                source_line = Some(SourceScrollTarget {path: file.path.to_owned(), version: file.version.clone(), line: line.line(), cascade: false});
            }
        }
        let key = (binary.id, function_idx, tab.area_state.cursor, tab.selected_subfunction_level);
        if self.source_scrolled_to.as_ref() != Some(&key) {
            self.source_scrolled_to = Some(key);
            if !suppress_code_autoscroll {
                if let Some(target) = source_line {
                    state.should_scroll_source = Some((Some(target), false));
                    ui.should_redraw = true;
                }
            }
        }

        let mut ip_lines: Vec<(usize, /*selected*/ bool)> = Vec::new();
        for (idx, frame) in state.stack.frames.iter().enumerate() {
            if frame.binary_id.as_ref().is_ok_and(|b| b == &binary.id) {
                let static_pseudo_addr = frame.pseudo_addr.wrapping_sub(frame.addr_static_to_dynamic);
                let (line, found) = disas.static_pseudo_addr_to_line(static_pseudo_addr);
                if found {
                    ip_lines.push((line, idx == state.selected_frame));
                }
            }
        }
        ip_lines.sort_unstable_by_key(|k| (k.0, !k.1));

        let mut address_breakpoints: Vec<(usize, /*enabled*/ bool, /*location_active*/ bool, /*conditional*/ bool)> = Vec::new();
        for (_, breakpoint) in debugger.breakpoints.iter() {
            match &breakpoint.on {
                BreakpointOn::Instruction(bp) => {
                    let mut location_active = false;
                    if breakpoint.active {
                        let i = debugger.breakpoint_locations.partition_point(|l| l.addr < bp.addr);
                        if i < debugger.breakpoint_locations.len() && debugger.breakpoint_locations[i].addr == bp.addr {
                            location_active = debugger.breakpoint_locations[i].active;
                        }
                    }
                    let addr = Self::fixup_breakpoint_address(bp, tab, &binary.addr_map);
                    address_breakpoints.push((addr, breakpoint.enabled, location_active, breakpoint.condition.is_some()));
                }
                _ => (),
            }
        }
        address_breakpoints.sort_unstable();

        with_parent!(ui, content, {
            let line_range = visible_y.start.max(0) as usize .. (visible_y.end.max(0) as usize).min(disas.lines.len());
            let mut main_ip_line: Option<usize> = None;
            for i in line_range.clone() {
                let line = &disas.lines[i];

                if line.kind == DisassemblyLineKind::Instruction {
                    let addr = binary.addr_map.static_to_dynamic(line.static_addr);

                    // (Comparing line number instead of address because the "instruction pointer" pseudoaddress may be in between instructions.)
                    let ip_idx = ip_lines.partition_point(|x| x.0 < i);
                    if ip_idx == ip_lines.len() || ip_lines[ip_idx].0 != i {
                        ui_write!(ui, default, "  ");
                    } else if ip_lines[ip_idx].1 {
                        main_ip_line = Some(i);
                        ui_write!(ui, instruction_pointer, "⮕ ");
                    } else {
                        ui_write!(ui, additional_instruction_pointer, "⮕ ");
                    }

                    let mut marker = "  ";
                    let mut style = ui.palette.secondary_breakpoint;
                    if line.kind == DisassemblyLineKind::Instruction {
                        let loc_idx = debugger.breakpoint_locations.partition_point(|loc| loc.addr < addr);
                        if loc_idx < debugger.breakpoint_locations.len() {
                            let loc = &debugger.breakpoint_locations[loc_idx];
                            if loc.addr == addr {
                                for b in &loc.breakpoints {
                                    match b {
                                        &BreakpointRef::Id {id, ..} => {
                                            let conditional = debugger.breakpoints.get(id).condition.is_some();
                                            (marker, style) = get_breakpoint_icon(/*enabled*/ true, /*active*/ true, /*secondary*/ true, conditional, /*data*/ false, /*stop_on_read*/ false, &ui.palette);
                                        }
                                        BreakpointRef::Step(_) => (),
                                    }
                                }
                            }
                        }

                        let bp_idx = address_breakpoints.partition_point(|(a, _, _, _)| *a < addr);
                        if bp_idx < address_breakpoints.len() {
                            let &(a, enabled, location_active, conditional) = &address_breakpoints[bp_idx];
                            if a == addr {
                                (marker, style) = get_breakpoint_icon(enabled, location_active, /*secondary*/ false, conditional, /*data*/ false, /*stop_on_read*/ false, &ui.palette);
                            }
                        }
                    }
                    styled_write!(ui.text, style, "{}", marker);

                    let addr_style = if line.is_statement {ui.palette.disas_address_statement} else {ui.palette.disas_address_not_statement};
                    styled_write!(ui.text, addr_style, "{:012x} ", addr);
                    ui_write!(ui, disas_relative_address, "<{: >+1$x}> ", line.relative_addr, rel_addr_digits + 1);
                    ui_write!(ui, disas_jump_arrow, " {} ", line.jump_indicator);

                    assert_eq!(ui.text.unclosed_line_width(), prefix_width);
                } else if line.kind != DisassemblyLineKind::Intro {
                    ui_write!(ui, default, "{:1$}", "", prefix_width);
                }

                // Reserve space for indentation. These characters won't be visible, we'll cover them with clickable vertical-line widgets below.
                if line.subfunction_level != 0 {
                    ui_write!(ui, default, "{:1$}", "", line.subfunction_level as usize * disas.indent_width);
                }

                let l = ui.text.import_lines(&disas.text, i..i+1).start;

                let mut w = widget!().identity(&('l', i)).fixed_height(1).fixed_y(i as isize).text(l).fill(' ', ui.palette.default).flags(WidgetFlags::HSCROLL_INDICATOR_RIGHT).highlight_on_hover();
                if i == tab.area_state.cursor {
                    w.style_adjustment.update(ui.palette.selected);
                }
                if &main_ip_line == &Some(i) {
                    w.style_adjustment.update(ui.palette.ip_line);
                }
                ui.add(w);
            }

            // Draw indentation lines.
            let mut change_subfunction_level = tab.selected_subfunction_level;
            for level in 1.. {
                let mut found = false;
                let mut start = line_range.start;
                while start < line_range.end {
                    let line = &disas.lines[start];
                    if line.subfunction_level < level {
                        start += 1;
                        continue;
                    }
                    found = true;

                    let line_sf_at_cur_level = |line: usize| -> usize {
                        let l = &disas.lines[line];
                        symbols.subfunction_ancestor_at_level(l.subfunction.clone().unwrap(), l.subfunction_level, level, function).0
                    };

                    let cur_sf = line_sf_at_cur_level(start);
                    let mut end = start + 1;
                    while end < line_range.end && disas.lines[end].subfunction_level >= level && line_sf_at_cur_level(end) == cur_sf {
                        end += 1;
                    }

                    let is_selected = selected_subfunction_identity == Some(symbols.shards[function.shard_idx()].subfunctions[cur_sf].identity);
                    let (symbol, style) = if is_selected {&ui.palette.tree_indent_selected} else {&ui.palette.tree_indent};
                    for i in start..end {
                        let mut s = *style;
                        // Manually highlight selected row because there's no transparency.
                        if i == tab.area_state.cursor {
                            s = ui.palette.selected.apply(s);
                        }
                        if &main_ip_line == &Some(i) {
                            s = ui.palette.ip_line.apply(s);
                        }
                        styled_writeln!(ui.text, s, "{}", symbol);
                    }
                    let lines = ui.text.num_lines()-(end-start)..ui.text.num_lines();

                    let w = widget!().identity(&('i', start, level)).fixed_width(disas.indent_width).fixed_x(prefix_width as isize + level as isize - 1).fixed_y(start as isize).fixed_height(end - start).text_lines(lines).highlight_on_hover();
                    with_parent!(ui, ui.add(w), {
                        if ui.check_mouse(MouseActions::CLICK) {
                            change_subfunction_level = level;
                        }
                    });

                    start = end;
                }
                if !found {
                    break;
                }
            }
            if change_subfunction_level != tab.selected_subfunction_level {
                tab.selected_subfunction_level = change_subfunction_level;
                ui.should_redraw = true;
            }
        });
    }
}

impl WindowContent for DisassemblyWindow {
    fn build(&mut self, state: &mut UIState, debugger: &mut Debugger, ui: &mut UI) {
        // First do things that may open or close tabs.

        let mut open_dialog = false;
        for action in ui.check_keys(&[KeyAction::Open, KeyAction::CloseTab, KeyAction::GoToLine, KeyAction::ReorderRowUp, KeyAction::ReorderRowDown]) {
            match action {
                KeyAction::Open if self.search_dialog.is_none() => {
                    open_dialog = true;
                }
                KeyAction::CloseTab => {self.handle_tabs_action(TabsAction::Close(self.tabs_state.selected));}
                KeyAction::ReorderRowUp if self.tabs_state.selected > 0 => {self.handle_tabs_action(TabsAction::Reorder {from_idx: self.tabs_state.selected, to_idx: self.tabs_state.selected - 1});}
                KeyAction::ReorderRowDown => {self.handle_tabs_action(TabsAction::Reorder {from_idx: self.tabs_state.selected, to_idx: self.tabs_state.selected + 2});}
                KeyAction::GoToLine => {
                    self.go_to_address_bar.hide_when_not_editing = true;
                    self.go_to_address_error = None;
                    self.go_to_address_bar.start_editing();
                }
                _ => (),
            }
        }

        self.build_search_dialog(open_dialog, state, debugger, ui);

        ui.cur_mut().set_vstack();
        let tabs_widget = ui.add(widget!().fixed_height(1));
        let go_to_address_bar = ui.add(widget!().fixed_height(0));
        let content_root = ui.add(widget!().height(AutoSize::Remainder(1.0)));

        with_parent!(ui, go_to_address_bar, {
            ui.multifocus();
            if self.go_to_address_bar.editing {
                let mut close = false;
                if ui.check_key(KeyAction::Enter) {
                    if self.go_to_address_bar.text.text.is_empty() {
                        close = true;
                    } else {
                        match self.find_address(&self.go_to_address_bar.text.text, debugger) {
                            Ok(target) => {
                                state.should_scroll_disassembly = Some((Ok(target), /*only_if_on_error_tab*/ false));
                                close = true;
                            }
                            Err(e) => self.go_to_address_error = Some(e),
                        }
                    }
                }
                if close {
                    self.go_to_address_bar.editing = false;
                    self.go_to_address_bar.visible = false;
                } else {
                    let left = ui_writeln!(ui, default_dim, "go to address (hex): ");
                    if let Some(e) = &self.go_to_address_error {
                        ui_write!(ui, error, "{}", e);
                    } else {
                        ui_write!(ui, default_dim, "(+n - relative)");
                    }
                    let right = ui.text.close_line();
                    if self.go_to_address_bar.build(Some(left), Some(right), ui) {
                        self.go_to_address_error = None;
                    }
                }
                if !self.go_to_address_bar.visible {
                    ui.should_redraw = true; // make sure our check_key() request is not active when the bar is not open
                }
            }
        });
        with_parent!(ui, tabs_widget, {ui.multifocus()});
        with_parent!(ui, content_root, {ui.multifocus()});
        ui.layout_children(Axis::Y);

        let mut scroll_to_addr: Option<(usize, u16)> = None;
        let mut suppress_code_autoscroll = false;
        if let Some((target, only_if_on_error_tab)) = mem::take(&mut state.should_scroll_disassembly) {
            let mut tab_to_restore: Option<usize> = None;
            if only_if_on_error_tab {
                tab_to_restore = self.close_error_tab();
            }

            if let Ok(target) = &target {
                suppress_code_autoscroll = !target.cascade;
                if tab_to_restore.is_none() {
                    scroll_to_addr = Some((target.static_pseudo_addr, target.subfunction_level));
                } else {
                    // (Not ideal that we don't scroll when the tab is not selected, but meh.)
                }
            } else {
                suppress_code_autoscroll = true;
            }

            self.open_function(target, debugger).unwrap();

            if let Some(i) = tab_to_restore {
                self.tabs_state.selected = i;
            }
        }

        close_excess_ephemeral_tabs(&mut self.tabs, &mut self.tabs_state, |t| t.ephemeral);
        self.evict_cache();

        // Now the set of tabs is final.

        let tabs_action;
        with_parent!(ui, tabs_widget, {
            let mut tabs = Tabs::new(mem::take(&mut self.tabs_state), ui);
            tabs.allow_reordering = true;
            for tab in &self.tabs {
                let full_title = match &tab.locator {
                    Some(locator) => locator.demangled_name.clone(),
                    None => String::new(),
                };
                tabs.add(Tab {identity: tab.identity, allow_closing: true, short_title: tab.title.clone(), full_title, ephemeral: tab.ephemeral, ..Default::default()}, ui);
            }
            (self.tabs_state, tabs_action) = tabs.finish(ui);
        });

        // Now the selected tab is final.

        // (We'll reassign it below if there's no error.)
        state.selected_addr = state.stack.frames.get(state.selected_frame).and_then(|f| {
            let sf = &state.stack.subframes[f.subframes.end-1];
            match (&f.binary_id, &sf.function_idx) {
                (Ok(b), Ok(function_idx)) => Some((*b, *function_idx, f.pseudo_addr)),
                _ => None,
            }
        });

        self.build_tab_content(content_root, scroll_to_addr, suppress_code_autoscroll, state, debugger, ui);
        
        if self.handle_tabs_action(tabs_action) {
            ui.should_redraw = true;
        }
    }

    fn get_key_hints(&self, out: &mut Vec<KeyHint>, debugger: &Debugger) {
        out.extend([
            KeyHint::key(KeyAction::Open, "find function"),
            KeyHint::key(KeyAction::GoToLine, "go to address"),
            KeyHint::key(KeyAction::CloseTab, "close/pin tab"),
            KeyHint::keys(&[KeyAction::PreviousLocation, KeyAction::NextLocation], "select level"),
            KeyHint::keys(&[KeyAction::ReorderRowUp, KeyAction::ReorderRowDown], "reorder tabs"),
            KeyHint::keys(&[KeyAction::Enter, KeyAction::DeleteRow, KeyAction::EditCondition], "breakpoint").if_not_core_dump(),
            KeyHint::key(KeyAction::StepToCursor, "run to cursor").if_not_core_dump(),
        ]);
    }

    fn save_state(&self, out: &mut Vec<u8>) -> Result<()> {
        for (idx, tab) in self.tabs.iter().enumerate() {
            if tab.ephemeral {
                continue;
            }
            let locator = match &tab.locator {
                None => continue,
                Some(x) => x };
            out.write_u8(if idx == self.tabs_state.selected {2} else {1})?;
            locator.save_state(out)?;
            tab.area_state.save_state(out)?;
            out.write_u16(tab.selected_subfunction_level)?;
        }
        out.write_u8(0)?;
        Ok(())
    }
    fn load_state(&mut self, inp: &mut &[u8]) -> Result<()> {
        loop {
            let select_this_tab = match inp.read_u8()? {
                0 => break,
                2 => true,
                _ => false,
            };
            let locator = FunctionLocator::load_state(inp)?;
            let title = Self::make_title(&locator.demangled_name);
            self.tabs.push(DisassemblyTab {identity: random(), title, locator: Some(locator), error: None, area_state: AreaState::load_state(inp)?, selected_subfunction_level: inp.read_u16()?, ephemeral: false, cached_function_idx: None});
            if select_this_tab {
                self.tabs_state.select(self.tabs.len() - 1);
            }
        }
        // TODO: Prevent scrolling code window before first input.
        Ok(())
    }

    fn drop_caches(&mut self) {
        self.cache.clear();
        for tab in &mut self.tabs {
            if tab.locator.is_some() {
                tab.error = None;
                tab.cached_function_idx = None;
            }
        }
    }
}

fn close_excess_ephemeral_tabs<T, F: FnMut(&T) -> bool>(tabs: &mut Vec<T>, tabs_state: &mut TabsState, mut is_ephemeral: F) {
    let ephemeral_tabs = tabs.iter().filter(|t| is_ephemeral(t)).count();
    if ephemeral_tabs <= 1 {
        return;
    }
    let mut i = 0;
    tabs.retain(|t| {
        if is_ephemeral(t) && i != tabs_state.selected {
            tabs_state.closed(i);
            false
        } else {
            i += 1;
            true
        }
    });
}

#[derive(Default)]
struct StatusWindow {}
impl WindowContent for StatusWindow {
    fn build(&mut self, state: &mut UIState, debugger: &mut Debugger, ui: &mut UI) {
        ui.cur_mut().axes[Axis::Y].flags.insert(AxisFlags::STACK);

        let mut symbols_progress_pct = 0;
        if debugger.target_state.process_ready() {
            if let &Some(binary_id) = &debugger.stopped_until_symbols_are_loaded {
                let (progress, _stage) = debugger.symbols.get_progress(binary_id);
                symbols_progress_pct = progress / 10000;
            }
        }

        let l = match debugger.target_state {
            ProcessState::NoProcess => ui_writeln!(ui, default_dim, "no process"),
            ProcessState::Starting => ui_writeln!(ui, state_other, "starting"),
            ProcessState::Exiting => ui_writeln!(ui, state_other, "exiting"),
            ProcessState::Stepping if debugger.stopped_until_symbols_are_loaded.is_some() => ui_writeln!(ui, state_other, "loading symbols ({}%), then stepping", symbols_progress_pct),
            ProcessState::Stepping => ui_writeln!(ui, state_other, "stepping"),
            ProcessState::Running if debugger.stopped_until_symbols_are_loaded.is_some() => ui_writeln!(ui, state_other, "loading symbols ({}%), then running", symbols_progress_pct),
            ProcessState::Running => ui_writeln!(ui, state_running, "running"),
            ProcessState::Suspended | ProcessState::CoreDump => {
                let mut stop_reason: (isize, Option<StopReason>) = (-1, None);
                for (tid, thread) in &debugger.threads {
                    for reason in &thread.stop_reasons {
                        let p = reason.priority();
                        if p > stop_reason.0 {
                            stop_reason = (p, Some(reason.clone()));
                        }
                    }
                }
                let state = if debugger.target_state == ProcessState::Suspended {"suspended"} else {"core dump"};
                match stop_reason.1 {
                    None => ui_writeln!(ui, state_suspended, "{}", state),
                    Some(StopReason::Breakpoint(_)) => ui_writeln!(ui, state_suspended, "{} (hit breakpoint)", state),
                    Some(StopReason::DebugTrap) => ui_writeln!(ui, state_suspended, "{} (debug trap)", state),
                    Some(StopReason::Step) => ui_writeln!(ui, state_suspended, "{} (stepped)", state),
                    Some(StopReason::Exception) => ui_writeln!(ui, state_suspended, "{} (exception during step)", state),
                    Some(StopReason::Signal(s)) => styled_writeln!(ui.text, ui.palette.thread_crash.apply(ui.palette.state_suspended), "{} (signal {})", state, signal_name(s)),
                }
            }
        };
        let style = ui.text.spans.last().clone().unwrap().1;
        ui.add(widget!().height(AutoSize::Text).text(l).fill(' ', style));

        let start = ui.text.num_lines();
        match debugger.target_state {
            ProcessState::NoProcess | ProcessState::CoreDump => {ui_writeln!(ui, default_dim, "pid: none");}
            _ => {
                ui_write!(ui, default_dim, "pid: ");
                ui_write!(ui, default, "{}", debugger.pid);
                ui_writeln!(ui, default_dim, " cpu {:.0}% mem {}", debugger.info.total_resource_stats.cpu_percentage(debugger.context.settings.periodic_timer_ns), PrettySize(debugger.info.total_resource_stats.latest.rss_bytes()));
            }
        }
        ui_writeln!(ui, default_dim, "nnd pid: {} cpu {:.0}% mem {}", my_pid(), debugger.my_resource_stats.cpu_percentage(debugger.context.settings.periodic_timer_ns), PrettySize(debugger.my_resource_stats.latest.rss_bytes()));
        match &debugger.persistent.path {
            Ok(p) => ui_writeln!(ui, default_dim, "{}/", p.display()),
            Err(e) if e.is_disabled() => ui_writeln!(ui, default_dim, "{}", e),
            Err(e) => ui_writeln!(ui, error, "{}", e),
        };

        if state.last_error != "" {
            ui_writeln!(ui, error, "{}", state.last_error);
        } else {
            ui.text.close_line();
        }
        ui.text.close_line();
        let end = ui.text.num_lines();

        ui.add(widget!().text_lines(start..end).height(AutoSize::Text));
        let log_widget = ui.add(widget!().height(AutoSize::Remainder(1.0)));
        ui.layout_children(Axis::Y);

        with_parent!(ui, log_widget, {
            let space_left = ui.cur().axes[Axis::Y].get_fixed_size();
            let log_lines = debugger.log.lines.len();
            let start = ui.text.num_lines();
            for line in &debugger.log.lines.make_contiguous()[log_lines.saturating_sub(space_left)..] {
                ui_writeln!(ui, default, "{}", line);
            }
            let end = ui.text.num_lines();
            ui.cur_mut().draw_text = Some(start..end);
        });
    }
}

#[derive(Default)]
struct HintsWindow {
    scroll: isize,
}

impl HintsWindow {
    const NORMAL_HEIGHT: usize = 12; // just enough to fit everything on a laptop-width screen (width affects height because of line wrap)
    const PROFILER_HEIGHT: usize = 17;

    fn build_profiling_charts(&mut self, debugger: &mut Debugger, ui: &mut UI) {
        ui.cur_mut().set_hstack();
        let viewport = ui.add(widget!().width(AutoSize::Remainder(1.0)));
        let scroll_bar = ui.add(widget!().fixed_width(1));
        ui.layout_children(Axis::X);
        let content_widget = ui.add(widget!().parent(viewport).fixed_y(0).height(AutoSize::Children).vstack());

        with_parent!(ui, content_widget, {
            styled_write!(ui.text, ui.palette.default, "frame: {:<10} widgets: {:<10} bucket: {:<10}", ui.frame_idx, ui.prev_tree.len(), PrettyDuration(debugger.context.settings.periodic_timer_ns as f64 / 1e9));
            let l = ui.text.close_line();
            ui.add(widget!().height(AutoSize::Text).text(l));

            enum Type {
                Count,
                Tsc,
                Bytes,
            }
            struct Chart {
                title: &'static [&'static str],
                data: Vec<usize>,
                type_: Type,
            }

            let chart_height = 2;
            let mut charts = [
                Chart {title: &["ui"     , "max"  ], type_: Type::Tsc  , data: Vec::new()},
                Chart {title: &["deb"    , "time" ], type_: Type::Tsc  , data: Vec::new()},
                Chart {title: &["deb"    , "count"], type_: Type::Count, data: Vec::new()},
                Chart {title: &["syscall", "time" ], type_: Type::Tsc  , data: Vec::new()},
                Chart {title: &["syscall", "count"], type_: Type::Count, data: Vec::new()},
                Chart {title: &["other"  , "time" ], type_: Type::Tsc  , data: Vec::new()},
                Chart {title: &["build"  , "max"  ], type_: Type::Tsc  , data: Vec::new()},
                Chart {title: &["render" , "max"  ], type_: Type::Tsc  , data: Vec::new()},
                Chart {title: &["fill"   , "max"  ], type_: Type::Tsc  , data: Vec::new()},
                Chart {title: &["input"  , "bytes"], type_: Type::Bytes, data: Vec::new()},
                Chart {title: &["output" , "bytes"], type_: Type::Bytes, data: Vec::new()},
            ];

            let title_width = charts.iter().map(|c| c.title.iter().map(|t| str_width(*t)).max().unwrap()).max().unwrap();
            let value_width = PrettyCount::MAX_LEN.max(PrettySize::MAX_LEN).max(PrettyDuration::MAX_LEN);
            let total_width = ui.cur().axes[Axis::X].get_fixed_size();
            let chart_width = total_width.saturating_sub(title_width + value_width + 2).max(1);
            for c in &mut charts {
                c.data = vec![0; chart_width];
            }

            let s_per_tsc = if debugger.prof.buckets.is_empty() {
                1.0
            } else {
                let a = &debugger.prof.buckets[debugger.prof.buckets.len().saturating_sub(chart_width)];
                let b = debugger.prof.buckets.back().unwrap();
                (b.end_time - a.start_time).as_secs_f64() / (b.end_tsc - a.start_tsc) as f64
            };

            for i in 0..chart_width.min(debugger.prof.buckets.len()) {
                let b = &debugger.prof.buckets[debugger.prof.buckets.len() - i - 1];
                let j = chart_width - i - 1;

                charts[ 0].data[j] = b.ui_max_tsc as usize;
                charts[ 1].data[j] = b.debugger_tsc as usize;
                charts[ 2].data[j] = b.debugger_count;
                charts[ 3].data[j] = b.syscall_tsc as usize;
                charts[ 4].data[j] = b.syscall_count;
                charts[ 5].data[j] = b.other_tsc as usize;
                charts[ 6].data[j] = b.ui_build_max_tsc as usize;
                charts[ 7].data[j] = b.ui_render_max_tsc as usize;
                charts[ 8].data[j] = b.ui_fill_max_tsc as usize;
                charts[ 9].data[j] = b.ui_input_bytes;
                charts[10].data[j] = b.ui_output_bytes;
            }

            let draw_hline = |left_corner: char, right_corner: char, ui: &mut UI| {
                with_parent!(ui, ui.add(widget!().fixed_height(1).hstack()), {
                    ui.add(widget!().fixed_width(1).fixed_x(title_width as isize).fill(left_corner, ui.palette.default));
                    ui.add(widget!().fixed_width(chart_width).fill('─', ui.palette.default));
                    ui.add(widget!().fixed_width(1).fill(right_corner, ui.palette.default));
                });
            };

            draw_hline('╭', '╮', ui);
            for idx in 0..charts.len() {
                if idx > 0 {
                    draw_hline('├', '┤', ui);
                }
                let chart = &charts[idx];
                let max = chart.data.iter().copied().max().unwrap();
                let max1 = max.max(1);
                with_parent!(ui, ui.add(widget!().fixed_height(chart_height).hstack()), {
                    let start = ui.text.num_lines();
                    for s in chart.title {
                        ui_writeln!(ui, default, "{}", s);
                    }
                    let end = ui.text.num_lines();
                    ui.add(widget!().fixed_width(title_width).text_lines(start..end));
                    ui.add(widget!().fixed_width(1).fill('│', ui.palette.default));

                    let start = ui.text.num_lines();
                    for i in 0..chart_height {
                        let h = (chart_height - i - 1) * 8;
                        for j in 0..chart_width {
                            let v = (chart.data[j] * (chart_height * 8) + max/2) / max1;
                            let c = match v {
                                v if v <= h   => ' ',
                                v if v == h+1 => '▁',
                                v if v == h+2 => '▂',
                                v if v == h+3 => '▃',
                                v if v == h+4 => '▄',
                                v if v == h+5 => '▅',
                                v if v == h+6 => '▆',
                                v if v == h+7 => '▇',
                                _             => '█',
                            };
                            ui.text.chars.push(c);
                        }
                        ui.text.close_span(ui.palette.default);
                        ui.text.close_line();
                    }
                    let end = ui.text.num_lines();
                    ui.add(widget!().fixed_width(chart_width).text_lines(start..end));

                    ui.add(widget!().fixed_width(1).fill('│', ui.palette.default));
                    let start = ui.text.num_lines();
                    for val in [max, *chart.data.last().unwrap()] {
                        match chart.type_ {
                            Type::Count => ui_writeln!(ui, default, "{}", PrettyCount(val)),
                            Type::Tsc => ui_writeln!(ui, default, "{}", PrettyDuration(s_per_tsc * val as f64)),
                            Type::Bytes => ui_writeln!(ui, default, "{}", PrettySize(val)),
                        };
                    }
                    let end = ui.text.num_lines();
                    ui.add(widget!().text_lines(start..end));
                });
            }
            draw_hline('╰', '╯', ui);
        });

        let root = ui.cur_parent;
        with_parent!(ui, viewport, {
            ui.focus();
            cursorless_scrolling_navigation(&mut self.scroll, None, root, scroll_bar, ui);
        });
    }
}
impl WindowContent for HintsWindow {
    fn build(&mut self, state: &mut UIState, debugger: &mut Debugger, ui: &mut UI) {
        if state.profiler_enabled {
            self.build_profiling_charts(debugger, ui);
            return;
        }

        let start = ui.text.num_lines();
        let mut column_breaks: Vec<usize> = Vec::new();
        column_breaks.push(start);
        for hint in &state.key_hints {
            if hint.hidden || (hint.if_not_core_dump && debugger.mode == RunMode::CoreDump) {
                continue;
            }
            if hint.window.is_some() {
                // Currently we put all non-window-specific hints in the left column and all window-specific ones in the right one.
                // It happens to fit just right for the current set of hints.
                if column_breaks.len() == 1 {
                    column_breaks.push(ui.text.num_lines());
                }
            }

            format_key_hint(hint, &mut ui.text, &ui.palette, &ui.key_binds, /*with_condition*/ false);
            ui.text.close_line();
        }
        let end = ui.text.num_lines();

        ui.cur_mut().set_hstack();
        let viewport = ui.add(widget!().width(AutoSize::Remainder(1.0)));
        let scroll_bar = ui.add(widget!().fixed_width(1));
        ui.layout_children(Axis::X);
        let content = ui.add(widget!().parent(viewport).height(AutoSize::Children).hstack());

        let num_columns = 2;
        let lines_per_column = (end - start + num_columns - 1) / num_columns;
        with_parent!(ui, content, {
            for i in 0..num_columns {
                if i != 0 {
                    ui.add(widget!().fixed_width(1).fixed_height(0));
                }
                let range = *column_breaks.get(i).unwrap_or(&end)..*column_breaks.get(i+1).unwrap_or(&end);
                ui.add(widget!().width(AutoSize::Remainder(2.0)).height(AutoSize::Text).text_lines(range).flags(WidgetFlags::LINE_WRAP));
            }
            ui.layout_children(Axis::X);
        });

        let root = ui.cur_parent;
        with_parent!(ui, viewport, {
            ui.focus();
            cursorless_scrolling_navigation(&mut self.scroll, None, root, scroll_bar, ui);
        });
    }
}

pub fn format_key_hint(hint: &KeyHint, text: &mut StyledText, palette: &Palette, key_binds: &KeyBinds, with_condition: bool) {
    let style = if hint.window.is_some() {
        palette.hint_window_dependent
    } else if !hint.condition.is_empty() {
        palette.hint_state_dependent
    } else {
        palette.hint_global
    };
    for (i, range) in hint.key_ranges.iter().enumerate() {
        if i != 0 {
            styled_write!(text, style, "/");
        }
        styled_write!(text, palette.hotkey.apply(style), "{}", key_binds.normal.action_to_key_name(range[0]));
        if range[0] != range[1] {
            styled_write!(text, style, "…");
            styled_write!(text, palette.hotkey.apply(style), "{}", key_binds.normal.action_to_key_name(range[1]));
        }
    }
    styled_write!(text, style, " - {}", hint.hint);
    if with_condition {
        if !hint.condition.is_empty() {
            styled_write!(text, palette.default_dim, " ({})", hint.condition);
        }
        if hint.if_not_core_dump {
            styled_write!(text, palette.default_dim, " (if not core dump)");
        }
    }
}

#[derive(Default)]
struct BinariesWindow {
    table_state: TableState,
}
impl WindowContent for BinariesWindow {
    fn build(&mut self, state: &mut UIState, debugger: &mut Debugger, ui: &mut UI) {
        let mut table = Table::new(mem::take(&mut self.table_state), ui, vec![
            Column::new("idx", AutoSize::Fixed(3), false),
            Column::new("name", AutoSize::Remainder(1.0), false),
            Column::new("offset", AutoSize::Fixed(12), false),
            Column::new("file", AutoSize::Fixed(PrettySize::MAX_LEN), false),
            Column::new("", AutoSize::Fixed(0), false).hide(),
        ]);
        table.hide_cursor_if_unfocused = true;
        for binary in debugger.symbols.iter() {
            table.start_row(binary.id, ui);

            ui_writeln!(ui, default_dim, "{}", binary.priority_idx + 1);
            table.text_cell(ui);

            // Path, progress bar, error message.
            with_parent!(ui, table.start_cell(ui), {
                ui.cur_mut().axes[Axis::Y].flags.insert(AxisFlags::STACK);

                // Path.
                let style = if binary.is_mapped {ui.palette.default} else {ui.palette.default_dim};
                let l = styled_writeln!(ui.text, style, "{}", binary.locator.path);
                ui.add(widget!().height(AutoSize::Text).flags(WidgetFlags::TEXT_TRUNCATION_ALIGN_RIGHT).text(l));

                // Progress bar.
                let mut indicated_loading = false;
                if binary.symbols.as_ref().is_err_and(|e| e.is_loading()) {
                    let (progress_ppm, loading_stage) = debugger.symbols.get_progress(binary.id);
                    let l = ui_writeln!(ui, default, "{}% ({})", (progress_ppm + 5000) / 10000, loading_stage);
                    let mut w = widget!().height(AutoSize::Text).text(l);
                    w.draw_progress_bar = Some((progress_ppm as f64 / 1e6, ui.palette.progress_bar));
                    ui.add(w);
                    indicated_loading = true;
                }

                // Error.
                let start = ui.text.num_lines();
                let mut print_error = |e: &Error| {
                    if e.is_loading() {
                        if !indicated_loading {
                            ui_writeln!(ui, default_dim, "loading");
                            indicated_loading = true;
                        }
                        return;
                    }
                    let style = if e.is_missing_symbols() {ui.palette.default_dim} else {ui.palette.error};
                    styled_writeln!(ui.text, style, "{}", e);
                };
                if let Err(e) = &binary.elves {
                    print_error(e);
                } else {
                    if let Err(e) = &binary.unwind {
                        print_error(e);
                    }
                    if let Err(e) = &binary.symbols {
                        print_error(e);
                    }
                }
                for w in &binary.warnings {
                    ui_writeln!(ui, default_dim, "{}", w);
                }
                let end = ui.text.num_lines();
                if end > start {
                    ui.add(widget!().height(AutoSize::Text).text_lines(start..end));
                }
            });

            if binary.is_mapped {
                ui_writeln!(ui, default_dim, "{:>12x}", binary.addr_map.static_to_dynamic(0) & 0xffffffffffff);
            } else {
                ui_writeln!(ui, default_dim, "");
            }
            table.text_cell(ui);

            // ELF or unwind error/loading/stats.
            match &binary.elves {
                Err(_) => {ui_writeln!(ui, default, "");}
                Ok(elves) => {
                    let max_size = elves.iter().map(|elf| elf.data().len()).max().unwrap();
                    ui_writeln!(ui, default_dim, "{}", PrettySize(max_size));
                }
            };
            table.text_cell(ui);

            let start = ui.text.num_lines();
            for s in &binary.notices {
                ui_writeln!(ui, default_dim, "{}", s);
            }
            let end = ui.text.num_lines();
            table.text_cell_lines(start..end, ui);
        }

        self.table_state = table.finish(ui);
    }

    fn get_key_hints(&self, out: &mut Vec<KeyHint>, debugger: &Debugger) {
        out.extend([
            KeyHint::key(KeyAction::Tooltip, "tooltip"),
        ]);
    }
}

#[derive(Default)]
struct ThreadsFilter {
    bar: SearchBar,
    cache_key: String, // when this changes, drop cached_results
    // Cached information about previously seen threads. We re-check each thread's stop_count each frame. Sorted by thread_idx.
    cached_results: Vec<(/*thread_idx*/ usize, /*stop_count*/ usize, /*passes_filter*/ bool)>,
    last_seen_filtered_count: usize,
}
impl ThreadsFilter {
    fn get_filtered_tids(&mut self, debugger: &mut Debugger) -> Vec<pid_t> {
        let mut tids: Vec<(usize, usize, pid_t)> = debugger.threads.values().map(|t| (t.idx, t.stop_count, t.tid)).collect();
        tids.sort_unstable_by_key(|t| t.0);
        let mut query = if self.bar.visible {self.bar.text.text.clone()} else {String::new()};
        if query != self.cache_key {
            self.cache_key = query.clone();
            self.cached_results.clear();
        }
        let name_only = if query.starts_with('"') {
            let end = if query.len() > 1 && query.ends_with('"') { query.len()-1 } else {query.len()};
            query = query[1..end].to_string();
            true
        } else {
            false
        };
        let (mut i, mut j) = (0, 0);
        let mut new_cached: Vec<(usize, usize, bool)> = Vec::new();
        let mut res: Vec<pid_t> = Vec::new();
        while i < tids.len() || j < self.cached_results.len() {
            if i < tids.len() && (j == self.cached_results.len() || tids[i].0 < self.cached_results[j].0 || (tids[i].0 == self.cached_results[j].0 && tids[i].1 != self.cached_results[j].1)) {
                // Cache miss.
                let (thread_idx, stop_count, tid) = tids[i].clone();
                let pass = Self::thread_passes(tid, &query, name_only, debugger);
                new_cached.push((thread_idx, stop_count, pass));
                if pass {
                    res.push(tid);
                }
                if j < self.cached_results.len() && tids[i].0 == self.cached_results[j].0 {
                    j += 1;
                }
                i += 1;
            } else if j < self.cached_results.len() && (i == tids.len() || self.cached_results[j].0 < tids[i].0) {
                // Thread disappeared, remove it from cache.
                j += 1;
            } else {
                // Cache hit.
                assert!(tids[i].1 == self.cached_results[j].1);
                new_cached.push(self.cached_results[j].clone());
                if self.cached_results[j].2 {
                    res.push(tids[i].2);
                }
                i += 1;
                j += 1;
            }
        }
        self.cached_results = new_cached;
        res
    }

    fn thread_passes(tid: pid_t, query: &str, name_only: bool, debugger: &mut Debugger) -> bool {
        if query.is_empty() {
            return true;
        }
        let name = debugger.threads.get(&tid).unwrap().info.resource_stats.latest.comm();
        if name.find(query).is_some() {
            return true;
        }
        if name_only {
            return false;
        }

        // This is very primitive right now, but I'm not sure in which direction to take it to be most useful.
        let stack = debugger.get_stack_trace(tid, false);
        for subframe in &stack.subframes {
            if subframe.function_idx.is_ok() {
                if subframe.function_name.find(query).is_some() {
                    return true;
                }
            }
            if let Some(line) = &subframe.line {
                if let Ok(s) = str::from_utf8(line.path.as_os_str().as_bytes()) {
                    if s.find(query).is_some() {
                        return true;
                    }
                }
            }
        }
        false
    }
}

#[derive(Default)]
struct ThreadsWindow {
    table_state: TableState,

    seen_stop_counts: HashMap<pid_t, usize>,
    filter: ThreadsFilter,
}
impl WindowContent for ThreadsWindow {
    fn build(&mut self, state: &mut UIState, debugger: &mut Debugger, ui: &mut UI) {
        ui.cur_mut().set_vstack();
        for action in ui.check_keys(&[KeyAction::Find, KeyAction::ToggleSort]) {
            match action {
                KeyAction::Find => self.filter.bar.start_editing(),
                KeyAction::ToggleSort if debugger.mode != RunMode::CoreDump => {
                    (self.table_state.sort_column, self.table_state.sort_descending) =
                        if (self.table_state.sort_column, self.table_state.sort_descending) == (0, false) {
                            (4, true)
                        } else {
                            (0, false)
                        };
                    self.table_state.scroll_to_cursor = true;
                }
                _ => (),
            }
        }
        with_parent!(ui, ui.add(widget!().identity(&'s')), {
            ui.focus();
            let l = ui_writeln!(ui, default_dim, "filter (name+stack): ");
            let r = if self.filter.bar.text.text.is_empty() {
                None
            } else {
                Some(ui_writeln!(ui, default_dim, "{}/{} threads", self.filter.last_seen_filtered_count, debugger.threads.len()))
            };
            self.filter.bar.build(Some(l), r, ui);
        });
        let table_widget = ui.add(widget!().identity(&'t').height(AutoSize::Remainder(1.0)));
        with_parent!(ui, table_widget, {
            ui.multifocus();
        });
        ui.layout_children(Axis::Y);

        let have_stats = debugger.mode != RunMode::CoreDump;
        let mut table = with_parent!(ui, table_widget, {
            Table::new(mem::take(&mut self.table_state), ui, vec![
                Column::new("idx", AutoSize::Fixed(5), true),
                Column::new("tid", AutoSize::Fixed(10), true),
                Column::new("name", AutoSize::Fixed(15), true),
                Column::new("s", AutoSize::Fixed(2), true).with_hidden(!have_stats),
                Column::new("cpu", AutoSize::Fixed(4), true).with_hidden(!have_stats),
                Column::new("function", AutoSize::Remainder(1.0), false),
                Column::new("addr", AutoSize::Fixed(12), true),
                Column::new("bin", AutoSize::Fixed(3), false),
            ])
        });

        let tids = self.filter.get_filtered_tids(debugger);
        if tids.len() != self.filter.last_seen_filtered_count {
            self.filter.last_seen_filtered_count = tids.len();
            ui.should_redraw = true;
        }
        let mut threads: Vec<&Thread> = tids.iter().map(|t| debugger.threads.get(t).unwrap()).collect();
        if (table.state.sort_column, table.state.sort_descending) != (0, false) {
            // This probably generates a ton of machine code. There's probably a better way to do this.
            // Doing an indirect function call for each comparison sounds slow. Maybe put field offset into a variable, for integer fields; the hard part is figuring out how to do this in a way that doesn't offend the sensibilities of the authors of the Optimizing Compiler.
            match (table.state.sort_column, table.state.sort_descending) {
                (0, false) => threads.sort_unstable_by_key(|t|  t.idx),
                (0, true ) => threads.sort_unstable_by_key(|t| !t.idx),
                (1, false) => threads.sort_unstable_by_key(|t|  t.tid),
                (1, true ) => threads.sort_unstable_by_key(|t| !t.tid),
                (2, false) => threads.sort_unstable_by_key(|t| (                  t.info.resource_stats.latest.comm() , t.idx)),
                (2, true ) => threads.sort_unstable_by_key(|t| (std::cmp::Reverse(t.info.resource_stats.latest.comm()), t.idx)),
                (3, false) => threads.sort_unstable_by_key(|t| (                  t.info.resource_stats.latest.state , t.tid)),
                (3, true ) => threads.sort_unstable_by_key(|t| (std::cmp::Reverse(t.info.resource_stats.latest.state), t.tid)),
                (4, false) => threads.sort_unstable_by_key(|t| ( (t.info.resource_stats.cpu_percentage(debugger.context.settings.periodic_timer_ns) * 1000.0) as isize, t.idx)),
                (4, true ) => threads.sort_unstable_by_key(|t| (-(t.info.resource_stats.cpu_percentage(debugger.context.settings.periodic_timer_ns) * 1000.0) as isize, t.idx)),
                (6, false) => threads.sort_unstable_by_key(|t| ( t.info.regs.get(RegisterIdx::Rip).map_or(0, |(r, _)| r), t.idx)),
                (6, true ) => threads.sort_unstable_by_key(|t| (!t.info.regs.get(RegisterIdx::Rip).map_or(0, |(r, _)| r), t.idx)),
                _ => (),
            }
        }

        // If some thread hit a breakpoint or fatal signal, switch to it.
        // If multiple threads stopped for different reasons, pick the highest-priority reason.
        self.seen_stop_counts.retain(|tid, _| debugger.threads.contains_key(tid));
        let mut switch_to: (/*priority*/ isize, pid_t) = (-1, 0);
        for (tid, thread) in &debugger.threads {
            if thread.stop_reasons.is_empty() {
                continue;
            }
            let seen = match self.seen_stop_counts.entry(*tid) {
                Entry::Vacant(v) => {
                    v.insert(thread.stop_count);
                    false
                }
                Entry::Occupied(mut o) => {
                    mem::replace(o.get_mut(), thread.stop_count) == thread.stop_count
                }
            };
            if seen {
                continue;
            }
            for reason in &thread.stop_reasons {
                let p = reason.priority();
                if p > switch_to.0 {
                    switch_to = (p, *tid);
                }
            }
        }
        if switch_to.0 >= 0 {
            state.selected_thread = switch_to.1;
            table.state.scroll_to_cursor = true;
        }

        table.state.cursor_elsewhere = false;
        if let Some(thread) = debugger.threads.get(&state.selected_thread) {
            if let Some(i) = threads.iter().position(|t| t.tid == state.selected_thread) {
                // Keep the cursor on the selected tid, but don't auto-scroll to cursor if that tid moves around (e.g. if the table is sorted by cpu% or if threads are added or removed).
                table.state.cursor = i;
            } else {
                // Selected thread doesn't pass the filter. Hide cursor.
                table.state.cursor_elsewhere = true;
            }
        } else {
            // Thread disappeared, switch to whatever thread took its position in the list.
            table.state.scroll_to_cursor = true;
        }

        // Global hotkeys.
        with_parent!(ui, ui.content_root, {
            for key in ui.check_keys(&[KeyAction::PreviousThread, KeyAction::NextThread]) {
                match key {
                    KeyAction::PreviousThread => table.state.select(table.state.cursor.saturating_sub(1)),
                    KeyAction::NextThread => table.state.select(table.state.cursor + 1),
                    _ => panic!("huh"),
                }
            }
        });

        let range = table.lazy(threads.len(), 1, ui);

        if !table.state.cursor_elsewhere {
            state.selected_thread = threads.get(table.state.cursor).map_or(0, |t| t.tid);
        }

        let visible_tids: Vec<pid_t> = threads[range.clone()].iter().map(|t| t.tid).collect();
        for i in range.clone() {
            let tid = visible_tids[i - range.start];
            let stack = debugger.get_stack_trace(tid, /* partial */ true);
            let t = debugger.threads.get(&tid).unwrap();
            let row_widget = table.start_row(hash(&tid), ui);
            
            ui_writeln!(ui, default_dim, "{}", t.idx);
            table.text_cell(ui);
            
            ui_writeln!(ui, default_dim, "{}", t.tid);
            table.text_cell(ui);

            if let Some(e) = &t.info.resource_stats.error {
                ui_writeln!(ui, error, "{}", e);
            } else {
                let name = t.info.resource_stats.latest.comm();
                ui_writeln!(ui, default, "{}", name);
            }
            table.text_cell(ui);

            let style = match t.info.resource_stats.latest.state {
                'R' | 'D' => ui.palette.running,
                'S' | 'T' | 't' => ui.palette.suspended,
                'Z' | 'X' | 'x' => ui.palette.error,
                _ => ui.palette.state_other,
            };
            styled_writeln!(ui.text, style, "{}", t.info.resource_stats.latest.state);
            table.text_cell(ui);

            ui_writeln!(ui, default_dim, "{:.0}%", t.info.resource_stats.cpu_percentage(debugger.context.settings.periodic_timer_ns));
            table.text_cell(ui);

            match t.state {
                ThreadState::Running => {
                    match &debugger.stepping {
                        Some(step) if step.tid == tid => ui_writeln!(ui, state_other, "stepping"),
                        _ => ui_writeln!(ui, state_running, "running"),
                    };
                    table.text_cell(ui);

                    ui.text.close_line();
                    table.text_cell(ui);
                    table.text_cell(ui);
                }
                ThreadState::Suspended if !stack.frames.is_empty() => {
                    let f = &stack.frames[0];
                    let sf = &stack.subframes[0];
                    if sf.function_idx.is_ok() {
                        ui_writeln!(ui, function_name, "{}", sf.function_name);
                    } else {
                        ui_writeln!(ui, default_dim, "?");
                    }
                    table.text_cell(ui);
                    
                    ui_writeln!(ui, default_dim, "{:x}", f.addr);
                    table.text_cell(ui);

                    match &f.binary_id {
                        Ok(binary_id) => ui_writeln!(ui, default_dim, "{}", debugger.symbols.get(*binary_id).unwrap().priority_idx + 1),
                        Err(_) => ui_writeln!(ui, default_dim, "?"),
                    };
                    table.text_cell(ui);
                }
                ThreadState::Suspended => {
                    match &stack.truncated {
                        Some(e) if e.is_loading() => ui_writeln!(ui, running, "[loading]"),
                        Some(e) => ui_writeln!(ui, error, "<{}>", e),
                        None => ui_writeln!(ui, default_dim, "[empty]"),
                    };
                    table.text_cell(ui);

                    ui.text.close_line();
                    table.text_cell(ui);
                    table.text_cell(ui);
                }
            }

            // Highlight threads that got a fatal signal or hit a breakpoint.
            let mut style_adjustment = StyleAdjustment::default();
            for stop in &t.stop_reasons {
                match stop {
                    StopReason::Signal(_) => {
                        style_adjustment = ui.palette.thread_crash;
                        break;
                    }
                    StopReason::Breakpoint(_) | StopReason::DebugTrap => style_adjustment = ui.palette.thread_breakpoint_hit,
                    StopReason::Step | StopReason::Exception => (),
                }
            }
            ui.get_mut(row_widget).style_adjustment.update(style_adjustment);
        }

        self.table_state = table.finish(ui);
    }

    fn drop_caches(&mut self) {
        self.filter.cached_results.clear();
    }

    fn get_key_hints(&self, out: &mut Vec<KeyHint>, debugger: &Debugger) {
        out.extend([
            KeyHint::key(KeyAction::Find, "filter"),
            KeyHint::key(KeyAction::Tooltip, "tooltip"),
            KeyHint::key(KeyAction::ToggleSort, "sort by cpu").if_not_core_dump(),
        ]);
    }
}

// Location of a stack trace subframe that tries to stay on the "same" subframe when the stack changes slightly,
// to avoid the focus jumping around unexpectedly to the user. Currently this only comes into play during initial loading, when stack changes as more unwind info or symbols were loaded.
// Specifically we want:
//  * When symbols finish loading, some frames get expanded into multiple subframes. Focus should stay on the same frame as it was, though subframe index changes completely.
//    Hence storing frame and subframe idx separately.
//  * If stack failed to fully unwind because unwind info hadn't been loaded yet, then a later unwind succeeded and produced longer stack, we should stay on the same frame relative to the top of the stack.
//    Hence frame_idx counting from the top rather than bottom (just like regular subframe_idx, nothing fancy).
//  * (Originally the idea was that this would store index from the *bottom* of the stack and be useful when window locking is implemented.
//     If the process is resumed and suspended without ever returning from the selected subfunction, keep focus on that subfunction.
//     But this is incompatible with the previous requirement: if stack became less truncated then we should keep index relative to the *top*.
//     Maybe window locking would require something like Debugger's stack digest. Or maybe we'll count from the top when unlocked and from the bottom when locked, or detect when base frame's addr changes.)
#[derive(Clone, Copy, PartialEq, Eq)]
struct StableSubframeIdx {
    frame_idx: usize,
    subframe_subidx: usize,
}
impl StableSubframeIdx {
    fn top() -> Self { Self {frame_idx: 0, subframe_subidx: 0} }
    fn new(stack: &StackTrace, mut subframe_idx: usize) -> Self {
        if stack.frames.is_empty() {
            return Self::top();
        }
        subframe_idx = subframe_idx.min(stack.subframes.len() - 1);
        let frame_idx = stack.subframes[subframe_idx].frame_idx;
        let frame = &stack.frames[frame_idx];
        Self {frame_idx, subframe_subidx: subframe_idx - frame.subframes.start}
    }
    fn subframe_idx(&self, stack: &StackTrace) -> usize {
        if stack.frames.is_empty() {
            return 0;
        }
        let frame_idx = self.frame_idx.min(stack.frames.len() - 1);
        let frame = &stack.frames[frame_idx];
        (frame.subframes.start + self.subframe_subidx).min(frame.subframes.end - 1)
    }
}

// This window is in charge of telling source and disassembly windows when to auto-open and auto-scroll.
struct StackWindow {
    table_state: TableState,
    // Previously selected frame in each thread, so that switching threads back and forth doesn't reset the scroll.
    // If thread's stop count changed, we switch to the top frame, unless the window is locked.
    threads: HashMap<pid_t, (/* stop_count */ usize, StableSubframeIdx)>,
    // When this changes, we scroll source and disassembly windows.
    seen: (/* tid */ pid_t, StableSubframeIdx, /* frame addr */ usize),
    // After symbols were loaded, tell disassembly and source windows to try opening the file/function again.
    rerequest_scroll: bool,
}
impl Default for StackWindow { fn default() -> Self { Self {table_state: TableState::default(), threads: HashMap::new(), seen: (0, StableSubframeIdx::top(), 0), rerequest_scroll: false} } }
impl WindowContent for StackWindow {
    fn build(&mut self, state: &mut UIState, debugger: &mut Debugger, ui: &mut UI) {
        state.stack = debugger.get_stack_trace(state.selected_thread, /* partial */ false);
        let rerequest_scroll = mem::take(&mut self.rerequest_scroll);

        assert_eq!(state.stack.frames.is_empty(), state.stack.subframes.is_empty());
        let num_rows = state.stack.subframes.len();
        let locked = false; // TODO: window locking

        // Behaviors that we're trying to implement here:
        //  * when switching threads back and forth without resuming the process, remember per-thread selected frame and auto-switch to that,
        //  * if a thread was resumed and stopped (e.g. a step or a breakpoint hit), switch to the top frame
        //     - even if the stack didn't change,
        //     - even if the thread was running for a very short time and no build() call happened during that,
        //     - even if the thread wasn't selected while it was running,
        //     - but if the stack window is locked, don't switch; keep the same position relative to the bottom of the stack,
        //  * when switching thread or stack frame, scroll the source and disassembly windows even if address didn't change (e.g. the same breakpoint was hit twice in a row)
        //     - including the switch-to-top case from above, even if top was already selected,
        //     - including the case when e.g. up-arrow key was pressed when already at the top of the stack (useful if the stack has only one frame),
        //  * if symbols loading completed and stack frames got expanded into multiple subframes of inlined functions, keep focus on the same frame,
        //  * when symbols loading completes, retry scrolling the source and disassembly windows, but only if they're currently showing an error (to avoid yanking valid file the user is looking at),
        //  * if the stack window is locked, and the process was stopped and resumed, and current frame's address changed, scroll the source and disassembly (if address didn't change, don't scroll).

        if !state.stack.frames.is_empty() {
            let deb_thr = debugger.threads.get(&state.selected_thread).unwrap();
            let stop_count = deb_thr.stop_count;

            let thr = self.threads.entry(state.selected_thread).or_insert((0, StableSubframeIdx::top()));
            if thr.0 == stop_count || locked {
                self.table_state.cursor = thr.1.subframe_idx(&state.stack);
            } else {
                self.table_state.select(deb_thr.subframe_to_select.unwrap_or(0));
            }
            thr.0 = stop_count;
        }

        // Global hotkeys.
        with_parent!(ui, ui.content_root, {
            for action in ui.check_keys(&[KeyAction::PreviousStackFrame, KeyAction::NextStackFrame]) {
                match action {
                    KeyAction::PreviousStackFrame => self.table_state.select(self.table_state.cursor.saturating_sub(1)),
                    KeyAction::NextStackFrame => self.table_state.select(self.table_state.cursor + 1),
                    _ => panic!("huh"),
                }
            }
        });

        let mut table = Table::new(mem::take(&mut self.table_state), ui, vec![
            Column::new("idx", AutoSize::Fixed(3), false),
            Column::new("location", AutoSize::Remainder(1.0), false),
            Column::new("address", AutoSize::Fixed(12), false),
            Column::new("bin", AutoSize::Fixed(3), false),
            Column::new("unwind info", AutoSize::Fixed(0), false).hide(),
        ]);

        let write_stack_truncated_error = |e: &Error, ui: &mut UI| -> usize {
            if e.is_usage() || e.is_loading() {
                ui_writeln!(ui, default_dim, "{}", e)
            } else {
                ui_writeln!(ui, error, "stack truncated: {}", e)
            }
        };
        for (idx, subframe) in state.stack.subframes.iter().enumerate() {
            table.start_row(idx, ui);
            let frame = &state.stack.frames[subframe.frame_idx];

            ui_writeln!(ui, default_dim, "{}", idx);
            table.text_cell(ui);

            with_parent!(ui, table.start_cell(ui), {
                ui.cur_mut().set_vstack();

                let (l, align_right) = match &subframe.function_idx {
                    Ok(_) => (ui_writeln!(ui, function_name, "{}", subframe.function_name), false),
                    Err(e) => (ui_writeln!(ui, error, "{}", e), false),
                };
                ui.add(widget!().height(AutoSize::Text).text(l).flags(if align_right {WidgetFlags::TEXT_TRUNCATION_ALIGN_RIGHT} else {WidgetFlags::empty()}));

                if let Some(info) = &subframe.line {
                    let name = info.path.as_os_str().to_string_lossy();
                    ui_write!(ui, filename, "{}", name);
                    if info.line.line() != 0 {
                        ui_write!(ui, line_number, ":{}", info.line.line());
                        if info.line.column() != 0 {
                            ui_write!(ui, column_number, ":{}", info.line.column());
                        }
                    }
                } else {
                    ui_write!(ui, default_dim, "?");
                }
                let l = ui.text.close_line();
                ui.add(widget!().height(AutoSize::Text).text(l).flags(WidgetFlags::TEXT_TRUNCATION_ALIGN_RIGHT));

                if idx + 1 == state.stack.subframes.len() {
                    if let Some(e) = &state.stack.truncated {
                        let l = write_stack_truncated_error(e, ui);
                        ui.add(widget!().height(AutoSize::Text).text(l));
                    }
                }
            });

            let is_inlined = idx != frame.subframes.end-1;
            if is_inlined {
                ui.text.close_line();
            } else {
                ui_writeln!(ui, default_dim, "{:x}", frame.addr);
            }
            table.text_cell(ui);

            if is_inlined {
                ui.text.close_line()
            } else {
                match &frame.binary_id {
                    Ok(b) => ui_writeln!(ui, default_dim, "{}", debugger.symbols.get(*b).unwrap().priority_idx + 1),
                    Err(_) => ui_writeln!(ui, default_dim, "?"),
                }
            };
            table.text_cell(ui);

            ui_writeln!(ui, default_dim, "{:?}", frame.unwind_source);
            table.text_cell(ui);
        }
        if state.stack.subframes.is_empty() {
            if let Some(e) = &state.stack.truncated {
                table.start_row(0, ui);
                ui.text.close_line();
                table.text_cell(ui);

                write_stack_truncated_error(e, ui);
                table.text_cell(ui);

                ui.text.close_line();
                table.text_cell(ui);
                table.text_cell(ui);
                table.text_cell(ui);
            }
        }

        self.table_state = table.finish(ui);
        let mut scroll_source_and_disassembly = self.table_state.did_scroll_to_cursor;

        if state.stack.frames.is_empty() {
            state.selected_frame = 0;
            state.selected_subframe = 0;
        } else {
            state.selected_subframe = self.table_state.cursor;
            let subframe = &state.stack.subframes[state.selected_subframe];
            state.selected_frame = subframe.frame_idx;
            let frame = &state.stack.frames[subframe.frame_idx];
            let thr = self.threads.entry(state.selected_thread).or_insert((0, StableSubframeIdx::top()));
            thr.1 = StableSubframeIdx::new(&state.stack, state.selected_subframe);

            let cur = (state.selected_thread, thr.1, frame.addr);
            scroll_source_and_disassembly |= cur != self.seen;
            if scroll_source_and_disassembly || rerequest_scroll {
                state.should_scroll_source = Some((subframe.line.as_ref().map(|line| SourceScrollTarget {path: line.path.clone(), version: line.version.clone(), line: line.line.line(), cascade: false}), !scroll_source_and_disassembly));
                state.should_scroll_disassembly = Some((match (&frame.binary_id, &state.stack.subframes[frame.subframes.end - 1].function_idx) {
                    (Err(e), _) => Err(e.clone()),
                    (_, Err(e)) => Err(e.clone()),
                    (&Ok(binary_id), &Ok(function_idx)) => Ok(DisassemblyScrollTarget {
                        binary_id, function_idx, static_pseudo_addr: frame.pseudo_addr.wrapping_sub(frame.addr_static_to_dynamic),
                        subfunction_level: (frame.subframes.end - state.selected_subframe - 1) as u16, cascade: false}),
                }, !scroll_source_and_disassembly));
            }
            self.seen = cur;
        }

        if self.threads.len() > debugger.threads.len() * 2 {
            self.threads.retain(|tid, _| { debugger.threads.contains_key(tid) });
        }
    }

    fn drop_caches(&mut self) {
        self.rerequest_scroll = true;
    }

    fn get_key_hints(&self, out: &mut Vec<KeyHint>, debugger: &Debugger) {
        out.extend([
            KeyHint::key(KeyAction::Tooltip, "tooltip"),
        ]);
    }
}

// For Rust standard library code, Rust compiler uses fake paths in debug symbols, like this:
// /rustc/5680fa18feaa87f3ff04063800aec256c3d4b4be/library/core/src/hash/sip.rs
// which means the file can be found here:
// https://github.com/rust-lang/rust/blob/5680fa18feaa87f3ff04063800aec256c3d4b4be/library/core/src/hash/sip.rs
fn rust_fake_path_to_url(path: &str) -> Option<String> {
    if path.len() < "/rustc/5680fa18feaa87f3ff04063800aec256c3d4b4be/".len() { return None; }
    if !path.starts_with("/rustc/") { return None; }
    if !(&path[7..47]).chars().all(|c| c.is_digit(16)) { return None; }
    let mut res = "https://github.com/rust-lang/rust/blob/".to_string();
    res.push_str(&path[7..]);
    Some(res)
}
// Rust function names in debug info look like this: nnd::pretty::prettify_value::hf586ae10d8ed2bb6
// Remove that last suffix.
fn rust_remove_function_name_hash_suffix(name: &mut &str) {
    if name.len() < 19 {
        return;
    }
    let i = name.len() - 19;
    if !name.is_char_boundary(i) {
        return;
    }
    let suf = &name[i..];
    if !suf.starts_with("::h") {
        return;
    }
    let suf = &suf[3..];
    if suf.chars().any(|c| !c.is_ascii_hexdigit()) {
        return;
    }
    *name = &name[..i];
}

#[derive(Default)]
struct CodeTab {
    title: String,
    identity: usize,
    path_in_symbols: PathBuf, // empty if not known
    version_in_symbols: FileVersionInfo,
    ephemeral: bool,
    area_state: AreaState,
}

struct SourceFile {
    header: StyledText, // can contain errors or warnings, not scrollable
    text: StyledText, // includes virtual space to cover all lines+columns mentioned in debug symbols
    local_path: PathBuf, // empty if error
    widest_line: usize,
    num_lines_in_local_file: usize,
}

#[derive(Default)]
struct CodeSearch {
    bar: SearchBar,

    query: SearchQuery,
    tab_identity: usize,

    match_ranges: Vec<Range<usize>>,
    matches: Vec<(/*line_idx*/ usize, /*column_ranges*/ Range<usize>)>,
    match_idx: usize,
    cursor_is_on_a_match: bool,
}
impl CodeSearch {
    // Does the search if needed, moves the cursor if needed.
    fn update(&mut self, tab: &mut CodeTab, text: &StyledText, mut select_match: isize) {
        let query = SearchQuery::parse(&self.bar.text.text, /*can_have_file*/ false, /*can_go_to_line*/ false);
        let query_changed = self.query != query;
        if (&self.query, self.tab_identity) != (&query, tab.identity) {
            (self.query, self.tab_identity) = (query, tab.identity);
            self.match_ranges.clear();
            self.matches.clear();
            if !self.query.is_empty {
                for line_idx in 0..text.num_lines() {
                    let start = self.match_ranges.len();
                    let s = text.get_line_str(line_idx).as_bytes();
                    let mut col = 0usize;
                    while let Some(pos) = memmem_maybe_case_sensitive(&s[col..], &self.query.s, self.query.case_sensitive) {
                        let needle_len = self.query.s.get().len();
                        col += pos;
                        self.match_ranges.push(col..col+needle_len);
                        col += needle_len;
                    }
                    let end = self.match_ranges.len();
                    if end > start {
                        self.matches.push((line_idx, start..end));
                    }
                }
            }
        }
        (self.match_idx, self.cursor_is_on_a_match) = self.calculate_match_idx(tab.area_state.cursor);
        if query_changed && !self.cursor_is_on_a_match && select_match == 0 {
            select_match = 1;
        }
        if select_match != 0 && !self.matches.is_empty() {
            let mut i = self.match_idx;
            if !self.cursor_is_on_a_match {
                if select_match > 0 {
                    i = (i + self.matches.len() - 1) % self.matches.len();
                }
                self.cursor_is_on_a_match = true;
            }
            self.match_idx = (i as isize + select_match).rem_euclid(self.matches.len() as isize) as usize;
            tab.area_state.select(self.matches[self.match_idx].0);
        }
        assert_eq!((self.match_idx, self.cursor_is_on_a_match), self.calculate_match_idx(tab.area_state.cursor));
    }

    fn needs_update(&mut self, tab: &CodeTab) -> bool {
        (&self.query, self.tab_identity, (self.match_idx, self.cursor_is_on_a_match)) != (&SearchQuery::parse(&self.bar.text.text, /*can_have_file*/ false, /*can_go_to_line*/ false), tab.identity, self.calculate_match_idx(tab.area_state.cursor))
    }

    fn calculate_match_idx(&self, cursor: usize) -> (usize, bool) {
        let i = self.matches.partition_point(|(line, _)| *line < cursor);
        let on = self.matches.get(i).is_some_and(|(line, _)| *line == cursor);
        (i, on)
    }

    fn match_ranges_on_line(&self, line_idx: usize) -> &[Range<usize>] {
        let i = self.matches.partition_point(|(l, _)| *l < line_idx);
        if i < self.matches.len() && self.matches[i].0 == line_idx {
            &self.match_ranges[self.matches[i].1.clone()]
        } else {
            &[]
        }
    }
}

#[derive(Default)]
struct CodeWindow {
    tabs: Vec<CodeTab>,
    tabs_state: TabsState,
    file_cache: HashMap<(PathBuf, FileVersionInfo), SourceFile>,

    search_dialog: Option<SearchDialog>,

    search: CodeSearch,
    go_to_line_bar: SearchBar,

    // When this changes (usually because the user moved the cursor around the file), we scroll disassembly to the address corresponding to the selected line.
    disassembly_scrolled_to: Option<(PathBuf, FileVersionInfo, /*cursor*/ usize)>,
}
// TODO: Column cursor mode, to set breakpoints on columns. And/or clickable statements.
impl CodeWindow {
    fn find_or_open_file<'a>(file_cache: &'a mut HashMap<(PathBuf, FileVersionInfo), SourceFile>, path_in_symbols: &Path, version: &FileVersionInfo, debugger: &Debugger, palette: &Palette) -> &'a SourceFile {
        file_cache.entry((path_in_symbols.to_owned(), version.clone())).or_insert_with(|| Self::open_file(path_in_symbols, version, debugger, palette))
    }

    fn open_file(path_in_symbols: &Path, version: &FileVersionInfo, debugger: &Debugger, palette: &Palette) -> SourceFile {
        let mut res = SourceFile {header: StyledText::default(), text: StyledText::default(), local_path: PathBuf::new(), widest_line: 0, num_lines_in_local_file: 0};

        if path_in_symbols.as_os_str().is_empty() {
            return res;
        }

        match Self::find_file(path_in_symbols, &debugger.context.settings.code_dirs) {
            Some((mut file, path)) => {
                res.local_path = match std::fs::canonicalize(&path) {
                    Ok(p) => p,
                    Err(_) => path
                };

                write!(res.header.chars, "{}", res.local_path.to_string_lossy()).unwrap();
                res.header.close_span(palette.filename);
                res.header.close_line();

                match Self::read_and_format_file(&mut file, debugger, &mut res, path_in_symbols, palette) {
                    Ok((len, md5)) => {
                        let mut warn = true;
                        if version.size != 0 && version.size as usize != len {
                            write!(res.header.chars, "file doesn't match debug symbols (different size: {} vs {})", len, version.size).unwrap();
                        } else if version.md5.is_some() && version.md5 != Some(md5) {
                            write!(res.header.chars, "file doesn't match debug symbols (md5 mismatch)").unwrap();
                        } else {
                            // We don't check modification time because it's usually not preserved by version control systems, so the check would only work if the binary was built locally.
                            warn = false;
                        }
                        if warn {
                            res.header.close_span(palette.warning);
                            res.header.close_line();
                        }
                    }
                    Err(e) => {
                        write!(res.header.chars, "{}", e).unwrap();
                        res.header.close_span(palette.error);
                        res.header.close_line();
                        res.text.clear();
                    }
                }
            }
            None => {
                let path_str = path_in_symbols.to_string_lossy();
                write!(res.header.chars, "{}", path_str).unwrap();
                res.header.close_span(palette.default);
                res.header.close_line();
                if let Some(url) = rust_fake_path_to_url(&path_str) {
                    write!(res.header.chars, "can be found here:").unwrap();
                    res.header.close_span(palette.default_dim);
                    res.header.close_line();
                    
                    write!(res.header.chars, "{}", url).unwrap();
                    res.header.close_span(palette.url);
                    res.header.close_line();
                } else {
                    write!(res.header.chars, "file not found (tried all suffixes of this path)").unwrap();
                    res.header.close_span(palette.default_dim);
                    res.header.close_line();
                }

                // Make a ghost file by adding LineInfo markers to empty space.
                let mut empty: &[u8] = &[];
                Self::read_and_format_file(&mut empty, debugger, &mut res, path_in_symbols, palette).unwrap();
            }
        }

        res
    }

    fn find_file(path_in_symbols: &Path, code_dirs: &[PathBuf]) -> Option<(File, PathBuf)> {
        let components: Vec<path::Component> = path_in_symbols.components().collect();
        if components.is_empty() {
            return None;
        }
        let absolute = match &components[0] {path::Component::RootDir => true, _ => false};

        // If "" is among the search dirs, try absolute path first. Otherwise try it last (because maybe the user is specifically trying to override the root directory).
        let try_absolute_first = code_dirs.iter().any(|d| d.as_os_str().is_empty());
        if absolute && try_absolute_first {
            if let Ok(f) = File::open(path_in_symbols) {
                return Some((f, path_in_symbols.to_owned()));
            }
        }
        // Search for the file in all suffixes of the path, in case the code is in a different place from where the binary was built, or we're in subdirectory (e.g. build command was run from foo/build/, and we're in foo/src/).
        for start in absolute as usize .. components.len() {
            for base in code_dirs {
                let mut path_to_try = base.clone();
                path_to_try.extend(components[start..].iter());
                if let Ok(f) = File::open(&path_to_try) {
                    return Some((f, path_to_try));
                }
            }
        }
        if absolute && !try_absolute_first {
            if let Ok(f) = File::open(path_in_symbols) {
                return Some((f, path_in_symbols.to_owned()));
            }
        }
        None
    }

    fn read_and_format_file(input: &mut dyn Read, debugger: &Debugger, res: &mut SourceFile, path_in_symbols: &Path, palette: &Palette) -> Result<(usize, [u8; 16])> {
        // Highlight all line+column locations where we can stop (statements and inlined function call sites).
        let mut markers: Vec<LineInfo> = Vec::new();
        for binary in debugger.symbols.iter() {
            let symbols = match &binary.symbols {
                Ok(s) => s,
                Err(_) => continue };
            markers.append(&mut symbols.list_lines_for_file(path_in_symbols));
        }
        markers.sort_unstable_by_key(|l| (l.line(), l.column().saturating_sub(1), !l.flags().contains(LineFlags::INLINED_FUNCTION)));

        let insert_markers_and_close_line = |line_idx: &mut usize, text: &mut StyledText, marker_idx: &mut usize| {
            assert_eq!(*text.lines.last().unwrap(), text.num_spans());
            let line_chars_start = text.spans.last().unwrap().0;
            *line_idx += 1;
            let mut prev_column = -1isize;
            while *marker_idx < markers.len() && markers[*marker_idx].line() <= *line_idx {
                let marker = &markers[*marker_idx];
                assert_eq!(marker.line(), *line_idx);
                let column = marker.column().saturating_sub(1);
                if column as isize <= prev_column {
                    assert_eq!(column as isize, prev_column);
                    *marker_idx += 1;
                    continue;
                }
                prev_column = column as isize;
                if line_chars_start + column >= text.chars.len() {
                    unsafe {text.chars.as_mut_vec().resize(line_chars_start + column + 1, b' ');}
                }
                let prev_span_end = text.spans.last().unwrap().0;
                assert!(line_chars_start + column >= prev_span_end);
                if line_chars_start + column > prev_span_end {
                    text.spans.push((line_chars_start + column, palette.default));
                }
                text.spans.push((line_chars_start + column + 1, if marker.flags().contains(LineFlags::INLINED_FUNCTION) {palette.code_inlined_site} else {palette.code_statement}));
                *marker_idx += 1;
            }
            text.close_span(palette.default);
            text.close_line();
        };

        let mut marker_idx = 0usize;
        while marker_idx < markers.len() && markers[marker_idx].line() == 0 {
            marker_idx += 1;
        }

        let mut line_idx = 0usize;
        let mut buffered = HashingBufReader::new(input);
        loop {
            let buf = buffered.fill_buf()?;
            if buf.is_empty() {
                if res.text.spans.last().unwrap().0 < res.text.chars.len() {
                    insert_markers_and_close_line(&mut line_idx, &mut res.text, &mut marker_idx);
                }
                break;
            }
            let c = buf[0];
            if c == b'\r' || c == b'\n' {
                buffered.consume(1);
                if c == b'\r' && buffered.fill_buf()?.starts_with(b"\n") {
                    buffered.consume(1);
                }
                insert_markers_and_close_line(&mut line_idx, &mut res.text, &mut marker_idx);
                continue;
            }
            if c == b'\t' {
                buffered.consume(1);
                for i in 0..debugger.context.settings.tab_width {
                    res.text.chars.push(' ');
                }
                continue;
            }
            let n = buf.iter().copied().position(|c| c == b'\r' || c == b'\n' || c == b'\t').unwrap_or(buf.len());
            match String::from_utf8_lossy(&buf[..n]) {
                Cow::Borrowed(s) => res.text.chars.push_str(s),
                Cow::Owned(s) => res.text.chars.push_str(&s) };
            buffered.consume(n);
        }
        res.num_lines_in_local_file = res.text.num_lines();

        while marker_idx < markers.len() {
            insert_markers_and_close_line(&mut line_idx, &mut res.text, &mut marker_idx);
        }

        res.widest_line = res.text.widest_line(0..res.text.num_lines());

        Ok((buffered.count, buffered.hasher.compute().into()))
    }

    fn make_title(path_in_symbols: &Path) -> String {
        if path_in_symbols.as_os_str().is_empty() {
            "[unknown]".to_string()
        } else if let Some(f) = path_in_symbols.file_name() {
            f.to_string_lossy().into_owned()
        } else {
            "?".to_string()
        }
    }

    fn switch_to_file(&mut self, path_in_symbols: &Path, version: &FileVersionInfo, debugger: &Debugger) {
        if let Some(i) = self.tabs.iter().position(|t| &t.path_in_symbols == path_in_symbols && &t.version_in_symbols == version) {
            self.tabs_state.select(i);
            return;
        }
        let title = Self::make_title(path_in_symbols);
        self.tabs.push(CodeTab {identity: random(), title, path_in_symbols: path_in_symbols.to_owned(), version_in_symbols: version.clone(), area_state: AreaState::default(), ephemeral: true});
        self.tabs_state.select(self.tabs.len() - 1);
    }

    fn toggle_breakpoint(tab: &CodeTab, delete: bool, edit_condition: bool, state: &mut UIState, debugger: &mut Debugger, ui: &mut UI) {
        if tab.path_in_symbols.as_os_str().is_empty() {
            return;
        }
        ui.should_redraw = true;
        let line_breakpoint = Self::make_breakpoint_for_current_line(tab);
        let breakpoint_id = debugger.find_line_breakpoint_fuzzy(&line_breakpoint);

        if delete {
            match breakpoint_id {
                Some(id) => { debugger.remove_breakpoint(id); },
                None => { state.last_error = "no breakpoint".to_string(); },
            }
            return;
        }

        let breakpoint_id = match breakpoint_id {
            Some(id) if edit_condition => id, // don't toggle existing breakpoint on alt-enter
            Some(id) => {
                let enable = !debugger.breakpoints.get(id).enabled;
                let r = debugger.set_breakpoint_enabled(id, enable);
                report_result(state, &r);
                id
            }
            None => {
                let r = debugger.add_breakpoint(BreakpointOn::Line(line_breakpoint));
                report_result(state, &r);
                match r {
                    Ok(x) => x,
                    Err(_) => return,
                }
            }
        };

        if edit_condition {
            state.should_edit_breakpoint_condition = Some(breakpoint_id);
        }
    }

    fn step_to_cursor(tab: &CodeTab, state: &mut UIState, debugger: &mut Debugger, ui: &mut UI) {
        if tab.path_in_symbols.as_os_str().is_empty() {
            return;
        }
        ui.should_redraw = true;
        let r = debugger.step_to_cursor(state.selected_thread, BreakpointOn::Line(Self::make_breakpoint_for_current_line(tab)));
        report_result(state, &r);
    }

    fn make_breakpoint_for_current_line(tab: &CodeTab) -> LineBreakpoint {
        LineBreakpoint {path: tab.path_in_symbols.clone(), file_version: tab.version_in_symbols.clone(), line: tab.area_state.cursor + 1, adjusted_line: None}
    }

    fn evict_cache(&mut self) {
        if self.file_cache.len().saturating_sub(self.tabs.len()) > 100 {
            // Drop half of the cached files that don't have tabs open.
            let in_use: HashSet<(PathBuf, FileVersionInfo)> = self.tabs.iter().map(|t| (t.path_in_symbols.clone(), t.version_in_symbols.clone())).collect();
            let mut i = 0;
            self.file_cache.retain(
                |k, _|
                if in_use.contains(k) {
                    true
                } else {
                    i += 1;
                    i % 2 == 0
                }
            );
        }
    }

    fn disassembly_scroll_key(&self) -> Option<(PathBuf, FileVersionInfo, usize)> {
        match self.tabs.get(self.tabs_state.selected) {
            Some(t) if !t.path_in_symbols.as_os_str().is_empty() => Some((t.path_in_symbols.clone(), t.version_in_symbols.clone(), t.area_state.cursor)),
            _ => None,
        }
    }

    fn scroll_disassembly_if_needed(&mut self, suppress: bool, select: isize, state: &mut UIState, debugger: &Debugger) {
        let key = match self.disassembly_scroll_key() {
            None => return,
            Some(key) if Some(&key) == self.disassembly_scrolled_to.as_ref() && select == 0 => return,
            Some(x) => x,
        };
        self.disassembly_scrolled_to = Some(key.clone());
        if suppress {
            return;
        }

        for binary in debugger.symbols.iter() {
            let symbols = match &binary.symbols {
                Ok(s) => s,
                Err(_) => continue,
            };
            let file_idx = match symbols.path_to_used_file.get(&key.0 as &Path) {
                Some(i) => *i,
                None => continue };
            let addrs0 = match symbols.line_to_addrs(file_idx, key.2 + 1, false) {
                Ok(x) => x,
                Err(_) => continue,
            };
            assert!(!addrs0.is_empty());
            let mut addrs: Vec<(/*function_idx*/ usize, /*subfunction_level*/ u16, /*static_addr*/ usize)> = Vec::new();
            for (line, level) in addrs0 {
                let static_addr = line.addr();
                if let Ok((_, function_idx)) = symbols.addr_to_function(static_addr) {
                    addrs.push((function_idx, level, static_addr));
                }
            }
            if addrs.is_empty() {
                continue;
            }
            addrs.sort_unstable_by_key(|(_, _, a)| *a);

            // You'd think it's trivial to scroll disassembly to the address corresponding to the selected line of source code.
            // But suppose the line is in a function that is inlined at various call sites, and may also have its own machine code.
            // Which of those should we select? Always the non-inlined one? No. The user could be looking at an inlined site
            // (e.g. autoselected based on stack trace) - then jumping to a totally different function would be jarring.
            // So I guess we should pick the address that's "closest" to the disassembly window's cursor, where "closest" means it's is in the
            // same function and has the lowest lowest-common-ancestor in subfunction tree. That's what we do here.
            // This can still be pretty annoying though: if you randomly scroll back and forth in the source file, the disassembly will probably
            // jump to a different function at some point and will forget the relevant inlined site; maybe we should take stack trace into account too?
            let mut closest_idx = addrs.iter().position(|&(function_idx, level, static_addr)| {
                if level == 0 {
                    return true;
                }
                if level != u16::MAX {
                    return false;
                }
                let function = &symbols.functions[function_idx];
                if function.num_levels() < 2 {
                    return true;
                }
                let ranges = symbols.subfunctions_at_level(1, function);
                let idx = ranges.partition_point(|r| r.addr_range.end <= static_addr);
                idx == ranges.len() || ranges[idx].addr_range.start > static_addr
            }).unwrap_or(0);
            let mut selected_idx: Option<usize> = None;
            if let Some((binary_id, selected_function_idx, selected_addr)) = &state.selected_addr {
                if let Some(binary) = debugger.symbols.get(*binary_id) {
                    let selected_static_addr = binary.addr_map.dynamic_to_static(*selected_addr);
                    let symbols = binary.symbols.as_ref().unwrap();
                    let function = &symbols.functions[*selected_function_idx];
                    let shard = &symbols.shards[function.shard_idx()];
                    let mut subfunction_ranges: Vec<Range<usize>> = Vec::new();
                    for level in 1..function.num_levels().max(1) {
                        let pc_ranges = symbols.subfunctions_at_level(level, function);
                        let idx = pc_ranges.partition_point(|r| r.addr_range.end <= selected_static_addr);
                        if idx == pc_ranges.len() || pc_ranges[idx].addr_range.start > selected_static_addr {
                            break;
                        }
                        subfunction_ranges.push(pc_ranges[idx].addr_range.clone());
                    }
                    let mut closest = (0usize, 0usize);
                    for (idx, &(function_idx, _, static_addr)) in addrs.iter().enumerate() {
                        if static_addr == selected_static_addr {
                            selected_idx = Some(idx);
                        }
                        if function_idx != *selected_function_idx {
                            continue;
                        }
                        let mut level = 0usize;
                        while level < subfunction_ranges.len() && subfunction_ranges[level].contains(&static_addr) {
                            level += 1;
                        }
                        if level+1 > closest.0 {
                            closest = (level+1, idx);
                        }
                    }
                    closest_idx = closest.1;
                }
            }

            let idx = match selected_idx {
                Some(i) => (i as isize + select) as usize % addrs.len(),
                None => closest_idx,
            };

            state.should_scroll_disassembly = Some((Ok(DisassemblyScrollTarget {binary_id: binary.id, function_idx: addrs[idx].0, static_pseudo_addr: addrs[idx].2, subfunction_level: addrs[idx].1, cascade: false}), false));

            break;
        }
    }

    fn build_search_dialog(&mut self, create: bool, state: &mut UIState, debugger: &mut Debugger, ui: &mut UI) {
        let dialog_widget = match make_dialog_frame(create, AutoSize::Remainder(0.75), AutoSize::Remainder(0.83), ui.palette.dialog, ui.palette.filename, "find file (by path from debug info)", ui) {
            None => {
                self.search_dialog = None;
                return;
            }
            Some(x) => x };

        let d = self.search_dialog.get_or_insert_with(|| SearchDialog::new(Arc::new(FileSearcher), debugger.context.clone()));
        with_parent!(ui, dialog_widget, {
            d.build(&debugger.symbols, ui);
        });

        if d.should_close_dialog {
            ui.close_dialog();
        }

        if let Some(res) = mem::take(&mut d.should_open_document) {
            let file = &res.symbols.files[res.id];
            let go_to_line = d.search.query.go_to_line.clone();
            self.switch_to_file(&res.file, &file.version, debugger);
            let tab = &mut self.tabs[self.tabs_state.selected];
            tab.ephemeral = false;
            if let Some(n) = go_to_line {
                tab.area_state.select(n.saturating_sub(1));
            }
        }
    }

    fn handle_tabs_action(&mut self, action: TabsAction) -> bool {
        if let &TabsAction::Close(idx) = &action {
            if let Some(tab) = self.tabs.get_mut(idx) {
                if tab.ephemeral && !tab.path_in_symbols.as_os_str().is_empty() {
                    tab.ephemeral = false;
                    return true;
                }
            }
        }
        self.tabs_state.apply_action(action, &mut self.tabs)
    }

    fn build_tab_content(&mut self, tabs_widget: WidgetIdx, search_select_match: isize, suppress_disassembly_autoscroll: bool, state: &mut UIState, debugger: &mut Debugger, ui: &mut UI) {
        let tab = match self.tabs.get_mut(self.tabs_state.selected) {
            None => return,
            Some(t) => t };
        let file = Self::find_or_open_file(&mut self.file_cache, &tab.path_in_symbols, &tab.version_in_symbols, debugger, &ui.palette);

        let mut select_disassembly_address: isize = 0;
        for action in ui.check_keys(&[KeyAction::Enter, KeyAction::EditCondition, KeyAction::DeleteRow, KeyAction::PreviousLocation, KeyAction::NextLocation, KeyAction::StepToCursor]) {
            match action {
                KeyAction::PreviousLocation => select_disassembly_address -= 1,
                KeyAction::NextLocation => select_disassembly_address += 1,
                KeyAction::Enter | KeyAction::DeleteRow | KeyAction::EditCondition => Self::toggle_breakpoint(tab, action == KeyAction::DeleteRow, action == KeyAction::EditCondition, state, debugger, ui),
                KeyAction::StepToCursor => Self::step_to_cursor(tab, state, debugger, ui),
                _ => (),
            }
        }

        let header_widget = ui.add(widget!().fixed_height(file.header.num_lines()));
        let search_bar = ui.add(widget!());
        let go_to_line_bar = ui.add(widget!().fixed_height(0));

        // Multifocus the widgets in the correct order.
        with_parent!(ui, go_to_line_bar, {ui.multifocus();});
        with_parent!(ui, search_bar, {ui.multifocus();});
        with_parent!(ui, tabs_widget, {ui.multifocus();});

        with_parent!(ui, search_bar, {
            self.search.update(tab, &file.text, search_select_match);

            let l = ui_writeln!(ui, default, "find: ");
            let r = if self.search.query.is_empty {
                None
            } else if self.search.matches.is_empty() {
                Some(ui_writeln!(ui, default_dim, "no results"))
            } else {
                Some(ui_writeln!(ui, default_dim, "{}/{}", self.search.match_idx.min(self.search.matches.len() - 1) + 1, self.search.matches.len()))
            };
            self.search.bar.build(Some(l), r, ui);
        });

        with_parent!(ui, go_to_line_bar, {
            if self.go_to_line_bar.visible {
                let prev_text = self.go_to_line_bar.text.text.clone();
                let num_lines = file.text.num_lines().max(1);
                let left = ui_writeln!(ui, default, "go to line (1-{}): ", num_lines);

                self.go_to_line_bar.hide_when_not_editing = true;
                self.go_to_line_bar.build(Some(left), None, ui);

                if self.go_to_line_bar.text.text != prev_text {
                    if let Ok(n) = self.go_to_line_bar.text.text.parse::<usize>() {
                        tab.area_state.select(n.saturating_sub(1));
                    }
                }

                if !self.go_to_line_bar.visible {
                    // The focus+capture_keys system has its quirks.
                    // This line is needed to prevent Escape key press from being eaten after closing go-to-file bar while search bar is also open.
                    // (Exact repro: run with --period 0; do a search, press Escape, press F3 to open the search bar without enabling its text input, press g to open the go-to-line bar,
                    //  press Escape or Enter to close the go-to-line bar, press Escape to close the search bar - and it doesn't close; press Escape again, and it closes.)
                    // This happens because on the frame when go-to-line bar is closed, it already requested captured keys for next frame, so they get routed to it even though it doesn't care about those inputs anymore.
                    ui.should_redraw = true;
                }
            }
        });

        let content_root = ui.add(widget!().height(AutoSize::Remainder(1.0)));
        with_parent!(ui, content_root, {
            ui.multifocus();
        });
        ui.layout_children(Axis::Y);

        // (path_in_symbols, line) -> (column, selected, top)
        let mut instruction_pointers: HashMap<(&Path, usize), (usize, bool, bool)> = HashMap::new();
        for (idx, subframe) in state.stack.subframes.iter().enumerate() {
            if let Some(info) = &subframe.line {
                instruction_pointers.insert((&info.path, info.line.line()), (info.line.column(), idx == state.selected_subframe, idx == 0));
            }
        }

        let line_num_len = (file.text.num_lines().saturating_add(1) as f64).log10().ceil() as usize;
        let prefix_width = line_num_len + 2 + 2 + 1;

        let (content, visible_y) = with_parent!(ui, content_root, {
            let header = ui.text.import_lines(&file.header, 0..file.header.num_lines());
            build_biscrollable_area_with_header(Some(header_widget), header, [prefix_width + file.widest_line, file.text.num_lines()], &mut tab.area_state, ui)
        });

        // Now the cursor is final.

        if self.search.needs_update(tab) {
            ui.should_redraw = true;
        }

        struct BreakpointLine {
            line: usize,
            id: BreakpointId,
            enabled: bool,
            has_locations: bool,
            active: bool,
            adjusted: bool,
            conditional: bool,
        }
        let mut breakpoint_lines: Vec<BreakpointLine> = Vec::new();
        for (id, breakpoint) in debugger.breakpoints.iter() {
            match &breakpoint.on {
                BreakpointOn::Line(bp) if bp.path == tab.path_in_symbols => {
                    let conditional = breakpoint.condition.is_some();
                    breakpoint_lines.push(BreakpointLine {line: bp.line, id, enabled: breakpoint.enabled, has_locations: false, active: breakpoint.active, adjusted: false, conditional});
                    if let Some(&adj) = bp.adjusted_line.as_ref() {
                        if adj != bp.line && breakpoint.enabled {
                            breakpoint_lines.push(BreakpointLine {line: adj, id, enabled: breakpoint.enabled, has_locations: false, active: breakpoint.active, adjusted: true, conditional});
                        }
                    }
                }
                _ => () };
        }
        breakpoint_lines.sort_by_key(|t| (t.id, /* should attribute locations to the adjusted line, if present */ !t.adjusted));
        for location in &debugger.breakpoint_locations {
            for br in &location.breakpoints {
                if let &BreakpointRef::Id {id, ..} = br {
                    let idx = breakpoint_lines.partition_point(|b| b.id < id);
                    if idx < breakpoint_lines.len() && breakpoint_lines[idx].id == id {
                        if location.active {
                            breakpoint_lines[idx].has_locations = true;
                        } else {
                            breakpoint_lines[idx].active = false;
                        }
                    }
                }
            }
        }
        breakpoint_lines.sort_by_key(|t| (t.line, /* if there's an adjusted and unadjusted breakpoint on the same line, show the unadjusted one */ t.adjusted));

        with_parent!(ui, content, {
            let line_range = visible_y.start.max(0) as usize .. (visible_y.end.max(0) as usize).min(file.text.num_lines());
            let mut adjustments: Vec<(Range<usize>, StyleAdjustment)> = Vec::new();
            for i in line_range.clone() {
                let mut column_number = 0usize;
                let mut is_main_ip = false;

                match instruction_pointers.get(&(&tab.path_in_symbols, i + 1)) {
                    None => ui_write!(ui, default, "  "),
                    Some(&(col, is_selected, _is_top)) => {
                        column_number = col;
                        let style = if is_selected {ui.palette.instruction_pointer} else {ui.palette.additional_instruction_pointer};
                        is_main_ip = is_selected;
                        styled_write!(ui.text, style, "⮕ ");
                    }
                };

                let idx = breakpoint_lines.partition_point(|t| t.line < i + 1);
                if idx < breakpoint_lines.len() && breakpoint_lines[idx].line == i + 1 {
                    let l = &breakpoint_lines[idx];
                    let (marker, style) = get_breakpoint_icon(l.enabled, l.active, l.adjusted, l.conditional, /*data*/ false, /*stop_on_read*/ false, &ui.palette);
                    styled_write!(ui.text, style, "{}", marker);
                } else {
                    ui_write!(ui, default, "  ");
                }

                ui_write!(ui, default_dim, "{: >2$}{}", i + 1, if i < file.num_lines_in_local_file {" "} else {"~"}, line_num_len);

                // Highlight search results.
                adjustments.clear();
                if self.search.bar.visible {
                    for r in self.search.match_ranges_on_line(i) {
                        adjustments.push((r.clone(), ui.palette.search_result));
                    }
                }

                // Underline the character at the column number.
                // Note that the text line should always be long enough to cover this line number because we extend lines when loading the file to cover all columns that appear in debug info.
                let line_len = file.text.get_line_str(i).len();
                if column_number != 0 {
                    adjustments.push((column_number-1..column_number, ui.palette.code_instruction_pointer_column));
                }
                adjustments.sort_unstable_by_key(|(r, _)| r.start);

                let l = ui.text.import_line_with_adjustments(&file.text, i, &adjustments);

                let mut w = widget!().fixed_height(1).fixed_y(i as isize).text(l).fill(' ', ui.palette.default).flags(WidgetFlags::HSCROLL_INDICATOR_RIGHT).highlight_on_hover();
                if i == tab.area_state.cursor {
                    w.style_adjustment.update(ui.palette.selected);
                }
                if is_main_ip {
                    w.style_adjustment.update(ui.palette.ip_line);
                }
                ui.add(w);
            }
        });

    self.scroll_disassembly_if_needed(suppress_disassembly_autoscroll, select_disassembly_address, state, debugger);
}
}
impl WindowContent for CodeWindow {
    fn build(&mut self, state: &mut UIState, debugger: &mut Debugger, ui: &mut UI) {
        let mut open_dialog = false;
        let mut search_select_match = 0isize;
        // TODO: Move CloseTab logic into Tabs, next to reordering logic. Also close tabs with middle click.
        for action in ui.check_keys(&[KeyAction::Open, KeyAction::CloseTab, KeyAction::ReorderRowUp, KeyAction::ReorderRowDown, KeyAction::GoToLine, KeyAction::Find, KeyAction::NextMatch, KeyAction::PreviousMatch]) {
            match action {
                KeyAction::Open if self.search_dialog.is_none() => open_dialog = true,
                KeyAction::CloseTab => {self.handle_tabs_action(TabsAction::Close(self.tabs_state.selected));}
                KeyAction::ReorderRowUp if self.tabs_state.selected > 0 => {self.handle_tabs_action(TabsAction::Reorder {from_idx: self.tabs_state.selected, to_idx: self.tabs_state.selected - 1});}
                KeyAction::ReorderRowDown => {self.handle_tabs_action(TabsAction::Reorder {from_idx: self.tabs_state.selected, to_idx: self.tabs_state.selected + 2});}
                KeyAction::GoToLine => {
                    self.go_to_line_bar.text.clear();
                    self.go_to_line_bar.start_editing();
                }
                KeyAction::Find => self.search.bar.start_editing(),
                KeyAction::NextMatch => {
                    self.search.bar.visible = true;
                    search_select_match += 1;
                }
                KeyAction::PreviousMatch => {
                    self.search.bar.visible = true;
                    search_select_match -= 1;
                }
                _ => (),
            }
        }

        self.build_search_dialog(open_dialog, state, debugger, ui);

        let suppress_disassembly_autoscroll = match &state.should_scroll_source {
            None => false,
            Some((None, _)) => true,
            Some((Some(SourceScrollTarget {cascade, ..}), _)) => !cascade,
        };
        let switch_to = match mem::take(&mut state.should_scroll_source) {
            Some((to, false)) => Some(to),
            Some((to, true)) if self.tabs.is_empty() || self.tabs[self.tabs_state.selected].path_in_symbols.as_os_str().is_empty() => Some(to),
            _ => None,
        };

        match switch_to {
            None => (),
            Some(None) => self.switch_to_file(Path::new(""), &FileVersionInfo::default(), debugger),
            Some(Some(target)) => {
                self.switch_to_file(&target.path, &target.version, debugger);
                let tab = &mut self.tabs[self.tabs_state.selected];
                tab.area_state.select(target.line.saturating_sub(1));
            }
        }

        close_excess_ephemeral_tabs(&mut self.tabs, &mut self.tabs_state, |t| t.ephemeral);
        self.evict_cache();

        // Now the set of tabs is final.

        ui.cur_mut().set_vstack();
        let tabs_widget = ui.add(widget!().fixed_height(1));
        let tabs_action;
        with_parent!(ui, tabs_widget, {
            let mut tabs = Tabs::new(mem::take(&mut self.tabs_state), ui);
            tabs.allow_reordering = true;
            for tab in &self.tabs {
                let full_title = tab.path_in_symbols.as_os_str().to_string_lossy().into_owned();
                tabs.add(Tab {identity: tab.identity, short_title: tab.title.clone(), full_title, ephemeral: tab.ephemeral, allow_closing: true, ..Default::default()}, ui);
            }
            (self.tabs_state, tabs_action) = tabs.finish(ui);
        });

        // Now the selected tab is final.

        self.build_tab_content(tabs_widget, search_select_match, suppress_disassembly_autoscroll, state, debugger, ui);

        if self.handle_tabs_action(tabs_action) {
            ui.should_redraw = true;
        }
    }

    fn drop_caches(&mut self) {
        self.file_cache.clear();
        self.search.tab_identity = 0;
    }

    fn get_key_hints(&self, out: &mut Vec<KeyHint>, debugger: &Debugger) {
        out.extend([
            KeyHint::key(KeyAction::Open, "open file"),
            KeyHint::key(KeyAction::CloseTab, "close/pin tab"),
            KeyHint::keys(&[KeyAction::PreviousLocation, KeyAction::NextLocation], "cycle disasm addrs"),
            KeyHint::key(KeyAction::GoToLine, "go to line"),
            KeyHint::key(KeyAction::Find, "find"),
            KeyHint::keys(&[KeyAction::NextMatch, KeyAction::PreviousMatch], "find next/previous"),
            KeyHint::keys(&[KeyAction::Enter, KeyAction::DeleteRow, KeyAction::EditCondition], "toggle/delete/edit breakpoint").if_not_core_dump(),
            KeyHint::keys(&[KeyAction::ReorderRowUp, KeyAction::ReorderRowDown], "reorder tabs"),
            KeyHint::key(KeyAction::StepToCursor, "run to cursor").if_not_core_dump(),
        ]);
    }

    fn save_state(&self, out: &mut Vec<u8>) -> Result<()> {
        for (i, tab) in self.tabs.iter().enumerate() {
            if tab.ephemeral {
                continue;
            }
            out.write_u8(if i == self.tabs_state.selected {2} else {1})?;
            out.write_path(&tab.path_in_symbols)?;
            tab.version_in_symbols.save_state(out)?;
            tab.area_state.save_state(out)?;
        }
        out.write_u8(0)?;
        Ok(())
    }
    fn load_state(&mut self, inp: &mut &[u8]) -> Result<()> {
        loop {
            match inp.read_u8()? {
                1 => (),
                2 => self.tabs_state.select(self.tabs.len()),
                _ => break,
            }
            let path_in_symbols = inp.read_path()?;
            let title = Self::make_title(&path_in_symbols);
            self.tabs.push(CodeTab {identity: random(), title, path_in_symbols, version_in_symbols: FileVersionInfo::load_state(inp)?, area_state: AreaState::load_state(inp)?, ephemeral: false});
        }
        // Prevent auto-scrolling the disassembly window before any input is made.
        self.disassembly_scrolled_to = self.disassembly_scroll_key();
        Ok(())
    }
}

#[derive(Default)]
struct BreakpointsWindow {
    table_state: TableState,
    selected_breakpoint: Option<BreakpointId>,
    condition_input: Option<(BreakpointId, TextInput)>,
}
impl WindowContent for BreakpointsWindow {
    fn get_key_hints(&self, out: &mut Vec<KeyHint>, debugger: &Debugger) {
        out.extend([
            KeyHint::key(KeyAction::DeleteRow, "delete breakpoint"),
            KeyHint::keys(&[KeyAction::Enter, KeyAction::EditCondition], "enable/disable/edit breakpoint"),
            KeyHint::key(KeyAction::Tooltip, "tooltip"),
        ]);
    }

    fn build(&mut self, state: &mut UIState, debugger: &mut Debugger, ui: &mut UI) {
        state.hit_breakpoints.clear();
        for (tid, thread) in &debugger.threads {
            for reason in &thread.stop_reasons {
                if let &StopReason::Breakpoint(id) = reason {
                    state.hit_breakpoints.push(id);
                }
            }
        }
        state.hit_breakpoints.sort();
        state.hit_breakpoints.dedup();

        let mut table = Table::new(mem::take(&mut self.table_state), ui, vec![
            Column::new("idx", AutoSize::Text, false),
            Column::new("", AutoSize::Fixed(4), false),
            Column::new("on", AutoSize::Remainder(1.0), false),
            Column::new("locs", AutoSize::Text, false),
            Column::new("hits", AutoSize::Text, false),
        ]);
        table.hide_cursor_if_unfocused = true;

        let mut start_editing_condition = false;
        if let Some(id) = mem::take(&mut state.should_edit_breakpoint_condition) {
            self.selected_breakpoint = Some(id);
            start_editing_condition = true;
        }

        for action in ui.check_keys(&[KeyAction::DeleteRow, KeyAction::Enter, KeyAction::EditCondition, KeyAction::Cancel]) {
            if action == KeyAction::Cancel {
                self.condition_input = None;
            }
            let id = match &self.selected_breakpoint {
                None => continue,
                &Some(x) => x };
            let breakpoint = match debugger.breakpoints.try_get(id) {
                None => continue,
                Some(x) => x };
            match action {
                KeyAction::DeleteRow => {
                    debugger.remove_breakpoint(id);
                    table.state.scroll_to_cursor = true; // to auto-update the code window
                }
                KeyAction::Enter | KeyAction::EditCondition if self.condition_input.as_ref().is_some_and(|(idd, _)| *idd == id) => {
                    let text = mem::take(&mut self.condition_input).unwrap().1.text;
                    let condition = if text.is_empty() {None} else {Some(text)};
                    debugger.set_breakpoint_condition(id, condition);
                }
                KeyAction::EditCondition => start_editing_condition = true,
                KeyAction::Enter => {
                    let enable = !breakpoint.enabled;
                    let r = debugger.set_breakpoint_enabled(id, enable);
                    report_result(state, &r);
                }
                _ => (),
            }
        }

        if start_editing_condition {
            if let &Some(id) = &self.selected_breakpoint {
                if let Some(breakpoint) = debugger.breakpoints.try_get(id) {
                    let text = breakpoint.condition.as_ref().map_or(String::new(), |(s, _, _)| s.clone());
                    self.condition_input = Some((id, TextInput::new_multiline(text)));
                }
            }
        }

        let mut breakpoints: Vec<BreakpointId> = debugger.breakpoints.iter().filter(|(_, b)| !b.hidden).map(|p| p.0).collect();
        breakpoints.sort_by_key(|id| id.seqno);

        if let &Some(id) = &self.selected_breakpoint {
            if let Some(idx) = breakpoints.iter().position(|b| b == &id) {
                table.state.cursor = idx;
            }
        }

        let mut locations: Vec<(BreakpointId, /*is_error*/ bool, /*i*/ usize)> = Vec::new();
        for (i, loc) in debugger.breakpoint_locations.iter().enumerate() {
            for b in &loc.breakpoints {
                match b {
                    BreakpointRef::Id {id, ..} => locations.push((*id, loc.error.is_some(), i)),
                    _ => ()}
            }
        }
        locations.sort_unstable_by_key(|(id, _, _)| *id);

        let mut text_input_parent_widget = None;
        for &id in &breakpoints {
            let b = debugger.breakpoints.get(id);
            let is_hit = state.hit_breakpoints.binary_search(&id).is_ok();
            let locs_begin = locations.partition_point(|t| t.0 < id);
            let locs_end = locations.partition_point(|t| t.0 <= id);
            let (data, stop_on_read) = match &b.on {
                BreakpointOn::Data(d) => (true, d.stop_on_read),
                _ => (false, false) };

            let mut error: Option<Error> = None;
            if b.enabled {
                match &b.addrs {
                    Err(e) if !e.is_not_calculated() && !e.is_loading() => error = Some(e.clone()),
                    _ => for &(_, is_error, loc_idx) in &locations[locs_begin..locs_end] {
                        if is_error {
                            error = Some(debugger.breakpoint_locations[loc_idx].error.clone().unwrap());
                            break;
                        }
                    }
                }
            }

            let row_widget = table.start_row(id.seqno, ui);

            ui_writeln!(ui, default_dim, "{}", id.seqno);
            table.text_cell(ui);

            ui_write!(ui, instruction_pointer, "{}", if is_hit {"⮕ "} else {"  "});
            let (marker, style) = get_breakpoint_icon(b.enabled, b.active, /*secondary*/ false, b.condition.is_some(), data, stop_on_read, &ui.palette);
            styled_writeln!(ui.text, style, "{}", marker);
            with_parent!(ui, table.text_cell(ui), {
                ui.cur_mut().flags.insert(WidgetFlags::HIGHLIGHT_ON_HOVER);
                if ui.check_mouse(MouseActions::CLICK) {
                    let enabled = b.enabled;
                    let r = debugger.set_breakpoint_enabled(id, !enabled);
                    report_result(state, &r);
                    ui.should_redraw = true;
                }
            });
            let b = debugger.breakpoints.get(id);

            match &b.on {
                BreakpointOn::Line(on) => {
                    let name = on.path.as_os_str().to_string_lossy();
                    ui_write!(ui, filename, "{}", name);
                    ui_write!(ui, line_number, ":{}", on.line);
                    if let &Some(adj) = &on.adjusted_line {
                        ui_write!(ui, default_dim, "→");
                        ui_write!(ui, line_number, "{}", adj);
                    }
                }
                BreakpointOn::Instruction(on) => {
                    if let Some((locator, offset)) = &on.function {
                        ui_write!(ui, function_name, "{}", locator.demangled_name);
                        ui_write!(ui, default, " + 0x{:x}", offset);
                    } else {
                        ui_write!(ui, default, "{:x}", on.addr);
                    }
                }
                BreakpointOn::InitialExec => ui_write!(ui, default, "early during startup"),
                BreakpointOn::PointOfInterest(point) => ui_write!(ui, default, "{}", point.name_for_ui()),
                BreakpointOn::Data(on) => ui_write!(ui, default, "0x{:x} ({}, {} bytes)", on.addr, if on.stop_on_read {"rw"} else {"w"}, on.size),
            }
            let row_is_focused = ui.check_focus();
            let l = ui.text.close_line();
            with_parent!(ui, table.start_cell(ui), {
                ui.cur_mut().set_vstack();

                ui.add(widget!().height(AutoSize::Text).text(l).flags(WidgetFlags::TEXT_TRUNCATION_ALIGN_RIGHT));

                if (row_is_focused || start_editing_condition) && self.condition_input.as_ref().is_some_and(|(idd, _)| *idd == id) {
                    text_input_parent_widget = Some(ui.cur_parent);
                } else if let Some((text, expr, err)) = &b.condition {
                    let l = ui_writeln!(ui, default, "{}", text);
                    let lines = ui.text.split_by_newline_character(l, None);
                    with_parent!(ui, ui.add(widget!().height(AutoSize::Text).text_lines(lines).flags(WidgetFlags::LINE_WRAP)), {
                        if ui.check_mouse(MouseActions::CLICK) {
                            state.should_edit_breakpoint_condition = Some(id);
                            ui.should_redraw = true;
                        }
                    });

                    if let Err(e) = expr {
                        let l = ui_writeln!(ui, error, "{}", e);
                        ui.add(widget!().height(AutoSize::Text).text(l).flags(WidgetFlags::LINE_WRAP));
                    } else if let Some(e) = err {
                        let l = ui_writeln!(ui, error, "{}", e);
                        ui.add(widget!().height(AutoSize::Text).text(l).flags(WidgetFlags::LINE_WRAP));
                    }
                }

                if let Some(e) = &error {
                    let l = ui_writeln!(ui, error, "{}", e);
                    ui.add(widget!().height(AutoSize::Text).text(l).flags(WidgetFlags::LINE_WRAP));
                }
            });

            if b.enabled && !b.on.is_data() {
                ui_writeln!(ui, default_dim, "{}", locs_end - locs_begin);
            } else {
                ui.text.close_line();
            }
            table.text_cell(ui);

            ui_writeln!(ui, default_dim, "{}", b.hits);
            table.text_cell(ui);

            if error.is_some() {
                let a = ui.palette.breakpoint_error;
                ui.get_mut(row_widget).style_adjustment.update(a);
            }
        }

        table.finish_horizontal_layout(ui);
        if let Some(input_parent_widget) = text_input_parent_widget {
            // Build the text input once we know the table column width.
            let input_widget = ui.add(widget!().parent(input_parent_widget).identity(&'i').height(AutoSize::Children));
            with_parent!(ui, input_widget, {
                let input = &mut self.condition_input.as_mut().unwrap().1;
                let changed = input.build(ui);
                table.state.scroll_to_cursor |= changed;
            });
        } else {
            self.condition_input = None;
        }

        self.table_state = table.finish(ui);

        self.selected_breakpoint = breakpoints.get(self.table_state.cursor).copied();

        if self.table_state.did_scroll_to_cursor {
            if let &Some(id) = &self.selected_breakpoint {
                match &debugger.breakpoints.get(id).on {
                    BreakpointOn::Line(on) => {
                        state.should_scroll_source = Some((Some(SourceScrollTarget {path: on.path.clone(), version: on.file_version.clone(), line: on.line, cascade: true}), false));
                    }
                    BreakpointOn::Instruction(on) => {
                        if let Some((locator, offset)) = &on.function {
                            if let Ok(binary) = Debugger::find_binary_fuzzy(&debugger.symbols, &locator.binary_locator) {
                                if let Ok(symbols) = &binary.symbols {
                                    if let Some(function_idx) = symbols.find_nearest_function(&locator.mangled_name, locator.addr) {
                                        let function = &symbols.functions[function_idx];
                                        state.should_scroll_disassembly = Some((Ok(DisassemblyScrollTarget {
                                            binary_id: binary.id, function_idx, static_pseudo_addr: function.addr.0 + offset, subfunction_level: on.subfunction_level, cascade: true}), false));
                                    }
                                }
                            }
                        }
                    }
                    BreakpointOn::PointOfInterest(point) => {
                        let mut found = false;
                        for binary in debugger.symbols.iter() {
                            let symbols = match &binary.symbols {
                                Ok(s) if binary.is_mapped => s,
                                _ => continue,
                            };
                            if let Some(static_addrs) = symbols.points_of_interest.get(point) {
                                for &static_addr in static_addrs {
                                    if let Some(line) = symbols.find_line(static_addr) {
                                        let file = &symbols.files[line.file_idx().unwrap()];
                                        state.should_scroll_source = Some((Some(SourceScrollTarget {path: file.path.to_owned(), version: file.version.clone(), line: line.line(), cascade: true}), false));
                                        found = true;
                                        break;
                                    }
                                }
                                if found {
                                    break;
                                }
                            }
                        }
                    }
                    BreakpointOn::InitialExec | BreakpointOn::Data(_) => (),
                }
            }
        }
    }
}

#[derive(Default)]
struct HelpDialog {
    tabs_state: TabsState,
    contents: Option<HelpDialogContents>,
    scroll: Vec<isize>, // parallel to contents.tabs
}
impl HelpDialog {
    fn drop_caches(&mut self) {
        self.contents = None;
    }

    fn build(&mut self, state: &mut UIState, ui: &mut UI) {
        if self.contents.is_none() {
            self.contents = Some(get_help_dialog_contents(&state.key_hints, ui));
        }
        let contents = self.contents.as_ref().unwrap();
        self.scroll.resize(contents.tabs.len(), 0);

        ui.cur_mut().set_vstack();
        let tabs_widget = ui.add(widget!().fixed_height(2));
        let main_widget = ui.add(widget!().height(AutoSize::Remainder(1.0)));
        ui.layout_children(Axis::Y);
        with_parent!(ui, tabs_widget, {
            let mut tabs = Tabs::new(mem::take(&mut self.tabs_state), ui);
            for &(title, _) in &contents.tabs {
                tabs.add(Tab {short_title: title.to_string(), ..Default::default()}, ui);
            }
            (self.tabs_state, _) = tabs.finish(ui);
        });

        let tab_idx = self.tabs_state.selected;
        let lines = ui.text.import_lines(&contents.text, contents.tabs[tab_idx].1.clone());

        let viewport;
        with_parent!(ui, main_widget, {
            ui.cur_mut().set_hstack();
            viewport = ui.add(widget!().width(AutoSize::Remainder(1.0)));
            let scroll_bar = ui.add(widget!().fixed_width(1));
            ui.layout_children(Axis::X);
            let content_widget = ui.add(widget!().parent(viewport).fixed_y(0).height(AutoSize::Text).flags(WidgetFlags::LINE_WRAP).text_lines(lines));

            with_parent!(ui, viewport, {
                ui.focus();
                cursorless_scrolling_navigation(&mut self.scroll[tab_idx], /*scroll_to*/ None, main_widget, scroll_bar, ui);
            });
        });

        with_parent!(ui, main_widget, {ui.multifocus();});
        with_parent!(ui, tabs_widget, {ui.multifocus();});
    }
}
