use crate::{*, terminal::*, common_ui::*, error::*, debugger::LineBreakpoint};
use std::{collections::{HashMap, hash_map::Entry}, path::PathBuf, fmt, fmt::Write as fmtWrite, path::Path, mem, env};

pub struct Settings {
    pub tab_width: usize,
    // TODO: Make these two special breakpoints (visible/editable in breakpoints window) instead of settings.
    pub stop_on_initial_exec: bool,
    pub stop_on_main: bool,
    pub fps: f64,
    pub max_threads: usize,
    // We currently use one timer for a few periodic tasks:
    //  * refreshing resource stats (cpu and memory usage) for each thread and total,
    //  * saving state to file (watches, breakpoints, etc) if changed (state is also saved on clean exit, but not on panic or crash),
    //  * rendering progress bar movement, // TODO: use animation system instead (after implementing animation system)
    //  * rotating profiling time series buckets.
    pub periodic_timer_ns: usize,
    pub mouse_mode: MouseMode,
    pub exception_aware_steps: bool,
    // If false, expect the debug info to contain full accurate mapping program_counter -> source_line.
    // If true, expect the mapping to be reliable only for the main/entry ("statement") instruction of each line+column, while
    // other instructions potentially have garbage line number info (often line number 0).
    // The `true` mode is more likely to understep or stop on an instruction with garbage line info (like line 0 or wrong file)
    // if the program wasn't built with sufficiently high debug info level.
    // The `false` mode is more likely to overstep.
    pub steps_stop_only_on_statements: bool,

    pub session_name: SessionName,
    
    pub debuginfod_urls: Vec<String>,
    pub debuginfod_cache_path: Option<PathBuf>,

    pub code_dirs: Vec<PathBuf>,
    pub supplementary_binary_paths: Vec<String>,

    pub stdin_file: Option<String>,
    pub stdout_file: Option<String>,
    pub stderr_file: Option<String>,

    pub disable_aslr: bool,

    pub fixed_fps: bool, // render `fps` times per second even if nothing changes
    pub trace_logging: bool, // verbose logging, e.g. log every signal passed-through to the process

    pub breakpoints: Vec<LineBreakpoint>,
}
impl Default for Settings {
    fn default() -> Self { Settings {
        tab_width: 2,
        stop_on_initial_exec: false,
        stop_on_main: false,
        fps: 144.0,
        max_threads: 128,
        periodic_timer_ns: 250_000_000,
        mouse_mode: MouseMode::Full,
        code_dirs: Vec::new(),
        supplementary_binary_paths: Vec::new(),
        exception_aware_steps: true,
        steps_stop_only_on_statements: true,

        session_name: SessionName::Auto,
        
        debuginfod_urls: Vec::new(), // populated by get_debuginfod_urls() later
        debuginfod_cache_path: None,

        stdin_file: None,
        stdout_file: None,
        stderr_file: None,

        disable_aslr: true,

        fixed_fps: false,
        trace_logging: false,

        breakpoints: Vec::new(),
    } }
}

// Which directory under ~/.nnd/ to use for things like log, redirected stdout and stderr, saved state, etc.
pub enum SessionName {
    // Pick the smallest available name "0", "1", ...
    Auto,
    // Pick a directory like "temp-0" and clear it at the start.
    Temp,
    // Do not create or touch any files. Log, stdout, etc all go to /dev/null. On crash, you get no stack trace.
    None,
    // Use the given name. If we fail to use it, refuse to start (in other modes we fall back to /dev/null).
    Name(String),
}
impl SessionName {
    pub fn is_temp(&self) -> bool { match self {Self::Temp => true, _ => false} }
    pub fn is_none(&self) -> bool { match self {Self::None => true, _ => false} }
    pub fn is_name(&self) -> bool { match self {Self::Name(_) => true, _ => false} }
}

pub fn get_debuginfod_urls(default: bool) -> Vec<String> {
    if default {
        // This is a "federated" server that queries ~10 other servers (debuginfod.ubuntu.com, debuginfod.fedoraproject.org, etc), see https://sourceware.org/elfutils/Debuginfod.html
        return vec!["https://debuginfod.elfutils.org/".to_string()];
    }
    match env::var("DEBUGINFOD_URLS") {
        Ok(v) => v.split_ascii_whitespace().map(|s| s.to_string()).collect(),
        Err(_) => Vec::new(),
    }
}

pub struct Palette {
    pub default: Style,
    pub default_dim: Style,
    pub error: Style,
    pub warning: Style,

    pub running: Style,
    pub suspended: Style,
    pub function_name: Style,
    pub filename: Style,
    pub line_number: Style,
    pub column_number: Style,
    pub type_name: Style,
    pub field_name: Style,
    pub keyword: Style,
    pub hotkey: StyleAdjustment,

    pub state_running: Style,
    pub state_suspended: Style,
    pub state_other: Style,

    pub hint_global: Style,
    pub hint_state_dependent: Style,
    pub hint_window_dependent: Style,

    // How to highlight things like selected table row or selected code line.
    pub selected: StyleAdjustment,
    // How to highlight clickable widgets on mouse hover.
    pub hovered: StyleAdjustment,
    // Line with instruction pointer in code or disassembly window.
    pub ip_line: StyleAdjustment,
    // How to draw widgets with REDRAW_IF_VISIBLE flag, as a sort of loading indicator. It should be visible very rarely and only for one frame.
    pub placeholder_fill: Option<(char, Style)>,
    // What to prepend/append when text is truncated on the left/right. E.g. '…'.
    pub truncation_indicator: (/*left*/ String, /*right*/ String, Style),
    // What to show at left and right ends of something horizontally scrollable. E.g.: '<', '>'
    pub hscroll_indicator: (/*left*/ String, /*right*/ String, Style),
    pub line_wrap_indicator: (/*start_of_line*/ String, /*end_of_line*/ String, Style),

    pub table_header: Style,
    pub striped_table: StyleAdjustment,

    pub tab_selected: Style,
    pub tab_ephemeral: (String, Style),
    pub tab_deselected: Style,
    pub tab_separator: (String, Style),

    // fg - left side, bg - right side.
    pub progress_bar: Style,

    pub scroll_bar_background: Style,
    pub scroll_bar_slider: Style,

    pub tooltip: StyleAdjustment,
    pub dialog: StyleAdjustment,

    pub text_input: Style,
    pub text_input_selected: Style,

    pub tree_indent: (String, Style),
    pub tree_indent_selected: (String, Style),
    pub tree_indent_limit_reached: (String, Style),

    pub window_border: Style,
    pub window_border_active: Style,
    pub window_title_active: Style,
    pub window_title_selected: Style,
    pub window_title_deselected: Style,
    pub window_title_separator: (String, Style),

    pub value: Style,
    pub value_misc: Style,
    pub value_dubious: StyleAdjustment,

    pub code_statement: Style,
    pub code_inlined_site: Style,
    pub code_instruction_pointer_column: StyleAdjustment,
    pub search_result: StyleAdjustment,
    pub instruction_pointer: Style,
    pub additional_instruction_pointer: Style,
    pub breakpoint: Style,
    pub secondary_breakpoint: Style,
    pub code_line_number: Style,
    pub url: Style,
    pub disas_default: Style,
    pub disas_keyword: Style,
    pub disas_mnemonic: Style,
    pub disas_register: Style,
    pub disas_number: Style,
    pub disas_function: Style,
    pub disas_jump_arrow: Style,
    pub disas_relative_address: Style,
    pub disas_filename: Style,
    pub disas_address_statement: Style,
    pub disas_address_not_statement: Style,

    pub thread_breakpoint_hit: StyleAdjustment,
    pub thread_crash: StyleAdjustment,
    pub breakpoint_error: StyleAdjustment,
}
impl Default for Palette {
    fn default() -> Self {
        let black = Color(0, 0, 0);
        let white = Color(0xff, 0xff, 0xff);
        let red = Color(255, 50, 50);
        let green = Color(0, 0xaa, 0);
        let blue = Color(0x63, 0x84, 0xff);
        let yellow = Color(0xaa, 0x55, 0);
        let cyan = Color(0, 0xaa, 0xaa);
        let magenta = Color(0xaa, 0, 0xaa);
        let dark_gray = Color(0x55, 0x55, 0x55);
        let light_green = Color(0x55, 0xff, 0x55);
        let light_blue = Color(0x55, 0x55, 0xff);

        Self {
            default: Style {fg: white, ..D!()},
            default_dim: Style {fg: white.darker(), ..D!()},
            error: Style {fg: red, ..D!()},
            warning: Style {fg: yellow, ..D!()},

            running: Style {fg: blue, ..D!()},
            suspended: Style {fg: light_green, ..D!()},

            function_name: Style {fg: white, ..D!()},
            filename: Style {fg: cyan, ..D!()},
            line_number: Style {fg: green, ..D!()},
            column_number: Style {fg: green.darker(), ..D!()},
            type_name: Style {fg: white, ..D!()},
            field_name: Style {fg: green, ..D!()},
            keyword: Style {fg: white, ..D!()},
            hotkey: StyleAdjustment {add_modifier: Modifier::UNDERLINED, ..D!()},

            state_running: Style {bg: blue, fg: black, ..D!()},
            state_suspended: Style {bg: light_green, fg: black, ..D!()},
            state_other: Style {bg: yellow, fg: black, ..D!()},

            hint_global: Style {fg: white.darker(), ..D!()},
            hint_state_dependent: Style {fg: Color(120, 80, 120), ..D!()},
            hint_window_dependent: Style {fg: Color(80, 120, 80), ..D!()},

            selected: StyleAdjustment {add_fg: (50, 50, 50), add_bg: (50, 50, 50), ..D!()},
            hovered: StyleAdjustment {add_fg: (20, 20, 20), add_bg: (25, 25, 25), ..D!()},
            ip_line: StyleAdjustment {add_fg: (5, 50, 5), add_bg: (5, 50, 5), ..D!()},

            table_header: Style {fg: white.darker(), ..D!()},
            //striped_table: StyleAdjustment {add_fg: (0, 0, 0), add_bg: (20, 20, 20), ..D!()},
            striped_table: StyleAdjustment::default(),

            tab_selected: Style {fg: white, bg: Color(40, 40, 40), modifier: Modifier::BOLD, ..D!()},
            tab_ephemeral: ("∗".to_string(), Style {fg: white, ..D!()}),
            tab_deselected: Style {fg: white.darker(), ..D!()},
            tab_separator: (" | ".to_string(), Style {fg: white.darker(), ..D!()}),

            placeholder_fill: Some(('.', Style {fg: white.darker(), bg: black, ..D!()})),
            truncation_indicator: (("…".to_string(), "…".to_string(), Style {fg: white.darker(), ..D!()})),
            hscroll_indicator: (("❮".to_string(), "❯".to_string(), Style {fg: white.darker(), ..D!()})),
            line_wrap_indicator: ("↳".to_string(), "↵".to_string(), Style {fg: white.darker(), ..D!()}),

            progress_bar: Style {fg: blue, bg: Color(30, 30, 30), ..D!()},
            scroll_bar_background: Style {fg: white.darker(), ..D!()},
            scroll_bar_slider: Style {fg: white.darker(), ..D!()},

            tooltip: StyleAdjustment {add_bg: (30, 40, 50), ..D!()},
            dialog: StyleAdjustment {add_fg: (10, 10, 10), add_bg: (20, 20, 20), ..D!()},

            text_input: Style {fg: white, ..D!()},
            text_input_selected: Style {fg: white, bg: blue, ..D!()},

            tree_indent: ("┆".to_string(), Style {fg: white.darker(), ..D!()}),
            tree_indent_selected: ("┇".to_string(), Style {fg: white, ..D!()}),
            tree_indent_limit_reached: ("┼".to_string(), Style {fg: white, ..D!()}),

            window_border: Style {fg: white.darker(), ..D!()},
            window_border_active: Style {fg: white, modifier: Modifier::BOLD, ..D!()},
            window_title_active: Style {fg: white, bg: Color(30, 30, 30), modifier: Modifier::BOLD, ..D!()},
            window_title_selected: Style {fg: white, bg: Color(30, 30, 30), ..D!()},
            window_title_deselected: Style {fg: white.darker(), ..D!()},
            window_title_separator: (" | ".to_string(), Style {fg: white.darker(), ..D!()}),

            value: Style {fg: white, ..D!()},
            value_misc: Style {fg: white.darker(), ..D!()},
            value_dubious: StyleAdjustment {add_fg: (-60, -60, -60), ..D!()},

            code_statement: Style {fg: white, bg: dark_gray, ..D!()},
            code_inlined_site: Style {fg: white, bg: light_blue, ..D!()},
            code_instruction_pointer_column: StyleAdjustment {add_bg: (0, 100, 0), add_fg: (-600, -600, -600), add_modifier: Modifier::UNDERLINED, ..D!()},
            search_result: StyleAdjustment {add_bg: (100, 100, 0), add_fg: (100, 100, 100), ..D!()},
            instruction_pointer: Style {fg: green, modifier: Modifier::BOLD, ..D!()},
            additional_instruction_pointer: Style {fg: blue, ..D!()},
            breakpoint: Style {fg: red, ..D!()},
            secondary_breakpoint: Style {fg: blue, ..D!()},
            code_line_number: Style {fg: white, ..D!()},
            url: Style {fg: blue, ..D!()},
            disas_default: Style {fg: white, ..D!()},
            disas_keyword: Style {fg: white.darker(), ..D!()},
            disas_mnemonic: Style {fg: green, modifier: Modifier::BOLD, ..D!()},
            disas_register: Style {fg: blue, ..D!()},
            disas_number: Style {fg: cyan, ..D!()},
            disas_function: Style {fg: magenta, ..D!()},
            disas_jump_arrow: Style {fg: white, ..D!()},
            disas_relative_address: Style {fg: cyan.darker(), ..D!()}, 
            disas_filename: Style {fg: cyan.darker(), ..D!()},
            disas_address_statement: Style {fg: white.darker(), ..D!()},
            disas_address_not_statement: Style {fg: white.darker().darker(), ..D!()},

            thread_breakpoint_hit: StyleAdjustment {add_fg: (100, 100, 100), add_bg: (10, 100, 10), ..D!()},
            thread_crash: StyleAdjustment {add_fg: (100, 100, 100), add_bg: (150, 50, 50), ..D!()},
            breakpoint_error: StyleAdjustment {add_fg: (100, 100, 100), add_bg: (150, 50, 50), ..D!()},
       }
    }
}

#[allow(non_camel_case_types)]
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone, Copy)]
#[repr(usize)]
pub enum KeyAction {
    Quit,

    Run,
    Continue,
    Suspend,
    Kill,
    SendSigint,

    StepIntoLine,
    StepIntoInstruction,
    StepOverLine,
    StepOverColumn,
    StepOverInstruction,
    StepOut,
    StepOutNoInline,
    StepToCursor,

    WindowUp,
    WindowDown,
    WindowLeft,
    WindowRight,
    Window0,
    Window1,
    Window2,
    Window3,
    Window4,
    Window5,
    Window6,
    Window7,
    Window8,
    Window9,

    // Arrow keys.
    CursorUp,
    CursorDown,
    CursorLeft,
    CursorRight,
    Enter, // return
    DeleteRow, // del
    Cancel, // escape
    PageUp,
    PageDown,
    Home,
    End,
    Tooltip,

    NextTab,
    PreviousTab,
    CloseTab,
    NextStackFrame,
    PreviousStackFrame,
    NextThread,
    PreviousThread,
    NextLocation,
    PreviousLocation,
    NextMatch,
    PreviousMatch,
    ToggleSort,

    Open,
    FindType,
    EditCondition,
    Find,
    GoToLine,

    DuplicateRow,

    DropCaches,
    ToggleProfiler,

    // Text input.
    Undo,
    Redo,
    Copy,
    Paste,
    Cut,
    NewLine,

    END_OF_ENUM,
}

#[derive(Eq, PartialEq, Copy, Clone)]
enum KeysConfigSection {
    Keys,
    Text,
    Settings,
}

#[derive(Eq, PartialEq, Debug)]
pub struct KeyMap {
    pub key_to_action: HashMap<KeyEx, KeyAction>,
    pub action_to_keys: HashMap<KeyAction, Vec<KeyEx>>,
}
impl KeyMap {
    pub fn actions_to_keys(&self, actions: &[KeyAction]) -> Vec<KeyEx> {
        let mut r: Vec<KeyEx> = Vec::new();
        for action in actions {
            if let Some(keys) = self.action_to_keys.get(action) {
                r.extend_from_slice(keys);
            }
        }
        r
    }

    pub fn action_to_key_name(&self, action: KeyAction) -> String {
        match self.action_to_keys.get(&action) {
            None => "<unbound>".to_string(),
            Some(v) if v.is_empty() => "<unbound>".to_string(),
            Some(v) => format!("{}", v[0]),
        }
    }

    fn new(key_to_action: &[(KeyEx, KeyAction)]) ->  Self {
        let mut r = KeyMap {key_to_action: key_to_action.iter().cloned().collect(), action_to_keys: HashMap::new()};
        // Order somewhat matters here: if there are multiple keys for the same action, we show only the first one in the hints window.
        // So here we add keys in the same order in which the keys were specified in the input, not in HashMap iteration order.
        for (key, action) in key_to_action {
            r.action_to_keys.entry(*action).or_default().push(*key);
        }
        r
    }
}

#[derive(Eq, PartialEq, Debug)]
pub struct KeyBinds {
    pub normal: KeyMap,
    pub text_input: KeyMap,
    pub vscroll_sensitivity: isize,
    pub hscroll_sensitivity: isize,
}
impl KeyBinds {
    pub fn write_config_example(out: &mut String, real_config_path: &Path, example_path: &Path, error_file_path: &Path, comment_out: bool) -> std::result::Result<(), fmt::Error> {
        write!(out, r###"# Example key bindings configuration.

# This file is autogenerated and overwritten on debugger startup. Don't edit it.
# The real config file should be placed at: {0}
# You may `cp {1} {0}` and edit {0}
#
# If the debugger fails to parse the config file, a file with error message will be created at: {2}
# The config is reloaded on the fly, no restart needed, just save the file.
#
# The basic syntax is: "action: key", e.g. "Find: C-f"
# All action names can be found in this config.
#
# Key names can be discovered using `nnd --echo-input`. It's highly recommended to use it to check every key combination beforehand; if you use incorrect name, it may silently fail to work.
# Many key combinations are unavailable or indistinguishable in terminal (e.g. tab, ctrl+tab, and ctrl+i all send the same control sequence).
# Prefixes: C- - ctrl, M- - alt.
# For shift+key combination, use capital letter, e.g. "X" for shift+x. Prefix S- can be used for some keys that don't have capital-letter versions, e.g. "S-F3" is shift+F3.
#
# To have multiple keys for the same action, use multiple lines with the same "action: " part.
# If an action is not listed, default key(s) for it are used. Assigning key(s) to an action overrides all default keys for that action.
# To remove default keys for an action without assigning a new key, use "unbind" as the key, e.g. "Find: unbind".
# Assigning the same key to multiple actions within the same section ([keys] or [text]) is not allowed.
#
# All lines here are commented out ('#') (except section names). Uncomment them in the real config to apply.

[keys]
"###,
               real_config_path.display(), example_path.display(), error_file_path.display())?;
        let prefix = if comment_out {"# "} else {""};
        let binds = KeyBinds::default();
        for action_idx in 0..(KeyAction::END_OF_ENUM as usize) {
            let action: KeyAction = unsafe {mem::transmute(action_idx)};
            if binds.text_input.action_to_keys.get(&action).is_some() {
                continue;
            }
            match binds.normal.action_to_keys.get(&action) {
                None => writeln!(out, "{}{:?}: unbind", prefix, action)?,
                Some(keys) => for key in keys {
                    writeln!(out, "{}{:?}: {}", prefix, action, key)?;
                }
            }
        }

        write!(out, r###"

# These keys apply during text editing.
[text]
"###)?;
        let mut text_input_actions: Vec<KeyAction> = binds.text_input.action_to_keys.keys().copied().collect();
        text_input_actions.sort_unstable();
        text_input_actions.dedup();
        for action in text_input_actions {
            let keys = binds.text_input.action_to_keys.get(&action).unwrap();
            for key in keys {
                writeln!(out, "{}{:?}: {}", prefix, action, key)?;
            }
        }

        write!(out, r###"

# Some settings that are not actually key binds.
[settings]
{0}vertical_scroll_sensitivity: {1}
{0}horizontal_scroll_sensitivity: {2}
"###,
               prefix,
               binds.vscroll_sensitivity,
               binds.hscroll_sensitivity)?;

        Ok(())
    }

    pub fn parse_config(text: &str, error_line_number: &mut usize) -> Result<Self> {
        let name_to_action: HashMap<String, KeyAction> = (0..KeyAction::END_OF_ENUM as usize).map(|i| {
            let action: KeyAction = unsafe {mem::transmute(i)};
            (format!("{:?}", action), action)
        }).collect();

        let mut section = KeysConfigSection::Keys;
        let mut res = KeyBinds::default();
        let mut parsed_keys: [Vec<(Option<KeyEx>, KeyAction)>; 2] = [Vec::new(), Vec::new()];
        for (line_idx, line) in text.lines().enumerate() {
            *error_line_number = line_idx + 1;
            let mut slice = line.trim_start();
            if slice.is_empty() || slice.starts_with('#') {
                continue;
            }

            // Section header.
            if slice.starts_with('[') {
                let n = match slice.find(']') {
                    None => return err!(Syntax, "unclosed '['"),
                    Some(x) => x };
                let name = slice[1..n].trim();
                section = match name {
                    "keys" => KeysConfigSection::Keys,
                    "text" => KeysConfigSection::Text,
                    "settings" => KeysConfigSection::Settings,
                    s => return err!(Syntax, "unknown section name: {}", name),
                };
                slice = slice[n+1..].trim_start();
            } else {
                // Action name.
                let n = match slice.find(':') {
                    None => return err!(Syntax, "no ':'"),
                    Some(x) => x };
                let action_name = slice[..n].trim();
                slice = &slice[n+1..].trim_start();

                if section == KeysConfigSection::Settings {
                    let n = slice.find(|c: char| !c.is_ascii_digit()).unwrap_or(slice.len());
                    let val = match slice[..n].parse::<isize>() {
                        Err(e) => return err!(Syntax, "bad number: {}", e),
                        Ok(x) => x };
                    slice = slice[n..].trim_start();
                    match action_name {
                        "vertical_scroll_sensitivity" => res.vscroll_sensitivity = val,
                        "horizontal_scroll_sensitivity" => res.hscroll_sensitivity = val,
                        s => return err!(Syntax, "unknown setting: '{}'", action_name),
                    }
                } else {
                    let action = match name_to_action.get(action_name) {
                        None => return err!(Syntax, "unknown action: '{}'", action_name),
                        Some(&x) => x };

                    // Key.
                    let n = slice.find(' ').unwrap_or(slice.len()); // if there's a comment after the key, it'll have to be separated by at least one space
                    let key_name = &slice[..n];
                    let key = if key_name == "unbind" {
                        None
                    } else {
                        match key_name.parse::<KeyEx>() {
                            Err(()) => return err!(Syntax, "bad key name: '{}' (use nnd --echo-input to find the exact key name to use)", key_name),
                            Ok(k) => Some(k),
                        }
                    };
                    slice = slice[n..].trim_start();

                    let idx = if section == KeysConfigSection::Keys {0} else {1};
                    parsed_keys[idx].push((key, action));
                }
            }

            if !slice.is_empty() && !slice.starts_with('#') {
                return err!(Syntax, "unexpected extra tokens starting at column {}", line.len() - slice.len() + 1);
            }
        }

        for is_text_input in 0..2 {
            let mut key_to_action: HashMap<KeyEx, KeyAction> = HashMap::new();
            let mut action_to_keys: HashMap<KeyAction, Vec<KeyEx>> = HashMap::new();
            for &(ref key, action) in &parsed_keys[is_text_input] {
                if let &Some(k) = key {
                    match key_to_action.entry(k) {
                        Entry::Occupied(o) => return err!(Syntax, "key {} is assigned to multiple actions: {:?} and {:?}", k, o.get(), action),
                        Entry::Vacant(v) => {v.insert(action);}
                    }
                    action_to_keys.entry(action).or_default().push(k);
                }
            }
            let map = if is_text_input == 0 {&mut res.normal} else {&mut res.text_input};
            for (&action, keys) in &map.action_to_keys {
                if action_to_keys.get(&action).is_none() {
                    for &k in keys {
                        match key_to_action.entry(k) {
                            Entry::Occupied(o) => return err!(Syntax, "key {} assigned to action {:?} conflicts with default key binding for {:?}", k, o.get(), action),
                            Entry::Vacant(v) => {v.insert(action);}
                        }
                        action_to_keys.entry(action).or_default().push(k);
                    }
                }
            }
            *map = KeyMap {key_to_action, action_to_keys};
        }

        Ok(res)
    }
}
impl Default for KeyBinds {
    fn default() -> Self {
        let normal = KeyMap::new(&[
            (Key::Char('q').ctrl(), KeyAction::Quit),
            (Key::Char('r').plain(), KeyAction::Run),
            (Key::Char('c').plain(), KeyAction::Continue),
            (Key::Char('p').plain(), KeyAction::Suspend),
            (Key::Char('c').ctrl(), KeyAction::Suspend),
            (Key::Char('k').ctrl(), KeyAction::Kill),
            (Key::Char('k').alt(), KeyAction::SendSigint),
            (Key::Up.alt(), KeyAction::WindowUp),
            (Key::Down.alt(), KeyAction::WindowDown),
            (Key::Left.alt(), KeyAction::WindowLeft),
            (Key::Right.alt(), KeyAction::WindowRight),
            (Key::Char('0').plain(), KeyAction::Window0),
            (Key::Char('1').plain(), KeyAction::Window1),
            (Key::Char('2').plain(), KeyAction::Window2),
            (Key::Char('3').plain(), KeyAction::Window3),
            (Key::Char('4').plain(), KeyAction::Window4),
            (Key::Char('5').plain(), KeyAction::Window5),
            (Key::Char('6').plain(), KeyAction::Window6),
            (Key::Char('7').plain(), KeyAction::Window7),
            (Key::Char('8').plain(), KeyAction::Window8),
            (Key::Char('9').plain(), KeyAction::Window9),
            (Key::Up.plain(), KeyAction::CursorUp),
            (Key::Down.plain(), KeyAction::CursorDown),
            (Key::Left.plain(), KeyAction::CursorLeft),
            (Key::Right.plain(), KeyAction::CursorRight),
            (Key::Char('\n').plain(), KeyAction::Enter),
            (Key::Delete.plain(), KeyAction::DeleteRow),
            (Key::Backspace.plain(), KeyAction::DeleteRow),
            (Key::Escape.plain(), KeyAction::Cancel),
            (Key::Char('g').ctrl(), KeyAction::Cancel),
            (Key::PageUp.plain(), KeyAction::PageUp),
            (Key::Char('v').alt(), KeyAction::PageUp),
            (Key::PageDown.plain(), KeyAction::PageDown),
            (Key::Char('v').ctrl(), KeyAction::PageDown),
            (Key::Home.plain(), KeyAction::Home),
            (Key::End.plain(), KeyAction::End),
            (Key::Char('i').ctrl(), KeyAction::Tooltip),
            (Key::Char('s').plain(), KeyAction::StepIntoLine),
            (Key::Char('S').plain(), KeyAction::StepIntoInstruction),
            (Key::Char('n').plain(), KeyAction::StepOverLine),
            (Key::Char('m').plain(), KeyAction::StepOverColumn),
            (Key::Char('N').plain(), KeyAction::StepOverInstruction),
            (Key::Char('f').plain(), KeyAction::StepOut),
            (Key::Char('F').plain(), KeyAction::StepOutNoInline),
            (Key::Char('C').plain(), KeyAction::StepToCursor),
            // (Ctrl+tab and ctrl+shift+tab are unrepresentable in ansi escape codes.)
            (Key::Char('t').ctrl(), KeyAction::NextTab),
            (Key::Char('b').ctrl(), KeyAction::PreviousTab),
            (Key::Char('w').ctrl(), KeyAction::CloseTab),
            (Key::Char(']').plain(), KeyAction::NextStackFrame),
            (Key::Char('[').plain(), KeyAction::PreviousStackFrame),
            (Key::Char('}').plain(), KeyAction::NextThread),
            (Key::Char('{').plain(), KeyAction::PreviousThread),
            (Key::Char('.').plain(), KeyAction::NextLocation),
            (Key::Char(',').plain(), KeyAction::PreviousLocation),
            (Key::Char('g').alt(), KeyAction::NextMatch),
            (Key::Char('G').alt(), KeyAction::PreviousMatch),
            (Key::F(3).plain(), KeyAction::NextMatch),
            (Key::F(3).shift(), KeyAction::PreviousMatch),
            (Key::Char('+').plain(), KeyAction::ToggleSort),
            (Key::Char('o').plain(), KeyAction::Open),
            (Key::Char('t').plain(), KeyAction::FindType),
            (Key::Char('\n').alt(), KeyAction::EditCondition),
            (Key::Char('/').plain(), KeyAction::Find),
            (Key::Char('g').plain(), KeyAction::GoToLine),
            (Key::Char('d').plain(), KeyAction::DuplicateRow),
            (Key::Char('l').ctrl(), KeyAction::DropCaches),
            (Key::Char('p').ctrl(), KeyAction::ToggleProfiler),
        ]);
        let text_input = KeyMap::new(&[
            (Key::Char('7').ctrl(), KeyAction::Undo), // ctrl+/ is indistinguishable from ctrl+7
            (Key::Char('_').alt(), KeyAction::Redo),
            (Key::Char('y').ctrl(), KeyAction::Paste),
            (Key::Char('c').ctrl(), KeyAction::Copy),
            (Key::Char('x').ctrl(), KeyAction::Cut),
            (Key::Char('v').ctrl(), KeyAction::Paste),
            (Key::Char('\n').alt(), KeyAction::NewLine),
        ]);
        KeyBinds {normal, text_input, vscroll_sensitivity: 4, hscroll_sensitivity: 20}
    }
}
