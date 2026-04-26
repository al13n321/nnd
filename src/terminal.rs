use crate::{*, common_ui::*, error::*, log::*, util::*, os::*};
use std::{result, io, mem, sync::atomic::{AtomicBool, Ordering}, cell::UnsafeCell, io::Write, str, str::FromStr, fmt, fmt::{Display, Formatter}};
use bitflags::*;
use unicode_segmentation::UnicodeSegmentation;
use unicode_width::UnicodeWidthStr;

#[derive(Clone, Copy)]
pub struct ScreenCell {
    pub style: Style,

    // Encodes a string containing the "extended grapheme cluster" for this cell, and its width. Stored inline if short, in long_graphemes if long.
    // If the symbol is wider than one cell (e.g. some icons), it lives in the leftmost of the cells, and the other cells contain ' '.
    // The high 2 bits of len_and_width are width-1 of the symbol.
    // If a wide symbol is partially clipped or covered (e.g. partially overwritten in ScreenBuffer's array), it's impossible to render correctly,
    // and we don't do any special handling for this case - the symbol just lives in the first cell, and the subsequent cells are spaces.
    len_and_width: u8,
    data: [u8; 4],
}
impl Default for ScreenCell { fn default() -> Self { Self {style: Style::default(), len_and_width: 1, data: [b' ', 0, 0, 0]} } }

#[derive(Default, Clone)]
pub struct ScreenBuffer {
    pub width: usize,
    pub height: usize,
    pub cells: Vec<ScreenCell>, // width * height
    pub long_graphemes: Vec<u8>,
}
impl ScreenBuffer {
    pub fn resize_and_clear(&mut self, width: usize, height: usize, style: Style) {
        (self.width, self.height) = (width, height);
        self.long_graphemes.clear();
        let cell = ScreenCell {style, ..Default::default()};
        // Clear cells to make sure no dangling references into long_graphemes exist.
        self.cells.clear();
        self.cells.resize(width*height, cell);
    }

    pub fn rect(&self) -> Rect { Rect {pos: [0, 0], size: [self.width, self.height]} }

    fn pack_grapheme(&mut self, mut s: &str, wid: usize, style: Style) -> ScreenCell {
        if s.len() > 63 {
            let mut i = 63;
            while !s.is_char_boundary(i) {
                i -= 1;
            }
            s = &s[..i];
        }
        let len_and_width = if wid <= 1 {
            s.len() as u8
        } else {
            s.len() as u8 | ((wid.min(4).max(1) as u8 - 1) << 6)
        };

        let mut data = [0u8; 4];
        if s.len() <= 4 {
            //data[..s.len()].copy_from_slice(s.as_bytes());
            small_memcpy(s.as_bytes(), &mut data);
        } else {
            assert!(self.long_graphemes.len() + s.len() < u32::MAX as usize);
            data = (self.long_graphemes.len() as u32).to_le_bytes();
            self.long_graphemes.extend_from_slice(s.as_bytes());
        }

        ScreenCell {style, len_and_width, data}
    }

    fn unpack_grapheme<'a>(&'a self, cell: &'a ScreenCell) -> (&'a str, /*extra_width*/ u8) {
        let len = cell.len_and_width & 63;
        let slice = if len <= 4 {
            &cell.data
        } else {
            &self.long_graphemes[u32::from_le_bytes(cell.data.clone()) as usize..]
        };
        (unsafe {str::from_utf8_unchecked(&slice[..len as usize])}, cell.len_and_width >> 6)
    }

    fn cell_equals(&self, cell: &ScreenCell, other: &Self, cell2: &ScreenCell) -> bool {
        if (cell.style, cell.len_and_width) != (cell2.style, cell2.len_and_width) {
            return false;
        }
        if cell.len_and_width & 64 <= 4 {
            return cell.data == cell2.data;
        }
        return self.unpack_grapheme(cell).0 == other.unpack_grapheme(cell2).0;
    }

    pub fn fill(&mut self, rect: Rect, grapheme: &str, style: Style) {
        assert!(str_width(grapheme) == 1);
        let cell = self.pack_grapheme(grapheme, 1, style);
        let rect = rect.intersection(self.rect());
        for y in rect.y() as usize..rect.bottom() as usize {
            self.cells[(y*self.width + rect.x() as usize)..(y*self.width + rect.right() as usize)].fill(cell);
        }
    }

    // Returns new x, possibly cut short by the clipping rectangle.
    pub fn put_text(&mut self, text: &str, style: Style, mut x: isize, y: isize, clip: Rect) -> isize {
        let clip = clip.intersection(self.rect());
        if y >= clip.bottom() || y < clip.y() {
            return x;
        }
        let row_start = y as usize * self.width;
        for s in text.graphemes(true) {
            if x >= clip.right() {
                break;
            }

            let w = s.width();
            let start = x;
            x += w as isize;

            if x <= clip.x() {
                continue;
            }

            if start >= clip.x() {
                let cell = self.pack_grapheme(s, w, style);
                self.cells[row_start + start as usize] = cell;
            }
            if w > 1 {
                let cell = self.pack_grapheme(" ", 1, style);
                self.cells[row_start + (start+1).max(clip.x()) as usize .. row_start + x.min(clip.right()) as usize].fill(cell);
            }
        }
        x
    }

    pub fn put_cell(&mut self, s: &str, wid: usize, style: Style, x: isize, y: isize) {
        self.cells[y as usize * self.width + x as usize] = self.pack_grapheme(s, wid, style);
    }

    pub fn get_cell(&self, x: usize, y: usize) -> (&str, /*extra_width*/ u8, Style) {
        let cell = &self.cells[y*self.width + x];
        let (s, extra_width) = self.unpack_grapheme(cell);
        (s, extra_width, cell.style)
    }
}

fn terminal_size(_prof: &mut ProfileBucket) -> Result<(/*rows*/ u16, /*columns*/ u16)> {
    let mut s: libc::winsize = unsafe {mem::zeroed()};
    let r = profile_syscall!(unsafe {libc::ioctl(libc::STDOUT_FILENO, libc::TIOCGWINSZ, &mut s as *mut _)});
    if r != 0 {
        return errno_err!("ioctl(STDOUT, TIOCGWINSZ) failed");
    }
    Ok((s.ws_row, s.ws_col))
}

// Some ANSI escape codes.
pub const CURSOR_HIDE: &'static str = "\x1B[?25l";
const CURSOR_SHOW: &'static str = "\x1B[?25h";
const SCREEN_ALTERNATE: &'static str = "\x1B[?1049h";
const SCREEN_MAIN: &'static str = "\x1B[?1049l";
const CLEAR_SCREEN: &'static str = "\x1B[2J";
const STYLE_RESET: &'static str = "\x1B[m";
const STYLE_RESET_TO_BLACK: &'static str = "\x1B[0;38;2;0;0;0;48;2;0;0;0m";
// Mouse parameters we use:
//  1002 - SET_BTN_EVENT_MOUSE - report mouse button presses/releases and mouse movement when any button is held (only if the cursor moved to a different cell in the terminal). OR ...
//  1003 - SET_ANY_EVENT_MOUSE - report all mouse movement (even if the cursor moved by one pixel, even though pixel coordinates are not reported).
//  1006 - SET_SGR_EXT_MODE_MOUSE - changes mouse events encoding to support coordinates > 223.
//  1004 - SET_FOCUS_EVENT_MOUSE - notify when the terminal loses and gains focus (useful if the user alt-tabs while holding mouse button - we don't get mouse release event in this case, so have to assume mouse release based on focus loss).
const MOUSE_ENABLE_COMMON: &'static str = "\x1b[?1006h\x1b[?1004h";
const MOUSE_BUTTON_EVENT_MODE: &'static str = "\x1b[?1002h";
const MOUSE_ANY_EVENT_MODE: &'static str = "\x1b[?1003h";
const MOUSE_DISABLE: &'static str = "\x1b[?1003l\x1b[?1002l\x1b[?1006l\x1b[?1004l";

static TERMINAL_STATE_TO_RESTORE: SyncUnsafeCell<[u8; mem::size_of::<libc::termios>()]> = SyncUnsafeCell::new([0u8; mem::size_of::<libc::termios>()]);
static TERMINAL_STATE_RESTORED: AtomicBool = AtomicBool::new(true);

// Changes terminal state to raw mode, alternate screen, and bar cursor.
// Called once at program startup. Not thread safe.
pub fn configure_terminal(mouse_mode: MouseMode) -> Result<()> {
    unsafe {
        assert!(TERMINAL_STATE_RESTORED.load(Ordering::SeqCst));
        let mut termios: libc::termios = mem::zeroed();
        let r = libc::tcgetattr(libc::STDOUT_FILENO, &mut termios);

        // (We can't just make TERMINAL_STATE_TO_RESTORE use libc::termios type because we can't initialize it because neither mem::zeroed() nor Default::default() are allowed in const context.
        //  And we can't just initialize it by listing its fields because some of those fields are different between musl and glibc versions of the libc crate.)
        let bytes = TERMINAL_STATE_TO_RESTORE.get();
        ptr::copy_nonoverlapping(&termios as *const libc::termios as *const u8, bytes as *mut [u8; mem::size_of::<libc::termios>()] as *mut u8, mem::size_of::<libc::termios>());

        if r != 0 { return errno_err!("tcgetarrt() failed"); }
        libc::cfmakeraw(&mut termios);
        let r = libc::tcsetattr(libc::STDOUT_FILENO, libc::TCSANOW, &termios);
        if r != 0 { return errno_err!("tcsetattr() failed"); }
        TERMINAL_STATE_RESTORED.store(false, Ordering::SeqCst);

        let (mouse1, mouse2) = match mouse_mode {
            MouseMode::Disabled => ("", ""),
            MouseMode::NoHover => (MOUSE_ENABLE_COMMON, MOUSE_BUTTON_EVENT_MODE),
            MouseMode::Full => (MOUSE_ENABLE_COMMON, MOUSE_ANY_EVENT_MODE),
        };
        write!(io::stdout(), "{}{}{}", SCREEN_ALTERNATE, mouse1, mouse2)?;
        io::stdout().flush()?;
        Ok(())
    }
}

// Undoes the changes made by configure_terminal(), and also unhides cursor (typically we hide it on each frame).
// If called multiple times, only the first call does anything. Can be called in parallel (but only the first call waits for the changes to be made; if there's a parallel call, it'll return immediately, possibly before the terminal was actually restored).
// It's important to try to always call this at least once before the process exits, including on panics.
// Otherwise we'll leave the terminal in a borked state for the user (but it's easy to unbork: `reset`).
// Would be nice to call this on signals too (e.g. SIGSEGV and SIGTERM) (even though it's not signal-safe), but currently we don't, because I couldn't find a way to both have a SIGSEGV handler and propagate the original fault address (si_addr), e.g. if a debugger is attached to this process.
pub fn restore_terminal() {
    unsafe {
        if TERMINAL_STATE_RESTORED.swap(true, Ordering::SeqCst) {
            return;
        }
        // Set the cursor style to blinking block because it's the most common one. Would be better to restore the original style that the cursor had on startup, but there appears to be no way to query or save that style.
        let _ = write!(io::stdout(), "{}{}{}\n", MOUSE_DISABLE, CURSOR_SHOW, SCREEN_MAIN).unwrap_or(());
        let _ = io::stdout().flush().unwrap_or(());

        let bytes = TERMINAL_STATE_TO_RESTORE.get();
        let mut termios: libc::termios = mem::zeroed();
        ptr::copy_nonoverlapping(bytes as *const [u8; mem::size_of::<libc::termios>()] as *const u8, &mut termios as *mut libc::termios as *mut u8, mem::size_of::<libc::termios>());
        let _ = libc::tcsetattr(libc::STDOUT_FILENO, libc::TCSANOW, &termios as *const libc::termios);
    }
}

pub struct TerminalRestorer;
impl Drop for TerminalRestorer { fn drop(&mut self) { restore_terminal(); } }

pub struct Terminal {
    prev_buffer: ScreenBuffer,
    temp_buffer: ScreenBuffer, // reuse buffer across frames
}
impl Terminal {
    pub fn new() -> Self { Self {prev_buffer: ScreenBuffer::default(), temp_buffer: ScreenBuffer::default()} }

    pub fn start_frame(&mut self, style: Style, prof: &mut ProfileBucket) -> Result<ScreenBuffer> {
        let (rows, columns) = terminal_size(prof)?;
        let mut b = mem::take(&mut self.temp_buffer);
        b.resize_and_clear(columns as usize, rows as usize, style);
        Ok(b)
    }

    pub fn clear(&mut self) -> Result<()> {
        self.prev_buffer = ScreenBuffer::default();
        write!(io::stdout(), "{}", CLEAR_SCREEN)?;
        io::stdout().flush()?;
        Ok(())
    }

    pub fn prepare_command_buffer(&self, buffer: &ScreenBuffer, show_cursor: Option<[isize; 2]>, set_os_clipboard: Option<&str>) -> Vec<u8> {
        let mut commands: Vec<u8> = Vec::new();
        let (mut cur_x, mut cur_y, mut cur_style) = (usize::MAX, usize::MAX, Style::default());
        write!(commands, "{}{}", CURSOR_HIDE, STYLE_RESET_TO_BLACK).unwrap();

        let mut write_range = |y: usize, x1: usize, x2: usize, buffer: &ScreenBuffer, commands: &mut Vec<u8>| -> /*x*/ usize {
            if cur_y == y {
                write!(commands, "\x1B[{}G", x1 + 1).unwrap();
            } else {
                write!(commands, "\x1B[{};{}H", y + 1, x1 + 1).unwrap();
            }
            let mut x = x1;
            while x < x2 {
                let (s, extra_width, style) = buffer.get_cell(x, y);

                if style != cur_style {
                    write!(commands, "\x1B[").unwrap();
                    if style.fg != cur_style.fg {
                        style.fg.write_ansi(commands, 0);
                    }
                    if style.bg != cur_style.bg {
                        style.bg.write_ansi(commands, 10);
                    }
                    modifier_diff_write_ansi(cur_style.modifier, style.modifier, commands);

                    cur_style = style;
                    *commands.last_mut().unwrap() = b'm'; // replace trailing ';' with 'm'
                }

                write!(commands, "{}", s).unwrap();
                x += 1 + extra_width as usize;
            }
            (cur_x, cur_y) = (x, y);
            x
        };

        if self.prev_buffer.rect() != buffer.rect() {
            write!(commands, "{}", CLEAR_SCREEN).unwrap();
            for y in 0..buffer.height {
                write_range(y, 0, buffer.width, &buffer, &mut commands);
            }
        } else {
            for y in 0..buffer.height {
                let (mut x1, mut x) = (0, 0);
                let width = buffer.width;
                while x < width {
                    let idx = y*buffer.width + x;
                    if buffer.cell_equals(&buffer.cells[idx], &self.prev_buffer, &self.prev_buffer.cells[idx]) {
                        if x > x1 {
                            let xx = write_range(y, x1, x, &buffer, &mut commands);
                            if xx > x {
                                x = xx;
                                x1 = xx;
                                continue;
                            }
                        }
                        x1 = x + 1;
                    }
                    x += 1;
                }
                if buffer.width > x1 {
                    write_range(y, x1, buffer.width, &buffer, &mut commands);
                }
            }
        }

        write!(commands, "{}", STYLE_RESET).unwrap();

        if let Some([x, y]) = show_cursor {
            if x >= 0 && y >= 0 && x <= buffer.width as isize && y <= buffer.height as isize {
                write!(commands, "\x1B[{};{}H{}", y + 1, x + 1, CURSOR_SHOW).unwrap();
            }
        }

        if let Some(clipboard) = set_os_clipboard {
            if !clipboard.is_empty() {
                let b64 = base64_encode(clipboard.as_bytes());
                write!(commands, "\x1b]52;c;{}\x07", b64).unwrap();
            }
        }

        commands
    }

    pub fn present(&mut self, buffer: ScreenBuffer, commands: Vec<u8>, _prof: &mut ProfileBucket) -> Result<()> {
        profile_syscall!({
            io::stdout().write_all(&commands)?;
            io::stdout().flush()?;
        });

        self.temp_buffer = mem::replace(&mut self.prev_buffer, buffer);
        Ok(())
    }
}


bitflags! {
#[derive(Default)]
pub struct ModKeys: u8 {
    // The values match the encoding in the ANSI escape codes, do not change.
    // SHIFT doesn't always appear as modifier: for Key::Char, it's built into the `char`, e.g. 'E' is shift+e.
    const SHIFT = 0x1;
    const ALT = 0x2; // or Meta
    const CTRL = 0x4;

    // Special value that can only be used in capture_keys. Means accept any combination of modifier keys.
    const ANY = 0x8;
}}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum Key {
    Char(char),
    F(u8),
    Backspace,
    Escape,
    Up,
    Down,
    Right,
    Left,
    PageUp,
    PageDown,
    Home,
    End,
    Insert,
    Delete,

    // Failed to parse, skipped bytes (available in EventInfo::bytes). This is a Key rather than Event just for convenience of propagating it through `UI` into TerminalWindow.
    Unknown,
}
impl Key {
    pub fn mods(self, mods: ModKeys) -> KeyEx { KeyEx {key: self, mods} }
    pub fn plain(self) -> KeyEx { KeyEx {key: self, mods: ModKeys::empty()} }
    pub fn ctrl(self) -> KeyEx { KeyEx {key: self, mods: ModKeys::CTRL} }
    pub fn shift(self) -> KeyEx { KeyEx {key: self, mods: ModKeys::SHIFT} }
    pub fn alt(self) -> KeyEx { KeyEx {key: self, mods: ModKeys::ALT} }
    pub fn any_mods(self) -> KeyEx { KeyEx {key: self, mods: ModKeys::ANY} }
    pub fn is_ordinary_char(self) -> bool {
        match self {
            Self::Char('\t') | Self::Char('\n') | Self::Char('\r') => false,
            Self::Char(_) => true,
            _ => false,
        }
    }
    pub fn is_arrow_key(self) -> bool { match self { Key::Left | Key::Right | Key::Up | Key::Down => true, _ => false } }
}
impl Display for Key {
    fn fmt(&self, f: &mut Formatter<'_>) -> result::Result<(), fmt::Error> {
        let s = match *self {
            Key::Left => "left",
            Key::Right => "right",
            Key::Up => "up",
            Key::Down => "down",
            Key::Insert => "ins",
            Key::Delete => "del",
            Key::Home => "home",
            Key::End => "end",
            Key::PageUp => "pageup",
            Key::PageDown => "pagedown",
            Key::Backspace => "backspace",
            Key::Escape => "esc",
            Key::F(n) => return write!(f, "F{}", n),
            Key::Char('\n') => "enter",
            Key::Char('\t') => "tab",
            Key::Char(' ') => "space",
            Key::Char('\\') => "\\\\", //////// ////////////////
            Key::Char(c) if c.is_ascii() && !c.is_ascii_control() => return write!(f, "{}", c), 
            Key::Char(c) => return write!(f, "\\x{:02x}", c as u32),
            Key::Unknown => "unknown",
        };
        write!(f, "{}", s)
    }
}
impl FromStr for Key {
    type Err = ();
    fn from_str(s: &str) -> result::Result<Self, ()> {
        // If one character, return that character (without checking if it's printable etc).
        let mut it = s.chars();
        let c = match it.next() {
            None => return Err(()),
            Some(x) => x };
        if it.next().is_none() {
            return Ok(Key::Char(c));
        }

        if !s.is_ascii() {
            return Err(());
        }

        Ok(match s {
            "left" => Key::Left,
            "right" => Key::Right,
            "up" => Key::Up,
            "down" => Key::Down,
            "ins" => Key::Insert,
            "del" => Key::Delete,
            "home" => Key::Home,
            "end" => Key::End,
            "pageup" => Key::PageUp,
            "pagedown" => Key::PageDown,
            "backspace" => Key::Backspace,
            "esc" => Key::Escape,
            "enter" => Key::Char('\n'),
            "tab" => Key::Char('\t'),
            "space" => Key::Char(' '),
            s if s.starts_with("F") => match s[1..].parse::<u8>() {
                Err(_) => return Err(()),
                Ok(n) => Key::F(n),
            }
            s if s.starts_with("\\x") => match u32::from_str_radix(&s[2..], 16) {
                Err(_) => return Err(()),
                Ok(n) => match char::try_from(n) {
                    Err(_) => return Err(()),
                    Ok(c) => Key::Char(c),
                }
            }
            _ => return Err(()),
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct KeyEx {
    pub key: Key,
    pub mods: ModKeys,
}
impl Display for KeyEx {
    fn fmt(&self, f: &mut Formatter<'_>) -> result::Result<(), fmt::Error> {
        if self.mods.contains(ModKeys::CTRL) {
            write!(f, "C-")?;
        }
        if self.mods.contains(ModKeys::ALT) {
            write!(f, "M-")?;
        }
        if self.mods.contains(ModKeys::SHIFT) {
            write!(f, "S-")?;
        }
        if self.mods.contains(ModKeys::ANY) {
            write!(f, "?-")?;
        }
        write!(f, "{}", self.key)
    }
}
impl FromStr for KeyEx {
    type Err = ();
    fn from_str(mut s: &str) -> result::Result<Self, ()> {
        let mut mods = ModKeys::empty();
        loop {
            if s.starts_with("C-") {
                if mods.contains(ModKeys::CTRL) { return Err(()); }
                mods.insert(ModKeys::CTRL);
            } else if s.starts_with("M-") {
                if mods.contains(ModKeys::ALT) { return Err(()); }
                mods.insert(ModKeys::ALT);
            } else if s.starts_with("S-") {
                if mods.contains(ModKeys::SHIFT) { return Err(()); }
                mods.insert(ModKeys::SHIFT);
            } else {
                break;
            }
            s = &s[2..];
        }
        Ok(KeyEx {key: s.parse()?, mods})
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MouseMode {
    // No mouse support.
    Disabled,
    // Respond to clicks and drags, but not to hovers.
    NoHover,
    // Respond to clicks, drags, and hovers.
    // Because of a weird quirk in how terminal mouse reporting works, this generates much more mouse events for us to parse and process.
    // (Specifically: there's a mode where mouse movement is reported only when a button is held down, and only when the cursor moves to a different cell in the terminal;
    //  and another mode where mouse movement is reported always, even if the mouse moved by one pixel. But pixel coordinates are not even reported, only cell coordinated,
    //  so why would the application be interested in small movement events? There's no mode to report movements regardless of button holding, but only when the cursor moves to a different cell.)
    Full,
}
impl Default for MouseMode { fn default() -> Self { Self::Full } }

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum MouseEvent {
    Press,
    Release,
    Move,
    ScrollUp,
    ScrollDown,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum MouseButton {
    Left,
    Middle,
    Right,
    None,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct MouseEventEx {
    pub pos: [isize; 2], // [x, y], 0-based
    pub button: MouseButton,
    pub event: MouseEvent,
    pub mods: ModKeys,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Event {
    Key(KeyEx),
    Mouse(MouseEventEx),
    // The terminal gained or lost focus.
    FocusIn,
    FocusOut,
}
impl Event {
    pub fn is_key(&self) -> bool { match self { Self::Key(_) => true, _ => false } }
}

// u8 array with small vec optimization. 24 bytes. 22 bytes of inline storage.
// Can be implemented more carefully to be 16 bytes (with 15 bytes of inline storage, which is just enough for EventInfo), and maybe unified with ValueBlob.
#[derive(Clone)]
pub enum SmallArray {
    Short {data: [u8; 22], len: u8},
    Long(Box<[u8]>),
}
impl SmallArray {
    pub fn new(data: &[u8]) -> Self {
        if data.len() <= 22 {
            let mut d = [0u8; 22];
            d[..data.len()].copy_from_slice(data);
            Self::Short {data: d, len: data.len() as u8}
        } else {
            Self::Long(Box::from(data))
        }
    }
    pub fn as_slice(&self) -> &[u8] {
        match self {
            Self::Short {data, len} => &data[..*len as usize],
            Self::Long(b) => &b,
        }
    }
}
impl Default for SmallArray { fn default() -> Self { Self::Short {data: [0; 22], len: 0} } }

#[derive(Clone)]
pub struct EventInfo {
    pub ev: Event,
    pub bytes: SmallArray,
}
impl EventInfo {
    pub fn new(ev: Event, bytes: &[u8]) -> Self {
        Self {ev, bytes: SmallArray::new(bytes)}
    }
}

pub struct InputReader {
    start: usize,
    end: usize,
    buf: [u8; 128],
    saw_extra_escape: bool,
}
impl InputReader {
    pub fn new() -> Self { Self {start: 0, end: 0, buf: [0; 128], saw_extra_escape: false} }

    // Reads readily available input from stdin, doesn't block.
    pub fn read(&mut self, out: &mut Vec<EventInfo>, prof: &mut ProfileBucket) -> Result<usize> {
        let mut bytes_read = 0usize;
        loop {
            if self.start * 2 > self.buf.len() {
                self.buf.copy_within(self.start..self.end, 0);
                self.end -= self.start;
                self.start = 0;
            }
            assert!(self.end < self.buf.len()); // true as long as escape sequences are shorter than buf.len()/2, which they should be
            let n = Self::read_bytes(&mut self.buf[self.end..], prof)?;
            if n == 0 {
                return Ok(bytes_read);
            }
            self.end += n;
            bytes_read += n;

            loop {
                let mut start = self.start;
                let mut e = self.parse_event();

                // Fix up weird escape sequences like <esc><esc>[5~ , where the extra <esc> means ALT key.
                // Apply this only to few keys where I saw this behavior (in iTerm2).
                if self.saw_extra_escape {
                    if let Ok(e) = &mut e {
                        if let Event::Key(k) = e {
                            if k.mods.is_empty() && [Key::Left, Key::Right, Key::Up, Key::Down, Key::PageUp, Key::PageDown].contains(&k.key) {
                                k.mods.insert(ModKeys::ALT);
                                self.saw_extra_escape = false;
                            }
                        }
                    }
                }
                if mem::take(&mut self.saw_extra_escape) && e != Err(true) {
                    out.push(EventInfo::new(Event::Key(Key::Escape.plain()), &self.buf[start..start+1]));
                    start += 1;
                }

                match e {
                    Ok(e) => out.push(EventInfo::new(e, &self.buf[start..self.start])),
                    // Quietly skip unrecognized escape sequence.
                    Err(false) => out.push(EventInfo::new(Event::Key(Key::Unknown.plain()), &self.buf[start..self.start])),
                    Err(true) => {
                        // Do rollback here so that parse_event() can just eat chars and not worry about peek/advance.
                        self.start = start;
                        break;
                    }
                }
            }
        }
    }

    fn read_bytes(buf: &mut [u8], _prof: &mut ProfileBucket) -> Result<usize> {
        loop { // retry EINTR
            let mut pfd = libc::pollfd {fd: libc::STDIN_FILENO, events: libc::POLLIN, revents: 0};
            let r = profile_syscall!(unsafe {libc::poll(&mut pfd as *mut libc::pollfd, 1, 0)});
            if r < 0 {
                let e = io::Error::last_os_error();
                if e.kind() == io::ErrorKind::Interrupted {
                    continue;
                }
                return Err(e.into());
            }
            if r == 0 {
                return Ok(0);
            }

            let r = profile_syscall!(unsafe {libc::read(libc::STDIN_FILENO, buf.as_ptr() as *mut libc::c_void, buf.len())});
            if r < 0 {
                let e = io::Error::last_os_error();
                if e.kind() == io::ErrorKind::Interrupted {
                    continue;
                }
                return Err(e.into());
            }
            return Ok(r as usize);
        }
    }

    // Event parsing functions use Result<..., bool>, where the bool is:
    //  * true if we reached end of buffer before getting a complete escape sequence,
    //  * false if we got an invalid or unsupported escape sequence.
    
    fn peek(&self) -> result::Result<u8, bool> {
        if self.start == self.end {
            Err(true)
        } else {
            Ok(self.buf[self.start])
        }
    }
    
    fn eat(&mut self) -> result::Result<u8, bool> {
        let c = self.peek()?;
        self.start += 1;
        Ok(c)
    }

    fn ansi_modifier(mut n: usize) -> result::Result<ModKeys, bool> {
        if n < 1 || n > 16 {
            Err(false)
        } else {
            n -= 1;
            if n & 8 == 8 {
                // Convert Meta to Alt.
                n |= 2;
                n ^= 8;
            }
            Ok(ModKeys::from_bits(n as u8).unwrap())
        }
    }

    fn ansi_key_xterm(c: u8) -> result::Result<Key, bool> {
        Ok(match c {
            b'A' => Key::Up,
            b'B' => Key::Down,
            b'C' => Key::Right,
            b'D' => Key::Left,
            b'H' => Key::Home,
            b'F' => Key::End,
            c @ b'P'..=b'S' => Key::F(1 + c - b'P'), // F1-F4
            _ => return Err(false),
        })
    }

    fn ansi_key_vt(n: usize) -> result::Result<Key, bool> {
        Ok(match n {
            1 => Key::Home,
            2 => Key::Insert,
            3 => Key::Delete,
            4 => Key::End,
            5 => Key::PageUp,
            6 => Key::PageDown,
            7 => Key::Home,
            8 => Key::End,
            10..=15 => Key::F(n as u8 - 10 + 0), // F0-F5
            17..=21 => Key::F(n as u8 - 17 + 6), // F6-F10
            23..=26 => Key::F(n as u8 - 23 + 11), // F11-F14
            28..=29 => Key::F(n as u8 - 28 + 15), // F15-F16
            31..=34 => Key::F(n as u8 - 31 + 17), // F17-F20
            _ => return Err(false),
        })
    }

    fn ansi_key_char(&mut self, c: u8) -> result::Result<KeyEx, bool> {
        Ok(match c {
            b'\n' | b'\r' => Key::Char('\n').plain(),
            b'\x7f' => Key::Backspace.plain(),
            b'\x08' => Key::Backspace.ctrl(), // ctrl+backspace is indistinguishable from ctrl+h
            b'\x00' => Key::Char(' ').ctrl(),
            b'\x01'..=b'\x1A' => Key::Char((c - 0x1 + b'a') as char).ctrl(), // ctrl+[a..z]; shift is ignored in this case
            b'\x1c'..=b'\x1f' => Key::Char((c - 0x1c + b'4') as char).ctrl(), // crtl+[4..7]; other digits don't work
            0..=127 => Key::Char(c.into()).plain(), // fast path for ASCII
            _ => {
                let utf8_len = match c {
                    0b00000000..=0b01111111 => 1,
                    0b11000000..=0b11011111 => 2,
                    0b11100000..=0b11101111 => 3,
                    0b11110000..=0b11110111 => 4,
                    _ => return Err(false),
                };
                let end = self.start - 1 + utf8_len;
                if end > self.end {
                    return Err(true);
                }
                let s = &self.buf[self.start-1..end];
                self.start = end;
                match std::str::from_utf8(s) {
                    Ok(s) => {
                        let mut it = s.chars();
                        let c = it.next().unwrap();
                        assert!(it.next().is_none());
                        Key::Char(c).plain()
                    }
                    Err(_) => return Err(false),
                }
            }
        })
    }

    fn parse_ansi_number(&mut self) -> result::Result<usize, bool> {
        let mut n = 0usize;
        let start = self.start;
        loop {
            let c = self.peek()?;
            if c >= b'0' && c <= b'9' {
                self.start += 1;
                if n > 1000000 || (n == 0 && self.start > start + 2) {
                    return Err(false);
                }
                n = n * 10 + (c - b'0') as usize;
            } else {
                return Ok(n);
            }
        }
    }

    // Returns Err if hit end of buffer before getting a complete escape sequence.
    fn parse_event(&mut self) -> result::Result<Event, bool> {
        Ok(match self.eat()? {
            // ANSI escape codes are a mess. Some escape sequences are prefixes of other escape sequences. There's no reliable way to distinguish them, so we have to guess.
            // E.g. <esc>OP could be [escape key, shift+o, shift+p] or [alt+shift+o, shift+p] or [F1].
            //
            // Main cases (from https://en.wikipedia.org/wiki/ANSI_escape_code#Terminal_input_sequences ):
            // <char> -> keypress
            // <esc> -> esc
            // <esc> <char> -> alt-keypress
            // <esc> '[' -> alt-[
            // <esc> '[' (<modifier>) <char>   -> keypress, <modifier> is a decimal number and defaults to 1 (xterm)
            // <esc> '[' (<keycode>) (';'<modifier>) '~'   -> keypress, <keycode> and <modifier> are decimal numbers and default to 1 (vt)
            // <esc> <esc> '[' <char>   -> alt-keypress
            // <esc> <esc> '[' <keycode> '~'   -> alt-keypress
            // <esc> '[' '<' ...  -> mouse event

            // Escape key.
            b'\x1B' if self.start == self.end && self.end < self.buf.len() => Event::Key(Key::Escape.plain()),
            // Escape sequences.
            b'\x1B' => {
                let mut c = self.eat()?;
                if c == b'\x1B' {
                    if self.start == self.end && self.end < self.buf.len() {
                        // Escape key twice.
                        self.start -= 1;
                        return Ok(Event::Key(Key::Escape.plain()));
                    }
                    // Maybe a weird "<esc><esc>[<key>" escape sequence, maybe escape key followed by escape sequence. The caller will decide.
                    self.saw_extra_escape = true;
                    c = self.eat()?;
                }
                match c {
                    // Mashing the escape key.
                    b'\x1B' => {
                        self.start -= 1;
                        Event::Key(Key::Escape.plain())
                    }
                    // Alt+O
                    b'O' if self.start == self.end && self.end < self.buf.len() => Event::Key(Key::Char('O').alt()),
                    // F1-F4
                    b'O' => match self.eat()? {
                        c @ b'P'..=b'S' => Event::Key(Key::F(1 + c - b'P').plain()),
                        b'A' => Event::Key(Key::Up.plain()),
                        b'B' => Event::Key(Key::Down.plain()),
                        b'C' => Event::Key(Key::Right.plain()),
                        b'D' => Event::Key(Key::Left.plain()),
                        _ => return Err(false),
                    }
                    // Alt+[
                    b'[' if self.start == self.end && self.end < self.buf.len() => Event::Key(Key::Char('[').alt()),
                    // Mouse events.
                    b'[' if self.peek()? == b'<' => {
                        self.start += 1;
                        let n = self.parse_ansi_number()?;
                        if self.eat()? != b';' {
                            return Err(false);
                        }
                        let x = self.parse_ansi_number()?;
                        if self.eat()? != b';' {
                            return Err(false);
                        }
                        let y = self.parse_ansi_number()?;
                        let c = self.eat()?;

                        let mut button = match n&3 {
                            0 => MouseButton::Left,
                            1 => MouseButton::Middle,
                            2 => MouseButton::Right,
                            3 => MouseButton::None,
                            _ => panic!("huh"),
                        };
                        let mods = ModKeys::from_bits(((n>>2)&7) as u8).unwrap();
                        let mut event = if c == b'm' {MouseEvent::Release} else {MouseEvent::Press};

                        if n&32 != 0 {
                            event = MouseEvent::Move;
                        }
                        if n&64 != 0 {
                            event = match n&3 {
                                0 => MouseEvent::ScrollUp,
                                1 => MouseEvent::ScrollDown,
                                // 2 => MouseEvent::ScrollLeft,
                                // 3 => MouseEvent::ScrollRight,
                                _ => return Err(false),
                            };
                            button = MouseButton::None;
                        }

                        Event::Mouse(MouseEventEx {pos: [x as isize - 1, y as isize - 1], button, event, mods})
                    }
                    b'[' if self.peek()? == b'I' => { self.start += 1; Event::FocusIn }
                    b'[' if self.peek()? == b'O' => { self.start += 1; Event::FocusOut }
                    // xterm and vt escape sequences.
                    b'[' => {
                        // [number] [;[number]] char
                        let n = self.parse_ansi_number()?;
                        let mut c = self.eat()?;
                        let mut mods = ModKeys::empty();
                        if c == b';' {
                            mods = Self::ansi_modifier(self.parse_ansi_number()?)?;
                            c = self.eat()?;
                        }

                        if c == b'~' {
                            // vt
                            Event::Key(Self::ansi_key_vt(n)?.mods(mods))
                        } else {
                            // xterm
                            Event::Key(Self::ansi_key_xterm(c)?.mods(mods))
                        }
                    }
                    // Alt+char
                    c => {
                        let mut k = self.ansi_key_char(c)?;
                        k.mods.insert(ModKeys::ALT);
                        Event::Key(k)
                    }
                }
            }
            // Char (includes some special keys, some codes for ctrl+key, shift+key if uppercase, some ctrl+shift+key).
            c => Event::Key(self.ansi_key_char(c)?),
        })
    }
}
