use crate::{*, common_ui::*, terminal::*, settings::*, util::*, log::*, pool::*, term_emu::*};
use std::{mem, ops::Range, collections::HashMap, time::{Instant, Duration}, hash::Hash, io, io::Write};
use bitflags::*;

// Immediate-mode UI library, inspired by https://www.rfleury.com/p/ui-series-table-of-contents
// Currently only does TUI, but probably can be made to support both GUI and TUI modes.

// Instructions for autolayout on how to calculate widget size.
#[derive(Clone, Copy, Debug)]
pub enum AutoSize {
    Fixed(usize),
    Text,
    // Sum of children sizes if STACK flag is set, max of children sizes otherwise.
    Children,
    // Same size as parent.
    Parent,
    // Take parent size, subtract sizes of children with Remainder sizes, split the remainder among Remainder children proportional to this number.
    Remainder(f64),
}
impl Default for AutoSize { fn default() -> Self { Self::Parent } }
impl AutoSize {
    pub fn is_children(&self) -> bool { match self { Self::Children => true, _ => false } }
    pub fn is_remainder(&self) -> bool { match self { Self::Remainder(_) => true, _ => false } }
    pub fn as_fixed(&self) -> Option<usize> { match self { Self::Fixed(x) => Some(*x), _ => None } }
}

bitflags! {
#[derive(Default)]
pub struct AxisFlags: u32 {
    // Children will be positioned one after another, like a stack of boxes (unrelated to stack data structure). Otherwise they'll all be at the same position.
    const STACK = 0x1;
    // Put this widget at the center of the parent. Not compatible with STACK on the parent.
    const CENTER = 0x2;

    // Position (rel_pos) won't be calculated by autolayout (it was either provided by the builder or already calculated by autolayout).
    // Otherwise rel_pos contains value from previous frame, or 0 if this widget didn't exist.
    const POS_KNOWN = 0x4;
    // Size won't be calculated by autolayout. Otherwise `size` contains value from previous frame or 0.
    const SIZE_KNOWN = 0x8;
}}

#[derive(Clone)]
pub struct Axis {
    pub flags: AxisFlags,
    pub auto_size: AutoSize,
    pub min_size: usize,
    pub max_size: usize,

    pub size: usize,
    pub rel_pos: isize, // relative to parent widget

    // Position relative to the screen. Calculated only at the end of the frame, when rendering. Any value assigned before that is ignored.
    pub abs_pos: isize,
}
impl Default for Axis { fn default() -> Self { Self {flags: AxisFlags::empty(), auto_size: AutoSize::Parent, min_size: 0, max_size: usize::MAX, size: 0, rel_pos: 0, abs_pos: 0} } }
impl Axis {
    // Index in `axes` list.
    pub const X: usize = 0;
    pub const Y: usize = 1;

    pub fn set_fixed_pos(&mut self, rel_pos: isize) {
        self.flags.insert(AxisFlags::POS_KNOWN);
        self.rel_pos = rel_pos;
    }
    pub fn set_fixed_size(&mut self, size: usize) {
        self.auto_size = AutoSize::Fixed(size);
        self.flags.insert(AxisFlags::SIZE_KNOWN);
        self.size = size;
    }
    pub fn get_fixed_size(&self) -> usize {
        assert!(self.flags.contains(AxisFlags::SIZE_KNOWN));
        self.size
    }
    pub fn get_fixed_pos(&self) -> isize {
        assert!(self.flags.contains(AxisFlags::POS_KNOWN));
        self.rel_pos
    }
    pub fn get_fixed_range(&self) -> Range<isize> {
        let p = self.get_fixed_pos();
        p..p+self.get_fixed_size() as isize
    }
    pub fn reset_size(&mut self) {
        self.flags.remove(AxisFlags::SIZE_KNOWN);
    }
}

bitflags! {
#[derive(Default)]
pub struct WidgetFlags: u32 {
    // By default, if text doesn't fit horizontally or vertically in its Widget's width, a "…" is shown at the end. This flag disables this behavior.
    const TEXT_TRUNCATION_INDICATOR_DISABLE = 0x1;
    // If the text doesn't fit horizontally, keep a suffix rather than a prefix, and put the "…" at the start. If the text is not truncated, it's aligned left.
    const TEXT_TRUNCATION_ALIGN_RIGHT = 0x2;
    const LINE_WRAP = 0x4;
    const REPEAT_TEXT_VERTICALLY = 0x8;
    // const REPEAT_TEXT_HORIZONTALLY = 0x10; - not implemented

    // These two flags are for drawing left/right arrows to the left and right of each line of text (or other content) to indicate that the text is cut off and horizontal scrolling is available.
    // Draws a corresponding arrow when the corresponding edge of this widget is clipped off by ancestor widgets.
    // For widgets with draw_text, HSCROLL_INDICATOR_RIGHT applies to each line individually, showing arrow only if the line is clipped (i.e. using line width instead of widget width).
    //
    // These flags are separate because they often should be applied to different widgets.
    // HSCROLL_INDICATOR_LEFT widget's rect should touch the right edge of the hscrollable area content rect; otherwise the arrow will be incorrectly missing if the viewport is
    // fully to the right of this widget (the widget is fully clipped, so there's nowhere to draw the arrow).
    // Symmetrically, HSCROLL_INDICATOR_RIGHT should be applied to widget with X position = 0.
    // Example widget tree:
    //   hscroll viewport
    //     hscroll content (width=100)  <-- put HSCROLL_INDICATOR_LEFT here
    //       line1 (width=42, hstack)   <-- put HSCROLL_INDICATOR_RIGHT here
    //         prefix widget
    //         suffix widget
    //       line2 (width=100)          <-- put HSCROLL_INDICATOR_RIGHT here
    // (In this example, we can't put HSCROLL_INDICATOR_RIGHT on "hscroll content" because it doesn't "know" that line1 is shorter than 100.
    //  And we can't put HSCROLL_INDICATOR_LEFT on "line1" because it'll fail to show the left arrow if hscroll offset is >= 42, when line1 is fully off-screen.)
    const HSCROLL_INDICATOR_LEFT = 0x20;
    const HSCROLL_INDICATOR_RIGHT = 0x40;

    // StyleAdjstment won't be inherited from ancestors. E.g. for drawing text input box with standard background in a panel with tinted background.
    const RESET_STYLE_ADJUSTMENT = 0x80;

    // If any part of this rect is visible (i.e. not clipped by parents' rects), trigger a redraw. May be useful for speculative hiding of elements,
    // but currently unused because I made everything non-speculative instead.
    const REDRAW_IF_VISIBLE = 0x100;

    // Any simple character key presses (no modifier keys, no special keys like tab or enter) are captured by this Widget as if they were in capture_keys.
    // Doesn't include text navigation keys like arrow keys, home/end, etc; they should be requested through capture_keys as usual.
    const CAPTURE_TEXT_INPUT_KEYS = 0x200;
    // Invert `capture_keys`: capture all keys except those.
    const CAPTURE_ALL_KEYS = 0x400;

    // Trigger redraw is this Widget gets focused or unfocused.
    const REDRAW_IF_FOCUS_CHANGES = 0x800;

    // Equivalent to:
    //   if ui.check_mouse(MouseActions::HOVER_SUBTREE) {
    //       widget.style_adjustment.update(ui.palette.hovered);
    //   }
    const HIGHLIGHT_ON_HOVER = 0x1000;

    // This widget's identity won't be hashed into children identities. Instead, the nearest ancestor without this flag will be hashed. As if this widget didn't exist and its children were its parent's children.
    const SKIP_IDENTITY = 0x2000;
    // When adding this widget, don't update its identity with parent's identity. This allows moving it to a different place in the tree without losing focus.
    const DETACHED_IDENTITY = 0x4000;
}}

bitflags! {
#[derive(Default)]
pub struct MouseActions : u16 {
    // Mouse click inside this Widget's rectangle, if not captured by any descendant Widget (e.g. button inside table row) and not obstructed by a later clickable Widget with overlapping rectangle (e.g. dialog box).
    const CLICK = 0x2;
    // Mouse cursor being inside this Widget's rectangle, not captured by descendant, not obstructed. Event produced every frame, not only on mouse move.
    const HOVER = 0x4;
    // Scroll wheel movement while the cursor is inside this Widget's rectangle, not captured by descendant, not obstructed.
    const SCROLL = 0x1;
    // If a CLICK happened in this widget and then the mouse is moved without releasing the left mouse button, a DRAG_OUT event will be dispatched to this widget (even if the cursor leaves it) on each frame until the button is released.
    // If both CLICK and DRAG_OUT are requested then both are delivered on the same frame when dragging starts.
    // At most one widget may receive DRAG_OUT on each frame.
    const DRAG_OUT = 0x8;
    // If mouse was left-clicked in any DRAG_OUT widget, then moved over this widget (which may be the same one), this widget will receive a DRAG_IN event each frame.
    // At most one widget may receive DRAG_IN on each frame; there's normally a corresponding DRAG_OUT on the same frame, but it's not guaranteed (e.g. maybe the DRAG_OUT widget disappeared on this frame).
    const DRAG_IN = 0x10;
    // If DRAG_IN happened, then the mouse button was released, a DROP will be reported together with the final DRAG_IN. A corresponding DRAG_OUT is reported on that frame as well.
    // Required DRAG_IN.
    const DROP = 0x20;
    // CLICK on this Widget or any descendant. E.g. for focusing a window on click, even if the click is also processed by some button inside the window.
    const CLICK_SUBTREE = 0x40;
    // HOVER on this Widget or any descendant. E.g. for highlighting a table row even when hovering over some button inside that row.
    const HOVER_SUBTREE = 0x80;
    const MIDDLE_CLICK = 0x100;
    const RIGHT_CLICK = 0x200;
}}

// Identifies a thing that is being drag'n'dropped.
#[derive(Clone, Copy, Eq, PartialEq)]
pub enum DragWhat {
    NoDrop, // draggable but not droppable, e.g. scroll bar
    Window(Id),
    Tab {tabs_identity: usize, tab_idx: usize},
}
impl Default for DragWhat { fn default() -> Self { Self::NoDrop } }

#[derive(Default)]
pub struct Widget {
    // Identifier for matching widgets across frames. Usually a hash of something.
    // 0 means not matched across frames (but still present in prev_tree).
    pub identity: usize,
    // Line of the source code that created this widget. Useful for debugging.
    pub source_line: u32,
    
    pub axes: [Axis; 2], // X, Y
    pub flags: WidgetFlags,

    pub draw_text: Option<Range<usize>>, // lines in UI.text
    line_wrapped_text: Option<Range<usize>>,

    // Tree links.
    pub parent: WidgetIdx,
    depth: usize,
    pub children: Vec<WidgetIdx>,

    // Adjust all styles in the subtree. E.g. for tinting panel background or highlighting a table row.
    // Combines with adjustments from ancestors, unless RESET_STYLE_ADJUSTMENT flag is set.
    pub style_adjustment: StyleAdjustment,

    // Fill the rect with repetitions of one character (must be 1 column wide).
    pub draw_fill: Option<(char, Style)>,

    // Draw a rectangle just inside this Widget. If draw_text is set, put it at the top left as a title.
    pub draw_frame: Option<(Style, /*rounded*/ bool)>,

    // Renders a progress bar, 1 cell high, horizontally filling this Widget.
    // The f64 is in [0, 1]. Style fg is for the left side of the progress bar, bg is for the right side.
    // If draw_text is set, the text is drawn at the center, using the progress bar's style (text color is the opposite fg/bg color of the progress bar); the text's style is ignored, only the first line is used.
    pub draw_progress_bar: Option<(f64, Style)>,

    pub draw_terminal: Option<Rc<TerminalEmulator>>,

    pub draw_cursor_if_focused: Option<[isize; 2]>,

    // Put this widget somewhere close to the given widget, like a tooltip. The given widget must be earier in the render order (tree DFS order) than this widget.
    pub position_next_to: Option<WidgetIdx>,

    // Which child should be focused if this Widget is focused. If multiple, they'll all be focused, see multifocus().
    // These links connect the Widget-s into a second tree that's a subset of the main tree.
    // Input is dispatched in order of DFS post-order traversal of that tree.
    // Most of the time there's at most one focused child, and the focus tree is just a path from some widget to the root in the main tree.
    // Multifocus is useful e.g. in the search dialog where the text input and the search results table are both interactable at the same time (with different keys).
    focus_children: Vec<WidgetIdx>,
    // When was the last time this Widget was focused.
    focus_frame_idx: usize,

    // Which keys should be dispatched to this Widget, if it's focused.
    pub capture_keys: Vec<KeyEx>,
    // Key press events dispatched to this Widget on this frame.
    pub keys: Vec<KeyEx>,

    // Which mouse events should be dispatched to this Widget (regardless of whether it's focused).
    pub capture_mouse: MouseActions,
    // Mouse events dispatched to this Widget on this frame.
    pub mouse: MouseActions,
    pub scroll: isize, // scroll amount, if `mouse` contains SCROLL
    pub mouse_pos: [isize; 2], // mouse position, relative to this widget, if `mouse` is not empty
    pub drag_out_what: DragWhat, // if `capture_mouse` contains DRAG_OUT
    pub drag_in_what: DragWhat, // if `mouse` contains DRAG_IN or DROP

    // Miscellaneous.
    pub scroll_bar_drag_offset: isize, // used only by scroll bar widgets
}
impl Widget {
    // Convenience functions to assign some fields, to be used before add()ing the Widget to UI.
    pub fn identity<T: Hash + ?Sized>(mut self, t: &T) -> Self { self.identity = hash::<T>(t); self } // example: identity(("row", row_id))
    pub fn source_line(mut self, l: u32) -> Self { self.source_line = l; self }
    pub fn parent(mut self, parent: WidgetIdx) -> Self { self.parent = parent; self }
    pub fn width(mut self, s: AutoSize) -> Self { self.axes[Axis::X].auto_size = s; self }
    pub fn height(mut self, s: AutoSize) -> Self { self.axes[Axis::Y].auto_size = s; self }
    pub fn fixed_width(mut self, s: usize) -> Self { self.axes[Axis::X].auto_size = AutoSize::Fixed(s); self }
    pub fn fixed_height(mut self, s: usize) -> Self { self.axes[Axis::Y].auto_size = AutoSize::Fixed(s); self }
    pub fn min_width(mut self, s: usize) -> Self { self.axes[Axis::X].min_size = s; self }
    pub fn min_height(mut self, s: usize) -> Self { self.axes[Axis::Y].min_size = s; self }
    pub fn max_width(mut self, s: usize) -> Self { self.axes[Axis::X].max_size = s; self }
    pub fn max_height(mut self, s: usize) -> Self { self.axes[Axis::Y].max_size = s; self }
    pub fn hstack(mut self) -> Self { self.axes[0].flags.insert(AxisFlags::STACK); self }
    pub fn vstack(mut self) -> Self { self.axes[1].flags.insert(AxisFlags::STACK); self }
    pub fn set_hstack(&mut self) -> &mut Self { self.axes[0].flags.insert(AxisFlags::STACK); self }
    pub fn set_vstack(&mut self) -> &mut Self { self.axes[1].flags.insert(AxisFlags::STACK); self }
    pub fn fixed_x(mut self, x: isize) -> Self { self.axes[Axis::X].rel_pos = x; self.axes[0].flags.insert(AxisFlags::POS_KNOWN); self }
    pub fn fixed_y(mut self, y: isize) -> Self { self.axes[Axis::Y].rel_pos = y; self.axes[1].flags.insert(AxisFlags::POS_KNOWN); self }
    pub fn set_fixed_x(&mut self, x: isize) -> &mut Self { self.axes[Axis::X].set_fixed_pos(x); self }
    pub fn set_fixed_y(&mut self, y: isize) -> &mut Self { self.axes[Axis::Y].set_fixed_pos(y); self }
    pub fn fixed_rect(mut self, r: Rect) -> Self { for ax in 0..2 { let axis = &mut self.axes[ax]; axis.flags.insert(AxisFlags::POS_KNOWN | AxisFlags::SIZE_KNOWN); axis.rel_pos = r.pos[ax]; axis.size = r.size[ax]; } self }
    pub fn hcenter(mut self) -> Self { self.axes[Axis::X].flags.insert(AxisFlags::CENTER); self }
    pub fn vcenter(mut self) -> Self { self.axes[Axis::Y].flags.insert(AxisFlags::CENTER); self }
    pub fn text_lines(mut self, lines: Range<usize>) -> Self { self.draw_text = Some(lines); self }
    pub fn text(mut self, line: usize) -> Self { self.draw_text = Some(line..line+1); self } // example: styled_write!(ui.text, ...); let l = ui.text.close_line(); Widget::new().text(l);
    pub fn fill(mut self, c: char, s: Style) -> Self { self.draw_fill = Some((c, s)); self }
    pub fn flags(mut self, f: WidgetFlags) -> Self { self.flags.insert(f); self }
    pub fn style_adjustment(mut self, a: StyleAdjustment) -> Self { self.style_adjustment = a; self }
    pub fn highlight_on_hover(mut self) -> Self { self.flags.insert(WidgetFlags::HIGHLIGHT_ON_HOVER); self }

    // These assert that the corresponding size/position is already calculated.
    pub fn get_fixed_width(&self) -> usize { self.axes[Axis::X].get_fixed_size() }
    pub fn get_fixed_height(&self) -> usize { self.axes[Axis::Y].get_fixed_size() }
    pub fn get_fixed_rect(&self) -> Rect { Rect {pos: [self.axes[Axis::X].get_fixed_pos(), self.axes[Axis::Y].get_fixed_pos()], size: [self.axes[Axis::X].get_fixed_size(), self.axes[Axis::Y].get_fixed_size()]} }
    pub fn get_fixed_x(&self) -> isize { self.axes[Axis::X].get_fixed_pos() }
    pub fn get_fixed_y(&self) -> isize { self.axes[Axis::Y].get_fixed_pos() }

    pub fn set_fixed_width(&mut self, s: usize) -> &mut Self { self.axes[0].set_fixed_size(s); self }
    pub fn set_fixed_height(&mut self, s: usize) -> &mut Self { self.axes[1].set_fixed_size(s); self }

    // Copy and clear all fields related to being already part of the tree. The resulting Widget can be add()ed to the tree.
    // ("Questionable" because I'm not sure it's a good idea to allow this, and am not sure it'll work well.)
    pub fn make_questionable_copy(&self) -> Self {
        let mut r = Self {
            identity: self.identity, source_line: self.source_line, axes: self.axes.clone(), flags: self.flags, draw_text: self.draw_text.clone(), style_adjustment: self.style_adjustment, draw_fill: self.draw_fill.clone(), draw_progress_bar: self.draw_progress_bar.clone(), draw_frame: self.draw_frame.clone(), draw_terminal: None,
            parent: WidgetIdx::invalid(), depth: 0, children: Vec::new(), position_next_to: None, focus_children: Vec::new(), capture_keys: Vec::new(), keys: Vec::new(), capture_mouse: MouseActions::empty(), mouse: MouseActions::empty(), scroll: 0, mouse_pos: [0, 0], drag_out_what: DragWhat::default(), drag_in_what: DragWhat::default(), scroll_bar_drag_offset: 0, line_wrapped_text: None, draw_cursor_if_focused: None, focus_frame_idx: 0};
        r.flags.remove(WidgetFlags::REDRAW_IF_FOCUS_CHANGES);
        for axis in &mut r.axes {
            axis.flags.remove(AxisFlags::POS_KNOWN | AxisFlags::SIZE_KNOWN);
        }
        r
    }
}

// Use this to create a Widget, instead of Widget::default().
#[macro_export]
macro_rules! widget {
    () => {Widget::default().source_line(line!())};
}

#[derive(Default, Clone, Copy, Eq, PartialEq, Hash)]
pub struct WidgetIdx(usize);
impl WidgetIdx {
    pub fn invalid() -> Self { Self(0) }
    pub fn is_valid(self) -> bool { self.0 != 0 }
}

// Usage:
//   with_parent(ui, ui.add(widget!()...), {
//       ...
//   })
// Warning: return/continue/break out of this macro is not allowed, it would bypass the `$ui.cur_parent = prev_parent` cleanup.
//          This isn't checked at compile time and usually causes an assertion failure later.
#[macro_export]
macro_rules! with_parent {
    ($ui:expr, $parent_expr:expr, {$($code:tt)*}) => {{
        let p = $parent_expr;
        let prev_parent = mem::replace(&mut $ui.cur_parent, p);
        let r = {$($code)*};
        assert!($ui.cur_parent == p);
        $ui.cur_parent = prev_parent;
        r
    }};
}

#[macro_export]
macro_rules! ui_write {
    ($ui:expr, $style:ident, $($arg:tt)*) => {
        styled_write!($ui.text, $ui.palette.$style, $($arg)*)
    };
}
#[macro_export]
macro_rules! ui_writeln {
    ($ui:expr, $style:ident, $($arg:tt)*) => {{
        styled_write!($ui.text, $ui.palette.$style, $($arg)*);
        $ui.text.close_line()
    }};
}

#[derive(Default)]
pub struct UI {
    // These can be changed at any time.
    pub palette: Palette,
    pub key_binds: KeyBinds,

    // These are assigned by end_build(), to be checked and acted on by the caller.
    // `should_redraw` means we should build another frame right away. Useful when a later stage of the UI update/build/rendering sequence made a change that affects an earlier stage.
    // E.g. if some part of the build code saw that a widget is focused, but then focus moved to another widget later in the build (e.g. a dialog opened).
    // This shouldn't happen many times in a row, the state is expected to converge quickly (usually in 0 redraws) in absence of input or changes.
    // (Can't we reorder stages such that there are no backwards dependencies like this? No, there are "circular" dependencies. E.g. a key press in the source code window may trigger
    //  disassembly window to scroll (to the corresponding line), and vice versa.)
    pub should_redraw: bool,
    pub should_show_cursor: Option<[isize; 2]>,
    pub should_set_os_clipboard: bool,
    pub prof_render_tsc: u64, // how long render() took during the latest end_build() call
    // TODO: Animation system.

    // Current frame that's being built.

    pub tree: Vec<Widget>,
    pub text: StyledText,
    pub scratch_text: StyledText,

    pub root: WidgetIdx,
    pub cur_parent: WidgetIdx,

    pub frame_idx: usize,

    // By default we add 3 layers as children of root: content, dialog, tooltip. The logic around this is quite separate from the rest of UI and can be moved to something like UIState instead, if needed.
    // Main content.
    pub content_root: WidgetIdx,
    // At most one dialog window can be present. It's a child of this Widget, drawn over main content, always has focus, is "owned" by some other widget, and disappears if its owner stops requesting it.
    dialog_root: WidgetIdx,
    dialog_owner: Option<usize>,
    // At most one tooltip can be present. It's drawn over everything else, never has focus, is "owned" by some other widget, and disappears if its owner stops requesting it or loses focus.
    tooltip_root: WidgetIdx,
    tooltip_owner: Option<usize>,

    // Previous frame.

    pub prev_tree: Vec<Widget>,
    prev_map: HashMap<usize, WidgetIdx>,
    prev_root: WidgetIdx,
    prev_focus_chain: Vec<WidgetIdx>,

    // All keyboard/mouse input events that happened since the last frame.
    // Used only for passthrough to the nested tty in the console window.
    pub frame_events: Vec<EventInfo>,

    // Our best guess at the current state of the mouse and terminal, based on previously seen Event-s.
    pub mouse_pos: [isize; 2],
    pub mouse_buttons_held: Vec<MouseButton>,
    pub is_terminal_unfocused: bool,

    // Key presses not dispatched to widgets yet.
    input_buffer: Vec<KeyEx>,

    // Information about mouse events that happened since last frame. If there were multiple clicks, we only keep the last one.
    mouse_click: Option<[isize; 2]>, // coordinates separate from mouse_pos, to be precise if a click happened in the middle of a fast motion
    mouse_middle_click: Option<[isize; 2]>,
    mouse_right_click: Option<[isize; 2]>,
    mouse_scroll: isize,
    mouse_drag_out_widget: Option<usize>,
    mouse_drop_pos: Option<[isize; 2]>, // mouse coordinates when mouse button was released, if mouse_drag_out_widget is Some

    // Other state.

    pub clipboard: String,
}
impl UI {
    // Returns true if any of the input was significant enough that we should redraw.
    pub fn buffer_input(&mut self, events: &[EventInfo]) -> bool {
        let mut any_significant = false;
        for e in events {
            match &e.ev {
                Event::Key(key) => self.input_buffer.push(key.clone()),
                Event::FocusIn | Event::FocusOut => {
                    self.mouse_drag_out_widget = None;
                    self.is_terminal_unfocused = e.ev == Event::FocusOut;
                }
                Event::Mouse(MouseEventEx {pos, event: MouseEvent::Move, ..}) if *pos == self.mouse_pos => continue, // mouse move within the same terminal cell, ignore these
                &Event::Mouse(MouseEventEx {pos, button, event, ..}) => {
                    if button == MouseButton::Left && event == MouseEvent::Press {
                        self.mouse_click = Some(pos);
                    } else if button == MouseButton::Left && event == MouseEvent::Release {
                        if self.mouse_drag_out_widget.is_some() {
                            self.mouse_drop_pos = Some(pos.clone());
                        }
                    } else if button == MouseButton::Middle && event == MouseEvent::Press {
                        self.mouse_middle_click = Some(pos.clone());
                    } else if button == MouseButton::Right && event == MouseEvent::Press {
                        self.mouse_right_click = Some(pos.clone());
                    } else if event == MouseEvent::ScrollUp {
                        self.mouse_scroll -= 1;
                    } else if event == MouseEvent::ScrollDown {
                        self.mouse_scroll += 1
                    }
                    self.mouse_pos = pos.clone();
                    if event == MouseEvent::Release {
                        self.mouse_buttons_held.retain(|b| *b != button);
                    }
                    if event == MouseEvent::Press {
                        if !self.mouse_buttons_held.iter().find(|b| **b == button).is_none() {
                            self.mouse_buttons_held.push(button);
                        }
                    }
                }
            }
            self.frame_events.push(e.clone());
            any_significant = true;
        }
        any_significant
    }

    pub fn start_build(&mut self, width: usize, height: usize) {
        assert!(self.tree.is_empty());
        self.dispatch_input();
        self.text.clear();
        self.tree.push(Widget::default()); // 0 is reserved as invalid index
        self.should_redraw = false;
        self.frame_idx += 1;

        let mut w = Widget {identity: hash(&"root"), source_line: line!(), axes: [Axis {size: width, flags: AxisFlags::SIZE_KNOWN | AxisFlags::POS_KNOWN, ..D!()}, Axis {size: height, flags: AxisFlags::SIZE_KNOWN | AxisFlags::POS_KNOWN, ..D!()}], ..D!()};
        self.carry_widget_state_from_previous_frame(&mut w);
        self.tree.push(w);
        self.root = WidgetIdx(1);
        self.cur_parent = self.root;

        self.content_root = self.add(widget!().identity(&"content"));
        self.dialog_root = self.add(widget!().identity(&"dialog"));
        self.tooltip_root = self.add(widget!().identity(&"tooltip"));

        self.cur_parent = self.content_root;
    }

    pub fn end_build(&mut self, screen: &mut ScreenBuffer) {
        // Last chance to change focus.
        {
            if self.dialog_owner.is_some() && self.tree[self.dialog_root.0].children.is_empty() {
                self.dialog_owner = None;
            }
            if self.tooltip_owner.is_some() && self.tree[self.tooltip_root.0].children.is_empty() {
                self.tooltip_owner = None;
            }
            let focus = if self.dialog_owner.is_some() {self.dialog_root} else {self.content_root};
            let w = &mut self.tree[self.root.0];
            w.focus_children = vec![focus];
        }

        self.determine_focus_chain();

        if let &Some(identity) = &self.tooltip_owner {
            if !self.prev_focus_chain.iter().any(|idx| self.tree[idx.0].identity == identity) {
                self.tooltip_owner = None;
            }
        }
        if self.tooltip_owner.is_none() {
            self.tree[self.tooltip_root.0].children.clear();
        }

        // Do x before y because text height may depend on its width if line wrapping is enabled.
        self.layout_subtree(self.root, Axis::X);
        self.layout_subtree(self.root, Axis::Y);

        let timer = TscScope::new();
        self.render(screen);
        self.prof_render_tsc = timer.finish();

        mem::swap(&mut self.tree, &mut self.prev_tree);
        self.prev_root = self.root;
        self.tree.clear();
        self.prev_map.clear();
        for (i, w) in self.prev_tree.iter_mut().enumerate() {
            if w.identity != 0 {
                let prev = self.prev_map.insert(w.identity, WidgetIdx(i));
                if let Some(_) = prev {
                    eprintln!("warning: duplicate widget identity: {} (line {})", w.identity, w.source_line);
                }
            }
            w.keys.clear();
            w.mouse = MouseActions::empty();
            w.scroll = 0;
            w.mouse_pos = [0, 0];
            w.draw_terminal = None;
        }
        self.frame_events.clear();
    }

    pub fn add(&mut self, mut w: Widget) -> WidgetIdx {
        if !w.parent.is_valid() {
            w.parent = self.cur_parent;
        }

        let new_idx = WidgetIdx(self.tree.len());

        let parent = &mut self.tree[w.parent.0];
        parent.children.push(new_idx);

        let parent = &self.tree[w.parent.0];

        // Assert that we're not adding children after calculating sizes that depend on them.
        // This check is not exhaustive, e.g. nothing prevents the caller from modifying a previously added Widget in a way that breaks layout.
        for ax in 0..2 {
            if w.axes[ax].flags.contains(AxisFlags::POS_KNOWN) {
                // Allow adding floating widgets after doing layout.
                continue;
            }
            assert!(!parent.axes[ax].auto_size.is_children() || !parent.axes[ax].flags.contains(AxisFlags::SIZE_KNOWN), "tried to add child (line {}) to a widget (line {}) whose size depends on children, after calculating its size", w.source_line, parent.source_line);
            if parent.children.len() > 1 {
                let prev_sibling = &self.tree[parent.children[parent.children.len() - 2].0];
                assert!(!prev_sibling.axes[ax].auto_size.is_remainder() || !prev_sibling.axes[ax].flags.contains(AxisFlags::SIZE_KNOWN), "tried to add sibling (line {}) of a widget (line {}) whose size depends on siblings, after calculating its size", w.source_line, prev_sibling.source_line);
            }
        }

        // Calculate size early if possible.
        for ax in 0..2 {
            let axis = &mut w.axes[ax];
            if !axis.flags.contains(AxisFlags::SIZE_KNOWN) {
                match &axis.auto_size {
                    AutoSize::Fixed(_) => { Self::try_calculate_simple_size(&mut w, ax, &mut self.text, &self.palette); }
                    AutoSize::Text => (), // text is often assigned later, after add()
                    AutoSize::Parent if parent.axes[ax].flags.contains(AxisFlags::SIZE_KNOWN) => { axis.size = parent.axes[ax].size.max(axis.min_size).min(axis.max_size); axis.flags.insert(AxisFlags::SIZE_KNOWN); }
                    AutoSize::Remainder(_) if axis.flags.contains(AxisFlags::STACK) && (axis.min_size != 0 || axis.max_size != usize::MAX) => panic!("min_size/max_size with AutoSize::Remainder is not supported"),
                    AutoSize::Children | AutoSize::Remainder(_) | AutoSize::Parent => (),
                }
            }
        }

        if !w.flags.contains(WidgetFlags::DETACHED_IDENTITY) {
            if w.identity == 0 {
                w.identity = parent.children.len();
            }

            let mut idx = w.parent;
            while idx.is_valid() {
                let p = &self.tree[idx.0];
                if !p.flags.contains(WidgetFlags::SKIP_IDENTITY) {
                    w.identity = hash(&(w.identity, p.identity));
                    break;
                }
                idx = p.parent;
            }
        }
        w.depth = parent.depth + 1;

        self.carry_widget_state_from_previous_frame(&mut w);

        self.tree.push(w);
        new_idx
    }

    // Request this widget to be focused, i.e. be a recepient of keyboard input after the end of this frame.
    // Whether the widget actually ends up focused is not determined until the end of the frame build. E.g. a dialog may be added later and steal focus from everyone else.
    // This function assigns the focus_children links of ancestors to point towards this Widget, stopping if an ancestor already has a focus link pointing elsewhere - that link won't be redirected.
    // E.g. if a different window is already focused, focus() on a widget inside the window won't focus this window.
    pub fn focus(&mut self) {
        let mut idx = self.cur_parent;
        let mut parent_idx = self.cur().parent;
        while parent_idx.is_valid() {
            let w = &mut self.tree[parent_idx.0];
            if !w.focus_children.is_empty() {
                break;
            }
            w.focus_children.push(idx);
            idx = parent_idx;
            parent_idx = w.parent;
        }
    }

    // Like focus(), but allows the direct parent to have multiple focused children.
    pub fn multifocus(&mut self) {
        let parent_idx = self.tree[self.cur_parent.0].parent;
        if !parent_idx.is_valid() {
            return;
        }
        let parent = &mut self.tree[parent_idx.0];
        if parent.focus_children.is_empty() {
            self.focus();
        } else if !parent.focus_children.iter().any(|c| *c == self.cur_parent) {
            parent.focus_children.push(self.cur_parent);
        }
    }

    // Focus current widget within the subtree of its ancestor. If that ancestor ends up focused, this widget will be focused.
    pub fn relative_focus(&mut self, ancestor: WidgetIdx) {
        let mut idx = self.cur_parent;
        let mut parent_idx = self.cur().parent;
        while parent_idx.is_valid() {
            let w = &mut self.tree[parent_idx.0];
            if !w.focus_children.is_empty() {
                return;
            }
            w.focus_children.push(idx);
            if parent_idx == ancestor {
                return;
            }
            idx = parent_idx;
            parent_idx = w.parent;
        }
        panic!("ancestor is not an ancestor");
    }

    // Checks whether this widget was focused on the previous frame. Sets REDRAW_IF_FOCUS_CHANGES flag.
    // Useful for auto-closing modal elements (e.g. watch text input) when they lose focus.
    // For auto-closing, this has to be used on some longer-lived ancestor widget; for a widget that was created+focus()ed on this frame, this returns false.
    pub fn check_focus(&mut self) -> bool {
        let w = &mut self.tree[self.cur_parent.0];
        w.flags.insert(WidgetFlags::REDRAW_IF_FOCUS_CHANGES);
        w.focus_frame_idx == self.frame_idx
    }

    fn carry_widget_state_from_previous_frame(&mut self, w: &mut Widget) {
        if let Some(prev_idx) = self.prev_map.get(&w.identity) {
            let prev = &mut self.prev_tree[prev_idx.0];
            for ax in 0..2 {
                let axis = &mut w.axes[ax];
                if !axis.flags.contains(AxisFlags::SIZE_KNOWN) {
                    axis.size = prev.axes[ax].size;
                }
                if !axis.flags.contains(AxisFlags::POS_KNOWN) {
                    axis.rel_pos = prev.axes[ax].rel_pos;
                }
                axis.abs_pos = prev.axes[ax].abs_pos;
            }
            w.keys = mem::take(&mut prev.keys);
            w.mouse = mem::take(&mut prev.mouse);
            w.scroll = mem::take(&mut prev.scroll);
            w.mouse_pos = mem::take(&mut prev.mouse_pos);
            w.drag_in_what = mem::take(&mut prev.drag_in_what);
            w.scroll_bar_drag_offset = mem::take(&mut prev.scroll_bar_drag_offset);
            w.focus_frame_idx = mem::take(&mut prev.focus_frame_idx);
        }        
    }

    // These are convenient, but it's ok to access `tree` directly too (to avoid borrowing the whole UI).
    pub fn get(&self, idx: WidgetIdx) -> &Widget { &self.tree[idx.0] }
    pub fn get_mut(&mut self, idx: WidgetIdx) -> &mut Widget { &mut self.tree[idx.0] }
    pub fn cur(&self) -> &Widget { &self.tree[self.cur_parent.0] }
    pub fn cur_mut(&mut self) -> &mut Widget { &mut self.tree[self.cur_parent.0] }

    // Calculate size if auto_size is Fixed, Text, or Children, i.e. doesn't depend on parent. If size was already calculated, returns it. Otherwise panics.
    // Traverses part of the subtree as (if children have auto_size = Children too).
    // All sizes that we manage to determine are marked as final (SIZE_KNOWN) and will be excluded from later autolayout passes.
    // Therefore modifying the subtree in a way that changes sizes isn't allowed after this call (e.g. adding children if auto_size is Children).
    pub fn calculate_size(&mut self, idx: WidgetIdx, axis_idx: usize) -> usize {
        self.calculate_bottom_up_sizes(idx, axis_idx, false);
        let axis = &self.tree[idx.0].axes[axis_idx];
        assert!(axis.flags.contains(AxisFlags::SIZE_KNOWN));
        axis.size
    }

    // Calculate sizes and relative positions of cur_parent's children. Particularly useful if some children have auto_size Remainder. Same caveats as calculate_size() - calculated sizes and positions are final.
    pub fn layout_children(&mut self, axis_idx: usize) {
        let idx = self.cur_parent;
        self.calculate_size(idx, axis_idx);
        let mut scratch = self.tree[idx.0].children.clone();
        for &c in &scratch {
            match &self.tree[c.0].axes[axis_idx].auto_size {
                AutoSize::Fixed(_) | AutoSize::Text | AutoSize::Children => self.calculate_bottom_up_sizes(c, axis_idx, false),
                AutoSize::Parent | AutoSize::Remainder(_) => (),
            }
        }
        self.calculate_children_layout(idx, axis_idx, &mut scratch);
    }

    pub fn layout_subtree(&mut self, root: WidgetIdx, ax: usize) {
        // DFS 1: bottom-to-top to calculate sizes that depend on children.
        self.calculate_bottom_up_sizes(root, ax, true);

        // DFS 2: top-to-bottom to calculate sizes that depend on parent, and calculate positions.
        let mut stack: Vec<WidgetIdx> = vec![root];
        let mut scratch: Vec<WidgetIdx> = Vec::new();
        while let Some(idx) = stack.pop() {
            self.calculate_children_layout(idx, ax, &mut scratch);

            for &c in &self.tree[idx.0].children {
                stack.push(c);
            }
        }
    }

    // Adds up rel_pos values on the path from ancestor to descendant. All these positions must have been already calculated, e.g. using layout_subtree().
    pub fn relative_position(&self, ancestor: WidgetIdx, mut descendant: WidgetIdx, ax: usize) -> isize {
        let mut res = 0isize;
        while descendant != ancestor {
            assert!(descendant.is_valid(), "relative_position(): ancestor is not an ancestor");
            let w = &self.tree[descendant.0];
            assert!(w.axes[ax].flags.contains(AxisFlags::POS_KNOWN), "relative_position(): layout not calculated");
            res += w.axes[ax].rel_pos;
            descendant = w.parent;
        }
        res
    }

    // Convenience functions.

    // Requests input for cur_parent for next frame, returns input that was requested on previous frame.
    // Multiple such calls for different keys can coexist on the same Widget; each call will return only the actions that it requested.
    pub fn check_keys(&mut self, actions: &[KeyAction]) -> Vec<KeyAction> {
        let w = &mut self.tree[self.cur_parent.0];
        if !w.flags.contains(WidgetFlags::CAPTURE_ALL_KEYS) {
            let req = self.key_binds.normal.actions_to_keys(actions);
            w.capture_keys.extend_from_slice(&req);
        }
        let mut res: Vec<KeyAction> = Vec::new();
        w.keys.retain(|key| {
            match self.key_binds.normal.key_to_action.get(key) {
                Some(a) if actions.iter().position(|x| x == a).is_some() => {
                    res.push(*a);
                    false
                }
                _ => true
            }
        });
        res
    }

    pub fn check_key(&mut self, action: KeyAction) -> bool {
        let keys = match self.key_binds.normal.action_to_keys.get(&action) {
            Some(x) => x,
            None => return false };
        let w = &mut self.tree[self.cur_parent.0];
        if !w.flags.contains(WidgetFlags::CAPTURE_ALL_KEYS) {
            w.capture_keys.extend_from_slice(keys);
        }
        let mut res = false;
        w.keys.retain(|key| {
            match keys.iter().position(|k| k == key) {
                None => true,
                Some(_) => {
                    res = true;
                    false
                }
            }
        });
        res
    }

    pub fn check_mouse(&mut self, e: MouseActions) -> bool {
        let w = &mut self.tree[self.cur_parent.0];
        w.capture_mouse.insert(e);
        w.mouse.contains(e)
    }
    pub fn check_scroll(&mut self) -> isize {
        let w = &mut self.tree[self.cur_parent.0];
        w.capture_mouse.insert(MouseActions::SCROLL);
        w.scroll
    }
    pub fn check_drag_out(&mut self, what: DragWhat) -> Option<[isize; 2]> {
        let w = &mut self.tree[self.cur_parent.0];
        w.capture_mouse.insert(MouseActions::DRAG_OUT);
        w.drag_out_what = what;
        if w.mouse.contains(MouseActions::DRAG_OUT) {
            Some(w.mouse_pos)
        } else {
            None
        }
    }
    pub fn check_drag_in(&mut self) -> Option<(DragWhat, [isize; 2], /*drop*/ bool)> {
        let w = &mut self.tree[self.cur_parent.0];
        w.capture_mouse.insert(MouseActions::DRAG_IN | MouseActions::DROP);
        if w.mouse.contains(MouseActions::DRAG_IN) {
            Some((w.drag_in_what, w.mouse_pos, w.mouse.contains(MouseActions::DROP)))
        } else {
            None
        }
    }

    // If cur_parent owns a dialog, returns a full-screen widget to which to add the dialog as a child.
    // If `create`, the dialog will be created if no dialog exists (neither owned by this widget nor anyone else).
    // If no children are added to the returned widget before the end of the frame, the dialog is considered closed.
    pub fn check_dialog(&mut self, create: bool) -> Option<WidgetIdx> {
        let identity = self.cur().identity;
        match &self.dialog_owner {
            Some(id) if id == &identity => Some(self.dialog_root),
            None if create => {
                self.dialog_owner = Some(identity);
                Some(self.dialog_root)
            }
            _ => None,
        }
    }
    pub fn close_dialog(&mut self) {
        self.dialog_owner = None;
        self.tree[self.dialog_root.0].children.clear();
    }

    // Default behavior for opening/closing tooltip: open on KeyAction::Tooltip, close on Tooltip or Cancel, position next to cur_parent.
    pub fn check_tooltip(&mut self) -> Option<WidgetIdx> {
        let identity = self.cur().identity;
        let pressed = self.check_key(KeyAction::Tooltip);
        match self.tooltip_owner.clone() {
            Some(id) if id != identity => return None, // someone else has a tooltip
            Some(_) if pressed || self.check_key(KeyAction::Cancel) => return None, // closed
            Some(_) => (), // exists
            None if pressed => self.tooltip_owner = Some(identity), // opened
            None => return None,
        }
        let idx = self.cur_parent;
        Some(with_parent!(self, self.tooltip_root, {
            let mut w = widget!().width(AutoSize::Children).height(AutoSize::Children).fill(' ', self.palette.default).hstack();
            w.position_next_to = Some(idx);
            w.style_adjustment = self.palette.tooltip;
            w.draw_frame = Some((self.palette.default_dim, /*rounded*/ false));
            let outer = self.add(w);
            // Margins.
            let mid;
            with_parent!(self, outer, {
                self.add(widget!().fixed_width(1));
                mid = self.add(widget!().width(AutoSize::Children).height(AutoSize::Children).vstack());
                self.add(widget!().fixed_width(1));
            });
            let inner;
            let (width, height) = (self.cur().get_fixed_width(), self.cur().get_fixed_height());
            with_parent!(self, mid, {
                self.add(widget!().fixed_height(1));
                inner = self.add(widget!().width(AutoSize::Children).height(AutoSize::Children).max_width(width.saturating_sub(2)).max_height(height.saturating_sub(2)));
                self.add(widget!().fixed_height(1));
            });
            inner
        }))
    }

    // Checks whether there's a relatively-focused widget with draw_cursor_if_focused set, in the given widget's subtree.
    pub fn subtree_has_cursor(&self, root: WidgetIdx) -> bool {
        let mut stack: Vec<WidgetIdx> = vec![root];
        while let Some(idx) = stack.pop() {
            let w = &self.tree[idx.0];
            if w.draw_cursor_if_focused.is_some() {
                return true;
            }
            for &c in w.focus_children.iter().rev() {
                stack.push(c);
            }
        }
        false
    }

    fn calculate_bottom_up_sizes(&mut self, root: WidgetIdx, ax: usize, all: bool) {
        let mut stack: Vec<(WidgetIdx, /*pass*/ u8)> = vec![(root, 0)];
        while let Some((idx, pass)) = stack.pop() {
            let w = &mut self.tree[idx.0];
            let axis = &mut w.axes[ax];
            
            if pass == 0 && !w.children.is_empty() && (all || (!axis.flags.contains(AxisFlags::SIZE_KNOWN) && axis.auto_size.is_children())) {
                // Visit children first.
                stack.push((idx, 1));
                for &c in &w.children {
                    stack.push((c, 0));
                }
                continue;
            }

            let axis = &w.axes[ax];
            match &axis.auto_size {
                _ if axis.flags.contains(AxisFlags::SIZE_KNOWN) => (),
                AutoSize::Text if ax == Axis::Y && w.flags.contains(WidgetFlags::LINE_WRAP) && !w.axes[Axis::X].flags.contains(AxisFlags::SIZE_KNOWN) => {
                    // Need to know width to calculate height. Try to calculate width. This doesn't cover all cases currently.
                    let mut p_idx = idx;
                    let mut path: Vec<WidgetIdx> = Vec::new();
                    let width;
                    loop {
                        assert!(p_idx.is_valid());
                        let p = &mut self.tree[p_idx.0];
                        if p.axes[Axis::X].flags.contains(AxisFlags::SIZE_KNOWN) {
                            width = p.axes[Axis::X].size;
                            break;
                        }
                        match &p.axes[Axis::X].auto_size {
                            AutoSize::Fixed(_) => {
                                Self::try_calculate_simple_size(p, Axis::X, &mut self.text, &self.palette);
                                width = p.axes[Axis::X].size;
                                break;
                            }
                            AutoSize::Text | AutoSize::Remainder(_) | AutoSize::Children => panic!("widget (line {}) has width {:?}, which is not supported with LINE_WRAP", p.source_line, p.axes[Axis::X].auto_size),
                            AutoSize::Parent => {
                                path.push(p_idx);
                                p_idx = p.parent;
                            }
                        }
                    }
                    for p_idx in path {
                        let ax = &mut self.tree[p_idx.0].axes[Axis::X];
                        ax.size = width;
                        ax.flags.insert(AxisFlags::SIZE_KNOWN);
                    }

                    // Finally calculate height.
                    Self::try_calculate_simple_size(&mut self.tree[idx.0], Axis::Y, &mut self.text, &self.palette);
                }
                AutoSize::Fixed(_) | AutoSize::Text => { Self::try_calculate_simple_size(w, ax, &mut self.text, &self.palette); }
                AutoSize::Parent => assert!(all, "can't calculate widget (line {}) size early because it depends on parent", w.source_line),
                AutoSize::Remainder(_) => assert!(all, "can't calculate widget (line {}) size early because it depends on siblings", w.source_line),
                AutoSize::Children => {
                    let mut size = 0usize;
                    let w = &self.tree[idx.0];
                    for &child_idx in &w.children {
                        let child_axis = &self.tree[child_idx.0].axes[ax];
                        if !child_axis.flags.contains(AxisFlags::SIZE_KNOWN) {
                            continue;
                        }
                        if w.axes[ax].flags.contains(AxisFlags::STACK) {
                            size += child_axis.size;
                        } else {
                            size = size.max(child_axis.size);
                        }
                    }
                    let axis = &mut self.tree[idx.0].axes[ax];
                    axis.size = size.max(axis.min_size).min(axis.max_size);
                    axis.flags.insert(AxisFlags::SIZE_KNOWN);
                }
            }
        }
    }

    fn try_calculate_simple_size(w: &mut Widget, ax: usize, text: &mut StyledText, palette: &Palette) -> bool {
        let size = match w.axes[ax].auto_size {
            AutoSize::Fixed(s) => s,
            AutoSize::Text if ax == Axis::X => text.widest_line(w.draw_text.clone().unwrap()), // text width
            AutoSize::Text if !w.flags.contains(WidgetFlags::LINE_WRAP) => w.draw_text.as_ref().unwrap().len(), // height without line wrap
            AutoSize::Text if w.axes[0].flags.contains(AxisFlags::SIZE_KNOWN) => Self::get_line_wrapped_text(w, text, palette).len(), // height with line wrap
            _ => return false,
        };
        let size = size.max(w.axes[ax].min_size).min(w.axes[ax].max_size);
        w.axes[ax].size = size;
        w.axes[ax].flags.insert(AxisFlags::SIZE_KNOWN);
        true
    }

    fn get_line_wrapped_text(w: &mut Widget, text: &mut StyledText, palette: &Palette) -> Range<usize> {
        match &w.line_wrapped_text {
            Some(x) => x.clone(),
            None => {
                let width = w.axes[Axis::X].size;
                let max_lines = if width == 0 {
                    0
                } else if w.axes[Axis::Y].flags.contains(AxisFlags::SIZE_KNOWN) {
                    w.axes[Axis::Y].size
                } else if w.axes[Axis::Y].max_size != usize::MAX {
                    w.axes[Axis::Y].max_size
                } else {
                    100000
                };
                let r = text.line_wrap(w.draw_text.clone().unwrap(), width, max_lines, &palette.line_wrap_indicator, &palette.truncation_indicator, None);
                w.line_wrapped_text = Some(r.clone());
                r
            }
        }
    }

    fn calculate_children_layout(&mut self, idx: WidgetIdx, ax: usize, scratch: &mut Vec<WidgetIdx>) {
        let w = &self.tree[idx.0];
        let axis = &w.axes[ax];
        let flags = axis.flags;
        let parent_size = axis.size;
        assert!(flags.contains(AxisFlags::SIZE_KNOWN));
        scratch.clear();
        scratch.extend_from_slice(&w.children);

        let mut remainder_helper = RemainderFractionHelper::new(parent_size);

        // Resolve AutoSize::Parent in children, add up final non-Remainder children sizes.
        for &child_idx in &*scratch {
            let child_axis = &mut self.tree[child_idx.0].axes[ax];

            if !child_axis.flags.contains(AxisFlags::SIZE_KNOWN) {
                match &child_axis.auto_size {
                    AutoSize::Parent => { child_axis.size = parent_size.max(child_axis.min_size).min(child_axis.max_size); child_axis.flags.insert(AxisFlags::SIZE_KNOWN); }
                    AutoSize::Remainder(f) if !flags.contains(AxisFlags::STACK) => { child_axis.size = ((parent_size as f64 * f.max(0.0) + 0.5) as usize).max(child_axis.min_size).min(child_axis.max_size); child_axis.flags.insert(AxisFlags::SIZE_KNOWN); }
                    AutoSize::Remainder(f) => remainder_helper.declare_remainder_fraction(*f, child_idx.0),
                    AutoSize::Children | AutoSize::Fixed(_) | AutoSize::Text => panic!("size {:?} was supposed to be resolved by now", child_axis.auto_size),
                }
            }
            if child_axis.flags.contains(AxisFlags::SIZE_KNOWN) { // (no, this can't be an `else`)
                remainder_helper.declare_fixed_part(child_axis.size);
            }
        }

        // Calculate Remainder sizes and all positions.
        let mut position = 0isize;
        for &child_idx in &*scratch {
            let child = &mut self.tree[child_idx.0];
            let child_axis = &mut child.axes[ax];
            if !child_axis.flags.contains(AxisFlags::SIZE_KNOWN) {
                let f = match &child_axis.auto_size {
                    AutoSize::Remainder(f) => f,
                    _ => panic!("huh"),
                };
                child_axis.size = remainder_helper.calculate_remainder_fraction(*f, child_idx.0).max(child_axis.min_size).min(child_axis.max_size);
                child_axis.flags.insert(AxisFlags::SIZE_KNOWN);
            }
            if !child_axis.flags.contains(AxisFlags::POS_KNOWN) {
                if child_axis.flags.contains(AxisFlags::CENTER) {
                    child_axis.rel_pos = (parent_size as isize - child_axis.size as isize) / 2;
                } else {
                    child_axis.rel_pos = position;
                }
                child_axis.flags.insert(AxisFlags::POS_KNOWN);
            }
            if flags.contains(AxisFlags::STACK) {
                position = child_axis.rel_pos + child_axis.size as isize;
            }
        }
    }

    fn render(&mut self, screen: &mut ScreenBuffer) {
        let mut stack: Vec<(WidgetIdx, /*pos*/ [isize; 2], /*clip*/ Rect, StyleAdjustment)> = vec![(self.root, [0, 0], screen.rect(), StyleAdjustment::default())];
        let mut should_redraw = false;
        let mut should_show_cursor: Option<[isize; 2]> = None;
        while let Some((idx, pos, clip, mut style_adjustment)) = stack.pop() {
            let w = &self.tree[idx.0];
            let mut pos = [pos[0] + w.axes[0].rel_pos, pos[1] + w.axes[1].rel_pos];

            if let Some(other_idx) = w.position_next_to.clone() {
                let root = &self.tree[self.root.0];
                let other = &self.tree[other_idx.0];
                // Candidate sides relative to other: up, left, bottom, right.
                let scores = [other.axes[1].abs_pos - w.axes[1].size as isize, other.axes[0].abs_pos - w.axes[0].size as isize,
                              root.axes[1].size as isize - other.axes[1].abs_pos - other.axes[1].size as isize - w.axes[1].size as isize,
                              root.axes[0].size as isize - other.axes[0].abs_pos - other.axes[0].size as isize - w.axes[0].size as isize];
                let which = scores.iter().enumerate().max_by_key(|(_, s)| *s).unwrap().0;
                pos = [other.axes[0].abs_pos + other.axes[0].size as isize / 2 - w.axes[0].size as isize / 2,
                       other.axes[1].abs_pos + other.axes[1].size as isize / 2 - w.axes[1].size as isize / 2];
                match which {
                    0 => pos[1] = other.axes[1].abs_pos - w.axes[1].size as isize,
                    1 => pos[0] = other.axes[0].abs_pos - w.axes[0].size as isize,
                    2 => pos[1] = other.axes[1].abs_pos + other.axes[1].size as isize,
                    3 => pos[0] = other.axes[0].abs_pos + other.axes[0].size as isize,
                    _ => panic!("huh"),
                }
                pos[0] = pos[0].min(root.axes[0].size as isize - w.axes[0].size as isize).max(0);
                pos[1] = pos[1].min(root.axes[1].size as isize - w.axes[1].size as isize).max(0);
            }

            let mut draw_text = w.draw_text.clone();
            let mut show_horizontal_text_truncation_indicator = !w.flags.contains(WidgetFlags::TEXT_TRUNCATION_INDICATOR_DISABLE);
            let mut show_vertical_text_truncation_indicator = !w.flags.contains(WidgetFlags::TEXT_TRUNCATION_INDICATOR_DISABLE);

            let w = &mut self.tree[idx.0];
            w.axes[0].abs_pos = pos[0];
            w.axes[1].abs_pos = pos[1];

            let rect = Rect {pos: pos.clone(), size: [w.axes[0].size, w.axes[1].size]};
            let mut clip = clip.intersection(rect);

            if draw_text.is_some() && w.flags.contains(WidgetFlags::LINE_WRAP) {
                if clip.is_empty() {
                    draw_text = None;
                } else {
                    draw_text = Some(Self::get_line_wrapped_text(w, &mut self.text, &self.palette));
                }
                show_horizontal_text_truncation_indicator = false;
                show_vertical_text_truncation_indicator = false;
            }
            if w.flags.contains(WidgetFlags::HIGHLIGHT_ON_HOVER) {
                w.capture_mouse.insert(MouseActions::HOVER_SUBTREE);
            }

            let w = &self.tree[idx.0];

            if w.flags.contains(WidgetFlags::RESET_STYLE_ADJUSTMENT) {
                style_adjustment = StyleAdjustment::default();
            }
            style_adjustment.update(w.style_adjustment);
            if w.flags.contains(WidgetFlags::HIGHLIGHT_ON_HOVER) && w.mouse.contains(MouseActions::HOVER_SUBTREE) {
                style_adjustment.update(self.palette.hovered);
            }

            if w.flags.contains(WidgetFlags::REDRAW_IF_VISIBLE) && !clip.is_empty() {
                should_redraw = true;

                if let Some((c, style)) = self.palette.placeholder_fill.clone() {
                    let mut buf = [0u8; 4];
                    screen.fill(clip, c.encode_utf8(&mut buf), style);
                }
            }

            if w.flags.contains(WidgetFlags::HSCROLL_INDICATOR_LEFT) {
                show_horizontal_text_truncation_indicator = false;
                if clip.x() > rect.x() && clip.width() > 0 {
                    for y in clip.y()..clip.bottom() {
                        screen.put_text(&self.palette.hscroll_indicator.0, style_adjustment.apply(self.palette.hscroll_indicator.2), clip.x(), y, clip);
                    }
                    let wid = str_width(&self.palette.hscroll_indicator.0).min(clip.width());
                    clip.pos[0] += wid as isize;
                    clip.size[0] -= wid;
                }
            }
            if w.flags.contains(WidgetFlags::HSCROLL_INDICATOR_RIGHT) {
                show_horizontal_text_truncation_indicator = false;
                if rect.right() > clip.right() && clip.width() > 0 {
                    let wid = str_width(&self.palette.hscroll_indicator.1);
                    let mut new_clip = clip;
                    new_clip.size[0] = new_clip.size[0].saturating_sub(wid);
                    for y in clip.y_range() {
                        if let Some(lines) = &w.draw_text {
                            let mut i = (y - rect.y()) as usize;
                            if w.flags.contains(WidgetFlags::REPEAT_TEXT_VERTICALLY) && !lines.is_empty() {
                                i %= lines.len();
                            }
                            let line_idx = lines.start + i;
                            let line_width = if line_idx < lines.end {str_width(self.text.get_line_str(line_idx))} else {0};
                            if rect.x() + line_width as isize <= new_clip.right() {
                                continue;
                            }
                        }
                        screen.put_text(&self.palette.hscroll_indicator.1, style_adjustment.apply(self.palette.hscroll_indicator.2), clip.right() - wid as isize, y, clip);
                    }
                    clip = new_clip;
                }
            }

            if let Some((c, style)) = w.draw_fill.clone() {
                let mut buf = [0u8; 4];
                screen.fill(clip, c.encode_utf8(&mut buf), style_adjustment.apply(style));
            }

            let mut text_x_offset = 0;
            if let Some((style, rounded)) = w.draw_frame.clone() {
                let style = style_adjustment.apply(style);
                screen.fill(Rect {pos: rect.pos, size: [1, 1]}, if rounded {"╭"} else {"┌"}, style);
                screen.fill(Rect {pos: [rect.x() + 1, rect.y()], size: [rect.width().saturating_sub(2), 1]}, "─", style);
                screen.fill(Rect {pos: [rect.right() - 1, rect.y()], size: [1, 1]}, if rounded {"╮"} else {"┐"}, style);
                screen.fill(Rect {pos: [rect.x(), rect.y() + 1], size: [1, rect.height().saturating_sub(2)]}, "│", style);
                screen.fill(Rect {pos: [rect.right() - 1, rect.y() + 1], size: [1, rect.height().saturating_sub(2)]}, "│", style);
                screen.fill(Rect {pos: [rect.x(), rect.bottom() - 1], size: [1, 1]}, if rounded {"╰"} else {"└"}, style);
                screen.fill(Rect {pos: [rect.x() + 1, rect.bottom() - 1], size: [rect.width().saturating_sub(2), 1]}, "─", style);
                screen.fill(Rect {pos: [rect.right() - 1, rect.bottom() - 1], size: [1, 1]}, if rounded {"╯"} else {"┘"}, style);
                text_x_offset = 1;
            }

            if let &Some((progress, style)) = &w.draw_progress_bar {
                let text = match &draw_text {
                    Some(r) if !r.is_empty() => self.text.get_line_str(r.start),
                    _ => "",
                };
                let text_x = rect.x() + (rect.width() as isize - str_width(text) as isize) / 2;

                let filled = (rect.width() as f64 * progress.min(1.0).max(0.0) + 0.5) as usize;
                let left_rect = clip.intersection(Rect {pos: rect.pos, size: [filled, 1]});
                let right_rect = clip.intersection(Rect {pos: [rect.x() + filled as isize, rect.y()], size: [rect.width() - filled, 1]});

                let right_style = style_adjustment.apply(style);
                let left_style = right_style.flip();
                screen.fill(left_rect, " ", left_style);
                screen.fill(right_rect, " ", right_style);
                screen.put_text(text, left_style, text_x, rect.y(), left_rect);
                screen.put_text(text, right_style, text_x, rect.y(), right_rect);
                draw_text = None;
            }

            if let Some(text_range) = draw_text {
                for y in clip.y_range() {
                    let mut indicate_vertical_truncation = show_vertical_text_truncation_indicator && y + 1 == rect.bottom();
                    let mut indicate_horizontal_truncation = show_horizontal_text_truncation_indicator;

                    let mut i = (y - rect.y()) as usize;
                    if w.flags.contains(WidgetFlags::REPEAT_TEXT_VERTICALLY) && !text_range.is_empty() {
                        i %= text_range.len();
                        indicate_vertical_truncation = false;
                    } else if i >= text_range.len() {
                        break;
                    } else {
                        indicate_vertical_truncation &= i + 1 < text_range.len();
                    }
                    let line_idx = text_range.start + i;

                    let mut spans = self.text.get_line(line_idx);
                    let line_str = self.text.get_line_str(line_idx);
                    let mut x = rect.x() + text_x_offset as isize;

                    if x + str_width(line_str) as isize <= rect.right() {
                        indicate_horizontal_truncation = false;
                    } else if w.flags.contains(WidgetFlags::TEXT_TRUNCATION_ALIGN_RIGHT) {
                        if indicate_horizontal_truncation {
                            x = screen.put_text(&self.palette.truncation_indicator.0, style_adjustment.apply(self.palette.truncation_indicator.2), x, y, clip);
                        }
                        let lim = (rect.right() - x).max(0) as usize;

                        let (mut skip, truncated_width) = str_suffix_with_width(line_str, lim);
                        x += (lim - truncated_width) as isize; // in case a wide character is half-truncated

                        // Find and print the partially truncated span.
                        while !spans.is_empty() {
                            let (s, style) = self.text.get_span(spans.start);
                            spans.start += 1;
                            if s.len() <= skip {
                                skip -= s.len();
                                continue;
                            }
                            x = screen.put_text(&s[skip..], style_adjustment.apply(style), x, y, clip);
                            break;
                        }
                        // Print the rest of the spans the normal way.
                        indicate_horizontal_truncation = false;
                    }

                    for span_idx in spans {
                        let (s, style) = self.text.get_span(span_idx);
                        x = screen.put_text(s, style_adjustment.apply(style), x, y, clip);
                        if x > clip.right() {
                            break;
                        }
                    }
                    if (indicate_vertical_truncation || indicate_horizontal_truncation) && rect.width() > 0 {
                        screen.put_text(&self.palette.truncation_indicator.1, style_adjustment.apply(self.palette.truncation_indicator.2), rect.right() - str_width(&self.palette.truncation_indicator.1) as isize, y, clip);
                    }
                }
            }

            if let Some(term) = &w.draw_terminal {
                let vt_screen = term.vt.screen();
                for y in clip.y_range() {
                    let ty = y - rect.y();
                    if ty > u16::MAX as isize {
                        break;
                    }
                    for x in clip.x_range() {
                        let tx = x - rect.x();
                        if tx > u16::MAX as isize {
                            break;
                        }
                        let mut contents = " ";
                        let mut width = 1;
                        let mut style = Style::default();
                        match vt_screen.cell(ty as u16, tx as u16) {
                            None => style = Style {fg: Color::TerminalDefault, bg: Color::TerminalDefault, modifier: Modifier::empty()},
                            Some(cell) => {
                                if cell.has_contents() {
                                    contents = cell.contents();
                                }
                                if cell.is_wide() {
                                    width = 2;
                                }

                                let convert_color = |c: vt100::Color| -> Color {
                                    match c {
                                        vt100::Color::Default => Color::TerminalDefault,
                                        vt100::Color::Rgb(r, g, b) => Color::Rgb(r, g, b),
                                        vt100::Color::Idx(i) => {
                                            if i < 8 {
                                                Color::Palette8(i)
                                            } else if i < 16 {
                                                Color::Palette8Bright(i - 8)
                                            } else {
                                                Color::Palette256(i)
                                            }
                                        }
                                    }
                                };
                                style.fg = convert_color(cell.fgcolor());
                                style.bg = convert_color(cell.bgcolor());

                                if cell.bold() {
                                    style.modifier.insert(Modifier::BOLD);
                                }
                                if cell.dim() {
                                    style.modifier.insert(Modifier::DIM);
                                }
                                if cell.italic() {
                                    style.modifier.insert(Modifier::ITALIC);
                                }
                                if cell.underline() {
                                    style.modifier.insert(Modifier::UNDERLINED);
                                }
                                if cell.inverse() {
                                    style.modifier.insert(Modifier::INVERT);
                                }
                            }
                        }
                        screen.put_cell(contents, width, style, x, y);
                    }
                }
            }

            if let &Some(p) = &w.draw_cursor_if_focused {
                let p = [rect.pos[0] + p[0], rect.pos[1] + p[1]];
                if w.focus_frame_idx == self.frame_idx + 1 && p[0] >= clip.pos[0] && p[1] >= clip.pos[1] && p[0] <= clip.right() && p[1] < clip.bottom() { // can't use clip.contains(p) because of the `<=` on this line (because we use bar cursor rather than block cursor)
                    should_show_cursor = Some(p);
                }
            }

            for &c in w.children.iter().rev() {
                stack.push((c, pos, clip, style_adjustment.clone()));
            }
        }
        self.should_redraw |= should_redraw;
        self.should_show_cursor = should_show_cursor;
    }

    fn determine_focus_chain(&mut self) {
        self.prev_focus_chain.clear();
        let mut stack: Vec<(WidgetIdx, /*pass*/ u8)> = vec![(self.root, 0)];
        while let Some((idx, pass)) = stack.pop() {
            let w = &mut self.tree[idx.0];
            if pass == 1 || w.focus_children.is_empty() {
                self.prev_focus_chain.push(idx);
                if w.focus_frame_idx < self.frame_idx && w.flags.contains(WidgetFlags::REDRAW_IF_FOCUS_CHANGES) {
                    self.should_redraw = true;
                }
                w.focus_frame_idx = self.frame_idx + 1;
                continue;
            }
            stack.push((idx, 1));
            for &c in w.focus_children.iter().rev() {
                stack.push((c, 0));
            }
        }
        for w in &self.tree {
            if w.flags.contains(WidgetFlags::REDRAW_IF_FOCUS_CHANGES) && w.focus_frame_idx == self.frame_idx {
                self.should_redraw = true;
            }
        }
    }
    
    fn dispatch_input(&mut self) {
        if self.prev_tree.is_empty() {
            return;
        }

        let mut keys = mem::take(&mut self.input_buffer);
        for &idx in &self.prev_focus_chain {
            if keys.is_empty() {
                break;
            }
            let w = &mut self.prev_tree[idx.0];
            let invert = w.flags.contains(WidgetFlags::CAPTURE_ALL_KEYS);
            let text_input = w.flags.contains(WidgetFlags::CAPTURE_TEXT_INPUT_KEYS);
            if !w.capture_keys.is_empty() || text_input || invert {
                keys.retain(|key| {
                    let mut matches = (text_input && key.mods.is_empty() && key.key.is_ordinary_char()) || w.capture_keys.iter().find(|k| k.key == key.key && (k.mods.contains(ModKeys::ANY) || k.mods == key.mods)).is_some();
                    if invert {
                        matches = !matches;
                    }
                    if matches {
                        w.keys.push(key.clone());
                        false
                    } else {
                        true
                    }
                });
            }
        }

        let report_event = |w: &mut Widget, ev: MouseActions, pos: [isize; 2]| {
            w.mouse.insert(ev);
            w.mouse_pos = [pos[0] - w.axes[0].abs_pos, pos[1] - w.axes[1].abs_pos];
        };
        let hovered_idx = self.find_widget_at_cursor(self.mouse_pos);
        let mut scroll = mem::take(&mut self.mouse_scroll);

        // Dispatch middle click and right click.
        for (mouse_action, click_pos) in [(MouseActions::MIDDLE_CLICK, mem::take(&mut self.mouse_middle_click)), (MouseActions::RIGHT_CLICK, mem::take(&mut self.mouse_right_click))] {
            if let Some(click_pos) = click_pos {
                let mut idx = if click_pos == self.mouse_pos {
                    hovered_idx
                } else {
                    self.find_widget_at_cursor(click_pos)
                };
                while idx.is_valid() {
                    let w = &mut self.prev_tree[idx.0];
                    if w.capture_mouse.contains(mouse_action) {
                        report_event(w, mouse_action, click_pos);
                        break;
                    }
                    idx = w.parent;
                }
            }
        }
        
        // Dispatch click, which may also start a drag.
        if let Some(click_pos) = mem::take(&mut self.mouse_click) {
            self.mouse_drag_out_widget = None;
            let mut idx = if click_pos == self.mouse_pos {
                hovered_idx
            } else {
                self.find_widget_at_cursor(click_pos)
            };
            let mut dispatched = false;
            while idx.is_valid() {
                let w = &mut self.prev_tree[idx.0];
                if !dispatched {
                    if w.capture_mouse.contains(MouseActions::CLICK) {
                        report_event(w, MouseActions::CLICK, click_pos);
                        dispatched = true;
                    }
                    if w.capture_mouse.contains(MouseActions::DRAG_OUT) {
                        self.mouse_drag_out_widget = Some(w.identity);
                        dispatched = true;
                    }
                }
                if w.capture_mouse.contains(MouseActions::CLICK_SUBTREE) {
                    report_event(w, MouseActions::CLICK_SUBTREE, click_pos);
                }
                idx = w.parent;
            }
        }

        // Dispatch DRAG_OUT, DRAG_IN, and DROP.
        if let Some(identity) = mem::take(&mut self.mouse_drag_out_widget) {
            if let Some(idx) = self.prev_map.get(&identity) {
                let out_w = &mut self.prev_tree[idx.0];
                if out_w.capture_mouse.contains(MouseActions::DRAG_OUT) {
                    report_event(out_w, MouseActions::DRAG_OUT, self.mouse_pos);

                    // Scroll in the correct widget when dragging a scroll bar.
                    if out_w.capture_mouse.contains(MouseActions::SCROLL) {
                        report_event(out_w, MouseActions::SCROLL, self.mouse_pos);
                        out_w.scroll = mem::take(&mut scroll);
                    }

                    if self.mouse_drop_pos.is_none() {
                        // Keep dragging.
                        self.mouse_drag_out_widget = Some(identity);
                    }

                    let what = out_w.drag_out_what;
                    if what != DragWhat::NoDrop {
                        // DRAG_IN and DROP.
                        let in_pos = self.mouse_drop_pos.clone().unwrap_or(self.mouse_pos.clone());
                        let mut in_idx = if in_pos == self.mouse_pos {
                            hovered_idx
                        } else {
                            self.find_widget_at_cursor(in_pos)
                        };

                        while in_idx.is_valid() {
                            let in_w = &mut self.prev_tree[in_idx.0];
                            if in_w.capture_mouse.contains(MouseActions::DRAG_IN) {
                                in_w.drag_in_what = what;
                                report_event(in_w, MouseActions::DRAG_IN, in_pos);

                                if self.mouse_drop_pos.is_some() {
                                    report_event(in_w, MouseActions::DROP, in_pos);
                                }

                                // This may become a problem: maybe under the cursor there are multiple widgets with DRAG_IN,
                                // but only one of them is interested in this DragWhat. We may have to add something like
                                // a bitmask in DragWhat to determine which DRAG_IN widgets are interested in which DragWhat values.
                                break;
                            }

                            in_idx = in_w.parent;
                        }
                    }
                }
            }
        }
        self.mouse_drop_pos = None;

        let mut hover = self.mouse_drag_out_widget.is_none();
        let mut idx = hovered_idx;
        while idx.is_valid() {
            let w = &mut self.prev_tree[idx.0];
            if hover && w.capture_mouse.contains(MouseActions::HOVER) {
                report_event(w, MouseActions::HOVER, self.mouse_pos);
                hover = false;
            }
            if self.mouse_drag_out_widget.is_none() && w.capture_mouse.contains(MouseActions::HOVER_SUBTREE) {
                report_event(w, MouseActions::HOVER_SUBTREE, self.mouse_pos);
            }
            if scroll != 0 && w.capture_mouse.contains(MouseActions::SCROLL) {
                report_event(w, MouseActions::SCROLL, self.mouse_pos);
                w.scroll = mem::take(&mut scroll);
            }
            idx = w.parent;
        }
    }

    fn find_widget_at_cursor(&self, cursor: [isize; 2]) -> WidgetIdx {
        let mut stack: Vec<WidgetIdx> = vec![self.prev_root];
        let mut res = WidgetIdx::invalid();
        // DFS in the same order in which we render, and take the last interactable widget under the cursor.
        while let Some(idx) = stack.pop() {
            let w = &self.prev_tree[idx.0];
            if cursor[0] < w.axes[0].abs_pos || cursor[1] < w.axes[1].abs_pos || cursor[0] >= w.axes[0].abs_pos + w.axes[0].size as isize || cursor[1] >= w.axes[1].abs_pos + w.axes[1].size as isize {
                continue;
            }
            // When should a later overlapping widget obstruct mouse interactions? E.g. should clicks on the tooltip be ignored or dispatched as if the tooltip is not there?
            // Currently the answer is: dispatched as if the tooltip is not there (as long as the tooltip has empty capture_mouse).
            if !w.capture_mouse.is_empty() {
                res = idx;
            }
            for &c in w.children.iter().rev() {
                stack.push(c);
            }
        }
        res
    }
}

// Utility for calculating AutoSize::Remainder(fraction) sizes.
pub struct RemainderFractionHelper {
    size_total: usize,
    fraction_total: f64,
    size_allocated: usize,
    fraction_allocated: f64,
    last_remainder_idx: usize,
}
impl RemainderFractionHelper {
    pub fn new(size_total: usize) -> Self { Self {size_total, fraction_total: 0.0, size_allocated: 0, fraction_allocated: 0.0, last_remainder_idx: 0} }
    pub fn declare_fixed_part(&mut self, size: usize) {
        self.size_total = self.size_total.saturating_sub(size);
    }
    pub fn declare_remainder_fraction(&mut self, fraction: f64, idx: usize) {
        self.fraction_total += fraction.max(0.0);
        self.last_remainder_idx = idx;
    }
    pub fn calculate_remainder_fraction(&mut self, fraction: f64, idx: usize) -> usize {
        self.fraction_allocated += fraction.max(0.0);
        let fraction_total = if self.fraction_total == 0.0 {1.0} else {self.fraction_total};
        let mut s = (self.size_total as f64 * self.fraction_allocated / fraction_total + 0.5) as usize;
        if idx == self.last_remainder_idx {
            s = self.size_total;
        }
        s = s.max(self.size_allocated).min(self.size_total);
        s - mem::replace(&mut self.size_allocated, s)
    }
}
