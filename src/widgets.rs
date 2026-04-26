use crate::{*, search::*, pool::*, symbols_registry::*, util::*, error::*, procfs::*, settings::*, context::*, imgui::*, common_ui::*, terminal::*};
use std::{io, ops::Range, sync::Arc, fmt::Write as fmtWrite, mem, collections::HashSet};

// React to keys like up/down/pageup/pagedown/home/end by moving `cursor`, within range [0, count).
// `cur_parent` is the "viewport" widget; its height should be known (for handling PageUp/PageDown keys); it needs to be focused for the input to work.
// `row_height` is used for PageUp/PageDown jump size.
// Returns true iff any relevant keys were pressed, even if it didn't move the cursor (e.g. trying to move up when already at the top) - useful as a trigger to scroll the view to the cursor.
pub fn list_cursor_navigation(cursor: &mut usize, count: usize, row_height: usize, ui: &mut UI) -> bool {
    list_cursor_navigation_with_variable_row_height(cursor, count, |_, _| row_height, ui)
}

pub fn list_cursor_navigation_with_variable_row_height<F: FnMut(usize, &mut UI) -> usize>(cursor: &mut usize, count: usize, mut row_height_fn: F, ui: &mut UI) -> bool {
    assert!(ui.cur().axes[Axis::Y].flags.contains(AxisFlags::SIZE_KNOWN));
    let viewport_height = ui.cur().axes[Axis::Y].size;
    let actions = ui.check_keys(&[KeyAction::CursorUp, KeyAction::CursorDown, KeyAction::PageUp, KeyAction::PageDown, KeyAction::Home, KeyAction::End]);
    let moved = !actions.is_empty();
    if count == 0 {
        *cursor = 0;
        return moved;
    }
    for action in actions {
        match action {
            KeyAction::CursorUp => *cursor = cursor.saturating_sub(1),
            KeyAction::CursorDown => *cursor += 1,
            KeyAction::PageDown => {
                // Take current row's top y coordinate, add viewport height, find the row that covers that y coordinate.
                let mut offset = viewport_height.saturating_sub(2);
                let mut i = (*cursor).min(count - 1);
                while i + 1 < count {
                    let h = row_height_fn(i, ui);
                    if h > offset {
                        if i == *cursor {
                            i += 1;
                        }
                        break;
                    }
                    offset -= h;
                    i += 1;
                }
                *cursor = i;
            }
            KeyAction::PageUp => {
                let mut offset = viewport_height.saturating_sub(2);
                let mut i = (*cursor).min(count - 1);
                while i > 0 {
                    let h = row_height_fn(i - 1, ui);
                    if h > offset {
                        if i == *cursor {
                            i -= 1;
                        }
                        break;
                    }
                    offset -= h;
                    i -= 1;
                }
                *cursor = i;
            }
            KeyAction::Home => *cursor = 0,
            KeyAction::End => *cursor = count - 1,
            _ => (),
        }
    }
    *cursor = (*cursor).min(count - 1);
    moved
}

// Manages a vertically scrollable area. Widgets involved:
//  * `ui.cur_parent` - the viewport
//  * `ui.cur_parent`'s only child - content, moved vertically according to scroll position
//  * `container` - respond to scroll wheel when the mouse is over this widget (usually an ancestor of the viewport that also includes things like scroll bar and table header)
//  * `scroll_bar` - tall widget of width 1 to the right of the viewport; should be initially empty, populated by this function; pass WidgetIdx::invalid() to disable
// If `scroll_to` is set, we'll scroll to the nearest position such that this range of y coordinates is visible (or as much as possible is visible, if it's taller than the viewport).
// Doesn't react to arrow keys, pageup/pagedown, home/end etc - the caller usually uses these to move the cursor instead of scrolling; use cursorless_scrolling_navigation to make these keys scroll the view.
// Returns the visible range of y coordinates.
pub fn scrolling_navigation(scroll: &mut isize, scroll_to: Option<Range<isize>>, container: WidgetIdx, scroll_bar: WidgetIdx, ui: &mut UI) -> Range<isize> {
    with_parent!(ui, container, {
        *scroll += ui.check_scroll() * ui.key_binds.vscroll_sensitivity;
    });

    let viewport_height = ui.calculate_size(ui.cur_parent, Axis::Y);
    let w = ui.cur();
    assert_eq!(w.children.len(), 1);
    let content_height = ui.calculate_size(w.children[0], Axis::Y);

    if let Some(r) = scroll_to {
        scroll_to_range(scroll, r, viewport_height);
    }

    *scroll = (*scroll).min(content_height as isize - viewport_height as isize).max(0);

    // Handle scroll bar.
    // ┳  ╷  ╷
    // ╇  ╈  │
    // │  ╇  ╈
    // ╵  ╵  ┻
    // TODO: Do rounding/biases such that the bar is placed in the top/bottom position only if the scroll position is exactly at the top/bottom.
    //       E.g. if we're scrolled one line away from the bottom of the content, it would be helpful for the scroll bar to indicate that,
    //       even if the content is long enough that one line of content corresponds to much less than one unit of scroll bar position.
    //       Similarly, make scroll bar always at least 2 units shorter than the available space, to distinguish at least among: top, bottom, neither.
    if scroll_bar.is_valid() && content_height > viewport_height {
        with_parent!(ui, scroll_bar, {
            let bar_height = ui.calculate_size(scroll_bar, Axis::Y).saturating_sub(1); // -1 because top and bottom half-characters are empty
            ui.cur_mut().flags.insert(WidgetFlags::HIGHLIGHT_ON_HOVER);
            if bar_height >= 3 {
                // Rounded down because we want non-full scrollbar when the content is just slightly taller than viewport.
                let slider_height = (bar_height * viewport_height / content_height).max(2);
                assert!(slider_height < bar_height);

                // Set slider position from scroll position.
                let scroll_range = (content_height - viewport_height) as isize; // 0 <= *scroll <= scroll_range
                let slider_range = (bar_height - slider_height) as isize; // 0 <= slider_y <= slider_range
                let mut slider_y = (slider_range * *scroll + scroll_range/2) / scroll_range;
                assert!(slider_y >= 0 && slider_y <= slider_range);

                let clicked = ui.check_mouse(MouseActions::CLICK);
                if let Some([_, y]) = ui.check_drag_out(DragWhat::NoDrop) {
                    let a = ui.palette.selected;
                    let w = ui.cur_mut();
                    w.style_adjustment.update(a);

                    let mid = slider_height as isize / 2;
                    if clicked {
                        // Started dragging, save the cursor offset from slider center.
                        w.scroll_bar_drag_offset = if y >= slider_y && y <= slider_y + slider_height as isize {
                            y - slider_y - mid
                        } else {
                            0
                        };
                    }
                    // Move the slider to the cursor.
                    slider_y = (y - w.scroll_bar_drag_offset - mid).min(slider_range).max(0);
                    // Set scroll position from slider position. Make sure min/max slider positions correspond to min/max scroll positions.
                    *scroll = (slider_y * scroll_range + slider_range/2) / slider_range;
                    assert!(*scroll >= 0 && *scroll <= scroll_range);
                }

                let start = ui.text.num_lines();
                for i in 0..bar_height + 1 {
                    if i == 0 && slider_y == 0 {
                        styled_write!(ui.text, ui.palette.scroll_bar_slider, "┳");
                    } else if i == 0 {
                        styled_write!(ui.text, ui.palette.scroll_bar_background, "╷");
                    } else if i as isize == slider_y {
                        styled_write!(ui.text, ui.palette.scroll_bar_slider, "╈");
                    } else if i == bar_height && slider_y == slider_range {
                        styled_write!(ui.text, ui.palette.scroll_bar_slider, "┻");
                    } else if i == bar_height {
                        styled_write!(ui.text, ui.palette.scroll_bar_background, "╵");
                    } else if i as isize == slider_y + slider_height as isize {
                        styled_write!(ui.text, ui.palette.scroll_bar_slider, "╇");
                    } else if i as isize > slider_y && (i as isize) < slider_y + slider_height as isize {
                        styled_write!(ui.text, ui.palette.scroll_bar_slider, "┃");
                    } else {
                        styled_write!(ui.text, ui.palette.scroll_bar_slider, "│");
                    }
                    ui.text.close_line();
                }
                ui.cur_mut().draw_text = Some(start..ui.text.num_lines());
            }
        });
    }
    if scroll_bar.is_valid() {
        let s = ui.palette.default;
        let w = ui.get_mut(scroll_bar);
        if w.draw_text.is_none() {
            w.draw_fill = Some((' ', s));
        }
    }

    let idx = ui.cur().children[0];
    let w = ui.get_mut(idx);
    w.axes[Axis::Y].flags.insert(AxisFlags::POS_KNOWN);
    w.axes[Axis::Y].rel_pos = -*scroll;

    *scroll..*scroll+viewport_height as isize
}

pub fn scroll_to_range(scroll: &mut isize, r: Range<isize>, viewport: usize) {
    if r.end - r.start > viewport as isize {
        *scroll = (*scroll).max(r.start).min(r.end - viewport as isize);
    } else {
        let margin = (viewport as isize / 4).min(5).min((viewport as isize - r.end + r.start) / 2);
        *scroll = (*scroll).max(r.end - viewport as isize + margin).min(r.start - margin);
    }
}

// Simple horizontal scrolling on left/right arrow keys.
pub fn hscrolling_navigation(hscroll: &mut isize, ui: &mut UI) {
    let w = ui.cur();
    assert_eq!(w.children.len(), 1, "scrollable viewport must have exactly one child (line {})", w.source_line);
    assert!(w.axes[Axis::X].flags.contains(AxisFlags::SIZE_KNOWN), "scrollable viewport width must be calculated in advance (line {})", w.source_line);
    let viewport_width = w.axes[Axis::X].size;
    let content_width = ui.calculate_size(w.children[0], Axis::X);

    // Scroll by viewport width-2 with each key press, the 2 to fit the HSCROLL_INDICATOR_*.
    let step = viewport_width.saturating_sub(2).max(1) as isize;
    for action in ui.check_keys(&[KeyAction::CursorLeft, KeyAction::CursorRight]) {
        match action {
            KeyAction::CursorLeft => *hscroll = hscroll.saturating_sub(step),
            KeyAction::CursorRight => *hscroll += step,
            _ => panic!("huh"),
        }
    }
    *hscroll = (*hscroll).min(content_width as isize - viewport_width as isize).max(0);

    let idx = ui.cur().children[0];
    let w = ui.get_mut(idx);
    w.axes[Axis::X].flags.insert(AxisFlags::POS_KNOWN);
    w.axes[Axis::X].rel_pos = -*hscroll;
}

// Like list_cursor_navigation() + scrolling_navigation(), but the up/down/pageup/pagedown/etc keys scroll the view instead of moving the cursor.
pub fn cursorless_scrolling_navigation(scroll: &mut isize, scroll_to: Option<Range<isize>>, container: WidgetIdx, scroll_bar: WidgetIdx, ui: &mut UI) -> Range<isize> {
    let viewport_height = ui.calculate_size(ui.cur_parent, Axis::Y);
    let w = ui.cur();
    assert_eq!(w.children.len(), 1);
    let content_height = ui.calculate_size(w.children[0], Axis::Y);
    if content_height > viewport_height {
        // Pretend there's a cursor glued to the top of the viewport.
        let mut uscroll = *scroll as usize;
        list_cursor_navigation(&mut uscroll, content_height - viewport_height + 1, 1, ui);
        *scroll = uscroll as isize;
    }
    scrolling_navigation(scroll, None, container, scroll_bar, ui)
}

#[derive(Default)]
pub struct Column {
    pub title: &'static str,
    pub auto_width: AutoSize, // Fixed, Text, Children, Remainder are supported
    pub sortable: bool,
    pub hidden: bool, // only visible in tooltip
    width: usize,
    pos: isize,
}
impl Column {
    pub fn new(title: &'static str, auto_width: AutoSize, sortable: bool) -> Self { Self {auto_width, title, sortable, width: str_width(title) + sortable as usize, pos: 0, hidden: false} }
    pub fn hide(mut self) -> Self { self.hidden = true; self }
    pub fn with_hidden(mut self, hidden: bool) -> Self { self.hidden = hidden; self }
}

#[derive(Default, Clone)]
pub struct TableState {
    pub cursor: usize,
    pub scroll: isize,
    pub scroll_to_cursor: bool,
    pub did_scroll_to_cursor: bool, // whether the latest finish() had a reason to auto-scroll (because of keyboard input or mouse click or because scroll_to_cursor was set from outside).
    pub sort_column: usize,
    pub sort_descending: bool,

    // Hide cursor. If any cursor movement key is pressed, unhide it and inset this flag. Used e.g. in filtered threads list if the selected thread doesn't pass the filter.
    pub cursor_elsewhere: bool,

    // TODO: Handle a specific special case: if the last fully visible row was resized and became partially visible, scroll to make it fully visible again.
    //       This often comes up in breakpoints window: you add a conditional breakpoint, resume the program, it stops at that breakpoint because condition evaluation failed,
    //       but there's no indication of that because error message is shown in a new line of the row.
}
impl TableState {
    pub fn select(&mut self, cursor: usize) {
        self.cursor = cursor;
        self.scroll_to_cursor = true;
        self.cursor_elsewhere = false;
    }
    pub fn select_if_changed(&mut self, cursor: usize) {
        self.scroll_to_cursor |= cursor != self.cursor;
        self.cursor = cursor;
    }
}

// For columns with auto_width = Text/Children, the width negotiation is a bit complicated:
//  1. Initially each cell+header of the column is created with the corresponding AutoSize.
//  2. After the whole table is populated, finish_layout() calls calculate_size() for all cells and calculates the final column width.
//     Then it iterates over all these cells again and changes their size (despite AxisFlags::SIZE_KNOWN!) to the column width.
//  3. Then the auto-tooltip code may clone cell's Widget subtree, change the cell width (usually to make it much wider), and recalculate layout inside the cell (e.g. a progress bar may fill the parent and become wider).
pub struct Table {
    pub state: TableState,
    pub enable_selection_icon: bool, // draw a '➤' to the left of the selected row
    pub hide_cursor_if_unfocused: bool,
    pub enable_tooltip: bool,
    columns: Vec<Column>,

    root: WidgetIdx,
    viewport: WidgetIdx,
    rows_container: WidgetIdx,
    scroll_bar: WidgetIdx,

    finished_layout: [bool; 2], // horizontal, vertical
    seen_row_ids: HashSet<usize>,

    // Lazy mode.
    lazy: bool,
    row_idxs: Range<usize>,
    total_rows: usize,
    fixed_row_height: usize,
}
impl Table {
    pub fn new(mut state: TableState, ui: &mut UI, columns: Vec<Column>) -> Self {
        let root = ui.cur_parent;
        let w = ui.get_mut(root);
        w.axes[Axis::Y].flags.insert(AxisFlags::STACK);
        assert!(w.axes[0].flags.contains(AxisFlags::SIZE_KNOWN) && w.axes[1].flags.contains(AxisFlags::SIZE_KNOWN), "Table widget requires the size to be known in advance");
        let (width, height) = (w.axes[Axis::X].size, w.axes[Axis::Y].size);
        let (viewport, rows_container, scroll_bar);

        with_parent!(ui, root, {
            // Header.
            with_parent!(ui, ui.add(widget!().hstack().fixed_height(1)), {
                for (i, col) in columns.iter().enumerate() {
                    with_parent!(ui, ui.add(widget!().width(AutoSize::Text).fixed_height(1)), {
                        ui_write!(ui, table_header, "{}", col.title);
                        if col.sortable {
                            ui.cur_mut().flags.insert(WidgetFlags::HIGHLIGHT_ON_HOVER);
                            if ui.check_mouse(MouseActions::CLICK) {
                                if state.sort_column == i {
                                    state.sort_descending ^= true;
                                } else {
                                    state.sort_column = i;
                                    state.sort_descending = false;
                                }
                                state.scroll_to_cursor = true;
                            }
                            let c = if state.sort_column != i {
                                '·'
                            } else if state.sort_descending {
                                '↑'
                            } else {
                                '↓'
                            };
                            ui_write!(ui, table_header, "{}", c);
                        }
                        let l = ui.text.close_line();
                        ui.cur_mut().draw_text = Some(l..l+1);
                    });
                }
            });

            with_parent!(ui, ui.add(widget!().hstack().fixed_height(height.saturating_sub(1))), {
                // Clipping rectangle for the scrollable area.
                viewport = ui.add(widget!().fixed_width(width.saturating_sub(1)));
                with_parent!(ui, viewport, {
                    ui.focus();
                    // Widget containing all rows, moves up and down when scrolling.
                    rows_container = ui.add(widget!().height(AutoSize::Children).vstack().fixed_y(0));
                });
                scroll_bar = ui.add(widget!().fixed_width(1));
            });
        });

        Self {state, columns, root, viewport, rows_container, scroll_bar, finished_layout: [false; 2], enable_selection_icon: true, hide_cursor_if_unfocused: false, enable_tooltip: true,
              lazy: false, row_idxs: 0..0, total_rows: 0, fixed_row_height: 0, seen_row_ids: HashSet::new()}
    }

    // Switches the table into "lazy mode": input is processed and vertical layout is determined right here, before rows are created, so that only visible rows have to be created.
    // Returns the range of rows that need to be created.
    pub fn lazy(&mut self, num_rows: usize, row_height: usize, ui: &mut UI) -> Range<usize> {
        assert!(row_height > 0);
        self.lazy = true;
        (self.total_rows, self.fixed_row_height) = (num_rows, row_height);
        with_parent!(ui, self.rows_container, {
            ui.cur_mut().axes[Axis::Y].auto_size = AutoSize::Fixed(num_rows * row_height);
            if ui.check_mouse(MouseActions::CLICK_SUBTREE) {
                let y = ui.cur().mouse_pos[1];
                if y >= 0 && (y as usize) < num_rows * row_height {
                    self.state.select(y as usize / row_height);
                }
            }
        });
        with_parent!(ui, self.viewport, {
            if self.state.cursor_elsewhere {
                self.state.cursor = num_rows;
            }
            if list_cursor_navigation(&mut self.state.cursor, num_rows, row_height, ui) {
                self.state.cursor_elsewhere = false;
                self.state.scroll_to_cursor = true;
            }
        });
        let scroll_to = if self.state.scroll_to_cursor && num_rows > 0 {
            Some((self.state.cursor*row_height) as isize..((self.state.cursor+1)*row_height) as isize)
        } else {
            None
        };
        let y_range = with_parent!(ui, self.viewport, {
            scrolling_navigation(&mut self.state.scroll, scroll_to, self.root, self.scroll_bar, ui)
        });
        self.row_idxs = (y_range.start as usize)/row_height..(y_range.end as usize + row_height - 1)/row_height;
        self.row_idxs.end = self.row_idxs.end.min(num_rows);
        self.row_idxs.start = self.row_idxs.start.min(self.row_idxs.end);
        self.row_idxs.clone()
    }

    pub fn start_row(&mut self, id: usize, ui: &mut UI) -> WidgetIdx {
        self.finish_row(ui);
        let ins = self.seen_row_ids.insert(id);
        assert!(ins);

        with_parent!(ui, self.rows_container, {
            let x = if self.enable_selection_icon {2} else {0}; // excluding the icon from selection highlighting looks slightly better (to me)
            let row_height = if self.lazy {AutoSize::Fixed(self.fixed_row_height)} else {AutoSize::Children};
            let w = widget!().identity(&id).hstack().fixed_x(x).height(row_height).fill(' ', ui.palette.default).highlight_on_hover();
            with_parent!(ui, ui.add(w), {
                if !self.lazy && ui.check_mouse(MouseActions::CLICK_SUBTREE) {
                    self.state.select(ui.get(self.rows_container).children.len() - 1);
                }
                ui.cur_parent
            })
        })
    }

    fn finish_row(&mut self, ui: &mut UI) {
        if let Some(&row) = ui.get(self.rows_container).children.last() {
            assert_eq!(ui.get(row).children.len(), self.columns.len(), "wrong number of cells in row");
        }
    }

    // Add cell with a single line of text.
    // Usage:
    //   ui_writeln!(ui, ...);
    //   table.text_cell(ui);
    pub fn text_cell(&mut self, ui: &mut UI) -> WidgetIdx {
        let l = ui.text.num_lines() - 1;
        self.text_cell_lines(l..l+1, ui)
    }

    // Add cell with multiple lines of text.
    pub fn text_cell_lines(&mut self, lines: Range<usize>, ui: &mut UI) -> WidgetIdx {
        with_parent!(ui, self.start_cell(ui), {
            ui.cur_mut().axes[Axis::Y].auto_size = AutoSize::Text;
            ui.cur_mut().draw_text = Some(lines);
            ui.cur_parent
        })
    }

    pub fn empty_cell(&mut self, ui: &mut UI) -> WidgetIdx {
        with_parent!(ui, self.start_cell(ui), {
            ui.cur_mut().axes[Axis::Y].set_fixed_size(1);
            ui.cur_parent
        })
    }

    // Add empty cell inside which you can add arbitrary widgets.
    pub fn start_cell(&mut self, ui: &mut UI) -> WidgetIdx {
        let w = *ui.get(self.rows_container).children.last().unwrap();
        let i = ui.get(w).children.len();
        assert!(i < self.columns.len());
        with_parent!(ui, w, {
            let cell = ui.add(widget!().width(self.columns[i].auto_width).height(AutoSize::Children));
            if self.columns[i].hidden {
                ui.get_mut(cell).axes[Axis::X].max_size = 0;
                // Prevent this cell from affecting row height.
                ui.get_mut(cell).axes[Axis::Y].max_size = 0;
            }
            cell
        })
    }

    pub fn finish_horizontal_layout(&mut self, ui: &mut UI) {
        assert!(!self.finished_layout[0]);
        self.finished_layout[0] = true;
        self.finish_row(ui);
        let num_rows = ui.get(self.rows_container).children.len();

        // Look at all cells to calculate Children and Text column widths.
        for row_idx in 0..num_rows {
            let row = ui.get(self.rows_container).children[row_idx];
            for (col_idx, col) in self.columns.iter_mut().enumerate() {
                match col.auto_width {
                    AutoSize::Fixed(_) | AutoSize::Remainder(_) => continue,
                    AutoSize::Children | AutoSize::Text => (),
                    _ => panic!("unexpected auto_width for column {}", col.title),
                }
                let cell = ui.get(row).children[col_idx];
                col.width = col.width.max(ui.calculate_size(cell, Axis::X));
            }
        }

        let reserved = if self.enable_selection_icon {2usize} else {0};

        // Calculate Remainder column widths.
        let mut remainder_helper = RemainderFractionHelper::new(ui.get(self.rows_container).axes[Axis::X].size);
        remainder_helper.declare_fixed_part(reserved);
        for (col_idx, col) in self.columns.iter_mut().enumerate() {
            if col.hidden {
                col.width = 0;
                continue;
            }
            match col.auto_width {
                AutoSize::Remainder(f) => remainder_helper.declare_remainder_fraction(f, col_idx),
                AutoSize::Children | AutoSize::Text => remainder_helper.declare_fixed_part(col.width),
                AutoSize::Fixed(x) => {
                    col.width = x;
                    remainder_helper.declare_fixed_part(col.width);
                }
                _ => panic!("unexpected auto_width for column {}", col.title),
            }
            if col_idx > 0 {
                remainder_helper.declare_fixed_part(1);
            }
        }
        let mut pos = 0isize;
        for (col_idx, col) in self.columns.iter_mut().enumerate() {
            if col.hidden {
                continue;
            }
            if col_idx > 0 {
                pos += 1;
            }
            match col.auto_width {
                AutoSize::Remainder(f) => col.width = remainder_helper.calculate_remainder_fraction(f, col_idx),
                _ => (),
            }
            col.pos = pos;
            pos += col.width as isize;
        }

        // Update all cells with final column widths and positions. (Instead of assigning positions manually we could add spacer widgets, but that would be slightly slower and no less code.)
        // Also apply striping to rows.
        let header = ui.get(self.root).children[0];
        for (col_idx, col) in self.columns.iter().enumerate() {
            let cell = ui.get(header).children[col_idx];
            let w = ui.get_mut(cell);
            w.axes[Axis::X].size = col.width;
            w.axes[Axis::X].rel_pos = reserved as isize + col.pos;
            w.axes[Axis::X].flags.insert(AxisFlags::SIZE_KNOWN | AxisFlags::POS_KNOWN);
        }
        for row_idx in 0..num_rows {
            let row = ui.get(self.rows_container).children[row_idx];
            if row_idx % 2 == 0 {
                let adj = ui.palette.striped_table;
                let w = ui.get_mut(row);
                w.style_adjustment.update(adj);
            }
            for (col_idx, col) in self.columns.iter().enumerate() {
                let cell = ui.get(row).children[col_idx];
                let w = ui.get_mut(cell);
                w.axes[Axis::X].auto_size = AutoSize::Fixed(col.width);
                w.axes[Axis::X].size = col.width;
                w.axes[Axis::X].rel_pos = col.pos;
                w.axes[Axis::X].flags.insert(AxisFlags::SIZE_KNOWN | AxisFlags::POS_KNOWN);
            }
        }
    }

    pub fn finish_vertical_layout(&mut self, ui: &mut UI) {
        assert!(!self.finished_layout[1]);
        self.finished_layout[1] = true;
        with_parent!(ui, self.rows_container, {
            let w = ui.cur_mut();
            if !self.lazy {
                self.row_idxs = 0..w.children.len();
            } else {
                w.axes[Axis::Y].auto_size = AutoSize::Fixed(self.total_rows * self.fixed_row_height);
                assert_eq!(w.children.len(), self.row_idxs.len(), "number of rows created doesn't match the range returned from lazy()");
                if !w.children.is_empty() {
                    let r = w.children[0];
                    let w = ui.get_mut(r);
                    w.axes[Axis::Y].flags.insert(AxisFlags::POS_KNOWN);
                    w.axes[Axis::Y].rel_pos = (self.row_idxs.start * self.fixed_row_height) as isize;
                }
            }
            ui.layout_children(Axis::Y);
        });
    }

    #[must_use]
    pub fn finish(mut self, ui: &mut UI) -> TableState {
        if !self.finished_layout[0] {
            self.finish_horizontal_layout(ui);
        }
        if !self.finished_layout[1] {
            self.finish_vertical_layout(ui);
        }

        if !self.lazy {
            let num_rows = ui.get(self.rows_container).children.len();
            with_parent!(ui, self.viewport, {
                if self.state.cursor_elsewhere {
                    self.state.cursor = num_rows;
                }
                if list_cursor_navigation_with_variable_row_height(&mut self.state.cursor, num_rows, |i, ui| ui.get(ui.get(self.rows_container).children[i]).axes[Axis::Y].size, ui) {
                    self.state.cursor_elsewhere = false;
                    self.state.scroll_to_cursor = true;
                }
            });
            let scroll_to = if self.state.scroll_to_cursor && num_rows > 0 {
                let ax = &ui.get(ui.get(self.rows_container).children[self.state.cursor]).axes[Axis::Y];
                Some(ax.rel_pos..ax.rel_pos + ax.size as isize)
            } else {
                None
            };
            with_parent!(ui, self.viewport, {
                scrolling_navigation(&mut self.state.scroll, scroll_to, self.root, self.scroll_bar, ui);
            });
        }

        let hide_cursor = with_parent!(ui, self.viewport, {
            (self.hide_cursor_if_unfocused && !ui.check_focus()) || self.state.cursor_elsewhere
        });
        if self.row_idxs.contains(&self.state.cursor) && !hide_cursor {
            with_parent!(ui, ui.get(self.rows_container).children[self.state.cursor - self.row_idxs.start], {
                ui.focus();
                let a = ui.palette.selected;
                let row = ui.cur_mut();
                row.style_adjustment.update(a);
                if self.enable_selection_icon {
                    let y = row.axes[Axis::Y].rel_pos;
                    with_parent!(ui, self.rows_container, {
                        ui.add(widget!().identity(&'>').fixed_width(1).fixed_x(0).fixed_height(1).fixed_y(y).fill('➤', ui.palette.default));
                    });
                }

                self.handle_tooltip(ui);
            });
        }

        self.state.did_scroll_to_cursor = mem::take(&mut self.state.scroll_to_cursor);
        self.state
    }

    fn handle_tooltip(&mut self, ui: &mut UI) {
        if !self.enable_tooltip {
            return;
        }
        let tooltip = match ui.check_tooltip() {
            Some(x) => x,
            None => return,
        };
        let row = ui.cur_parent;
        with_parent!(ui, tooltip, {
            ui.cur_mut().axes[Axis::Y].flags.insert(AxisFlags::STACK);
            let mut width = 0usize;
            for (col_idx, col) in self.columns.iter().enumerate() {
                width = width.max(str_width(col.title));
                let l = styled_writeln!(ui.text, ui.palette.table_header, "{}", col.title);
                ui.add(widget!().height(AutoSize::Text).text(l).flags(WidgetFlags::LINE_WRAP));

                let cell = ui.get(row).children[col_idx];
                let w = Self::questionable_autotooltip(ui, cell);
                width = width.max(w);

                if col_idx + 1 < self.columns.len() {
                    ui.add(widget!().fixed_height(1));
                }
            }
            let max_width = ui.cur().axes[Axis::X].max_size;
            ui.cur_mut().axes[Axis::X].set_fixed_size(width.min(max_width));
        });
    }

    fn questionable_autotooltip(ui: &mut UI, cell: WidgetIdx) -> usize {
        let mut width = 0usize;
        let mut stack: Vec<(WidgetIdx, WidgetIdx)> = vec![(cell, ui.cur_parent)];
        while let Some((from, to)) = stack.pop() {
            let mut w = ui.get(from).make_questionable_copy();
            if let Some(lines) = w.draw_text.clone() {
                for line in lines {
                    width = width.max(str_width(ui.text.get_line_str(line)));
                }
            }
            w.flags.insert(WidgetFlags::LINE_WRAP);
            w.parent = to;
            if from == cell {
                w.axes[Axis::X].auto_size = AutoSize::Parent;
                w.axes[Axis::X].max_size = usize::MAX;
                w.axes[Axis::Y].max_size = usize::MAX;
            }
            let new_to = ui.add(w);
            for c in ui.get(from).children.iter().rev() {
                stack.push((*c, new_to));
            }
        }
        width
    }
}


#[derive(Default)]
pub struct TabsState {
    pub selected: usize,
    pub hscroll: isize,
    pub scroll_to_selected_tab: bool,
}
impl TabsState {
    pub fn select(&mut self, tab_idx: usize) {
        self.selected = tab_idx;
        self.scroll_to_selected_tab = true;
    }
    // Call when a tab is removed from the list.
    pub fn closed(&mut self, tab_idx: usize) {
        if self.selected > tab_idx {
            self.selected -= 1;
        }
        self.scroll_to_selected_tab = true;
    }
    pub fn apply_action<T>(&mut self, action: TabsAction, tabs: &mut Vec<T>) -> bool {
        match action {
            TabsAction::None => false,
            TabsAction::Close(idx) => if idx < tabs.len() {
                tabs.remove(idx);
                self.closed(idx);
                true
            } else {
                false
            }
            TabsAction::Reorder {from_idx, to_idx} => {
                let new_idx = if to_idx <= from_idx {
                    to_idx
                } else {
                    to_idx - 1
                };
                if new_idx != from_idx && from_idx < tabs.len() && new_idx < tabs.len() {
                    // (Remove+insert instead of a more efficient rotate because this seems less error-prone.)
                    let t = tabs.remove(from_idx);
                    tabs.insert(new_idx, t);

                    if self.selected == from_idx {
                        self.selected = new_idx;
                        self.scroll_to_selected_tab = true;
                    } else {
                        if self.selected > from_idx {
                            self.selected -= 1;
                        }
                        if self.selected >= new_idx {
                            self.selected += 1;
                        }
                    }
                    true
                } else {
                    false
                }
            }
            TabsAction::DropWindow {..} => panic!("unexpected DropWindow event"),
        }
    }
}

#[derive(Debug)]
pub enum TabsAction {
    None,
    Reorder {
        from_idx: usize, // take the tab at this index
        to_idx: usize, // and put it just before the tab that's currently at this index
    },
    DropWindow { // used if allow_dropping_window
        window_id: Id,
        to_idx: usize,
    },
    Close(usize),
}

#[derive(Default)]
pub struct Tab {
    pub identity: usize,
    pub short_title: String,
    pub full_title: String,
    pub ephemeral: bool,
    pub hotkey_number: Option<usize>,
    pub custom_drag: Option<DragWhat>,
    pub allow_closing: bool,

    // (These shouldn't be used from the outside, they're public only to make Default work, to avoid the annoying "builder pattern".)
    pub idx: usize,
    pub widget: WidgetIdx,
    pub separator_widget: WidgetIdx,
    pub disambiguation_suffix: String,
}

pub struct Tabs {
    pub tabs: Vec<Tab>,
    pub state: TabsState,
    pub custom_styles: Option<(/*selected*/ Style, /*ephemeral*/ (String, Style), /*deselected*/ Style, /*separator*/ (String, Style))>,
    pub allow_reordering: bool,
    // React to DRAG_IN with DragWhat::Window.
    pub allow_dropping_window: bool,
    viewport: WidgetIdx,
    content: WidgetIdx,
    action: TabsAction,
}
impl Tabs {
    pub fn new(state: TabsState, ui: &mut UI) -> Self {
        let content = ui.add(widget!().width(AutoSize::Children).fixed_height(1).flags(WidgetFlags::HSCROLL_INDICATOR_LEFT | WidgetFlags::HSCROLL_INDICATOR_RIGHT).hstack());
        Self {tabs: Vec::new(), state, allow_reordering: false, allow_dropping_window: false, viewport: ui.cur_parent, content, custom_styles: None, action: TabsAction::None}
    }

    pub fn add(&mut self, mut tab: Tab, ui: &mut UI) {
        tab.idx = self.tabs.len();
        if tab.identity == 0 {
            tab.identity = tab.idx;
        }
        with_parent!(ui, self.content, {
            tab.separator_widget = ui.add(widget!().width(AutoSize::Text));
            tab.widget = ui.add(widget!().identity(&('t', tab.identity)).width(AutoSize::Text).max_width(35).highlight_on_hover());
            let tabs_identity = ui.cur().identity;

            with_parent!(ui, tab.widget, {
                if ui.check_mouse(MouseActions::CLICK) {
                    self.state.select(tab.idx);
                }

                if tab.allow_closing && ui.check_mouse(MouseActions::MIDDLE_CLICK) {
                    self.action = TabsAction::Close(tab.idx);
                }

                if let &Some(what) = &tab.custom_drag {
                    ui.check_drag_out(what);
                } else if self.allow_reordering {
                    ui.check_drag_out(DragWhat::Tab {tabs_identity, tab_idx: tab.idx});
                }
            });
        });

        self.tabs.push(tab);
    }

    #[must_use]
    pub fn finish(mut self, ui: &mut UI) -> (TabsState, TabsAction) {
        self.disambiguate_titles(ui);

        self.state.selected = self.state.selected.min(self.tabs.len().saturating_sub(1));
        for key in ui.check_keys(&[KeyAction::PreviousTab, KeyAction::NextTab]) {
            if !self.tabs.is_empty() {
                match key {
                    KeyAction::PreviousTab => self.state.select((self.state.selected + self.tabs.len() - 1)%self.tabs.len()),
                    KeyAction::NextTab => self.state.select((self.state.selected + 1)%self.tabs.len()),
                    _ => panic!("huh"),
                }
            }
        }

        let (selected, ephemeral, deselected, separator) = match self.custom_styles.clone() {
            Some(x) => x,
            None => (ui.palette.tab_selected, ui.palette.tab_ephemeral.clone(), ui.palette.tab_deselected, ui.palette.tab_separator.clone()),
        };

        let mut show_drop_indicator: Option<isize> = None;
        if self.allow_reordering || self.allow_dropping_window {
            with_parent!(ui, self.content, {
                if let Some((what, pos, drop)) = ui.check_drag_in() {
                    // Map `pos` to tab idx. Use tab positions and sizes from previous frame.
                    for (i, tab) in self.tabs.iter().enumerate() {
                        let w = ui.get(tab.widget);
                        let mid = w.axes[Axis::X].rel_pos + w.axes[Axis::X].size as isize / 2;
                        let (to_idx, x) = if pos[Axis::X] <= mid {
                            (i, w.axes[Axis::X].rel_pos - 2)
                        } else if i + 1 == self.tabs.len() {
                            (self.tabs.len(), w.axes[Axis::X].rel_pos + w.axes[Axis::X].size as isize + 1)
                        } else {
                            continue;
                        };

                        let action = match what {
                            DragWhat::Tab {tabs_identity, tab_idx} if self.allow_reordering && tabs_identity == ui.cur().identity && tab_idx != to_idx && tab_idx + 1 != to_idx => TabsAction::Reorder {from_idx: tab_idx, to_idx},
                            DragWhat::Window(window_id) if self.allow_dropping_window && &tab.custom_drag != &Some(DragWhat::Window(window_id)) && &self.tabs[to_idx.saturating_sub(1)].custom_drag != &Some(DragWhat::Window(window_id)) => TabsAction::DropWindow {window_id, to_idx},
                            _ => break,
                        };

                        show_drop_indicator = Some(x);
                        if drop {
                            self.action = action;
                        }

                        break;
                    }
                }
            });
        }

        let padding_line = styled_writeln!(ui.text, separator.1, " ");
        for (i, tab) in self.tabs.iter().enumerate() {
            let l = if i == 0 {padding_line} else {styled_writeln!(ui.text, separator.1, "{}", separator.0)};
            ui.get_mut(tab.separator_widget).draw_text = Some(l..l+1);

            let style = match (i == self.state.selected, tab.ephemeral) {
                (true, _) => selected,
                (false, true) => ephemeral.1,
                (false, false) => deselected,
            };

            if tab.ephemeral {
                styled_write!(ui.text, style, "{}", ephemeral.0);
            }
            styled_write!(ui.text, style, "{}", tab.short_title);
            if !tab.disambiguation_suffix.is_empty() {
                styled_write!(ui.text, style, "{}", tab.disambiguation_suffix);
            }
            if let &Some(n) = &tab.hotkey_number {
                styled_write!(ui.text, style, " ");
                styled_write!(ui.text, ui.palette.hotkey.apply(style), "{}", n);
            }
            let l = ui.text.close_line();

            ui.get_mut(tab.widget).draw_text = Some(l..l+1);
        }
        ui.add(widget!().parent(self.content).text(padding_line).width(AutoSize::Text));

        if let Some(x) = show_drop_indicator {
            let wid = str_width(&ui.palette.tab_drop_indicator.0);
            let l = styled_writeln!(ui.text, ui.palette.tab_drop_indicator.1, "{}", ui.palette.tab_drop_indicator.0);
            ui.add(widget!().parent(self.content).text(l).fixed_x(x - wid as isize / 2).width(AutoSize::Text));
        }
        
        self.state.hscroll += with_parent!(ui, self.viewport, {
            ui.check_scroll() * ui.key_binds.hscroll_sensitivity
        });
        let viewport_width = ui.calculate_size(self.viewport, Axis::X);
        let content_width = ui.calculate_size(self.content, Axis::X);
        with_parent!(ui, self.content, {
            ui.layout_children(Axis::X);
            if mem::take(&mut self.state.scroll_to_selected_tab) && !self.tabs.is_empty() {
                let w = ui.get(self.tabs[self.state.selected].widget);
                scroll_to_range(&mut self.state.hscroll, w.axes[Axis::X].get_fixed_range(), viewport_width);
            }
        });
        self.state.hscroll = self.state.hscroll.min(content_width as isize - viewport_width as isize).max(0);
        let w = ui.get_mut(self.content);
        w.axes[Axis::X].rel_pos = -self.state.hscroll;
        w.axes[Axis::X].flags.insert(AxisFlags::POS_KNOWN);
        (self.state, self.action)
    }

    fn disambiguate_titles(&mut self, ui: &mut UI) {
        let mut sorted_tabs: Vec<(usize, &Tab)> = self.tabs.iter().enumerate().collect();
        sorted_tabs.sort_by_key(|(i, t)| &t.short_title);
        let mut res: Vec<(usize, String)> = Vec::new();
        let mut start = 0;
        while start < sorted_tabs.len() {
            let mut end = start + 1;
            let short_title = &sorted_tabs[start].1.short_title;
            while end < sorted_tabs.len() && &sorted_tabs[end].1.short_title == short_title {
                end += 1;
            }
            if end == start + 1 {
                start += 1;
                continue;
            }

            let full_title = &sorted_tabs[start].1.full_title;
            let (mut common_prefix, mut common_suffix) = (full_title.len(), full_title.len());
            for i in start+1..end {
                let t = &sorted_tabs[i].1.full_title;
                common_prefix = longest_common_prefix(&full_title[..common_prefix], t);
                common_suffix = longest_common_suffix(&full_title[full_title.len()-common_suffix..], t);
            }
            for (i, &(idx, tab)) in sorted_tabs[start..end].iter().enumerate() {
                let suffix = if common_prefix + common_suffix < tab.full_title.len() {
                    format!(" [{}]", &tab.full_title[common_prefix..tab.full_title.len()-common_suffix])
                } else {
                    format!(" [#{}]", i + 1)
                };
                res.push((idx, suffix));
            }

            start = end;
        }
        for (idx, suffix) in res {
            self.tabs[idx].disambiguation_suffix = suffix;
        }
    }
}

fn longest_common_prefix(a: &str, b: &str) -> usize {
    let mut i = 0;
    while i < a.len().min(b.len()) && a.as_bytes()[i] == b.as_bytes()[i] {
        i += 1;
    }
    while !a.is_char_boundary(i) {
        i -= 1;
    }
    i
}
fn longest_common_suffix(a: &str, b: &str) -> usize {
    let mut i = 0;
    while i < a.len().min(b.len()) && a.as_bytes()[a.len()-1-i] == b.as_bytes()[b.len()-1-i] {
        i += 1;
    }
    while !a.is_char_boundary(a.len()-i) {
        i -= 1;
    }
    i
}


pub struct TextInput {
    pub text: String,
    pub cursor: usize,
    pub mark: usize,

    pub multiline: bool,
    pub line_wrap: bool,
    pub capture_vertical_movement_keys: bool, // Up/Down arrow keys, PageUp/PageDown
    pub capture_return_key: bool, // Char('\n'); but ctrl+return is always captured

    pub scroll_to_cursor: bool,
    // true if right arrow key was pressed when the cursor was already at the end.
    // For open dialog it's used as a signal to open file/function without closing the dialog.
    pub moved_past_the_end: bool,

    undo: Vec<(String, /*old_cursor*/ usize, /*new_cursor*/ usize)>,
    undo_idx: usize,

    scroll: isize,
    hscroll: isize,
    // How the `text` characters are laid out on screen. Used for moving cursor up and down.
    lines: Vec<(/*start_x*/ isize, /*bytes*/ Range<usize>)>,
    viewport_height: usize,

    // If moving vertically through: long line -> short line -> long line, remember the cursor horizontal position even if it's beyond the short line's width.
    saved_x: Option<isize>,
    // If we're doing a sequence of emacs-like cut operations, e.g. pressing C-k a few times to cut multiple lines. Each line should be appended to clipboard instead of replacing it.
    killing_spree: bool,
}
impl Default for TextInput {
    fn default() -> Self { Self {text: String::new(), cursor: 0, mark: 0, multiline: false, line_wrap: false, capture_vertical_movement_keys: false, capture_return_key: false, undo: vec![(String::new(), 0, 0)], undo_idx: 0, scroll: 0, hscroll: 0, scroll_to_cursor: false, moved_past_the_end: false, lines: Vec::new(), saved_x: None, killing_spree: false, viewport_height: 0} }
}
impl TextInput {
    pub fn new_with_text(text: String) -> Self { Self {cursor: text.len(), mark: text.len(), multiline: false, line_wrap: false, capture_vertical_movement_keys: false, capture_return_key: false, undo: vec![(text.clone(), text.len(), text.len())], text, undo_idx: 0, scroll: 0, hscroll: 0, scroll_to_cursor: true, moved_past_the_end: false, lines: Vec::new(), saved_x: None, killing_spree: false, viewport_height: 0} }
    pub fn new_multiline(text: String) -> Self { Self {cursor: text.len(), mark: text.len(), multiline: true, line_wrap: true, capture_vertical_movement_keys: true, capture_return_key: false, undo: vec![(text.clone(), text.len(), text.len())], text, undo_idx: 0, scroll: 0, hscroll: 0, scroll_to_cursor: true, moved_past_the_end: false, lines: Vec::new(), saved_x: None, killing_spree: false, viewport_height: 0} }

    pub fn go_to_end(&mut self) {
        self.cursor = self.text.len();
        self.mark = self.cursor;
        self.scroll_to_cursor = true;
    }
    pub fn select_all(&mut self) {
        self.cursor = self.text.len();
        self.mark = 0;
        self.scroll_to_cursor = true;
    }
    pub fn clear(&mut self) {
        self.text.clear();
        self.go_to_end();
    }

    // Returns true if there was any input (or if scroll_to_cursor was set to true from the outside).
    // cur_parent's axes determine scrolling/resizing behavior:
    //  * If AutoSize::Fixed, the viewport size is fixed, and the text is scrollable inside it.
    //  * If AutoSize::Children, the viewport size is set to text size. If text is bigger than the Axis's max_size, the viewport size is clamped and scrolling is enabled.
    // In multiline mode, space for vertical scroll bar is reserved even if the text fits (except AutoSize::Children with max_size = MAX).
    pub fn build(&mut self, ui: &mut UI) -> bool {
        for ax in 0..2 {
            let axis = &ui.cur().axes[ax];
            assert!(axis.flags.contains(AxisFlags::SIZE_KNOWN) || axis.auto_size.is_children(), "only Fixed or Children viewport sizes are supported by TextInput; got {:?}", axis.auto_size);
        }

        {
            let s = ui.palette.default;
            let w = ui.cur_mut();
            w.flags.insert(WidgetFlags::RESET_STYLE_ADJUSTMENT);
            w.draw_fill = Some((' ', s));
        }

        let enable_scroll_bar = self.multiline && (ui.cur().axes[1].flags.contains(AxisFlags::SIZE_KNOWN) || ui.cur().axes[1].max_size < usize::MAX);
        let (mut viewport_widget, mut scroll_bar) = (ui.cur_parent, WidgetIdx::invalid());
        if enable_scroll_bar {
            ui.cur_mut().axes[0].flags.insert(AxisFlags::STACK);
            let mut w = widget!();
            for ax in 0..2 {
                let sub = if ax == 0 {1} else {0};
                let axis = &ui.cur().axes[ax];
                if axis.flags.contains(AxisFlags::SIZE_KNOWN) {
                    w.axes[ax].auto_size = AutoSize::Fixed(axis.size.saturating_sub(sub));
                } else {
                    w.axes[ax].auto_size = AutoSize::Children;
                    w.axes[ax].min_size = axis.min_size.saturating_sub(sub);
                    w.axes[ax].max_size = axis.max_size;
                    if axis.max_size < usize::MAX {
                        w.axes[ax].max_size = axis.max_size.saturating_sub(sub);
                    }
                }
            }

            viewport_widget = ui.add(w);
            scroll_bar = ui.add(widget!().fixed_width(1).fixed_height(0));
        };

        let content_widget = ui.add(widget!().parent(viewport_widget).height(AutoSize::Text).width(AutoSize::Text).fixed_x(0).flags(WidgetFlags::HSCROLL_INDICATOR_LEFT | WidgetFlags::HSCROLL_INDICATOR_RIGHT));

        self.update(content_widget, ui);
        with_parent!(ui, viewport_widget, {
            self.render(content_widget, scroll_bar, ui);
        });
        mem::take(&mut self.scroll_to_cursor)
    }

    fn update(&mut self, content_widget: WidgetIdx, ui: &mut UI) {
        self.moved_past_the_end = false;

        with_parent!(ui, content_widget, {
            ui.focus();

            let clicked = ui.check_mouse(MouseActions::CLICK);
            if let Some(pos) = ui.check_drag_out(DragWhat::NoDrop) {
                self.cursor = self.coordinates_to_offset(pos);
                if clicked {
                    self.mark = self.cursor;
                }
            }
        });

        ui.cur_mut().flags.insert(WidgetFlags::CAPTURE_TEXT_INPUT_KEYS);
        // Most text navigation keys are currently not customizable by KeyBinds as it doesn't seem useful and there are too many.
        ui.cur_mut().capture_keys.extend_from_slice(&[
            Key::Left.any_mods(), Key::Right.any_mods(), Key::Char('b').ctrl(), Key::Char('f').ctrl(), Key::Char('b').alt(), Key::Char('f').alt(), Key::Char('B').alt(), Key::Char('F').alt(),
            Key::Home.any_mods(), Key::End.any_mods(), Key::Char('a').ctrl(), Key::Char('e').ctrl(), Key::Char('A').ctrl(), Key::Char('E').ctrl(),
            Key::Char('<').alt(), Key::Char('>').alt(),
            Key::Backspace.any_mods(), Key::Delete.any_mods(), Key::Char('d').ctrl(), Key::Char('d').alt(), Key::Char('w').ctrl(),
            Key::Char('k').ctrl(), Key::Char('u').ctrl(),
        ]);
        // TODO: Use bracketed paste mode to handle pasting multiline text when capture_return_key is false.
        if self.capture_return_key {
            ui.cur_mut().capture_keys.push(Key::Char('\n').plain());
        }
        if self.capture_vertical_movement_keys {
            ui.cur_mut().capture_keys.extend_from_slice(&[
                Key::Up.plain(), Key::Up.shift(), Key::Down.plain(), Key::Down.shift(), Key::Char('n').ctrl(), Key::Char('p').ctrl(),
                Key::PageUp.plain(), Key::PageUp.shift(), Key::PageDown.plain(), Key::PageDown.shift(),
                // The ctrl+v is a collision between page-down (emacs style) and paste (in KeyBinds.text_input by default). The text_input takes precedence, but the user may unbind it and get the emacs-like behavior.
                // (Ctrl+shift+v is unrepresentable in ansi escape codes.)
                Key::Char('v').ctrl(), Key::Char('v').alt(), Key::Char('V').alt(),
            ]);
        }
        let req: Vec<KeyEx> = ui.key_binds.text_input.key_to_action.keys().copied().collect();
        ui.cur_mut().capture_keys.extend_from_slice(&req);

        let mut keys = mem::take(&mut ui.cur_mut().keys);
        keys.retain(|key| {
            let mut moved = true; // scroll to cursor
            let mut edited = false; // add undo entry
            let mut killed = false; // did emacs-style cut operation
            let saved_x = mem::take(&mut self.saved_x);
            let old_cursor = self.cursor;
            match ui.key_binds.text_input.key_to_action.get(key) {
                Some(KeyAction::Undo) => {
                    if self.undo_idx > 0 {
                        self.cursor = self.undo[self.undo_idx].1;
                        self.undo_idx -= 1;
                        self.text = self.undo[self.undo_idx].0.clone();
                        self.mark = self.cursor;
                    } else {
                        moved = false;
                    }
                }
                Some(KeyAction::Redo) => {
                    if self.undo_idx + 1 < self.undo.len() {
                        self.undo_idx += 1;
                        (self.text, _, self.cursor) = self.undo[self.undo_idx].clone();
                        self.mark = self.cursor;
                    } else {
                        moved = false;
                    }
                }
                Some(KeyAction::Copy) => {
                    let r = self.selection();
                    if !r.is_empty() {
                        ui.clipboard = self.text[r].to_string();
                        ui.sync_clipboard_to_os();
                    }
                    moved = false;
                }
                Some(KeyAction::Cut) => {
                    if !self.selection().is_empty() {
                        self.delete_selection(true, false, ui);
                        ui.sync_clipboard_to_os();
                        edited = true;
                    }
                }
                Some(KeyAction::Paste) => {
                    if !ui.clipboard.is_empty() {
                        self.delete_selection(false, false, ui);
                        self.text.insert_str(self.cursor, &ui.clipboard);
                        self.cursor += ui.clipboard.len();
                        self.mark = self.cursor;
                        edited = true;
                    }
                }
                Some(KeyAction::NewLine) if self.multiline => {
                    self.delete_selection(false, false, ui);
                    self.text.insert(self.cursor, '\n');
                    self.move_cursor(false, true);
                    self.mark = self.cursor;
                    edited = true;
                }
                _ => match key.key {
                    Key::Char(c) if (key.mods.is_empty() || c == '\n') && (c != '\n' || self.multiline) => {
                        self.delete_selection(false, false, ui);
                        self.text.insert(self.cursor, c);
                        self.move_cursor(false, true);
                        self.mark = self.cursor;
                        edited = true;
                    }
                    Key::Left | Key::Right | Key::Char('b') | Key::Char('f') | Key::Char('B') | Key::Char('F') => {
                        let select = key.mods.contains(ModKeys::SHIFT) || key.key == Key::Char('B') || key.key == Key::Char('F');
                        let arrow = key.key == Key::Left || key.key == Key::Right;
                        let word = key.mods.contains(ModKeys::ALT) || (arrow && key.mods.contains(ModKeys::CTRL));
                        let right = key.key == Key::Right || key.key == Key::Char('f') || key.key == Key::Char('F');
                        self.move_cursor(word, right);
                        if !select {
                            self.mark = self.cursor;
                        }
                    }
                    Key::Home | Key::End | Key::Char('a') | Key::Char('e') | Key::Char('A') | Key::Char('E') | Key::Char('<') | Key::Char('>') => {
                        let select = key.mods.contains(ModKeys::SHIFT) || key.key == Key::Char('A') || key.key == Key::Char('E');
                        let whole_text = key.key == Key::Char('<') || key.key == Key::Char('>') || (key.mods.contains(ModKeys::CTRL) && (key.key == Key::Home || key.key == Key::End));
                        let home = key.key == Key::Home || key.key == Key::Char('a') || key.key == Key::Char('A') || key.key == Key::Char('<');

                        self.cursor = match (whole_text, home) {
                            (true, true) => 0,
                            (true, false) => self.text.len(),
                            (false, home) => {
                                let mut pos = self.offset_to_coordinates(self.cursor);
                                pos[0] = if home {0} else {isize::MAX};
                                self.coordinates_to_offset(pos)
                            }
                        };
                        if !select {
                            self.mark = self.cursor;
                        }
                    }
                    Key::Backspace | Key::Delete | Key::Char('d') | Key::Char('w') => {
                        let to_clipboard = key.mods.contains(ModKeys::ALT) || key == &Key::Char('w').ctrl(); // backspace/delete/ctrl+backspace/ctrl+delete don't put the string into clipboard, while more emacs-like alt+backspace/alt+d/etc do
                        if self.cursor == self.mark {
                            let word = key.mods.contains(ModKeys::ALT) || (key.mods.contains(ModKeys::CTRL) && key.key != Key::Char('d'));
                            let right = key.key == Key::Delete || key.key == Key::Char('d');
                            self.move_cursor(word, right);
                        }
                        self.delete_selection(to_clipboard, true, ui);
                        edited = true;
                        killed |= to_clipboard;
                    }
                    Key::Char('k') | Key::Char('u') if key.mods == ModKeys::CTRL => {
                        self.mark = self.cursor;
                        let mut pos = self.offset_to_coordinates(self.cursor);
                        pos[0] = if key.key == Key::Char('k') {isize::MAX} else {0};
                        let new_cursor = self.coordinates_to_offset(pos);
                        if new_cursor == self.cursor {
                            self.move_cursor(false, key.key == Key::Char('k'));
                        } else {
                            self.cursor = new_cursor;
                        }
                        self.delete_selection(true, true, ui);
                        edited = true;
                        killed = true;
                    }
                    Key::Up | Key::Down | Key::Char('n') | Key::Char('p') | Key::PageUp | Key::PageDown | Key::Char('v') | Key::Char('V') => {
                        let select = key.mods.contains(ModKeys::SHIFT);
                        let dy = match key.key {
                            Key::Up | Key::Char('p') => -1,
                            Key::Down | Key::Char('n') => 1,
                            k if k == Key::PageUp || (k == Key::Char('v') && key.mods.contains(ModKeys::ALT)) => -(self.viewport_height.saturating_sub(2) as isize),
                            _ => self.viewport_height.saturating_sub(2) as isize,
                        };

                        let mut pos = self.offset_to_coordinates(self.cursor);

                        pos[0] = saved_x.unwrap_or(pos[0]);
                        self.saved_x = Some(pos[0]);

                        pos[1] += dy;
                        self.cursor = self.coordinates_to_offset(pos);
                        if !select {
                            self.mark = self.cursor;
                        }
                    }
                    _ => return true,
                }
            }
            if moved {
                self.scroll_to_cursor = true;
            }
            if edited {
                self.undo_idx += 1;
                self.undo.truncate(self.undo_idx);
                self.undo.push((self.text.clone(), old_cursor, self.cursor));
            }
            self.killing_spree = killed;
            false
        });
        ui.cur_mut().keys = keys;

        if self.undo.len() > 1000 {
            let n = (self.undo.len() - 500).min(self.undo_idx);
            self.undo.drain(..n);
            self.undo_idx -= n;
        }
    }

    fn selection(&self) -> Range<usize> {
        self.mark.min(self.cursor)..self.mark.max(self.cursor)
    }
        
    fn move_cursor(&mut self, word: bool, right: bool) {
        match (word, right) {
            (false, false) if self.cursor > 0 => self.cursor = self.text[..self.cursor].char_indices().rev().next().unwrap().0,
            (false, true) if self.cursor == self.text.len() => self.moved_past_the_end = true,
            (false, true) => self.cursor = self.text[self.cursor..].char_indices().nth(1).map_or(self.text.len(), |t| self.cursor + t.0),
            (true, false) => {self.text[..self.cursor].char_indices().rev().skip_while(|t| !Self::is_word_character(t.1)).skip_while(|t| if Self::is_word_character(t.1) { self.cursor = t.0; true } else { false }).next();}
            (true, true) => self.cursor = self.text[self.cursor..].char_indices().skip_while(|t| !Self::is_word_character(t.1)).skip_while(|t| Self::is_word_character(t.1)).next().map_or(self.text.len(), |t| self.cursor + t.0),
            _ => (),
        }
    }

    fn is_word_character(c: char) -> bool {
        match c {
            'a'..='z' | 'A'..='Z' | '0'..='9' | '_' => true,
            _ => false }
    }

    fn delete_selection(&mut self, to_clipboard: bool, kill: bool, ui: &mut UI) {
        let r = self.selection();
        if to_clipboard {
            if !kill || !self.killing_spree {
                ui.clipboard.clear();
            }
            // Append or prepend to the clipboard.
            let pos = if self.cursor > self.mark {ui.clipboard.len()} else {0};
            ui.clipboard.insert_str(pos, &self.text[r.clone()]);
        }
        self.text.replace_range(r.clone(), "");
        self.cursor = r.start;
        self.mark = self.cursor;
    }

    fn offset_to_coordinates(&self, offset: usize) -> [isize; 2] {
        if self.lines.is_empty() {
            return [0, 0];
        }
        let i = self.lines.partition_point(|(_, r)| r.end <= offset).min(self.lines.len() - 1);
        let (start_x, range) = self.lines[i].clone();
        let w = str_width(&self.text[range.start..offset]);
        [start_x + w as isize, i as isize]
    }

    fn coordinates_to_offset(&self, pos: [isize; 2]) -> usize {
        if pos[1] < 0 {
            return 0;
        }
        if pos[1] >= self.lines.len() as isize {
            return self.text.len();
        }
        let i = pos[1].max(0).min(self.lines.len() as isize - 1) as usize;
        let (start_x, mut range) = self.lines[i].clone();
        if i + 1 < self.lines.len() {
            // Exclude the '\n'.
            range.end -= 1;
        }
        let (j, _, _, _) = str_prefix_with_width(&self.text[range.clone()], (pos[0] - start_x).max(0) as usize);
        range.start + j
    }

    fn render(&mut self, content_widget: WidgetIdx, scroll_bar: WidgetIdx, ui: &mut UI) {
        let selection = self.selection();
        styled_write!(ui.text, ui.palette.text_input, "{}", &self.text[..selection.start]);
        styled_write!(ui.text, ui.palette.text_input_selected, "{}", &self.text[selection.clone()]);
        styled_write!(ui.text, ui.palette.text_input, "{}", &self.text[selection.end..]);
        let l = ui.text.close_line();

        let mut line_map: Vec<Range<usize>> = Vec::new();
        let mut line_range = if self.multiline {
            ui.text.split_by_newline_character(l, Some(&mut line_map))
        } else {
            line_map.push(0..self.text.len());
            l..l+1
        };

        ui.get_mut(content_widget).draw_text = Some(line_range.clone());
        let mut content_width = ui.calculate_size(content_widget, 0);
        let viewport_width = ui.calculate_size(ui.cur_parent, 0);

        self.lines.clear();
        if self.line_wrap && content_width > viewport_width {
            let mut wrap_map: Vec<(isize, usize, Range<usize>)> = Vec::new();
            line_range = ui.text.line_wrap(line_range, viewport_width, 10000, &ui.palette.line_wrap_indicator, &ui.palette.truncation_indicator, Some(&mut wrap_map));
            for (start_x, line_idx, r) in wrap_map {
                self.lines.push((start_x, r.start + line_map[line_idx].start .. r.end + line_map[line_idx].start));
            }
            ui.get_mut(content_widget).draw_text = Some(line_range);
            ui.get_mut(content_widget).axes[Axis::X].reset_size();
            content_width = ui.calculate_size(content_widget, 0);
        } else {
            for r in line_map {
                self.lines.push((0, r));
            }
        }

        self.viewport_height = ui.calculate_size(ui.cur_parent, Axis::Y);
        if scroll_bar.is_valid() {
            ui.get_mut(scroll_bar).axes[Axis::Y].size = self.viewport_height;
        }
        
        let cursor_pos = self.offset_to_coordinates(self.cursor);
        ui.get_mut(content_widget).draw_cursor_if_focused = Some(cursor_pos);

        // Vertical and horizontal scrolling.
        let scroll_wheel_widget = content_widget; // same widget where MouseEvent::DRAG_OUT is captured, to make scrolling work while dragging
        if self.multiline {
            let scroll_to = if self.scroll_to_cursor {
                Some(cursor_pos[1]..cursor_pos[1]+1)
            } else {
                None
            };
            scrolling_navigation(&mut self.scroll, scroll_to, scroll_wheel_widget, scroll_bar, ui);
        } else {
            with_parent!(ui, scroll_wheel_widget, {
                self.hscroll += ui.check_scroll() * ui.key_binds.hscroll_sensitivity;
            });
        }
        if self.scroll_to_cursor {
            scroll_to_range(&mut self.hscroll, cursor_pos[0]..cursor_pos[0], viewport_width);
        }
        self.hscroll = self.hscroll.min(content_width as isize - viewport_width as isize).max(0);
        ui.get_mut(content_widget).axes[Axis::X].rel_pos = -self.hscroll;
    }
}

pub fn make_dialog_frame(create: bool, width: AutoSize, height: AutoSize, style_adjustment: StyleAdjustment, border: Style, title: &str, ui: &mut UI) -> Option<WidgetIdx> {
    let dialog_root = match ui.check_dialog(create) {
        None => return None,
        Some(x) => x };
    let dialog = with_parent!(ui, dialog_root, {
        if ui.check_mouse(MouseActions::CLICK) || !ui.check_keys(&[KeyAction::Cancel, KeyAction::Quit]).is_empty() {
            None // (can't return from inside with_parent)
        } else {
            let l = ui_writeln!(ui, default, "{}", title);
            let mut w = widget!().width(width).height(height).hcenter().vcenter().fill(' ', ui.palette.default).style_adjustment(style_adjustment).text(l);
            w.draw_frame = Some((border, /*rounded*/ true));
            let d = ui.add(w);
            ui.layout_children(Axis::X);
            ui.layout_children(Axis::Y);
            Some(d)
        }
    });
    let dialog = match dialog {
        None => {
            ui.close_dialog();
            return None;
        }
        Some(x) => x,
    };
    with_parent!(ui, dialog, {
        ui.check_mouse(MouseActions::CLICK); // clicking inside the dialog shouldn't close it
        let (w, h) = (ui.cur().get_fixed_width(), ui.cur().get_fixed_height());
        with_parent!(ui, ui.add(widget!().fixed_width(w.saturating_sub(4)).fixed_height(h.saturating_sub(4)).fixed_x(2).fixed_y(2)), {
            ui.focus();
            Some(ui.cur_parent)
        })
    })
}

pub struct SearchDialog {
    input: TextInput,
    pub search: SymbolSearcher,
    table_state: TableState,

    pub should_open_document: Option<SearchResultInfo>,
    pub should_close_dialog: bool,
    pub loading: bool,
}

impl SearchDialog {
    pub fn new(searcher: Arc<dyn Searcher>, context: Arc<Context>) -> Self { Self {input: TextInput::default(), search: SymbolSearcher::new(searcher, context), table_state: TableState::default(), should_open_document: None, should_close_dialog: false, loading: false} }

    pub fn build(&mut self, registry: &SymbolsRegistry, ui: &mut UI) {
        self.should_open_document = None;
        self.should_close_dialog = false;
        self.loading = false;

        ui.cur_mut().set_vstack();
        with_parent!(ui, ui.add(widget!().identity(&'i').fixed_height(1)), {
            ui.focus();
            self.input.build(ui);
        });
        ui.add(widget!().fixed_height(1));

        if self.search.update(registry, &self.input.text) {
            self.table_state.select(0);
        }

        let res = self.search.get_results();
        let properties = self.search.searcher.properties();
        let lines_per_result = properties.have_names as usize + properties.have_files as usize;
        self.loading = !res.complete;

        let mut w = widget!().height(AutoSize::Text);
        let start = ui.text.num_lines();
        ui_writeln!(ui, default_dim, "fuzzy search{}",
                    if properties.have_files && properties.have_names {
                        ", use '@filename' to search by file, add ':number' to filter by line number"
                    } else if properties.can_go_to_line {
                        ", add ':number' to go to line"
                    } else {""});
        if self.search.waiting_for_symbols {
            ui_writeln!(ui, warning, "waiting for symbols to load (see 'binaries' window for progress)")
        } else if res.complete {
            if res.results.len() == res.total_results {
                ui_writeln!(ui, default_dim, "{} matches ({} searched)", res.results.len(), PrettySize(res.bytes_done))
            } else {
                ui_writeln!(ui, default_dim, "showing {}/{} matches ({} searched)", res.results.len(), res.total_results, PrettySize(res.bytes_done))
            }
        } else {
            let progress = res.items_done as f64 / res.items_total.max(1) as f64;
            w.draw_progress_bar = Some((progress, ui.palette.progress_bar));
            ui_writeln!(ui, default, "{}", PrettySize(res.bytes_done))
        };
        w = w.text_lines(start..ui.text.num_lines());
        ui.add(w);

        let table_widget = ui.add(widget!().identity("table").height(AutoSize::Remainder(1.0)));
        ui.layout_children(Axis::Y);
        with_parent!(ui, table_widget, {
            ui.multifocus();
            let mut columns = vec![Column::new("", AutoSize::Remainder(1.0), false)];
            if properties.have_mangled_names {
                // Hidden column only visible in tooltip.
                columns.push(Column::new("mangled name", AutoSize::Fixed(0), false).hide());
            }
            let mut table = Table::new(mem::take(&mut self.table_state), ui, columns);
            let range = table.lazy(res.results.len(), lines_per_result, ui);
            for (i, result) in res.results[range].iter().enumerate() {
                let r = self.search.format_result(result);
                table.start_row(i, ui);
                with_parent!(ui, table.start_cell(ui), {
                    ui.cur_mut().axes[Axis::Y].flags.insert(AxisFlags::STACK);
                    if properties.have_names {
                        let l = styled_writeln!(ui.scratch_text, ui.palette.function_name, "{}", r.name);
                        let adj: Vec<(Range<usize>, StyleAdjustment)> = r.name_match_ranges.iter().map(|r| (r.clone(), ui.palette.search_result)).collect();
                        let l = ui.text.import_line_with_adjustments(&ui.scratch_text, l, &adj);
                        ui.add(widget!().height(AutoSize::Text).flags(WidgetFlags::TEXT_TRUNCATION_ALIGN_RIGHT).text(l));
                    }
                    if properties.have_files {
                        styled_write!(ui.scratch_text, ui.palette.filename, "{}", r.file.as_os_str().to_string_lossy());
                        if r.line.file_idx().is_some() && r.line.line() != 0 {
                            styled_write!(ui.scratch_text, ui.palette.line_number, ":{}", r.line.line());
                            if r.line.column() != 0 {
                                styled_write!(ui.scratch_text, ui.palette.column_number, ":{}", r.line.column());
                            }
                        }
                        let l = ui.scratch_text.close_line();
                        let adj: Vec<(Range<usize>, StyleAdjustment)> = r.file_match_ranges.iter().map(|r| (r.clone(), ui.palette.search_result)).collect();
                        let l = ui.text.import_line_with_adjustments(&ui.scratch_text, l, &adj);
                        ui.add(widget!().height(AutoSize::Text).flags(WidgetFlags::TEXT_TRUNCATION_ALIGN_RIGHT).text(l));
                    }
                });

                if properties.have_mangled_names {
                    let l = styled_writeln!(ui.scratch_text, ui.palette.default, "{}", r.mangled_name);
                    let adj: Vec<(Range<usize>, StyleAdjustment)> = r.mangled_name_match_ranges.iter().map(|r| (r.clone(), ui.palette.search_result)).collect();
                    ui.text.import_line_with_adjustments(&ui.scratch_text, l, &adj);
                    table.text_cell(ui);
                }
            }
            self.table_state = table.finish(ui);
        });

        let enter = ui.check_key(KeyAction::Enter);
        if (enter || self.input.moved_past_the_end) && !res.results.is_empty() {
            let r = &res.results[self.table_state.cursor];
            let res = self.search.format_result(r);
            self.should_open_document = Some(res);
        }
        self.should_close_dialog |= enter;
    }
}

#[derive(Default)]
pub struct SearchBar {
    pub text: TextInput,
    pub visible: bool,
    pub editing: bool,

    pub hide_when_not_editing: bool,
}
impl SearchBar {
    // Sets cur_parent's height to 0 or 1. Returns true if there was any input.
    pub fn build(&mut self, left_text: Option<usize>, right_text: Option<usize>, ui: &mut UI) -> bool {
        let mut had_input = false;
        if self.editing && ui.check_key(KeyAction::Enter) {
            self.editing = false;
            had_input = true;
        }
        if self.visible && ui.check_key(KeyAction::Cancel) {
            self.editing = false;
            self.visible = false;
            had_input = true;
        }
        if self.editing && !ui.check_focus() {
            self.editing = false;
        }
        if !self.editing && self.hide_when_not_editing {
            self.visible = false;
        }
        if !self.editing && self.text.text.is_empty() {
            self.visible = false;
        }
        if !self.visible {
            ui.cur_mut().set_fixed_height(0);
            return had_input;
        }

        ui.cur_mut().set_fixed_height(1);
        ui.cur_mut().axes[Axis::X].flags.insert(AxisFlags::STACK);
        if let Some(l) = left_text {
            ui.add(widget!().width(AutoSize::Text).text(l));
        }
        let text_widget = ui.add(widget!().identity(&'t').width(AutoSize::Remainder(1.0)).min_width(10));
        if let Some(l) = right_text {
            ui.add(widget!().width(AutoSize::Text).text(l));
        }
        ui.layout_children(Axis::X);

        with_parent!(ui, text_widget, {
            ui.focus();
            if self.editing {
                had_input |= self.text.build(ui);
            } else {
                let l = ui_writeln!(ui, default, "{}", self.text.text);
                ui.cur_mut().draw_text = Some(l..l+1);
            }
        });

        had_input
    }

    pub fn start_editing(&mut self) {
        self.visible = true;
        self.editing = true;
        self.text.select_all();
    }

    pub fn hide(&mut self) {
        self.visible = false;
        self.editing = false;
    }
}

#[derive(Default)]
pub struct AreaState {
    pub cursor: usize,
    pub scroll: isize,

    pub hcursor: usize,
    pub hscroll: isize,

    pub scroll_to_cursor: bool,

    // These can be used for horizontal cursor in code window.
    pub cursor_extra_height: usize,
    pub no_auto_hscroll: bool, // auto prevents clearing of scroll_to_cursor (so that the caller can use it to do their own auto-hscroll)
}
impl AreaState {
    pub fn select(&mut self, cursor: usize) {
        self.cursor = cursor;
        self.hcursor = 0;
        self.scroll_to_cursor = true;
    }

    pub fn save_state(&self, out: &mut Vec<u8>) -> Result<()> {
        out.write_usize(self.cursor)?;
        out.write_isize(self.scroll)?;
        out.write_usize(self.hcursor)?;
        out.write_isize(self.hscroll)?;
        Ok(())
    }

    pub fn load_state(inp: &mut &[u8]) -> Result<Self> {
        Ok(Self {cursor: inp.read_usize()?, scroll: inp.read_isize()?, hcursor: inp.read_usize()?, hscroll: inp.read_isize()?, scroll_to_cursor: false, cursor_extra_height: 0, no_auto_hscroll: false})
    }
}

// Makes the tree of widgets used by code and disassembly windows (simplified):
//  +-header_widget (hscrollable)------------+
//  | header                                 |
//  +----------------------------------------+
//  +-cur_parent-----------------------------+
//  | +-h/v scrollable------+ +-vscrollbar-+ |
//  | | content             | |            | |
//  | +---------------------+ +------------+ |
//  +----------------------------------------+
//
// Moves cursor by arrow keys and clicks (using CLICK rather than CLICK_SUBTREE, so the caller may intercept it).
// Horizontal scrolling is synced between the header and the main content.
// Returns content widget and its visible Y range. Remember to put HSCROLL_INDICATOR_RIGHT flag on each widget inside `content`.
pub fn build_biscrollable_area_with_header(header_viewport: Option<WidgetIdx>, header_lines: Range<usize>, mut content_size: [usize; 2], state: &mut AreaState, ui: &mut UI) -> (WidgetIdx, Range<isize>) {
    content_size[Axis::X] = content_size[Axis::X].max(ui.text.widest_line(header_lines.clone()));
    content_size[Axis::X] = content_size[Axis::X].max(ui.cur().get_fixed_width());

    let (header_viewport, main_root) = if let Some(h) = header_viewport {
        (h, ui.cur_parent)
    } else {
        ui.cur_mut().set_vstack();
        let h = ui.add(widget!().fixed_height(header_lines.len()));
        let r = ui.add(widget!().height(AutoSize::Remainder(1.0)));
        ui.layout_children(Axis::Y);
        (h, r)
    };
    
    let header_content = ui.add(widget!().parent(header_viewport).text_lines(header_lines).fixed_width(content_size[Axis::X]).flags(WidgetFlags::HSCROLL_INDICATOR_RIGHT));

    let (main_viewport, scroll_bar);
    with_parent!(ui, main_root, {
        ui.cur_mut().set_hstack();
        main_viewport = ui.add(widget!().width(AutoSize::Remainder(1.0)));
        scroll_bar = ui.add(widget!().fixed_width(1));
        ui.layout_children(Axis::X);
    });

    let content = ui.add(widget!().parent(main_viewport).fixed_width(content_size[Axis::X]).fixed_height(content_size[Axis::Y] + state.cursor_extra_height).flags(WidgetFlags::HSCROLL_INDICATOR_LEFT));
    with_parent!(ui, content, {
        if ui.check_mouse(MouseActions::CLICK) {
            let y = ui.cur().mouse_pos[Axis::Y];
            if y >= 0 && (y as usize) < content_size[Axis::Y] + state.cursor_extra_height {
                let mut i = y as usize;
                if i > state.cursor + state.cursor_extra_height {
                    i -= state.cursor_extra_height;
                } else if i > state.cursor {
                    i = state.cursor;
                }
                state.select(i);
            }
        }
    });

    let visible_y;
    with_parent!(ui, main_viewport, {
        ui.focus();
        state.scroll_to_cursor |= list_cursor_navigation(&mut state.cursor, content_size[Axis::Y], 1, ui);
        let scroll_to = if state.scroll_to_cursor {Some(state.cursor as isize .. (state.cursor + state.cursor_extra_height) as isize + 1)} else {None};
        visible_y = scrolling_navigation(&mut state.scroll, scroll_to, main_root, scroll_bar, ui);
    });

    if !state.no_auto_hscroll {
        if state.scroll_to_cursor {
            scroll_to_range(&mut state.hscroll, state.hcursor as isize .. state.hcursor as isize + 1, content_size[Axis::X]);
        }
        with_parent!(ui, main_viewport, {
            hscrolling_navigation(&mut state.hscroll, ui);
        });
        let x = ui.get(content).get_fixed_x();
        ui.get_mut(header_content).set_fixed_x(x);
        state.scroll_to_cursor = false;
    }

    (content, visible_y)
}
