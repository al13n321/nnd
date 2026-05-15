use crate::{common_ui::*, settings::*};
use std::{mem, ops::Range, path::Path, sync::LazyLock};
use tree_sitter::Language;
use tree_sitter_highlight::{Highlight, HighlightConfiguration, HighlightEvent, Highlighter};

const HIGHLIGHT_NAMES: &[&str] = &[
    "attribute",
    "boolean",
    "comment",
    "comment.documentation",
    "constant",
    "constant.builtin",
    "constructor",
    "escape",
    "function",
    "function.builtin",
    "keyword",
    "module",
    "number",
    "operator",
    "property",
    "property.builtin",
    "punctuation",
    "punctuation.bracket",
    "punctuation.delimiter",
    "punctuation.special",
    "string",
    "string.escape",
    "string.special",
    "tag",
    "type",
    "type.builtin",
    "variable",
    "variable.builtin",
    "variable.member",
    "variable.parameter",
];

static RUST_CONFIG: LazyLock<Option<HighlightConfiguration>> = LazyLock::new(|| {
    make_config(
        tree_sitter_rust::LANGUAGE.into(),
        "rust",
        tree_sitter_rust::HIGHLIGHTS_QUERY,
        tree_sitter_rust::INJECTIONS_QUERY,
    )
});
static C_CONFIG: LazyLock<Option<HighlightConfiguration>> = LazyLock::new(|| {
    make_config(
        tree_sitter_c::LANGUAGE.into(),
        "c",
        tree_sitter_c::HIGHLIGHT_QUERY,
        "",
    )
});
static CPP_CONFIG: LazyLock<Option<HighlightConfiguration>> = LazyLock::new(|| {
    make_config(
        tree_sitter_cpp::LANGUAGE.into(),
        "cpp",
        tree_sitter_cpp::HIGHLIGHT_QUERY,
        "",
    )
});
static ZIG_CONFIG: LazyLock<Option<HighlightConfiguration>> = LazyLock::new(|| {
    make_config(
        tree_sitter_zig::LANGUAGE.into(),
        "zig",
        tree_sitter_zig::HIGHLIGHTS_QUERY,
        tree_sitter_zig::INJECTIONS_QUERY,
    )
});

fn make_config(
    language: Language,
    name: &str,
    highlights_query: &str,
    injections_query: &str,
) -> Option<HighlightConfiguration> {
    let mut config =
        HighlightConfiguration::new(language, name, highlights_query, injections_query, "").ok()?;
    config.configure(HIGHLIGHT_NAMES);
    Some(config)
}

fn config_for_path(path: &Path) -> Option<&'static HighlightConfiguration> {
    let ext = path.extension()?.to_str()?.to_ascii_lowercase();
    match ext.as_str() {
        "rs" => RUST_CONFIG.as_ref(),
        "c" => C_CONFIG.as_ref(),
        "cc" | "cpp" | "cxx" | "c++" | "h" | "hh" | "hpp" | "hxx" | "h++" => CPP_CONFIG.as_ref(),
        "zig" => ZIG_CONFIG.as_ref(),
        _ => None,
    }
}

fn config_for_injection(name: &str) -> Option<&'static HighlightConfiguration> {
    match name {
        "rust" | "rs" => RUST_CONFIG.as_ref(),
        "c" => C_CONFIG.as_ref(),
        "cpp" | "c++" | "cc" | "cxx" => CPP_CONFIG.as_ref(),
        "zig" => ZIG_CONFIG.as_ref(),
        _ => None,
    }
}

fn highlight_style(highlight: Highlight, palette: &Palette) -> Style {
    let Some(name) = HIGHLIGHT_NAMES.get(highlight.0) else {
        return palette.default;
    };
    match *name {
        "attribute" => palette.code_attribute,
        "boolean" => palette.code_constant,
        "comment" | "comment.documentation" => palette.code_comment,
        "constant" | "constant.builtin" => palette.code_constant,
        "constructor" => palette.code_type,
        "escape" | "string.escape" | "string.special" => palette.code_escape,
        "function" | "function.builtin" => palette.code_function,
        "keyword" => palette.code_keyword,
        "module" => palette.code_module,
        "number" => palette.code_number,
        "operator" => palette.code_operator,
        "property" | "property.builtin" | "variable.member" => palette.code_property,
        "punctuation" | "punctuation.bracket" | "punctuation.delimiter" | "punctuation.special" => {
            palette.code_punctuation
        }
        "string" => palette.code_string,
        "tag" => palette.code_type,
        "type" | "type.builtin" => palette.code_type,
        "variable" | "variable.builtin" => palette.code_variable,
        "variable.parameter" => palette.code_parameter,
        _ => palette.default,
    }
}

fn style_with_syntax(mut base: Style, syntax: Style) -> Style {
    // Preserve debugger overlays such as statement and inlined-site backgrounds.
    base.fg = syntax.fg;
    base.modifier.insert(syntax.modifier);
    base
}

pub fn apply_to_text(text: &mut StyledText, path: &Path, palette: &Palette) {
    if text.num_lines() == 0 {
        return;
    }
    let Some(config) = config_for_path(path) else {
        return;
    };

    let (source, source_line_starts, source_line_lens, text_line_starts) =
        make_source_for_parser(text);
    if source.is_empty() {
        return;
    }

    let mut highlighter = Highlighter::new();
    let events = match highlighter.highlight(config, source.as_bytes(), None, |name| {
        config_for_injection(name)
    }) {
        Ok(events) => events,
        Err(_) => return,
    };

    let mut active_highlights: Vec<Highlight> = Vec::new();
    let mut ranges: Vec<(Range<usize>, Style)> = Vec::new();
    for event in events {
        match event {
            Ok(HighlightEvent::HighlightStart(highlight)) => active_highlights.push(highlight),
            Ok(HighlightEvent::HighlightEnd) => {
                active_highlights.pop();
            }
            Ok(HighlightEvent::Source { start, end }) => {
                if let Some(highlight) = active_highlights.last().copied() {
                    let style = highlight_style(highlight, palette);
                    push_text_ranges_for_source_range(
                        start..end,
                        style,
                        &source_line_starts,
                        &source_line_lens,
                        &text_line_starts,
                        &mut ranges,
                    );
                }
            }
            Err(_) => return,
        }
    }

    if ranges.is_empty() {
        return;
    }
    apply_ranges_to_text(text, &ranges);
}

fn make_source_for_parser(text: &StyledText) -> (String, Vec<usize>, Vec<usize>, Vec<usize>) {
    let mut source = String::with_capacity(text.chars.len() + text.num_lines().saturating_sub(1));
    let mut source_line_starts = Vec::with_capacity(text.num_lines());
    let mut source_line_lens = Vec::with_capacity(text.num_lines());
    let mut text_line_starts = Vec::with_capacity(text.num_lines());

    for line_idx in 0..text.num_lines() {
        let line = text.get_line_str(line_idx);
        source_line_starts.push(source.len());
        source_line_lens.push(line.len());
        text_line_starts.push(text.get_line_char_range(line_idx).start);
        source.push_str(line);
        if line_idx + 1 < text.num_lines() {
            source.push('\n');
        }
    }

    (
        source,
        source_line_starts,
        source_line_lens,
        text_line_starts,
    )
}

fn push_text_ranges_for_source_range(
    range: Range<usize>,
    style: Style,
    source_line_starts: &[usize],
    source_line_lens: &[usize],
    text_line_starts: &[usize],
    out: &mut Vec<(Range<usize>, Style)>,
) {
    let mut pos = range.start;
    while pos < range.end {
        let line_idx = source_line_starts
            .partition_point(|&start| start <= pos)
            .saturating_sub(1);
        if line_idx >= source_line_starts.len() {
            break;
        }

        let source_line_start = source_line_starts[line_idx];
        let source_line_end = source_line_start + source_line_lens[line_idx];
        if pos < source_line_end {
            let end = range.end.min(source_line_end);
            out.push((
                text_line_starts[line_idx] + (pos - source_line_start)
                    ..text_line_starts[line_idx] + (end - source_line_start),
                style,
            ));
            pos = end;
        } else {
            pos += 1; // Skip the synthetic '\n' between StyledText lines.
        }
    }
}

fn apply_ranges_to_text(text: &mut StyledText, ranges: &[(Range<usize>, Style)]) {
    let old = mem::take(text);
    let mut new = StyledText::default();
    let mut range_idx = 0usize;

    for line_idx in 0..old.num_lines() {
        for span_idx in old.get_line(line_idx) {
            let span_style = old.spans[span_idx + 1].1;
            let mut pos = old.spans[span_idx].0;
            let span_end = old.spans[span_idx + 1].0;

            while pos < span_end {
                while range_idx < ranges.len() && ranges[range_idx].0.end <= pos {
                    range_idx += 1;
                }

                let (end, style) = if range_idx < ranges.len()
                    && ranges[range_idx].0.start < span_end
                    && ranges[range_idx].0.end > pos
                {
                    let range = &ranges[range_idx];
                    if range.0.start > pos {
                        (range.0.start.min(span_end), span_style)
                    } else {
                        (
                            range.0.end.min(span_end),
                            style_with_syntax(span_style, range.1),
                        )
                    }
                } else {
                    (span_end, span_style)
                };

                if end <= pos {
                    break;
                }
                new.chars.push_str(&old.chars[pos..end]);
                new.close_span(style);
                pos = end;
            }
        }
        new.close_line();
    }

    *text = new;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn highlights_rust_keyword() {
        let palette = Palette::default();
        let mut text = StyledText::default();
        text.chars.push_str("fn main() { let x = 1; }");
        text.close_span(palette.default);
        text.close_line();

        apply_to_text(&mut text, Path::new("main.rs"), &palette);

        assert!(text.spans.iter().any(|(_, style)| style.fg == palette.code_keyword.fg));
    }

    #[test]
    fn initializes_supported_grammars() {
        let palette = Palette::default();
        for (path, source) in [
            ("main.c", "int main(void) { return 1; }"),
            ("main.cpp", "class Thing { public: int value; };"),
            ("main.zig", "const x: i32 = 1;"),
        ] {
            let mut text = StyledText::default();
            text.chars.push_str(source);
            text.close_span(palette.default);
            text.close_line();

            apply_to_text(&mut text, Path::new(path), &palette);

            assert!(text.spans.iter().any(|(_, style)| style.fg != palette.default.fg), "{path}");
        }
    }
}
