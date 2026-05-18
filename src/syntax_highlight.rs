// This file was vibecoded mostly by Claude 4.7.
use crate::{common_ui::*, settings::*};
use std::{mem, ops::Range, path::Path, sync::LazyLock};
use tree_sitter::Language;
use tree_sitter_highlight::{Highlight, HighlightConfiguration, HighlightEvent, Highlighter};

// Capture names recognized by the tree-sitter highlights queries. Order is the contract with tree_sitter_highlight: `HighlightConfiguration::configure` assigns `Highlight(n)` to the n-th name we pass it, so this enum's discriminants and the `HIGHLIGHT_NAMES` array below must stay in lockstep — handled by deriving the array from `HighlightKind::name()`.
#[repr(usize)]
#[derive(Copy, Clone)]
enum HighlightKind {
    Attribute,
    Boolean,
    Comment,
    CommentDocumentation,
    Constant,
    ConstantBuiltin,
    Constructor,
    Escape,
    Function,
    FunctionBuiltin,
    Keyword,
    Module,
    Number,
    Operator,
    Property,
    PropertyBuiltin,
    Punctuation,
    PunctuationBracket,
    PunctuationDelimiter,
    PunctuationSpecial,
    String,
    StringEscape,
    StringSpecial,
    Tag,
    Type,
    TypeBuiltin,
    Variable,
    VariableBuiltin,
    VariableMember,
    VariableParameter,
    #[doc(hidden)]
    Count,
}

impl HighlightKind {
    const COUNT: usize = Self::Count as usize;

    const fn name(self) -> &'static str {
        match self {
            Self::Attribute => "attribute",
            Self::Boolean => "boolean",
            Self::Comment => "comment",
            Self::CommentDocumentation => "comment.documentation",
            Self::Constant => "constant",
            Self::ConstantBuiltin => "constant.builtin",
            Self::Constructor => "constructor",
            Self::Escape => "escape",
            Self::Function => "function",
            Self::FunctionBuiltin => "function.builtin",
            Self::Keyword => "keyword",
            Self::Module => "module",
            Self::Number => "number",
            Self::Operator => "operator",
            Self::Property => "property",
            Self::PropertyBuiltin => "property.builtin",
            Self::Punctuation => "punctuation",
            Self::PunctuationBracket => "punctuation.bracket",
            Self::PunctuationDelimiter => "punctuation.delimiter",
            Self::PunctuationSpecial => "punctuation.special",
            Self::String => "string",
            Self::StringEscape => "string.escape",
            Self::StringSpecial => "string.special",
            Self::Tag => "tag",
            Self::Type => "type",
            Self::TypeBuiltin => "type.builtin",
            Self::Variable => "variable",
            Self::VariableBuiltin => "variable.builtin",
            Self::VariableMember => "variable.member",
            Self::VariableParameter => "variable.parameter",
            Self::Count => unreachable!(),
        }
    }

    // Safe because variants of a fieldless `#[repr(usize)]` enum without explicit discriminants are sequential 0..COUNT.
    const fn from_index(n: usize) -> Self {
        assert!(n < Self::COUNT);
        unsafe { mem::transmute(n) }
    }
}

const HIGHLIGHT_NAMES: [&str; HighlightKind::COUNT] = {
    let mut arr = [""; HighlightKind::COUNT];
    let mut i = 0;
    while i < HighlightKind::COUNT {
        arr[i] = HighlightKind::from_index(i).name();
        i += 1;
    }
    arr
};

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
    // tree-sitter-cpp's highlights query only adds C++-specific captures and assumes the C query is also active (this is what nvim-treesitter wires up via the grammar's `inherits: c` directive). tree-sitter-highlight doesn't honor that on its own, so concatenate them ourselves.
    let combined = format!("{}\n{}", tree_sitter_c::HIGHLIGHT_QUERY, tree_sitter_cpp::HIGHLIGHT_QUERY);
    make_config(
        tree_sitter_cpp::LANGUAGE.into(),
        "cpp",
        &combined,
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
static ODIN_CONFIG: LazyLock<Option<HighlightConfiguration>> = LazyLock::new(|| {
    make_config(
        tree_sitter_odin::LANGUAGE.into(),
        "odin",
        tree_sitter_odin::HIGHLIGHTS_QUERY,
        tree_sitter_odin::INJECTIONS_QUERY,
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
    config.configure(&HIGHLIGHT_NAMES);
    Some(config)
}

fn config_for_path(path: &Path) -> Option<&'static HighlightConfiguration> {
    let ext = path.extension()?.to_str()?.to_ascii_lowercase();
    match ext.as_str() {
        "rs" => RUST_CONFIG.as_ref(),
        "c" => C_CONFIG.as_ref(),
        "cc" | "cpp" | "cxx" | "c++" | "h" | "hh" | "hpp" | "hxx" | "h++" => CPP_CONFIG.as_ref(),
        "zig" => ZIG_CONFIG.as_ref(),
        "odin" => ODIN_CONFIG.as_ref(),
        _ => None,
    }
}

fn config_for_injection(name: &str) -> Option<&'static HighlightConfiguration> {
    match name {
        "rust" | "rs" => RUST_CONFIG.as_ref(),
        "c" => C_CONFIG.as_ref(),
        "cpp" | "c++" | "cc" | "cxx" => CPP_CONFIG.as_ref(),
        "zig" => ZIG_CONFIG.as_ref(),
        "odin" => ODIN_CONFIG.as_ref(),
        _ => None,
    }
}

fn highlight_style(highlight: Highlight, palette: &Palette) -> Style {
    debug_assert!(highlight.0 < HighlightKind::COUNT);
    if highlight.0 >= HighlightKind::COUNT {
        return palette.default;
    }
    use HighlightKind::*;
    match HighlightKind::from_index(highlight.0) {
        Attribute => palette.code_attribute,
        Boolean | Constant | ConstantBuiltin => palette.code_constant,
        Comment | CommentDocumentation => palette.code_comment,
        Constructor | Tag | Type | TypeBuiltin => palette.code_type,
        Escape | StringEscape | StringSpecial => palette.code_escape,
        Function | FunctionBuiltin => palette.code_function,
        Keyword => palette.code_keyword,
        Module => palette.code_module,
        Number => palette.code_number,
        Operator => palette.code_operator,
        Property | PropertyBuiltin | VariableMember => palette.code_property,
        Punctuation | PunctuationBracket | PunctuationDelimiter | PunctuationSpecial => palette.code_punctuation,
        String => palette.code_string,
        Variable | VariableBuiltin => palette.code_variable,
        VariableParameter => palette.code_parameter,
        Count => unreachable!(),
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

    let (buf, line_breaks) = flatten(text);
    if buf.chars.is_empty() {
        return;
    }

    let mut highlighter = Highlighter::new();
    let events = match highlighter.highlight(config, buf.chars.as_bytes(), None, |name| {
        config_for_injection(name)
    }) {
        Ok(events) => events,
        Err(_) => return,
    };

    let mut active_highlights: Vec<Highlight> = Vec::new();
    let mut syntax_ranges: Vec<(Range<usize>, Style)> = Vec::new();
    for event in events {
        match event {
            Ok(HighlightEvent::HighlightStart(highlight)) => active_highlights.push(highlight),
            Ok(HighlightEvent::HighlightEnd) => {
                active_highlights.pop();
            }
            Ok(HighlightEvent::Source { start, end }) => {
                if let Some(highlight) = active_highlights.last().copied() {
                    syntax_ranges.push((start..end, highlight_style(highlight, palette)));
                }
            }
            Err(_) => return,
        }
    }

    if syntax_ranges.is_empty() {
        return;
    }

    *text = rebuild(&buf, &syntax_ranges, &line_breaks);
}

// Concatenate `text` into a single-line StyledText with synthetic '\n' between original lines, recording the position of each '\n'. The '\n's are absorbed into the preceding span; their style is irrelevant since they get discarded by `rebuild`.
fn flatten(text: &StyledText) -> (StyledText, Vec<usize>) {
    let mut buf = StyledText::default();
    buf.chars.reserve(text.chars.len() + text.num_lines().saturating_sub(1));
    let mut line_breaks = Vec::with_capacity(text.num_lines().saturating_sub(1));

    for line_idx in 0..text.num_lines() {
        buf.import_spans(text, text.get_line(line_idx));
        if line_idx + 1 < text.num_lines() {
            line_breaks.push(buf.chars.len());
            buf.chars.push('\n');
            if buf.num_spans() == 0 {
                buf.close_span(Style::default());
            } else {
                buf.spans.last_mut().unwrap().0 = buf.chars.len();
            }
        }
    }
    buf.close_line();

    (buf, line_breaks)
}

// Walk `buf` once, merging the base spans with `syntax_ranges` (sorted, non-overlapping, indexed in `buf.chars`) and splitting at `line_breaks`, dropping the '\n' bytes.
fn rebuild(
    buf: &StyledText,
    syntax_ranges: &[(Range<usize>, Style)],
    line_breaks: &[usize],
) -> StyledText {
    let mut out = StyledText::default();
    out.chars.reserve(buf.chars.len() - line_breaks.len());
    let total = buf.chars.len();
    let mut pos = 0usize;
    let mut i_span = 1usize;
    let mut i_range = 0usize;
    let mut i_break = 0usize;

    while pos < total {
        if i_break < line_breaks.len() && line_breaks[i_break] == pos {
            out.close_line();
            pos += 1;
            i_break += 1;
            continue;
        }

        while i_range < syntax_ranges.len() && syntax_ranges[i_range].0.end <= pos {
            i_range += 1;
        }
        while buf.spans[i_span].0 <= pos {
            i_span += 1;
        }

        let base_style = buf.spans[i_span].1;
        let mut end = buf.spans[i_span].0;
        let mut style = base_style;

        if i_break < line_breaks.len() {
            end = end.min(line_breaks[i_break]);
        }
        if i_range < syntax_ranges.len() {
            let r = &syntax_ranges[i_range];
            if r.0.start <= pos {
                end = end.min(r.0.end);
                style = style_with_syntax(base_style, r.1);
            } else {
                end = end.min(r.0.start);
            }
        }

        out.chars.push_str(&buf.chars[pos..end]);
        out.close_span(style);
        pos = end;
    }
    out.close_line();

    out
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
