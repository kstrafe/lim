#![doc = include_str!("../docs/language.md")]
// Lim fences use metadata validated by tests/language_docs.rs, not rustdoc.
#![allow(rustdoc::invalid_codeblock_attributes)]

use std::{
    collections::{BTreeSet, HashMap, HashSet},
    env, fmt, fs,
    path::{Path, PathBuf},
};

mod analysis_error;
mod async_cells;
mod async_cfg;
mod async_contract;
mod async_dispatch;
mod async_emit;
mod async_exec;
mod async_fn;
mod async_interfaces;
mod async_lease;
mod async_lend;
mod async_owner;
mod async_pattern;
mod async_prepare;
mod async_projection;
mod async_render;
mod async_retire;
mod async_source;
mod async_storage;
mod async_values;
// Retain the lexical model only for differential regression tests. Production
// borrowing is decided by checked places, callee contracts and typed flow.
#[cfg(test)]
mod borrowcheck;
mod cache_report;
mod call_self_loans;
mod codegen;
mod diagnostic_json;
mod elf_object;
mod elf_writer;
mod generator;
mod gensym;
mod instruction_encoder;
mod linearcheck;
mod native_assembly;
mod native_linker;
mod output;
mod pin_access;
mod pin_ownership;
mod reachability;
mod source_error;
mod stack_usage;
mod standard_library;
mod syntax_bundle;
mod syntax_collection;
mod thread_contract;
mod typecheck;
mod typed_body;
mod typed_borrow;
mod typed_flow;
mod typed_ir;
mod typed_place;
mod unsafecheck;
use source_error::SourceError;

pub use cache_report::with_cache_report;
pub use codegen::generate_assembly;
pub use codegen::generate_assembly_for_target;
pub use diagnostic_json::render_diagnostic_json;
pub use output::{reject_source_output_collision, write_output_atomic};
pub use stack_usage::stack_usage_report;
pub use typecheck::{check_types, type_has_thread_property, CheckedProgram};

/// CPU architecture descriptions understood by the native backend.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TargetArchitecture {
    X86_64,
}

/// Calling conventions understood by the native backend.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TargetAbi {
    SystemV,
}

/// Explicit target information carried through native code generation.
///
/// The current backend implements only x86-64 System V, but keeping the target
/// explicit prevents code generation from silently acquiring host-dependent
/// ABI behavior as more backends are added.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TargetDescription {
    pub architecture: TargetArchitecture,
    pub abi: TargetAbi,
}

impl TargetDescription {
    pub const X86_64_SYSTEM_V: Self = Self {
        architecture: TargetArchitecture::X86_64,
        abi: TargetAbi::SystemV,
    };

    pub fn host() -> Result<Self, String> {
        if env::consts::ARCH == "x86_64" && env::consts::OS == "linux" {
            Ok(Self::X86_64_SYSTEM_V)
        } else {
            Err(format!(
                "host '{}-{}' is not supported by the native backend; supported targets: x86_64-sysv (Linux ELF)",
                env::consts::ARCH,
                env::consts::OS
            ))
        }
    }

    pub fn parse(name: &str) -> Result<Self, String> {
        match name {
            "x86_64-sysv" | "x86_64-unknown-linux-gnu" => Ok(Self::X86_64_SYSTEM_V),
            other => Err(format!(
                "unsupported target '{other}'; supported targets: x86_64-sysv"
            )),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub line: usize,
    pub column: usize,
    /// Index into `Program::source_files`; standalone parses use zero.
    pub source_id: u32,
}

impl Span {
    const fn new(start: usize, end: usize, line: usize, column: usize) -> Self {
        Self {
            start,
            end,
            line,
            column,
            source_id: 0,
        }
    }
}

/// Stable high-level categories for compiler diagnostics.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DiagnosticCode {
    Lex = 1000,
    Parse = 2000,
    Generator = 3000,
    Type = 4000,
    Borrow = 4100,
    Linear = 4200,
    Unsafe = 4300,
    Codegen = 5000,
    Link = 6000,
    Cli = 7000,
}

/// Structured diagnostic data for editor and tooling integrations.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Diagnostic {
    pub code: DiagnosticCode,
    pub message: String,
    pub span: Option<Span>,
    pub labels: Vec<DiagnosticLabel>,
    pub expansion_provenance: Vec<DiagnosticLabel>,
    pub notes: Vec<String>,
    pub source_name: Option<String>,
    pub source_text: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DiagnosticLabel {
    pub message: String,
    pub span: Span,
    pub source_name: Option<String>,
    pub source_text: Option<String>,
}

impl Diagnostic {
    pub fn new(code: DiagnosticCode, message: impl Into<String>) -> Self {
        Self {
            code,
            message: message.into(),
            span: None,
            labels: Vec::new(),
            expansion_provenance: Vec::new(),
            notes: Vec::new(),
            source_name: None,
            source_text: None,
        }
    }

    pub fn with_span(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }

    pub fn with_source(mut self, name: impl Into<String>, source: impl Into<String>) -> Self {
        self.source_name = Some(name.into());
        self.source_text = Some(source.into());
        self
    }

    pub fn note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    pub fn code_string(&self) -> String {
        format!("E{:04}", self.code as u16)
    }
}

/// Render a diagnostic with a source excerpt and underline when it has a span.
pub fn render_diagnostic(diagnostic: &Diagnostic, source: &str, filename: &str) -> String {
    let source = diagnostic.source_text.as_deref().unwrap_or(source);
    let filename = diagnostic.source_name.as_deref().unwrap_or(filename);
    let mut output = format!(
        "error[{}]: {}",
        diagnostic.code_string(),
        diagnostic.message
    );
    if let Some(span) = diagnostic.span {
        output.push_str(&render_source_hunk(source, filename, span, "here"));
    }
    for label in &diagnostic.labels {
        let label_source = label.source_text.as_deref().unwrap_or(source);
        let label_filename = label.source_name.as_deref().unwrap_or(filename);
        output.push_str(&render_source_hunk(
            label_source,
            label_filename,
            label.span,
            &label.message,
        ));
    }
    for note in &diagnostic.notes {
        output.push_str(&format!("\n  = note: {note}"));
    }
    output
}

/// Format a legacy parser/compiler error string as a diagnostic.
pub fn render_error(source: &str, filename: &str, error: &str) -> String {
    let (code, message) = if let Some((code, message)) = error.strip_prefix('E').and_then(|rest| {
        let (digits, message) = rest.split_once(' ')?;
        Some((digits.parse::<u16>().ok()?, message))
    }) {
        (diagnostic_code_from_number(code), message.to_owned())
    } else if let Some((line, column, message)) = parse_location_prefix(error) {
        let span = source_span_at(source, line, column, token_width_at(source, line, column));
        return render_diagnostic(
            &Diagnostic::new(diagnostic_code_for_positioned_message(&message), message)
                .with_span(span),
            source,
            filename,
        );
    } else if error.starts_with("linear value ")
        || error.starts_with("assignment would destroy live linear")
    {
        (DiagnosticCode::Linear, error.to_owned())
    } else if error.contains("requires #unsafe") || error.starts_with("unsafe ") {
        (DiagnosticCode::Unsafe, error.to_owned())
    } else {
        (DiagnosticCode::Type, error.to_owned())
    };

    render_diagnostic(&Diagnostic::new(code, message), source, filename)
}

fn token_width_at(source: &str, line: usize, column: usize) -> usize {
    let line_text = source.lines().nth(line.saturating_sub(1)).unwrap_or("");
    let mut token = line_text.chars().skip(column.saturating_sub(1));
    let Some(first) = token.next() else {
        return 1;
    };
    if first == '"' {
        let mut width = 1;
        let mut escaped = false;
        for ch in token {
            width += 1;
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                return width;
            }
        }
        return width;
    }
    1 + token
        .take_while(|ch| !ch.is_whitespace() && !matches!(ch, '(' | ')' | '[' | ']' | ','))
        .count()
}

fn diagnostic_code_from_number(number: u16) -> DiagnosticCode {
    match number {
        1000 => DiagnosticCode::Lex,
        2000 => DiagnosticCode::Parse,
        3000 => DiagnosticCode::Generator,
        4100 => DiagnosticCode::Borrow,
        4200 => DiagnosticCode::Linear,
        4300 => DiagnosticCode::Unsafe,
        5000 => DiagnosticCode::Codegen,
        6000 => DiagnosticCode::Link,
        _ => DiagnosticCode::Type,
    }
}

fn diagnostic_code_for_positioned_message(message: &str) -> DiagnosticCode {
    let lower = message.to_ascii_lowercase();
    if lower.contains("generator") {
        DiagnosticCode::Generator
    } else if lower.contains("string")
        || lower.contains("escape")
        || lower.contains("unicode")
        || lower.contains("character literal")
    {
        DiagnosticCode::Lex
    } else if lower.contains("import") {
        DiagnosticCode::Type
    } else {
        DiagnosticCode::Parse
    }
}

fn parse_location_prefix(error: &str) -> Option<(usize, usize, String)> {
    let (line, rest) = error.split_once(':')?;
    let (column, message) = rest.split_once(':')?;
    Some((
        line.parse().ok()?,
        column.parse().ok()?,
        message.trim().to_owned(),
    ))
}

fn source_span_at(source: &str, line: usize, column: usize, width: usize) -> Span {
    let mut offset = 0;
    let mut line_text = "";
    for (index, text) in source.split_inclusive('\n').enumerate() {
        if index + 1 == line {
            line_text = text.strip_suffix('\n').unwrap_or(text);
            break;
        }
        offset += text.len();
    }
    let column_offset = line_text
        .char_indices()
        .nth(column.saturating_sub(1))
        .map_or(line_text.len(), |(byte, _)| byte);
    let start = offset + column_offset;
    let end = line_text
        .get(column_offset..)
        .and_then(|tail| tail.char_indices().nth(width.saturating_sub(1)))
        .map_or(start, |(byte, ch)| start + byte + ch.len_utf8());
    Span::new(start, end.max(start), line, column)
}

fn render_source_hunk(source: &str, filename: &str, span: Span, label: &str) -> String {
    let line_text = source
        .lines()
        .nth(span.line.saturating_sub(1))
        .unwrap_or("");
    let prefix = line_text.chars().take(span.column.saturating_sub(1));
    let start_display = prefix.fold(0, |column, ch| advance_display_column(column, ch));
    let selected = source.get(span.start..span.end).unwrap_or("");
    let selected_width = selected
        .chars()
        .take(80)
        .take_while(|ch| *ch != '\n' && *ch != '\r')
        .fold(0, advance_display_column)
        .min(80)
        .max(1);
    let (rendered_line, marker_start) = diagnostic_line_excerpt(
        line_text,
        span.column.saturating_sub(1),
        start_display,
        selected_width,
    );
    let line_number_width = span.line.to_string().len();
    let marker = format!(
        "{}{}{}",
        " ".repeat(marker_start),
        "^".repeat(selected_width),
        if label.is_empty() {
            String::new()
        } else {
            format!(" {label}")
        }
    );
    format!(
        "\n  --> {filename}:{line}:{column}\n{blank:>line_number_width$} |\n{line:>line_number_width$} | {line_text}\n{blank:>line_number_width$} | {marker}",
        line = span.line,
        column = span.column,
        blank = "",
        line_text = rendered_line,
        marker = marker,
        line_number_width = line_number_width,
    )
}

fn diagnostic_line_excerpt(
    line: &str,
    start_character: usize,
    start_display: usize,
    selection_width: usize,
) -> (String, usize) {
    const MAX_LINE_CHARS: usize = 240;
    const CONTEXT_CHARS: usize = 80;
    let line_characters = line.chars().count();
    if line_characters <= MAX_LINE_CHARS {
        return (expand_tabs(line), start_display);
    }
    let window_start = start_character.saturating_sub(CONTEXT_CHARS);
    let window_end = line_characters.min(
        start_character
            .saturating_add(selection_width.min(80))
            .saturating_add(CONTEXT_CHARS),
    );
    let has_left_ellipsis = window_start > 0;
    let has_right_ellipsis = window_end < line_characters;
    let prefix_display = line
        .chars()
        .take(window_start)
        .fold(0, advance_display_column);
    let mut absolute_column = prefix_display;
    let mut within_prefix_display = 0;
    for character in line
        .chars()
        .skip(window_start)
        .take(start_character.saturating_sub(window_start))
    {
        let next = advance_display_column(absolute_column, character);
        within_prefix_display += next - absolute_column;
        absolute_column = next;
    }
    let marker_start = usize::from(has_left_ellipsis) + within_prefix_display;

    let mut rendered = String::new();
    if has_left_ellipsis {
        rendered.push('…');
    }
    absolute_column = prefix_display;
    for character in line
        .chars()
        .skip(window_start)
        .take(window_end - window_start)
    {
        if character == '\t' {
            let spaces = 4 - absolute_column % 4;
            rendered.push_str(&" ".repeat(spaces));
            absolute_column += spaces;
        } else {
            rendered.push(character);
            absolute_column = advance_display_column(absolute_column, character);
        }
    }
    if has_right_ellipsis {
        rendered.push('…');
    }
    (rendered, marker_start)
}

fn expand_tabs(text: &str) -> String {
    let mut expanded = String::with_capacity(text.len());
    let mut column = 0;
    for ch in text.chars() {
        if ch == '\t' {
            let spaces = 4 - column % 4;
            expanded.push_str(&" ".repeat(spaces));
            column += spaces;
        } else {
            expanded.push(ch);
            column = advance_display_column(column, ch);
        }
    }
    expanded
}

fn advance_display_column(column: usize, ch: char) -> usize {
    if ch == '\t' {
        column + (4 - column % 4)
    } else {
        column + display_char_width(ch)
    }
}

fn display_char_width(ch: char) -> usize {
    let value = ch as u32;
    if matches!(
        value,
        0x0300..=0x036f
            | 0x0483..=0x0489
            | 0x0591..=0x05bd
            | 0x05bf
            | 0x05c1..=0x05c2
            | 0x0610..=0x061a
            | 0x064b..=0x065f
            | 0x0670
            | 0x06d6..=0x06ed
            | 0x1ab0..=0x1aff
            | 0x1dc0..=0x1dff
            | 0x20d0..=0x20ff
            | 0xfe00..=0xfe0f
            | 0xfe20..=0xfe2f
            | 0xe0100..=0xe01ef
    ) {
        0
    } else if matches!(
        value,
        0x1100..=0x115f
            | 0x2329..=0x232a
            | 0x2e80..=0xa4cf
            | 0xac00..=0xd7a3
            | 0xf900..=0xfaff
            | 0xfe10..=0xfe19
            | 0xfe30..=0xfe6f
            | 0xff00..=0xff60
            | 0xffe0..=0xffe6
            | 0x1f300..=0x1faff
            | 0x20000..=0x3fffd
    ) {
        2
    } else {
        1
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TokenKind {
    LParen,
    RParen,
    Colon,
    Quote,
    QuasiQuote,
    Unquote,
    UnquoteSplicing,
    At,
    Symbol(String),
    Integer(i128),
    UnsignedInteger(u128),
    Float(String),
    Char(char),
    String(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LexError {
    pub message: String,
    pub span: Span,
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}:{}: {}",
            self.span.line, self.span.column, self.message
        )
    }
}

impl std::error::Error for LexError {}

pub fn lex(source: &str) -> Result<Vec<Token>, LexError> {
    Lexer::new(source).run()
}

struct Lexer<'a> {
    source: &'a [u8],
    offset: usize,
    line: usize,
    column: usize,
}

impl<'a> Lexer<'a> {
    fn new(source: &'a str) -> Self {
        Self {
            source: source.as_bytes(),
            offset: 0,
            line: 1,
            column: 1,
        }
    }

    fn run(mut self) -> Result<Vec<Token>, LexError> {
        let mut tokens = Vec::new();
        while let Some(byte) = self.peek() {
            match byte {
                b' ' | b'\t' | b'\r' | b'\n' => {
                    self.advance();
                }
                b';' => {
                    self.skip_comment();
                }
                b'#' if self.source.get(self.offset + 1) == Some(&b'\\') => {
                    tokens.push(self.char_token()?)
                }
                b'#' if self.source.get(self.offset + 1).is_some_and(|next| {
                    next.is_ascii_alphabetic()
                        || *next == b'_'
                        || matches!(next, b'!' | b'+' | b'-' | b'*' | b'/' | b'%')
                        || matches!(next, b'&' | b'|' | b'^' | b'<' | b'>' | b'=')
                }) =>
                {
                    tokens.push(self.atom()?)
                }
                b'#' => {
                    self.skip_comment();
                }
                b'(' => tokens.push(self.one(TokenKind::LParen)),
                b')' => tokens.push(self.one(TokenKind::RParen)),
                b':' => tokens.push(self.one(TokenKind::Colon)),
                b'\'' => tokens.push(self.one(TokenKind::Quote)),
                b'`' => tokens.push(self.one(TokenKind::QuasiQuote)),
                b',' if self.source.get(self.offset + 1) == Some(&b'@') => {
                    self.advance();
                    tokens.push(self.one(TokenKind::UnquoteSplicing));
                }
                b',' => tokens.push(self.one(TokenKind::Unquote)),
                b'@' => tokens.push(self.one(TokenKind::At)),
                b'"' => tokens.push(self.string_token()?),
                _ => tokens.push(self.atom()?),
            }
        }
        Ok(tokens)
    }

    fn peek(&self) -> Option<u8> {
        self.source.get(self.offset).copied()
    }

    fn advance(&mut self) -> Option<u8> {
        let byte = self.peek()?;
        self.offset += 1;
        if byte == b'\n' {
            self.line += 1;
            self.column = 1;
        } else if byte & 0b1100_0000 != 0b1000_0000 {
            self.column += 1;
        }
        Some(byte)
    }

    fn one(&mut self, kind: TokenKind) -> Token {
        let start = self.offset;
        let line = self.line;
        let column = self.column;
        self.advance();
        Token {
            kind,
            span: Span::new(start, self.offset, line, column),
        }
    }

    fn skip_comment(&mut self) {
        while let Some(byte) = self.peek() {
            self.advance();
            if byte == b'\n' {
                break;
            }
        }
    }

    fn atom(&mut self) -> Result<Token, LexError> {
        let start = self.offset;
        let line = self.line;
        let column = self.column;
        while let Some(byte) = self.peek() {
            if byte.is_ascii_whitespace()
                || matches!(
                    byte,
                    b'(' | b')' | b':' | b'\'' | b'`' | b',' | b'"' | b'@' | b';'
                )
            {
                break;
            }
            self.advance();
        }
        let text = std::str::from_utf8(&self.source[start..self.offset]).unwrap();
        let kind = if let Some(value) = parse_integer_literal(text) {
            TokenKind::Integer(value)
        } else if let Some(value) = parse_unsigned_integer_literal(text) {
            TokenKind::UnsignedInteger(value)
        } else if (text.contains('.') || text.contains('e') || text.contains('E'))
            && text.parse::<f64>().is_ok()
        {
            TokenKind::Float(text.to_owned())
        } else {
            TokenKind::Symbol(text.to_owned())
        };
        Ok(Token {
            kind,
            span: Span::new(start, self.offset, line, column),
        })
    }

    fn string_token(&mut self) -> Result<Token, LexError> {
        let start = self.offset;
        let line = self.line;
        let column = self.column;
        self.advance(); // opening quote
        let mut value = String::new();
        loop {
            match self.advance() {
                None => {
                    return Err(LexError {
                        message: "unterminated string".into(),
                        span: Span::new(start, self.offset, line, column),
                    })
                }
                Some(b'"') => break,
                Some(b'\\') => match self.advance() {
                    Some(b'n') => value.push('\n'),
                    Some(b'r') => value.push('\r'),
                    Some(b't') => value.push('\t'),
                    Some(b'\\') => value.push('\\'),
                    Some(b'"') => value.push('"'),
                    Some(b'u') => {
                        let character = self.unicode_escape_character()?;
                        value.push(character);
                    }
                    Some(byte) => {
                        return Err(self.error(&format!("unknown escape \\{}", byte as char)))
                    }
                    None => return Err(self.error("unterminated string escape")),
                },
                Some(byte) if byte.is_ascii() => value.push(byte as char),
                Some(byte) => {
                    let rest = std::str::from_utf8(&self.source[self.offset - 1..])
                        .expect("lexer input is valid UTF-8");
                    let character = rest.chars().next().expect("non-empty UTF-8 suffix");
                    for _ in 1..character.len_utf8() {
                        self.advance();
                    }
                    value.push(character);
                    let _ = byte;
                }
            }
        }
        Ok(Token {
            kind: TokenKind::String(value),
            span: Span::new(start, self.offset, line, column),
        })
    }

    fn unicode_escape_character(&mut self) -> Result<char, LexError> {
        if self.peek() != Some(b'{') {
            return Err(self.error("Unicode escape must use the form \\u{...}"));
        }
        self.advance();
        let digits_start = self.offset;
        while let Some(byte) = self.peek() {
            if byte == b'}' {
                let digits = std::str::from_utf8(&self.source[digits_start..self.offset])
                    .expect("lexer input is valid UTF-8");
                self.advance();
                return decode_unicode_escape(digits).map_err(|message| self.error(message));
            }
            if !byte.is_ascii_hexdigit() {
                return Err(self.error("Unicode escape contains a non-hexadecimal digit"));
            }
            self.advance();
        }
        Err(self.error("unterminated Unicode escape"))
    }

    fn char_token(&mut self) -> Result<Token, LexError> {
        let start = self.offset;
        let line = self.line;
        let column = self.column;
        self.advance(); // '#'
        self.advance(); // '\\'
        let value_start = self.offset;
        while let Some(byte) = self.peek() {
            if byte.is_ascii_whitespace()
                || matches!(byte, b'(' | b')' | b'\'' | b'"' | b'@' | b'#' | b';')
            {
                break;
            }
            self.advance();
        }
        let text = std::str::from_utf8(&self.source[value_start..self.offset])
            .expect("lexer input is valid UTF-8");
        let character = match text {
            "space" => ' ',
            "newline" => '\n',
            "tab" => '\t',
            "return" => '\r',
            "null" => '\0',
            _ => {
                if let Some(digits) = text.strip_prefix("u{") {
                    let Some(digits) = digits.strip_suffix('}') else {
                        return Err(self.error("Unicode character escape must end with '}'"));
                    };
                    decode_unicode_escape(digits).map_err(|message| self.error(message))?
                } else {
                    let mut chars = text.chars();
                    let Some(character) = chars.next() else {
                        return Err(self.error("character literal is empty"));
                    };
                    if chars.next().is_some() {
                        return Err(self.error("character literal must contain one character"));
                    }
                    character
                }
            }
        };
        Ok(Token {
            kind: TokenKind::Char(character),
            span: Span::new(start, self.offset, line, column),
        })
    }

    fn error(&self, message: &str) -> LexError {
        LexError {
            message: message.to_owned(),
            span: Span::new(self.offset, self.offset, self.line, self.column),
        }
    }
}

fn decode_unicode_escape(digits: &str) -> Result<char, &'static str> {
    if digits.is_empty() {
        return Err("Unicode escape must contain at least one hexadecimal digit");
    }
    if digits.len() > 6 {
        return Err("Unicode escape contains too many hexadecimal digits");
    }
    let value = u32::from_str_radix(digits, 16)
        .map_err(|_| "Unicode escape contains an invalid hexadecimal value")?;
    char::from_u32(value).ok_or("Unicode escape is not a valid Unicode scalar value")
}

fn parse_integer_literal(text: &str) -> Option<i128> {
    let (negative, digits) = match text.strip_prefix('-') {
        Some(digits) => (true, digits),
        None => (false, text),
    };
    let (radix, digits) = if let Some(digits) = digits.strip_prefix("0x") {
        (16, digits)
    } else if let Some(digits) = digits.strip_prefix("0o") {
        (8, digits)
    } else if let Some(digits) = digits.strip_prefix("0b") {
        (2, digits)
    } else {
        (10, digits)
    };
    if digits.is_empty() || digits.starts_with('_') || digits.ends_with('_') {
        return None;
    }
    let digits = digits.replace('_', "");
    if negative {
        let magnitude = u128::from_str_radix(&digits, radix).ok()?;
        let minimum_magnitude = (i128::MAX as u128) + 1;
        if magnitude == minimum_magnitude {
            Some(i128::MIN)
        } else {
            i128::try_from(magnitude).ok()?.checked_neg()
        }
    } else {
        i128::from_str_radix(&digits, radix).ok()
    }
}

fn parse_unsigned_integer_literal(text: &str) -> Option<u128> {
    if text.starts_with('-') {
        return None;
    }
    let digits = text
        .strip_prefix("0x")
        .or_else(|| text.strip_prefix("0o"))
        .or_else(|| text.strip_prefix("0b"))
        .unwrap_or(text);
    let radix = if text.starts_with("0x") {
        16
    } else if text.starts_with("0o") {
        8
    } else if text.starts_with("0b") {
        2
    } else {
        10
    };
    if digits.is_empty() || digits.starts_with('_') || digits.ends_with('_') {
        return None;
    }
    u128::from_str_radix(&digits.replace('_', ""), radix).ok()
}

fn parse_typed_integer_atom(text: &str) -> Option<(Expr, &'static str)> {
    const SUFFIXES: [&str; 12] = [
        "i128", "u128", "isize", "usize", "i64", "u64", "i32", "u32", "i16", "u16", "i8", "u8",
    ];
    let (digits, suffix) = SUFFIXES
        .iter()
        .find_map(|suffix| text.strip_suffix(suffix).map(|digits| (digits, *suffix)))?;
    if digits.is_empty() || !digits.as_bytes().iter().any(u8::is_ascii_digit) {
        return None;
    }
    let literal = parse_integer_literal(digits)
        .map(Expr::Integer)
        .or_else(|| parse_unsigned_integer_literal(digits).map(Expr::UnsignedInteger))?;
    Some((literal, suffix))
}

fn parse_typed_float_atom(text: &str) -> Option<(Expr, &'static str)> {
    let (digits, suffix) = ["f32", "f64"]
        .iter()
        .find_map(|suffix| text.strip_suffix(suffix).map(|digits| (digits, *suffix)))?;
    if digits.is_empty() || !digits.as_bytes().iter().any(u8::is_ascii_digit) {
        return None;
    }
    digits
        .parse::<f64>()
        .ok()?
        .is_finite()
        .then(|| (Expr::Float(digits.to_owned()), suffix))
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Expr {
    List(Vec<Expr>),
    Block(Vec<Statement>),
    Symbol(String),
    /// An explicit, normalized user-call target, never reader syntax or a value.
    /// Kept distinct from builtin heads even when their spellings coincide.
    Function(String),
    Integer(i128),
    UnsignedInteger(u128),
    Float(String),
    Char(char),
    String(String),
    Loop(Vec<Statement>),
    Labeled {
        label: String,
        expression: Box<Expr>,
    },
    /// The generated-code sigil in source, e.g. `(@optional (: type T : name T?))`.
    At,
    Quote(Box<Expr>),
    QuasiQuote(Box<Expr>),
    Unquote(Box<Expr>),
    UnquoteSplicing(Box<Expr>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SpannedExpr {
    pub expr: Expr,
    pub span: Span,
    /// Exact source children in expression order. Preserved separately from
    /// `Expr` so later lowering can retain source locations without wrapping
    /// every syntax node in the public AST.
    pub children: Vec<SpannedExpr>,
}

/// Select the value expression most directly responsible for a statement-level
/// diagnostic, falling back to the complete source expression for forms whose
/// operands are not named in the statement syntax.
pub(crate) fn source_value_expression(expression: &SpannedExpr) -> &SpannedExpr {
    let Expr::List(items) = &expression.expr else {
        return expression;
    };
    let Some(Expr::Symbol(head)) = items.first() else {
        return expression;
    };
    let value_index = match head.as_str() {
        "#let" | "#let-mut" | "let" | "let-mut" | "#let-else" | "let-else" => Some(3),
        "#return" | "return" | "#break" | "break" | "#break-to" => Some(1),
        "#set" | "set" => Some(2),
        "#set-field" | "set-field" | "#set-index" | "set-index" => Some(3),
        "#pin-set-field" | "pin-set-field" => Some(4),
        _ => None,
    };
    value_index
        .and_then(|index| expression.children.get(index))
        .unwrap_or(expression)
}

pub(crate) fn source_value_span(expression: &SpannedExpr) -> Span {
    source_value_expression(expression).span
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseError {
    pub message: String,
    pub span: Span,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}:{}: {}",
            self.span.line, self.span.column, self.message
        )
    }
}

impl std::error::Error for ParseError {}

pub fn parse(source: &str) -> Result<Vec<SpannedExpr>, String> {
    let tokens = lex(source).map_err(|error| error.to_string())?;
    Parser::new(&tokens)
        .run()
        .map_err(|error| error.to_string())
}

/// Format canonical Lim source using the parsed S-expression structure.
pub fn format_source(source: &str) -> Result<String, String> {
    let expressions = parse(source)?;
    let comments = source_comments(source);
    let mut output = String::new();
    let mut comment_index = 0;
    let mut cursor = 0;
    for (index, expression) in expressions.iter().enumerate() {
        while let Some(comment) = comments.get(comment_index) {
            if comment.span.end > expression.span.start {
                break;
            }
            if comment.span.start >= cursor {
                if !output.is_empty() && !output.ends_with('\n') {
                    output.push('\n');
                }
                output.push_str(&comment.text);
                output.push('\n');
            }
            cursor = comment.span.end;
            comment_index += 1;
        }
        if !output.is_empty() && !output.ends_with('\n') {
            output.push('\n');
        }
        output.push_str(&pretty_spanned_expression(expression, source, &comments, 0));
        cursor = expression.span.end;
        let next_start = expressions
            .get(index + 1)
            .map_or(source.len(), |next| next.span.start);
        while let Some(comment) = comments.get(comment_index) {
            if comment.span.start < expression.span.end || comment.span.start >= next_start {
                break;
            }
            if comment.span.line == source_line_at(source, expression.span.end) {
                output.push(' ');
                output.push_str(&comment.text);
                output.push('\n');
            } else {
                if !output.ends_with('\n') {
                    output.push('\n');
                }
                output.push_str(&comment.text);
                output.push('\n');
            }
            cursor = comment.span.end;
            comment_index += 1;
        }
    }
    while let Some(comment) = comments.get(comment_index) {
        if comment.span.start >= cursor {
            if !output.is_empty() && !output.ends_with('\n') {
                output.push('\n');
            }
            output.push_str(&comment.text);
            output.push('\n');
        }
        comment_index += 1;
    }
    if output.is_empty() || !output.ends_with('\n') {
        output.push('\n');
    }
    Ok(output)
}

/// Format a source file and every transitively imported internal source file.
/// External imports are deliberately not opened or modified.
pub fn format_project_from_path(source_path: &Path) -> Result<Vec<PathBuf>, String> {
    fn discover(
        path: &Path,
        visited: &mut HashSet<PathBuf>,
        files: &mut Vec<(PathBuf, String)>,
    ) -> Result<(), String> {
        let path = fs::canonicalize(path)
            .map_err(|error| format!("cannot resolve source '{}': {error}", path.display()))?;
        if !visited.insert(path.clone()) {
            return Ok(());
        }
        let source = fs::read_to_string(&path)
            .map_err(|error| format!("cannot read source '{}': {error}", path.display()))?;
        let expressions = parse(&source).map_err(|error| format!("{}: {error}", path.display()))?;
        let mut imports = Vec::new();
        for expression in &expressions {
            collect_internal_imports(&expression.expr, &mut imports)?;
        }
        files.push((path.clone(), source));
        for import in imports {
            let imported = path.parent().unwrap_or_else(|| Path::new(".")).join(import);
            discover(&imported, visited, files)?;
        }
        Ok(())
    }

    fn collect_internal_imports(
        expression: &Expr,
        imports: &mut Vec<String>,
    ) -> Result<(), String> {
        let Expr::List(items) = expression else {
            return Ok(());
        };
        if let Some(specification) = import_form(expression)? {
            if !specification.external
                && standard_library::source(Path::new(specification.path)).is_none()
            {
                imports.push(specification.path.to_owned());
            }
            return Ok(());
        }
        if matches!(items.first(), Some(Expr::Symbol(keyword)) if keyword == "#cfg-if" || keyword == "#cfg-else")
        {
            for branch in items.iter().skip(
                if items.first().is_some_and(
                    |item| matches!(item, Expr::Symbol(keyword) if keyword == "#cfg-if"),
                ) {
                    2
                } else {
                    1
                },
            ) {
                collect_internal_imports(branch, imports)?;
            }
        }
        Ok(())
    }

    let mut files = Vec::new();
    discover(source_path, &mut HashSet::new(), &mut files)?;
    let mut formatted_files = Vec::with_capacity(files.len());
    for (path, source) in files {
        let formatted =
            format_source(&source).map_err(|error| format!("{}: {error}", path.display()))?;
        formatted_files.push((path, formatted));
    }
    let mut paths = Vec::with_capacity(formatted_files.len());
    for (path, formatted) in formatted_files {
        write_output_atomic(&path, formatted.as_bytes())
            .map_err(|error| format!("cannot write '{}': {error}", path.display()))?;
        paths.push(path);
    }
    Ok(paths)
}

#[derive(Clone)]
struct SourceComment {
    span: Span,
    text: String,
}

fn source_comments(source: &str) -> Vec<SourceComment> {
    let mut in_string = false;
    let mut escaped = false;
    let mut offset = 0;
    let mut line = 1;
    let mut column = 1;
    let mut comments = Vec::new();
    while offset < source.len() {
        let character = source[offset..].chars().next().unwrap();
        let width = character.len_utf8();
        if in_string {
            if escaped {
                escaped = false;
            } else if character == '\\' {
                escaped = true;
            } else if character == '"' {
                in_string = false;
            }
        } else if character == '#' && source.as_bytes().get(offset + 1) == Some(&b'\\') {
            offset += 2;
            column += 2;
            while offset < source.len() {
                let current = source[offset..].chars().next().unwrap();
                if current.is_whitespace()
                    || matches!(current, '(' | ')' | '\'' | '"' | '@' | '#' | ';')
                {
                    break;
                }
                offset += current.len_utf8();
                column += 1;
            }
            continue;
        } else if character == '"' {
            in_string = true;
        } else if character == ';' || (character == '#' && !is_hash_atom_start(source, offset)) {
            let start = offset;
            let start_line = line;
            let start_column = column;
            while offset < source.len() {
                let current = source[offset..].chars().next().unwrap();
                if current == '\n' {
                    break;
                }
                offset += current.len_utf8();
                column += 1;
            }
            comments.push(SourceComment {
                span: Span::new(start, offset, start_line, start_column),
                text: source[start..offset].to_owned(),
            });
            continue;
        }
        offset += width;
        if character == '\n' {
            line += 1;
            column = 1;
        } else {
            column += 1;
        }
    }
    comments
}

fn source_line_at(source: &str, offset: usize) -> usize {
    source[..offset.min(source.len())]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1
}

fn is_hash_atom_start(source: &str, offset: usize) -> bool {
    source.as_bytes().get(offset + 1).is_some_and(|next| {
        next.is_ascii_alphabetic()
            || *next == b'_'
            || matches!(next, b'!' | b'+' | b'-' | b'*' | b'/' | b'%')
            || matches!(next, b'&' | b'|' | b'^' | b'<' | b'>' | b'=')
    })
}

fn pretty_spanned_expression(
    expression: &SpannedExpr,
    source: &str,
    comments: &[SourceComment],
    indent: usize,
) -> String {
    // A colon-grouped list is parser sugar. Keep its spelling when formatting
    // instead of printing its desugared list-of-lists representation.
    if is_colon_list_source(expression, source) {
        return source[expression.span.start..expression.span.end].to_owned();
    }
    let has_comments = comments.iter().any(|comment| {
        comment.span.start > expression.span.start && comment.span.end < expression.span.end
    });
    if !has_comments
        && !expression
            .children
            .iter()
            .any(|child| contains_colon_list_source(child, source))
    {
        return pretty_expression(&expression.expr, indent);
    }
    match &expression.expr {
        Expr::List(items) => {
            if items.is_empty() {
                return "()".into();
            }
            let mut rendered = String::from("(");
            let mut cursor = expression.span.start + 1;
            for child in &expression.children {
                let gap_comments = comments
                    .iter()
                    .filter(|comment| {
                        comment.span.start >= cursor && comment.span.end <= child.span.start
                    })
                    .collect::<Vec<_>>();
                for comment in gap_comments {
                    if rendered == "(" || !rendered.ends_with('\n') {
                        rendered.push('\n');
                    }
                    if comment.span.start > expression.span.start + 1 {
                        rendered.push_str(&" ".repeat(indent + 2));
                    }
                    rendered.push_str(&comment.text);
                    rendered.push('\n');
                }
                if rendered == "(" || !rendered.ends_with('\n') {
                    rendered.push('\n');
                }
                rendered.push_str(&" ".repeat(indent + 2));
                rendered.push_str(&pretty_spanned_expression(
                    child,
                    source,
                    comments,
                    indent + 2,
                ));
                cursor = child.span.end;
            }
            for comment in comments.iter().filter(|comment| {
                comment.span.start >= cursor && comment.span.end < expression.span.end
            }) {
                if comment.span.line
                    == expression
                        .children
                        .last()
                        .map_or(0, |child| source_line_at(source, child.span.end))
                {
                    rendered.push(' ');
                } else {
                    rendered.push('\n');
                    rendered.push_str(&" ".repeat(indent + 2));
                }
                rendered.push_str(&comment.text);
                rendered.push('\n');
            }
            rendered.push_str(&" ".repeat(indent));
            rendered.push(')');
            rendered
        }
        Expr::Quote(_) | Expr::QuasiQuote(_) | Expr::Unquote(_) | Expr::UnquoteSplicing(_) => {
            let prefix = match expression.expr {
                Expr::Quote(_) => "'",
                Expr::QuasiQuote(_) => "`",
                Expr::Unquote(_) => ",",
                Expr::UnquoteSplicing(_) => ",@",
                _ => unreachable!(),
            };
            format!(
                "{prefix}{}",
                expression
                    .children
                    .first()
                    .map_or_else(String::new, |child| {
                        pretty_spanned_expression(child, source, comments, indent)
                    })
            )
        }
        _ => source[expression.span.start..expression.span.end].to_owned(),
    }
}

fn is_colon_list_source(expression: &SpannedExpr, source: &str) -> bool {
    matches!(expression.expr, Expr::List(_))
        && source[expression.span.start + 1..expression.span.end - 1]
            .trim_start()
            .starts_with(':')
}

fn contains_colon_list_source(expression: &SpannedExpr, source: &str) -> bool {
    is_colon_list_source(expression, source)
        || expression
            .children
            .iter()
            .any(|child| contains_colon_list_source(child, source))
}

fn pretty_expression(expression: &Expr, indent: usize) -> String {
    let Expr::List(items) = expression else {
        return expression_source(expression).unwrap_or_else(|_| "<?>".into());
    };
    if items.iter().all(|item| !matches!(item, Expr::List(_))) {
        return expression_source(expression).unwrap_or_else(|_| "<?>".into());
    }
    let padding = " ".repeat(indent + 2);
    let next = items
        .iter()
        .map(|item| format!("{}{}", padding, pretty_expression(item, indent + 2)))
        .collect::<Vec<_>>()
        .join("\n");
    format!("(\n{next}\n{})", " ".repeat(indent))
}

/// Rust-like scalar types understood by the first typed AST pass.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Type {
    Unit,
    Never,
    Bool,
    Char,
    I8,
    I16,
    I32,
    I64,
    I128,
    Isize,
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
    F32,
    F64,
    Reference {
        mutable: bool,
        target: Box<Type>,
    },
    /// A reference whose referent has been pinned in place. This is distinct
    /// from pinning the reference handle itself.
    PinnedReference {
        mutable: bool,
        target: Box<Type>,
    },
    /// Linear ownership of a stationary allocation. Moving this pointer-sized
    /// value transfers ownership without moving the allocation.
    PinOwned(Box<Type>),
    RawPointer {
        mutable: bool,
        target: Box<Type>,
    },
    /// Immutable, borrowed, dynamically-sized view of elements.
    Slice(Box<Type>),
    /// Exclusive, borrowed, dynamically-sized view of elements.
    MutableSlice(Box<Type>),
    /// Naturally aligned atomic scalar storage.
    Atomic(Box<Type>),
    Generic(String),
    Tuple(Vec<Type>),
    Array(Box<Type>, usize),
    Named(String),
}

impl Type {
    pub fn from_name(name: &str) -> Self {
        match name {
            "()" => Self::Unit,
            "!" => Self::Never,
            "bool" => Self::Bool,
            "char" => Self::Char,
            "i8" => Self::I8,
            "i16" => Self::I16,
            "i32" => Self::I32,
            "i64" => Self::I64,
            "i128" => Self::I128,
            "isize" => Self::Isize,
            "u8" => Self::U8,
            "u16" => Self::U16,
            "u32" => Self::U32,
            "u64" => Self::U64,
            "u128" => Self::U128,
            "usize" => Self::Usize,
            "f32" => Self::F32,
            "f64" => Self::F64,
            _ => Self::Named(name.to_owned()),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Parameter {
    pub name: String,
    pub ty: Type,
    pub mutable: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GeneratedFunctionSignature {
    pub name: String,
    pub parameters: Vec<Parameter>,
    pub return_type: Type,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Statement {
    Let {
        name: String,
        ty: Type,
        value: Expr,
        mutable: bool,
    },
    Destructure {
        pattern: Expr,
        ty: Type,
        value: Expr,
        mutable: bool,
    },
    LetElse {
        pattern: Expr,
        ty: Type,
        value: Expr,
        else_body: Vec<Statement>,
    },
    Assign {
        name: String,
        value: Expr,
    },
    ArrayAssign {
        name: String,
        index: Expr,
        value: Expr,
    },
    FieldAssign {
        name: String,
        field: String,
        value: Expr,
    },
    TupleAssign {
        name: String,
        index: usize,
        value: Expr,
    },
    EnumPayloadAssign {
        name: String,
        variant: String,
        index: usize,
        value: Expr,
    },
    While {
        condition: Expr,
        body: Vec<Statement>,
    },
    Loop {
        body: Vec<Statement>,
    },
    For {
        init: Box<Statement>,
        condition: Expr,
        step: Box<Statement>,
        body: Vec<Statement>,
    },
    Labeled {
        label: String,
        statement: Box<Statement>,
    },
    Break,
    BreakValue(Expr),
    BreakTo(String),
    BreakToValue {
        label: String,
        value: Expr,
    },
    Continue,
    ContinueTo(String),
    Return(Option<Expr>),
    Expr(Expr),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Function {
    pub name: String,
    pub external: bool,
    /// Calling this function requires an explicit unsafe region.
    pub unsafe_call: bool,
    pub calling_convention: CallingConvention,
    pub type_parameters: Vec<String>,
    pub parameters: Vec<Parameter>,
    pub return_type: Type,
    pub body: Vec<Statement>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CallingConvention {
    Lim,
    C,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Representation {
    Lim,
    C,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Field {
    pub name: String,
    pub ty: Type,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EnumVariant {
    pub name: String,
    pub fields: Vec<Type>,
    pub discriminant: u64,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ThreadProperty {
    Send,
    Sync,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Item {
    TypeAlias {
        name: String,
        type_parameters: Vec<String>,
        target: Type,
    },
    Function(Function),
    Struct {
        name: String,
        representation: Representation,
        type_parameters: Vec<String>,
        fields: Vec<Field>,
    },
    Enum {
        name: String,
        representation: Representation,
        type_parameters: Vec<String>,
        variants: Vec<EnumVariant>,
    },
    Let {
        name: String,
        ty: Type,
        value: Expr,
        mutable: bool,
    },
    Static {
        name: String,
        ty: Type,
        value: Expr,
    },
    UnsafeThreadAnnotation {
        property: ThreadProperty,
        type_name: String,
    },
    LinearAnnotation {
        type_name: String,
    },
    OpaqueAnnotation {
        type_name: String,
    },
    ThreadTask {
        name: String,
        worker: String,
        generated_functions: Vec<GeneratedFunctionSignature>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Program {
    pub items: Vec<Item>,
    pub(crate) source: Option<String>,
    pub(crate) source_files: Vec<SourceFile>,
    pub(crate) statement_spans: HashMap<(String, usize), Span>,
    pub(crate) statement_expressions: HashMap<(String, usize), SpannedExpr>,
    pub(crate) declaration_spans: HashMap<String, Span>,
    pub(crate) declaration_expressions: HashMap<String, SpannedExpr>,
    pub(crate) declaration_occurrences: HashMap<String, Vec<SpannedExpr>>,
    pub(crate) generated_source_invocations: HashMap<u32, Span>,
    pub(crate) syntax_bundle_uses: HashMap<Span, Vec<Span>>,
    pub(crate) async_functions: Vec<async_source::Source>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SourceFile {
    pub path: PathBuf,
    pub source: String,
}

/// Compile-time key/value settings used by `#cfg-*` forms.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompileConfig {
    values: HashMap<String, String>,
    module_paths: Vec<PathBuf>,
}

/// Versioned project settings consumed by the command-line build driver.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProjectMetadata {
    pub schema_version: u32,
    pub name: String,
    pub source_root: PathBuf,
    pub output_directory: PathBuf,
    pub module_paths: Vec<PathBuf>,
    pub target: Option<TargetDescription>,
    pub link_libraries: Vec<String>,
    pub link_objects: Vec<PathBuf>,
}

/// Read and validate a dependency-free, versioned `lim.project` manifest.
pub fn read_project(path: &Path) -> Result<ProjectMetadata, String> {
    let source = fs::read_to_string(path)
        .map_err(|error| format!("cannot read project manifest '{}': {error}", path.display()))?;
    let base = path.parent().unwrap_or_else(|| Path::new("."));
    let mut schema_version = None;
    let mut name = None;
    let mut source_root = None;
    let mut output_directory = None;
    let mut module_paths = Vec::new();
    let mut target = None;
    let mut link_libraries = Vec::new();
    let mut link_objects = Vec::new();
    let mut singular_keys = HashSet::new();
    for (line_number, line) in source.lines().enumerate() {
        let line = line.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        let (key, value) = line.split_once('=').ok_or_else(|| {
            format!(
                "{}:{}: manifest entries must use key = value",
                path.display(),
                line_number + 1
            )
        })?;
        let key = key.trim();
        let value = value.trim().trim_matches('"');
        let repeatable = matches!(key, "module-path" | "link-lib" | "link-object");
        if !repeatable && !singular_keys.insert(key.to_owned()) {
            return Err(format!(
                "{}:{}: duplicate manifest key '{key}'",
                path.display(),
                line_number + 1
            ));
        }
        match key {
            "schema-version" if value == "1" => schema_version = Some(1),
            "schema-version" => {
                return Err(format!(
                    "{}:{}: unsupported schema-version '{value}' (expected 1)",
                    path.display(),
                    line_number + 1
                ))
            }
            "name" if !value.is_empty() => name = Some(value.to_owned()),
            "source-root" if !value.is_empty() => source_root = Some(base.join(value)),
            "output-dir" if !value.is_empty() => output_directory = Some(base.join(value)),
            "target" if !value.is_empty() => target = Some(TargetDescription::parse(value)?),
            "module-path" if !value.is_empty() => module_paths.push(base.join(value)),
            "link-lib" if !value.is_empty() && !value.starts_with('-') => {
                link_libraries.push(value.to_owned())
            }
            "link-object" if !value.is_empty() => link_objects.push(base.join(value)),
            other => {
                return Err(format!(
                    "{}:{}: unknown manifest key '{other}'",
                    path.display(),
                    line_number + 1
                ))
            }
        }
    }
    let source_root = source_root.unwrap_or_else(|| base.to_path_buf());
    if !source_root.is_dir() {
        return Err(format!(
            "project source root '{}' is not an existing directory",
            source_root.display()
        ));
    }
    let source_root = source_root.canonicalize().map_err(|error| {
        format!(
            "cannot resolve project source root '{}': {error}",
            source_root.display()
        )
    })?;
    let mut canonical_roots = HashSet::new();
    for root in &mut module_paths {
        if !root.is_dir() {
            return Err(format!(
                "project module root '{}' is not an existing directory",
                root.display()
            ));
        }
        *root = root.canonicalize().map_err(|error| {
            format!(
                "cannot resolve project module root '{}': {error}",
                root.display()
            )
        })?;
        if !canonical_roots.insert(root.clone()) {
            return Err(format!(
                "duplicate project module root '{}'",
                root.display()
            ));
        }
    }
    let mut object_paths = HashSet::new();
    for object in &mut link_objects {
        if !object.is_file() {
            return Err(format!(
                "project link object '{}' is not an existing file",
                object.display()
            ));
        }
        *object = object.canonicalize().map_err(|error| {
            format!(
                "cannot resolve project link object '{}': {error}",
                object.display()
            )
        })?;
        if !object_paths.insert(object.clone()) {
            return Err(format!(
                "duplicate project link object '{}'",
                object.display()
            ));
        }
    }
    Ok(ProjectMetadata {
        schema_version: schema_version.ok_or_else(|| {
            format!(
                "project manifest '{}' has no schema-version = 1",
                path.display()
            )
        })?,
        name: name.ok_or_else(|| format!("project manifest '{}' has no name", path.display()))?,
        source_root,
        output_directory: output_directory.unwrap_or_else(|| base.join("build")),
        module_paths,
        target,
        link_libraries,
        link_objects,
    })
}

impl Default for CompileConfig {
    fn default() -> Self {
        let platform = env::consts::OS;
        let architecture = env::consts::ARCH;
        let target = match (architecture, platform) {
            ("x86_64", "linux") => "x86_64-unknown-linux-gnu",
            _ => "unknown",
        };
        Self {
            values: HashMap::from([
                ("platform".into(), platform.into()),
                ("os".into(), platform.into()),
                ("arch".into(), architecture.into()),
                ("target".into(), target.into()),
            ]),
            module_paths: Vec::new(),
        }
    }
}

impl CompileConfig {
    /// Set or override a configuration key, such as `feature=sorting` or
    /// `platform=linux`.
    pub fn set(&mut self, key: impl Into<String>, value: impl Into<String>) {
        self.values.insert(key.into(), value.into());
    }

    /// Add a stable search root for string paths in `#import` forms.
    pub fn add_module_path(&mut self, path: impl Into<PathBuf>) {
        self.module_paths.push(path.into());
    }
}

/// Parse a Lim program into the typed declaration AST.
///
/// Lim has one program syntax: builtin forms and operators use their `#`
/// prefix, and every non-external function ends with an explicit return.
/// The lower-level [`parse`] function remains available for raw S-expressions
/// that have not acquired a language-level meaning yet.
pub fn parse_program(source: &str) -> Result<Program, String> {
    let base =
        env::current_dir().map_err(|error| format!("cannot get current directory: {error}"))?;
    parse_program_in_directory(source, &base, None, &CompileConfig::default(), None)
        .map_err(String::from)
}

/// Parse a Lim program using explicit compile-time configuration values.
pub fn parse_program_with_config(source: &str, config: &CompileConfig) -> Result<Program, String> {
    let base =
        env::current_dir().map_err(|error| format!("cannot get current directory: {error}"))?;
    parse_program_in_directory(source, &base, None, config, None).map_err(String::from)
}

/// Parse a Lim program while resolving file imports relative to `source_path`.
pub fn parse_program_from_path(source: &str, source_path: &Path) -> Result<Program, String> {
    let base = source_path.parent().unwrap_or_else(|| Path::new("."));
    parse_program_in_directory(
        source,
        base,
        Some(source_path),
        &CompileConfig::default(),
        None,
    )
    .map_err(String::from)
}

/// Parse a Lim program while resolving imports and evaluating cfg forms using `config`.
pub fn parse_program_from_path_with_config(
    source: &str,
    source_path: &Path,
    config: &CompileConfig,
) -> Result<Program, String> {
    let base = source_path.parent().unwrap_or_else(|| Path::new("."));
    parse_program_in_directory(source, base, Some(source_path), config, None).map_err(String::from)
}

/// Parse a source file using cfg settings and a persistent generator cache.
pub fn parse_program_from_path_with_config_and_cache(
    source: &str,
    source_path: &Path,
    config: &CompileConfig,
    cache_directory: &Path,
) -> Result<Program, String> {
    let base = source_path.parent().unwrap_or_else(|| Path::new("."));
    parse_program_in_directory(
        source,
        base,
        Some(source_path),
        config,
        Some(cache_directory),
    )
    .map_err(String::from)
}

/// Compile a Lim source file to native assembly with recoverable diagnostics.
pub fn compile_source_to_assembly(
    source: &str,
    source_path: &Path,
    config: &CompileConfig,
    cache_directory: &Path,
    target: TargetDescription,
) -> Result<String, Diagnostic> {
    compile_source_to_assembly_for_output(
        source,
        source_path,
        config,
        cache_directory,
        target,
        None,
    )
}

/// As above, also protect every resolved source from output replacement.
pub fn compile_source_to_assembly_for_output(
    source: &str,
    source_path: &Path,
    config: &CompileConfig,
    cache_directory: &Path,
    target: TargetDescription,
    output: Option<&Path>,
) -> Result<String, Diagnostic> {
    compile_source_with_artifacts(
        source,
        source_path,
        config,
        cache_directory,
        target,
        output,
        None,
        false,
    )
}

/// Compile and materialize inspectable generators, sharing async capture analysis.
pub fn compile_source_with_generated_sources(
    source: &str,
    source_path: &Path,
    config: &CompileConfig,
    cache_directory: &Path,
    target: TargetDescription,
    output: Option<&Path>,
    generated_directory: &Path,
) -> Result<String, Diagnostic> {
    compile_source_with_artifacts(
        source,
        source_path,
        config,
        cache_directory,
        target,
        output,
        Some(generated_directory),
        false,
    )
}

/// Emit only executable-reachable functions after validating the full program.
/// Assembly/library emission should use `compile_source_with_generated_sources`.
pub fn compile_executable_source_with_generated_sources(
    source: &str,
    source_path: &Path,
    config: &CompileConfig,
    cache_directory: &Path,
    target: TargetDescription,
    output: Option<&Path>,
    generated_directory: &Path,
) -> Result<String, Diagnostic> {
    compile_source_with_artifacts(
        source,
        source_path,
        config,
        cache_directory,
        target,
        output,
        Some(generated_directory),
        true,
    )
}

fn compile_source_with_artifacts(
    source: &str,
    source_path: &Path,
    config: &CompileConfig,
    cache_directory: &Path,
    target: TargetDescription,
    output: Option<&Path>,
    generated_directory: Option<&Path>,
    executable: bool,
) -> Result<String, Diagnostic> {
    // Import loading lexes and parses the root source, preserving its spans.
    let prepared = prepare_program_syntax(
        source,
        source_path.parent().unwrap_or(Path::new(".")),
        Some(source_path),
        config,
        Some(cache_directory),
    )
    .map_err(|message| generator_diagnostic(message, source_path, source))?;
    let (program, capture_plans) = parse_prepared_program_with_capture_plans(&prepared)
        .map_err(|message| generator_diagnostic(message, source_path, source))?;
    if let Some(directory) = generated_directory {
        write_prepared_generated_sources(
            &prepared,
            directory,
            Some(cache_directory),
            &capture_plans,
        )
        .map_err(|message| generator_diagnostic(message, source_path, source))?;
    }
    let checked = typecheck::CheckedProgram::validate_with_span(&program).map_err(
        |(message, code, span, labels)| analysis_diagnostic(message, code, span, labels, &program),
    )?;
    if let Some(output) = output {
        for file in &program.source_files {
            if file.path.exists() {
                reject_source_output_collision(&file.path, output)
                    .map_err(|error| Diagnostic::new(DiagnosticCode::Link, error.to_string()))?;
            }
        }
    }
    let assembly = if executable {
        codegen::generate_checked_executable_assembly(&checked, target)
    } else {
        codegen::generate_checked_assembly(&checked, target)
    };
    assembly.map_err(|message| codegen_diagnostic(message, &program))
}

fn analysis_diagnostic(
    message: String,
    code: DiagnosticCode,
    structured_span: Option<Span>,
    structured_labels: Vec<(Span, String)>,
    program: &Program,
) -> Diagnostic {
    let mut diagnostic = Diagnostic::new(code, message.clone());
    if let Some(span) = structured_span {
        if let Some(file) = program.source_files.get(span.source_id as usize) {
            diagnostic = diagnostic
                .with_span(span)
                .with_source(file.path.display().to_string(), file.source.clone());
        }
    }
    for (span, label) in structured_labels {
        if let Some(file) = program.source_files.get(span.source_id as usize) {
            diagnostic.labels.push(DiagnosticLabel {
                message: label,
                span,
                source_name: Some(file.path.display().to_string()),
                source_text: Some(file.source.clone()),
            });
        }
    }
    let mut origin = structured_span;
    if let Some(span) = structured_span {
        for (usage, definitions) in &program.syntax_bundle_uses {
            if usage.source_id == span.source_id
                && usage.start <= span.start
                && span.end <= usage.end
            {
                for definition in definitions {
                    if let Some(file) = program.source_files.get(definition.source_id as usize) {
                        diagnostic.labels.push(DiagnosticLabel {
                            message: "syntax bundle defined here".into(),
                            span: *definition,
                            source_name: Some(file.path.display().to_string()),
                            source_text: Some(file.source.clone()),
                        });
                    }
                }
            }
        }
    }
    let mut seen = HashSet::new();
    while let Some(invocation) = origin
        .and_then(|span| program.generated_source_invocations.get(&span.source_id))
        .copied()
    {
        if !seen.insert(invocation.source_id) {
            break;
        }
        if let Some(file) = program.source_files.get(invocation.source_id as usize) {
            diagnostic.expansion_provenance.push(DiagnosticLabel {
                message: "generated from this invocation".into(),
                span: invocation,
                source_name: Some(file.path.display().to_string()),
                source_text: Some(file.source.clone()),
            });
        }
        origin = Some(invocation);
    }
    diagnostic
}

fn attach_generator_source(error: SourceError, source_files: &[SourceFile]) -> SourceError {
    error.attach(source_files)
}

fn generator_diagnostic(error: SourceError, root_path: &Path, root_source: &str) -> Diagnostic {
    let mut diagnostic = error.diagnostic();
    if diagnostic.source_name.is_none() {
        diagnostic.source_name = Some(root_path.display().to_string());
        diagnostic.source_text = Some(root_source.to_owned());
    }
    diagnostic
}

fn codegen_diagnostic(error: SourceError, program: &Program) -> Diagnostic {
    analysis_diagnostic(
        error.message,
        DiagnosticCode::Codegen,
        error.span,
        Vec::new(),
        program,
    )
}

/// Assemble and link native output, returning a structured link diagnostic on
/// linker failure. Shared libraries are added only for unresolved symbols or
/// explicitly requested libraries, not syscall-only code.
pub fn link_native_binary(
    assembly: &str,
    output: &Path,
    object_files: &[PathBuf],
    libraries: &[String],
    target: TargetDescription,
) -> Result<(), Diagnostic> {
    if target != TargetDescription::X86_64_SYSTEM_V {
        return Err(Diagnostic::new(
            DiagnosticCode::Link,
            "native linker has no implementation for the selected target",
        ));
    }
    let directory = output::StagingDirectory::beside(output).map_err(|error| {
        Diagnostic::new(
            DiagnosticCode::Link,
            format!("cannot stage output: {error}"),
        )
    })?;
    let staged_output = directory.0.join("binary");
    // Returning from main terminates the process, including io_uring workers;
    // thread-only SYS_exit can lose main's status when another task exits last.
    let entry = "\n.section .text\n.globl _start\n.type _start, @function\n_start:\n    xor ebp, ebp\n    and rsp, -16\n    call main\n    mov edi, eax\n    mov eax, 231\n    syscall\n    ud2\n.size _start, .-_start\n";
    let complete_assembly = format!("{assembly}{entry}");
    let build = || -> Result<Vec<u8>, String> {
        let assembled = native_assembly::assemble(&complete_assembly)?;
        let objects = object_files
            .iter()
            .map(|path| {
                let bytes = fs::read(path)
                    .map_err(|error| format!("cannot read object {}: {error}", path.display()))?;
                elf_object::relocatable(&bytes)
                    .map_err(|error| format!("invalid object {}: {error}", path.display()))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let linked = native_linker::link(&assembled, &objects, true)?;
        if linked.foreign.is_empty()
            && linked.foreign_got.is_empty()
            && linked.foreign_copy.is_empty()
            && linked.foreign_absolute.is_empty()
            && libraries.is_empty()
        {
            elf_writer::executable_with_sections(
                &linked.code,
                linked.entry,
                &linked.rodata,
                &linked.data,
            )
        } else {
            let interpreter = native_dynamic_linker();
            let needed = native_linker::resolve_libraries(
                &linked.foreign,
                &linked.foreign_got,
                &linked.foreign_copy,
                &linked.foreign_absolute,
                libraries,
                &interpreter,
            )?;
            elf_writer::dynamic_executable(linked, &needed, &interpreter)
        }
    };
    let image = build().map_err(|error| Diagnostic::new(DiagnosticCode::Link, error))?;
    fs::write(&staged_output, image).map_err(|error| {
        Diagnostic::new(
            DiagnosticCode::Link,
            format!("cannot write native ELF: {error}"),
        )
    })?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&staged_output, fs::Permissions::from_mode(0o755)).map_err(
            |error| {
                Diagnostic::new(
                    DiagnosticCode::Link,
                    format!("cannot make native ELF executable: {error}"),
                )
            },
        )?;
    }
    fs::rename(&staged_output, output).map_err(|error| {
        Diagnostic::new(
            DiagnosticCode::Link,
            format!("cannot publish output: {error}"),
        )
    })
}

fn native_dynamic_linker() -> String {
    env::var("LIM_DYNAMIC_LINKER")
        .ok()
        .filter(|path| Path::new(path).is_absolute())
        .or_else(|| {
            env::current_exe()
                .ok()
                .and_then(|path| fs::read(path).ok())
                .and_then(|bytes| elf_object::interpreter_path(&bytes).ok().flatten())
        })
        .unwrap_or_else(|| "/lib64/ld-linux-x86-64.so.2".to_owned())
}

/// Attach a Lim source span to a link failure when its unresolved symbol is
/// spelled in the root source. The assembly-only linking API cannot infer a
/// Lim location; CLI callers can supply their source after linking fails.
pub fn locate_link_diagnostic(mut diagnostic: Diagnostic, source: &str) -> Diagnostic {
    if diagnostic.code != DiagnosticCode::Link || diagnostic.span.is_some() {
        return diagnostic;
    }
    if let Some(mnemonic) = diagnostic
        .message
        .split("unsupported instruction '")
        .nth(1)
        .and_then(|rest| rest.split_once('\'').map(|(name, _)| name))
    {
        if let Some(at) = source.rfind(mnemonic) {
            let before = &source[..at];
            let line = before.bytes().filter(|byte| *byte == b'\n').count() + 1;
            let column = before.rsplit('\n').next().unwrap_or("").chars().count() + 1;
            diagnostic.span = Some(source_span_at(
                source,
                line,
                column,
                mnemonic.chars().count(),
            ));
            return diagnostic;
        }
    }
    let symbol = [
        "no linked shared library exports '",
        "undefined native symbol '",
        "duplicate native symbol '",
    ]
    .iter()
    .find_map(|prefix| diagnostic.message.strip_prefix(prefix))
    .and_then(|rest| rest.split_once('\'').map(|(name, _)| name));
    let Some(symbol) = symbol else {
        return diagnostic;
    };
    if let Ok(expressions) = parse(source) {
        diagnostic.span = expressions
            .iter()
            .filter_map(|expression| source_symbol_span(expression, symbol, true))
            .max_by_key(|span| span.start);
    }
    diagnostic
}

#[cfg(test)]
mod link_location_tests {
    use super::*;

    #[test]
    fn unresolved_symbol_highlights_the_call_not_its_declaration() {
        let source = "(#extern-fn #abi-c unavailable () u64)\n(#fn main () u64 (#return (#unsafe (#call unavailable (:)))))\n";
        let diagnostic = locate_link_diagnostic(
            Diagnostic::new(
                DiagnosticCode::Link,
                "no linked shared library exports 'unavailable' (assembly line 8)",
            ),
            source,
        );
        let span = diagnostic.span.unwrap();
        assert_eq!(span.line, 2);
        assert_eq!(&source[span.start..span.end], "unavailable");
    }

    #[test]
    fn unsupported_asm_instruction_highlights_its_source_text() {
        let source =
            "(#fn main () () (#unsafe (#asm () () \"vaddps ymm0, ymm1, ymm2\")) (#return ()))";
        let diagnostic = locate_link_diagnostic(
            Diagnostic::new(
                DiagnosticCode::Link,
                "assembly line 9: unsupported instruction 'vaddps'",
            ),
            source,
        );
        let span = diagnostic.span.unwrap();
        assert_eq!(&source[span.start..span.end], "vaddps");
    }
}

type AsyncCapturePlans = HashMap<(u32, usize, usize), HashMap<usize, HashSet<String>>>;

fn async_generated_source(
    invocation: &Expr,
    span: Span,
    capture_plans: Option<&AsyncCapturePlans>,
    copy_types: &HashSet<String>,
    type_environment: &async_fn::AsyncTypeEnvironment,
) -> Result<String, String> {
    let key = (span.source_id, span.start, span.end);
    let captures = capture_plans.and_then(|plans| plans.get(&key));
    let source = async_fn::generated_source_with_environment(
        invocation,
        captures,
        copy_types,
        type_environment,
    )?;
    // Private capture witnesses are checked too: freshen introduced match
    // bindings before analysis, without changing public parameter keys.
    // The uncollapsed helpers are private capture-analysis witnesses only.
    // Executable/inspectable output uses one dispatcher per concrete future.
    if capture_plans.is_some() {
        async_dispatch::collapse(&source, type_environment)
    } else {
        async_dispatch::hygienize_source(&source, type_environment)
    }
}

fn async_type_environment(expressions: &[SpannedExpr]) -> async_fn::AsyncTypeEnvironment {
    let mut environment = async_fn::AsyncTypeEnvironment::default();
    for expression in expressions {
        // Only declarations contributing to the environment need normalization.
        // In particular, do not copy an async invocation's entire function body.
        if !matches!(&expression.expr, Expr::List(items)
            if matches!(items.first(), Some(Expr::Symbol(head))
                if matches!(head.as_str(), "#fn" | "#unsafe-fn" | "#extern-fn" | "#enum" | "#type" | "#struct")))
        {
            continue;
        }
        // Async lowering needs function signatures, not a second parse of
        // every imported function body. Ordinary parsing validates the bodies.
        let signature = match &expression.expr {
            Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#fn" | "#unsafe-fn")) => {
                Expr::List(items.iter().take(4).cloned().collect())
            }
            other => other.clone(),
        };
        let normalized = normalize_keywords(signature);
        let parsed = match &normalized {
            Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "fn" | "unsafe-fn")) => {
                parse_function_parts(items, false, false).map(Item::Function)
            }
            _ => parse_item(&normalized),
        };
        let Ok(item) = parsed else {
            continue;
        };
        match item {
            Item::Enum { name, variants, .. } => {
                environment.enums.insert(
                    name,
                    variants
                        .into_iter()
                        .map(|variant| {
                            (
                                variant.name,
                                variant.fields.iter().map(type_source).collect(),
                            )
                        })
                        .collect(),
                );
            }
            Item::TypeAlias { name, target, .. } => {
                environment.aliases.insert(name, type_source(&target));
            }
            Item::Struct { name, fields, .. } => {
                environment.struct_field_order.insert(
                    name.clone(),
                    fields.iter().map(|field| field.name.clone()).collect(),
                );
                environment.struct_fields.insert(
                    name,
                    fields
                        .into_iter()
                        .map(|field| (field.name, type_source(&field.ty)))
                        .collect(),
                );
            }
            Item::Function(function) => {
                environment.function_parameter_order.insert(
                    function.name.clone(),
                    function
                        .parameters
                        .iter()
                        .map(|parameter| parameter.name.clone())
                        .collect(),
                );
                environment
                    .function_results
                    .insert(function.name.clone(), type_source(&function.return_type));
                environment.functions.insert(
                    function.name,
                    function
                        .parameters
                        .into_iter()
                        .map(|parameter| (parameter.name, type_source(&parameter.ty)))
                        .collect(),
                );
            }
            _ => {}
        }
    }
    environment
}

fn async_copy_type_names_from_items(items: &[Item]) -> HashSet<String> {
    let program = Program {
        items: items.to_vec(),
        source: None,
        source_files: Vec::new(),
        statement_spans: HashMap::new(),
        statement_expressions: HashMap::new(),
        declaration_spans: HashMap::new(),
        declaration_expressions: HashMap::new(),
        declaration_occurrences: HashMap::new(),
        generated_source_invocations: HashMap::new(),
        syntax_bundle_uses: HashMap::new(),
        async_functions: Vec::new(),
    };
    let linear_types = linearcheck::LinearTypes::from_program(&program);
    items
        .iter()
        .filter_map(|item| match item {
            Item::TypeAlias { name, .. } | Item::Struct { name, .. } | Item::Enum { name, .. } => {
                Some(name.clone())
            }
            _ => None,
        })
        .filter(|name| !linear_types.is_linear(&Type::Named(name.clone())))
        .collect()
}

fn async_copy_type_names(expressions: &[SpannedExpr]) -> HashSet<String> {
    let items = expressions
        .iter()
        .filter(|expression| {
            matches!(&expression.expr,
            Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(head))
                if matches!(head.as_str(), "#type" | "#struct" | "#enum" | "#linear")))
        })
        .filter_map(|expression| parse_item(&normalize_keywords(expression.expr.clone())).ok())
        .collect::<Vec<_>>();
    async_copy_type_names_from_items(&items)
}

fn async_copy_type_identity(types: &HashSet<String>) -> String {
    let mut names = types.iter().collect::<Vec<_>>();
    names.sort();
    format!("{names:?}")
}

fn async_type_environment_identity(environment: &async_fn::AsyncTypeEnvironment) -> String {
    let mut enums = environment.enums.iter().collect::<Vec<_>>();
    enums.sort_by(|left, right| left.0.cmp(right.0));
    let enums = enums
        .into_iter()
        .map(|(name, variants)| {
            let mut variants = variants.iter().collect::<Vec<_>>();
            variants.sort_by(|left, right| left.0.cmp(right.0));
            let variants = variants
                .into_iter()
                .map(|(name, fields)| format!("{name}:{fields:?}"))
                .collect::<Vec<_>>()
                .join(",");
            format!("{name}{{{variants}}}")
        })
        .collect::<Vec<_>>()
        .join(";");
    let mut aliases = environment.aliases.iter().collect::<Vec<_>>();
    aliases.sort_by(|left, right| left.0.cmp(right.0));
    let aliases = aliases
        .into_iter()
        .map(|(name, target)| format!("{name}={target}"))
        .collect::<Vec<_>>()
        .join(";");
    let mut functions = environment.functions.iter().collect::<Vec<_>>();
    functions.sort_by(|left, right| left.0.cmp(right.0));
    let functions = functions
        .into_iter()
        .map(|(name, parameters)| {
            let mut parameters = parameters.iter().collect::<Vec<_>>();
            parameters.sort_by(|left, right| left.0.cmp(right.0));
            let parameters = parameters
                .into_iter()
                .map(|(name, ty)| format!("{name}:{ty}"))
                .collect::<Vec<_>>()
                .join(",");
            format!(
                "{name}[order={:?}]({parameters})->{}",
                environment.function_parameter_order.get(name),
                environment
                    .function_results
                    .get(name)
                    .map_or("", String::as_str)
            )
        })
        .collect::<Vec<_>>()
        .join(";");
    let mut structs = environment.struct_fields.iter().collect::<Vec<_>>();
    structs.sort_by(|left, right| left.0.cmp(right.0));
    let structs = structs
        .into_iter()
        .map(|(name, fields)| {
            let mut fields = fields.iter().collect::<Vec<_>>();
            fields.sort_by(|left, right| left.0.cmp(right.0));
            let fields = fields
                .into_iter()
                .map(|(name, ty)| format!("{name}:{ty}"))
                .collect::<Vec<_>>()
                .join(",");
            format!(
                "{name}[order={:?}]{{{fields}}}",
                environment.struct_field_order.get(name)
            )
        })
        .collect::<Vec<_>>()
        .join(";");
    format!("enums:{enums};aliases:{aliases};functions:{functions};structs:{structs}")
}

struct AsyncCaptureInvocation {
    key: (u32, usize, usize),
    poll_name: String,
    pinned: bool,
}

fn async_capture_invocations(program: &Program) -> Vec<AsyncCaptureInvocation> {
    let mut invocations = Vec::new();
    for span in program.generated_source_invocations.values() {
        let Some(file) = program.source_files.get(span.source_id as usize) else {
            continue;
        };
        let Some(text) = file.source.get(span.start..span.end) else {
            continue;
        };
        let Ok(mut parsed) = parse(text) else {
            continue;
        };
        if parsed.len() != 1 {
            continue;
        }
        let expression = parsed.remove(0).expr;
        let Ok(normalized) = normalize_builtin_generator_invocation(&expression) else {
            continue;
        };
        let Expr::List(items) = &normalized else {
            continue;
        };
        let Some(Expr::Symbol(kind)) = items.get(1) else {
            continue;
        };
        let pinned = kind == "async-fn-pinned";
        if kind != "async-fn" && !pinned {
            continue;
        }
        let Some(Expr::List(names)) = items.get(2) else {
            continue;
        };
        let Some(Expr::Symbol(poll_name)) = names.get(4) else {
            continue;
        };
        invocations.push(AsyncCaptureInvocation {
            key: (span.source_id, span.start, span.end),
            poll_name: poll_name.clone(),
            pinned,
        });
    }
    invocations
}

fn async_capture_plans(
    program: &Program,
    live_parameters: &HashMap<String, HashSet<usize>>,
    invocations: &[AsyncCaptureInvocation],
) -> AsyncCapturePlans {
    let mut plans = HashMap::new();
    for invocation in invocations {
        let mut stages = HashMap::new();
        let prefix = format!(
            "{}{}-resume-",
            invocation.poll_name,
            if invocation.pinned { "-move" } else { "" }
        );
        for item in &program.items {
            let Item::Function(function) = item else {
                continue;
            };
            let Some(stage_index) = function
                .name
                .strip_prefix(&prefix)
                .and_then(|suffix| suffix.parse::<usize>().ok())
            else {
                continue;
            };
            let capture_count = function.parameters.len().saturating_sub(2);
            let live = live_parameters.get(&function.name);
            let captures = function
                .parameters
                .iter()
                .enumerate()
                .take(capture_count)
                .filter(|(parameter_index, _)| {
                    live.is_some_and(|live| live.contains(parameter_index))
                })
                .map(|(_, parameter)| parameter.name.clone())
                .collect();
            stages.insert(stage_index, captures);
        }
        plans.insert(invocation.key, stages);
    }
    plans
}

fn async_capture_plan_identity(plan: Option<&HashMap<usize, HashSet<String>>>) -> String {
    let Some(plan) = plan else {
        return "syntax-fallback".into();
    };
    let mut stages = plan.iter().collect::<Vec<_>>();
    stages.sort_by_key(|(stage, _)| **stage);
    stages
        .into_iter()
        .map(|(stage, names)| {
            let mut names = names.iter().collect::<Vec<_>>();
            names.sort();
            format!("{stage}:{names:?}")
        })
        .collect::<Vec<_>>()
        .join(";")
}

fn parse_program_in_directory(
    source: &str,
    base: &Path,
    source_path: Option<&Path>,
    config: &CompileConfig,
    cache_directory: Option<&Path>,
) -> Result<Program, SourceError> {
    parse_program_in_directory_with_capture_plans(
        source,
        base,
        source_path,
        config,
        cache_directory,
    )
    .map(|(program, _)| program)
}

fn parse_program_in_directory_with_capture_plans(
    source: &str,
    base: &Path,
    source_path: Option<&Path>,
    config: &CompileConfig,
    cache_directory: Option<&Path>,
) -> Result<(Program, AsyncCapturePlans), SourceError> {
    let prepared = prepare_program_syntax(source, base, source_path, config, cache_directory)?;
    parse_prepared_program_with_capture_plans(&prepared)
}

fn parse_prepared_program_with_capture_plans(
    prepared: &PreparedProgramSyntax,
) -> Result<(Program, AsyncCapturePlans), SourceError> {
    let capture_cache_key = format!(
        "lim-async-captures-v1\nimplementation={}\n{}",
        env!("LIM_BUILD_FINGERPRINT"),
        prepared.dependency_context
    );
    if let Some(directory) = prepared
        .capture_cache_directory
        .as_deref()
        .filter(|_| prepared.expressions.iter().any(is_async_invocation))
    {
        if let Some(plans) = generator::read_cached_expansion(directory, &capture_cache_key)
            .and_then(|forms| decode_async_capture_plans(&forms))
        {
            if let Ok(program) = parse_prepared_program_with_async_captures(prepared, Some(&plans))
            {
                crate::cache_report::record(
                    "async-captures",
                    &generator::cache_path(directory, &capture_cache_key),
                    &capture_cache_key,
                    "hit",
                );
                return Ok((program, plans));
            }
        }
    }
    let probe = parse_prepared_program_with_async_captures(prepared, None)?;
    let invocations = async_capture_invocations(&probe);
    if invocations.is_empty() {
        return Ok((probe, AsyncCapturePlans::new()));
    }
    let prefixes = invocations
        .iter()
        .map(|invocation| {
            format!(
                "{}{}-resume-",
                invocation.poll_name,
                if invocation.pinned { "-move" } else { "" }
            )
        })
        .collect::<Vec<_>>();
    let live_parameters = match typecheck::typed_async_capture_requirements(&probe, &prefixes) {
        Ok(live_parameters) => live_parameters,
        Err(_) => {
            // Keep parsing semantically invalid programs so callers can ask
            // the ordinary checked-program boundary for its source diagnostic.
            let no_typed_capture_plan = AsyncCapturePlans::new();
            let fallback =
                parse_prepared_program_with_async_captures(prepared, Some(&no_typed_capture_plan))?;
            return Ok((fallback, no_typed_capture_plan));
        }
    };
    let capture_plans = async_capture_plans(&probe, &live_parameters, &invocations);
    if capture_plans.is_empty() {
        return Ok((probe, capture_plans));
    }
    let program = parse_prepared_program_with_async_captures(prepared, Some(&capture_plans))?;
    if let Some(directory) = prepared.capture_cache_directory.as_deref() {
        crate::cache_report::record(
            "async-captures",
            &generator::cache_path(directory, &capture_cache_key),
            &capture_cache_key,
            "missing-or-invalid",
        );
        generator::write_cached_expansion(
            directory,
            &capture_cache_key,
            &encode_async_capture_plans(&capture_plans),
        );
    }
    Ok((program, capture_plans))
}

fn encode_async_capture_plans(plans: &AsyncCapturePlans) -> Vec<Expr> {
    let mut entries = plans.iter().collect::<Vec<_>>();
    entries.sort_by_key(|(key, _)| **key);
    entries
        .into_iter()
        .map(|((source_id, start, end), stages)| {
            let mut stages = stages.iter().collect::<Vec<_>>();
            stages.sort_by_key(|(stage, _)| **stage);
            Expr::List(vec![
                Expr::List(vec![
                    Expr::Integer(i128::from(*source_id)),
                    Expr::Integer(*start as i128),
                    Expr::Integer(*end as i128),
                ]),
                Expr::List(
                    stages
                        .into_iter()
                        .map(|(stage, captures)| {
                            let mut captures = captures
                                .iter()
                                .cloned()
                                .map(Expr::Symbol)
                                .collect::<Vec<_>>();
                            captures.sort_by(|left, right| match (left, right) {
                                (Expr::Symbol(left), Expr::Symbol(right)) => left.cmp(right),
                                _ => unreachable!(),
                            });
                            Expr::List(vec![Expr::Integer(*stage as i128), Expr::List(captures)])
                        })
                        .collect(),
                ),
            ])
        })
        .collect()
}

fn decode_async_capture_plans(forms: &[Expr]) -> Option<AsyncCapturePlans> {
    fn index(expression: &Expr) -> Option<usize> {
        let Expr::Integer(value) = expression else {
            return None;
        };
        usize::try_from(*value).ok()
    }
    let mut plans = AsyncCapturePlans::new();
    if forms.is_empty() {
        return None;
    }
    for form in forms {
        let Expr::List(entry) = form else {
            return None;
        };
        let [Expr::List(key), Expr::List(stages)] = entry.as_slice() else {
            return None;
        };
        let [source_id, start, end] = key.as_slice() else {
            return None;
        };
        let key = (
            u32::try_from(index(source_id)?).ok()?,
            index(start)?,
            index(end)?,
        );
        if key.1 > key.2 {
            return None;
        }
        let mut decoded_stages = HashMap::new();
        for stage in stages {
            let Expr::List(stage) = stage else {
                return None;
            };
            let [stage, Expr::List(names)] = stage.as_slice() else {
                return None;
            };
            let mut captures = HashSet::new();
            for name in names {
                let Expr::Symbol(name) = name else {
                    return None;
                };
                if !captures.insert(name.clone()) {
                    return None;
                }
            }
            if decoded_stages.insert(index(stage)?, captures).is_some() {
                return None;
            }
        }
        if plans.insert(key, decoded_stages).is_some() {
            return None;
        }
    }
    Some(plans)
}

struct PreparedProgramSyntax {
    bundles: syntax_bundle::Bundles,
    capture_cache_directory: Option<PathBuf>,
    root_source: String,
    expressions: Vec<SpannedExpr>,
    source_files: Vec<SourceFile>,
    dependency_context: String,
    user_generated: Vec<Expr>,
    async_copy_types: HashSet<String>,
    async_types: async_fn::AsyncTypeEnvironment,
    worker_functions: HashMap<String, Function>,
}

fn prepare_program_syntax(
    source: &str,
    base: &Path,
    source_path: Option<&Path>,
    config: &CompileConfig,
    cache_directory: Option<&Path>,
) -> Result<PreparedProgramSyntax, SourceError> {
    let (loaded, source_files) = load_imports_with_sources(source, base, source_path, config)?;
    let dependency_context = generator_dependency_context(&loaded, config);
    let mut bundles = syntax_bundle::Bundles::default();
    let loaded = bundles
        .expand(loaded, false)
        .map_err(|error| error.attach(&source_files))?;
    let (expanded, user_generated) = generator::expand_with_generated_cached_with_context(
        loaded,
        cache_directory,
        &dependency_context,
    )
    .map_err(|error| attach_generator_source(error, &source_files))?;
    let expressions = expand_cfg_forms(expanded, config)
        .map_err(|error| attach_generator_source(error, &source_files))?;
    let expressions = bundles
        .expand(expressions, true)
        .map_err(|error| error.attach(&source_files))?;
    // Generated declarations and cfg selection are already expanded here, so
    // detect async users after those passes rather than from the root file.
    let needs_async = expressions.iter().any(is_async_invocation);
    let (async_copy_types, async_types) = if needs_async {
        (
            async_copy_type_names(&expressions),
            async_type_environment(&expressions),
        )
    } else {
        (HashSet::new(), async_fn::AsyncTypeEnvironment::default())
    };
    let needs_workers = expressions.iter().any(is_thread_spawn_invocation);
    let worker_functions = expressions
        .iter()
        .filter(|_| needs_workers)
        .filter_map(|expression| {
            match parse_item(&normalize_keywords(expression.expr.clone())).ok()? {
                Item::Function(function) if !function.external => {
                    Some((function.name.clone(), function))
                }
                _ => None,
            }
        })
        .collect();
    Ok(PreparedProgramSyntax {
        bundles,
        capture_cache_directory: cache_directory.map(Path::to_path_buf),
        root_source: source.to_owned(),
        expressions,
        source_files,
        dependency_context,
        user_generated,
        async_copy_types,
        async_types,
        worker_functions,
    })
}

fn parse_prepared_program_with_async_captures(
    prepared: &PreparedProgramSyntax,
    capture_plans: Option<&AsyncCapturePlans>,
) -> Result<Program, SourceError> {
    parse_prepared_program_items(prepared, capture_plans, true)
}

/// Declaration input for original-body planning. Async interfaces live in an
/// explicit deferred registry, not invented executable/extern declarations.
/// Ordinary bodies are parsed but stay unnormalized until layout completion;
/// the planner checks only the source models attached to this context.
fn parse_prepared_async_declarations(
    prepared: &PreparedProgramSyntax,
) -> Result<Program, SourceError> {
    parse_prepared_program_items(prepared, None, false)
}

fn parse_prepared_program_items(
    prepared: &PreparedProgramSyntax,
    capture_plans: Option<&AsyncCapturePlans>,
    expand_async: bool,
) -> Result<Program, SourceError> {
    let expressions = prepared.expressions.clone();
    let mut source_files = prepared.source_files.clone();
    let async_copy_types = &prepared.async_copy_types;
    let async_types = &prepared.async_types;
    let mut items = Vec::with_capacity(expressions.len());
    let mut statement_spans = HashMap::new();
    let mut statement_expressions = HashMap::new();
    let mut declaration_spans = HashMap::new();
    let mut declaration_expressions = HashMap::new();
    let mut declaration_occurrences: HashMap<String, Vec<SpannedExpr>> = HashMap::new();
    let mut generated_source_invocations = HashMap::new();
    let mut async_functions = Vec::new();
    let worker_functions = &prepared.worker_functions;
    for mut expression in expressions {
        if !expand_async && is_async_invocation(&expression) {
            continue;
        }
        let original_async = async_source::Source::from_invocation(&expression)?;
        validate_prefixed_forms(&expression.expr).map_err(|error| {
            attach_span_to_source_error_kind(error, expression.span, &source_files, "parse error: ")
        })?;
        normalize_match_case_forms(&mut expression).map_err(|(error, span)| {
            attach_span_to_source_error_kind(error, span, &source_files, "parse error: ")
        })?;
        let form_span = expression.span;
        let invocation_text = source_files
            .get(form_span.source_id as usize)
            .and_then(|file| file.source.get(form_span.start..form_span.end))
            .unwrap_or("")
            .trim_start();
        let is_generated_output =
            expression.children.is_empty() && invocation_text.starts_with("(@");
        if is_generated_output {
            let generated_text = expression_source(&expression.expr)?;
            let source_id = u32::try_from(source_files.len())
                .map_err(|_| "too many source files while tracking generator output".to_owned())?;
            let mut parsed = parse(&generated_text)?;
            if parsed.len() != 1 {
                return Err("generator output did not parse as exactly one source form".into());
            }
            let mut generated_expression = parsed.remove(0);
            set_source_id(&mut generated_expression, source_id);
            source_files.push(SourceFile {
                path: PathBuf::from(format!(
                    "<generated from {}:{}:{}>",
                    source_files.get(form_span.source_id as usize).map_or_else(
                        || "<source>".to_owned(),
                        |file| file.path.display().to_string()
                    ),
                    form_span.line,
                    form_span.column
                )),
                source: generated_text,
            });
            generated_source_invocations.insert(source_id, form_span);
            expression = generated_expression;
        }
        let original_async = match original_async {
            Some(source) => Some(source),
            None => async_source::Source::from_invocation(&expression)?,
        };
        if let Some(source) = original_async {
            async_functions.push(source);
        }
        collect_function_statement_spans(
            &expression,
            &mut statement_spans,
            &mut statement_expressions,
        );
        let normalized_invocation = normalize_builtin_generator_invocation(&expression.expr)
            .map_err(|error| {
                attach_span_to_source_error_kind(
                    error,
                    form_span,
                    &source_files,
                    "generator error: ",
                )
            })?;
        // Keep the original source tree for diagnostics without recursively
        // copying it. Normalization below works on its own invocation tree.
        let source_expression = expression;
        let mut expression = normalize_keywords(normalized_invocation.clone());
        normalize_match_cases_expr(&mut expression);
        let mut generated_declarations = HashMap::new();
        if let Expr::List(forms) = &expression {
            if matches!(forms.first(), Some(Expr::At)) {
                let kind = forms.get(1).and_then(|form| match form {
                    Expr::Symbol(kind) => Some(kind.as_str()),
                    _ => None,
                });
                if matches!(
                    kind,
                    Some(
                        "thread-spawn"
                            | "optional"
                            | "result"
                            | "vec"
                            | "vec-alloc"
                            | "vec-sort"
                            | "async-fn"
                            | "async-fn-pinned"
                    )
                ) {
                    let generated_text = if matches!(kind, Some("async-fn" | "async-fn-pinned")) {
                        async_generated_source(
                            &normalized_invocation,
                            form_span,
                            capture_plans,
                            &async_copy_types,
                            &async_types,
                        )
                        .ok()
                    } else {
                        kind.and_then(|kind| {
                            materialize_builtin_generated_source(kind, forms, &worker_functions)
                                .ok()
                        })
                    };
                    if let Some(generated_text) = generated_text {
                        let source_id = u32::try_from(source_files.len()).map_err(|_| {
                            "too many source files while tracking builtin output".to_owned()
                        })?;
                        let source_path = format!(
                            "<generated from {}:{}:{}>",
                            source_files.get(form_span.source_id as usize).map_or_else(
                                || "<source>".to_owned(),
                                |file| file.path.display().to_string()
                            ),
                            form_span.line,
                            form_span.column
                        );
                        let mut generated_forms = parse(&generated_text)?;
                        for generated_form in &mut generated_forms {
                            set_source_id(generated_form, source_id);
                            normalize_match_case_forms(generated_form)
                                .map_err(|(error, _)| error)?;
                            collect_function_statement_spans(
                                generated_form,
                                &mut statement_spans,
                                &mut statement_expressions,
                            );
                            let parsed_item =
                                parse_item(&normalize_keywords(generated_form.expr.clone()));
                            if let Ok(item) = parsed_item {
                                for name in item_declared_names(&item) {
                                    generated_declarations.insert(name, generated_form.clone());
                                }
                            }
                        }
                        source_files.push(SourceFile {
                            path: PathBuf::from(source_path),
                            source: generated_text,
                        });
                        generated_source_invocations.insert(source_id, form_span);
                    }
                }
            }
        }
        let parsed_items = if let Expr::List(forms) = &expression {
            if matches!(forms.first(), Some(Expr::At)) {
                let generated = if matches!(forms.get(1), Some(Expr::Symbol(kind)) if kind == "async-fn" || kind == "async-fn-pinned")
                {
                    if let Some(error) = async_contract::check(&source_expression, &async_types) {
                        return Err(attach_span_to_source_error_kind(
                            error.message,
                            error.span,
                            &source_files,
                            "generator error: ",
                        ));
                    }
                    if let Err(error) = async_cfg::check(&source_expression, &async_types) {
                        return Err(attach_span_to_source_error_kind(
                            error.message,
                            error.span,
                            &source_files,
                            "generator error: ",
                        ));
                    }
                    async_generated_source(
                        &normalized_invocation,
                        form_span,
                        capture_plans,
                        &async_copy_types,
                        &async_types,
                    )
                    .and_then(|source| parse_generated_source_items(&source))
                } else {
                    parse_generated_items(forms)
                };
                generated.map_err(|error| {
                    let is_async_fn = matches!(forms.get(1), Some(Expr::Symbol(kind)) if kind == "async-fn" || kind == "async-fn-pinned");
                    let escaped_name = error.split_once("unknown value '")
                        .and_then(|(_, rest)| rest.split_once("' outside").map(|(name, _)| name));
                    let error_span = if is_async_fn && escaped_name.is_some() {
                        source_value_symbol_span(&source_expression, escaped_name.unwrap())
                            .unwrap_or(form_span)
                    } else if is_async_fn && error.contains("shadowing") {
                        let details = match &normalized_invocation {
                            Expr::List(invocation) => invocation.get(4),
                            _ => None,
                        }
                        .and_then(|function| async_function_shadowing(function).ok().flatten());
                        details
                            .and_then(|(name, statement_index)| {
                                let statement = statement_index.and_then(|index| {
                                    async_function_statement_source(&source_expression, index)
                                })?;
                                shadow_binding_span(statement.span, &name, &source_files)
                            })
                            .unwrap_or(form_span)
                    } else if is_async_fn
                        && async_lowering_statement_index(&error).is_some()
                    {
                        let statement_index = async_lowering_statement_index(&error)
                            .expect("checked async statement marker");
                        match &normalized_invocation {
                            Expr::List(invocation) => invocation.get(4),
                            _ => None,
                        }
                        .and_then(|_| {
                            async_function_statement_source(&source_expression, statement_index)
                        })
                        .and_then(|statement| {
                            if error.contains("body cannot return")
                                || error.contains("does not support body returns")
                            {
                                if let Some(span) =
                                    source_form_head_span(statement, &["#return"])
                                {
                                    return Some(span);
                                }
                            }
                            let await_index = if error.contains(
                                "nested #await requires an explicit result type",
                            ) {
                                1
                            } else if error.contains(
                                "awaited #let-else #for initialization cannot yet be combined with suspension",
                            ) {
                                1
                            } else {
                                0
                            };
                            source_form_head_span_nth(statement, &["#await"], await_index)
                                .or_else(|| source_form_head_span_nth(statement, &["#await"], 0))
                                .or(Some(statement.span))
                        })
                        .unwrap_or(form_span)
                    } else if is_async_fn && (error.contains("await") || error.contains("capture")) {
                        source_form_head_span(&source_expression, &["#await"])
                            .unwrap_or(form_span)
                    } else {
                        form_span
                    };
                    attach_span_to_source_error_kind(
                        format!(
                            "{error} while expanding generated declaration {}",
                            expression_source(&expression).unwrap_or_else(|_| "<?>".into())
                        ),
                        error_span,
                        &source_files,
                        "generator error: ",
                    )
                })?
            } else {
                vec![parse_item(&expression).map_err(|error| {
                    let error_span =
                        precise_parse_error_span(&source_expression, &error).unwrap_or(form_span);
                    attach_span_to_source_error_kind(
                        error,
                        error_span,
                        &source_files,
                        "parse error: ",
                    )
                })?]
            }
        } else {
            vec![parse_item(&expression).map_err(|error| {
                attach_span_to_source_error_kind(error, form_span, &source_files, "parse error: ")
            })?]
        };
        for item in parsed_items {
            for name in item_declared_names(&item) {
                let expression = generated_declarations
                    .get(&name)
                    .unwrap_or(&source_expression)
                    .clone();
                declaration_occurrences
                    .entry(name.clone())
                    .or_default()
                    .push(expression.clone());
                declaration_spans.entry(name.clone()).or_insert(form_span);
                declaration_expressions.entry(name).or_insert(expression);
            }
            items.push(item);
        }
    }
    for item in &items {
        for name in item_declared_names(item) {
            if let Some(definition) = prepared.bundles.definitions.get(&name) {
                return Err(SourceError::new(
                    format!("declaration '{name}' conflicts with a syntax bundle"),
                    DiagnosticCode::Parse,
                )
                .at(*declaration_spans.get(&name).unwrap_or(&definition.span))
                .with_label(definition.span, "syntax bundle defined here")
                .attach(&source_files));
            }
        }
    }
    rename_shadowed_locals(
        &mut items,
        &statement_spans,
        &declaration_spans,
        &source_files,
        &prepared.bundles.definitions,
    )?;
    synthesize_thread_join_results(&mut items, &declaration_spans, &source_files)?;
    let mut items = specialize_generic_types(
        items,
        &statement_spans,
        &statement_expressions,
        &declaration_spans,
        &declaration_expressions,
        &source_files,
    )?;
    if expand_async {
        normalize_function_calls(
            &mut items,
            &statement_spans,
            &statement_expressions,
            &declaration_spans,
            &declaration_expressions,
            &source_files,
        )?;
        normalize_struct_literals(
            &mut items,
            &statement_spans,
            &statement_expressions,
            &declaration_spans,
            &declaration_expressions,
            &source_files,
        )?;
    }
    Ok(Program {
        items,
        source: Some(prepared.root_source.clone()),
        source_files,
        statement_spans,
        statement_expressions,
        declaration_spans,
        declaration_expressions,
        declaration_occurrences,
        generated_source_invocations,
        syntax_bundle_uses: prepared.bundles.uses.clone(),
        async_functions,
    })
}

fn item_declared_names(item: &Item) -> Vec<String> {
    match item {
        Item::LinearAnnotation { type_name } => vec![format!("$linear:{type_name}")],
        Item::OpaqueAnnotation { type_name } => vec![format!("$opaque:{type_name}")],
        Item::Function(function) => vec![function.name.clone()],
        Item::Struct { name, .. }
        | Item::Enum { name, .. }
        | Item::TypeAlias { name, .. }
        | Item::ThreadTask { name, .. }
        | Item::Static { name, .. }
        | Item::Let { name, .. } => vec![name.clone()],
        Item::UnsafeThreadAnnotation {
            type_name,
            property,
        } => {
            vec![format!("$unsafe-impl:{property:?}:{type_name}")]
        }
    }
}

fn synthesize_thread_join_results(
    items: &mut Vec<Item>,
    declaration_spans: &HashMap<String, Span>,
    source_files: &[SourceFile],
) -> Result<(), SourceError> {
    let tasks = items
        .iter()
        .filter_map(|item| match item {
            Item::ThreadTask {
                name,
                worker,
                generated_functions,
            } => Some((name.clone(), worker.clone(), generated_functions.clone())),
            _ => None,
        })
        .collect::<Vec<_>>();
    for (name, worker, declared_generated_functions) in tasks {
        let Some(worker_function) = items.iter().find_map(|item| match item {
            Item::Function(function) if function.name == worker => Some(function.clone()),
            _ => None,
        }) else {
            continue;
        };
        let expected_generated_functions = thread_task_function_signatures(&name, &worker_function);
        if !declared_generated_functions.is_empty()
            && declared_generated_functions != expected_generated_functions
        {
            let error = format!(
                "generated function signatures for '#thread-task {name}' do not match worker '{worker}'"
            );
            return Err(declaration_spans
                .get(&name)
                .map_or(error.clone().into(), |span| {
                    attach_span_to_source_error(error, *span, source_files)
                }));
        }
        for item in items.iter_mut() {
            if let Item::ThreadTask {
                name: task_name,
                generated_functions,
                ..
            } = item
            {
                if task_name == &name {
                    *generated_functions = expected_generated_functions.clone();
                }
            }
        }
        let return_type = worker_function.return_type.clone();
        for expected in thread_task_generated_enums(&name, return_type) {
            let Item::Enum {
                name: generated_name,
                ..
            } = &expected
            else {
                unreachable!("thread task generated item is an enum")
            };
            if let Some(existing) = items.iter().find(|item| {
                matches!(item, Item::Enum { name: existing_name, .. } if existing_name == generated_name)
            }) {
                if existing != &expected {
                    let error = format!(
                        "explicit generated thread type '{}' does not match its #thread-task declaration",
                        generated_name
                    );
                    return Err(declaration_spans.get(&name).map_or(error.clone().into(), |span| {
                        attach_span_to_source_error(error, *span, source_files)
                    }));
                }
            } else {
                items.push(expected);
            }
        }
    }
    Ok(())
}

fn thread_task_function_signatures(
    name: &str,
    worker: &Function,
) -> Vec<GeneratedFunctionSignature> {
    let spawn_parameters = worker
        .parameters
        .iter()
        .map(|parameter| Parameter {
            name: parameter.name.clone(),
            ty: parameter.ty.clone(),
            mutable: false,
        })
        .collect();
    vec![
        GeneratedFunctionSignature {
            name: format!("{name}-spawn"),
            parameters: spawn_parameters,
            return_type: Type::Named(format!("{name}-spawn-result")),
        },
        GeneratedFunctionSignature {
            name: format!("{name}-join"),
            parameters: vec![Parameter {
                name: "task".into(),
                ty: Type::Named(name.into()),
                mutable: false,
            }],
            return_type: Type::Named(format!("{name}-join-result")),
        },
    ]
}

#[test]
fn synthesized_thread_calls_require_named_arguments() {
    let prefix =
        "(#fn worker ((left u64) (right u64)) u64 (#return left)) (@thread-spawn (: task Task : worker worker))";
    let program = |call: &str| {
        format!(
            "{prefix} (#fn main () () (#let result Task-spawn-result {call}) (#return (#panic)))"
        )
    };
    assert!(parse_program(&program("(#call Task-spawn (: right 2u64 : left 1u64))")).is_ok());
    for call in [
        "(Task-spawn 1u64 2u64)",
        "(#call Task-spawn (: left 1u64))",
        "(#call Task-spawn (: left 1u64 : left 2u64))",
        "(#call Task-spawn (: left 1u64 : wrong 2u64))",
    ] {
        assert!(parse_program(&program(call)).is_err(), "{call}");
    }
}

fn thread_task_generated_enums(name: &str, return_type: Type) -> Vec<Item> {
    let spawn_error_name = format!("{name}-spawn-error");
    vec![
        Item::Enum {
            name: spawn_error_name.clone(),
            representation: Representation::Lim,
            type_parameters: Vec::new(),
            variants: vec![
                EnumVariant {
                    name: format!("{name}-spawn-allocation-error"),
                    fields: Vec::new(),
                    discriminant: 0,
                },
                EnumVariant {
                    name: format!("{name}-spawn-creation-error"),
                    fields: Vec::new(),
                    discriminant: 1,
                },
            ],
        },
        Item::Enum {
            name: format!("{name}-spawn-result"),
            representation: Representation::Lim,
            type_parameters: Vec::new(),
            variants: vec![
                EnumVariant {
                    name: format!("{name}-spawn-ok"),
                    fields: vec![Type::Named(name.into())],
                    discriminant: 0,
                },
                EnumVariant {
                    name: format!("{name}-spawn-error"),
                    fields: vec![Type::Named(spawn_error_name)],
                    discriminant: 1,
                },
            ],
        },
        Item::Enum {
            name: format!("{name}-join-result"),
            representation: Representation::Lim,
            type_parameters: Vec::new(),
            variants: vec![
                EnumVariant {
                    name: format!("{name}-join-ok"),
                    fields: vec![return_type],
                    discriminant: 0,
                },
                EnumVariant {
                    name: format!("{name}-join-error"),
                    fields: vec![Type::Tuple(vec![Type::Named(name.into()), Type::I32])],
                    discriminant: 1,
                },
            ],
        },
    ]
}

fn thread_task_generated_source(name: &str, worker: &str, worker_function: &Function) -> String {
    let spawn_parameters = worker_function
        .parameters
        .iter()
        .map(|parameter| format!("({} {})", parameter.name, type_source(&parameter.ty)))
        .collect::<Vec<_>>()
        .join(" ");
    format!(
        "(#thread-task {name} {worker} (#thread-task-spawn {name}-spawn ({spawn_parameters}) {name}-spawn-result) (#thread-task-join {name}-join ((task {name})) {name}-join-result))\n(#enum {name}-spawn-error ({name}-spawn-allocation-error {name}-spawn-creation-error))\n(#enum {name}-spawn-result (({name}-spawn-ok {name}) ({name}-spawn-error {name}-spawn-error)))\n(#enum {name}-join-result (({name}-join-ok {}) ({name}-join-error (#tuple {name} i32))))\n",
        type_source(&worker_function.return_type)
    )
}

/// Preserve source locations for top-level function statements before the
/// source forms are lowered into the compiler AST.  The lowered `Statement`
/// representation intentionally remains location-agnostic for now; this
/// side table lets diagnostics refer to the original statement without
/// guessing from identifier occurrences.
fn collect_function_statement_spans(
    expression: &SpannedExpr,
    spans: &mut HashMap<(String, usize), Span>,
    expressions: &mut HashMap<(String, usize), SpannedExpr>,
) {
    let Expr::List(items) = &expression.expr else {
        return;
    };
    if !matches!(items.first(), Some(Expr::Symbol(name)) if matches!(name.as_str(), "#fn" | "fn" | "#unsafe-fn" | "unsafe-fn"))
        || items.len() < 5
    {
        return;
    }
    let Some(Expr::Symbol(name)) = items.get(1) else {
        return;
    };
    for (statement_index, statement) in expression.children.iter().skip(4).enumerate() {
        let key = (name.clone(), statement_index);
        spans.insert(key.clone(), statement.span);
        expressions.insert(key, statement.clone());
    }
}

fn precise_parse_error_span(expression: &SpannedExpr, error: &str) -> Option<Span> {
    if error == "#std is only valid as a top-level declaration" {
        return source_form_head_span(expression, &["#std"]);
    }
    let variant = error
        .strip_prefix("duplicate enum variant '")?
        .split('\'')
        .next()?;
    let Expr::List(items) = &expression.expr else {
        return None;
    };
    if !matches!(items.first(), Some(Expr::Symbol(head)) if head == "#enum" || head == "enum") {
        return None;
    }
    let variants = expression.children.get(2)?;
    let mut found = false;
    for form in &variants.children {
        let name = match &form.expr {
            Expr::Symbol(_) => Some(form),
            Expr::List(_) => form.children.first(),
            _ => None,
        }?;
        if matches!(&name.expr, Expr::Symbol(name) if name == variant) {
            if found {
                return Some(name.span);
            }
            found = true;
        }
    }
    None
}

fn set_source_id(expression: &mut SpannedExpr, source_id: u32) {
    expression.span.source_id = source_id;
    for child in &mut expression.children {
        set_source_id(child, source_id);
    }
}

/// Validate source-level named calls and lower them to the positional call
/// representation consumed by the existing analysis and backend passes.
fn normalize_function_calls(
    items: &mut [Item],
    statement_spans: &HashMap<(String, usize), Span>,
    statement_expressions: &HashMap<(String, usize), SpannedExpr>,
    declaration_spans: &HashMap<String, Span>,
    declaration_expressions: &HashMap<String, SpannedExpr>,
    source_files: &[SourceFile],
) -> Result<(), SourceError> {
    let signatures = items
        .iter()
        .filter_map(|item| match item {
            Item::Function(function) => Some((
                function.name.clone(),
                function
                    .parameters
                    .iter()
                    .map(|parameter| parameter.name.clone())
                    .collect::<Vec<_>>(),
            )),
            Item::ThreadTask { .. } => None,
            _ => None,
        })
        .collect::<HashMap<_, _>>();
    let mut signatures = signatures;
    for generated in items.iter().filter_map(|item| match item {
        Item::ThreadTask {
            generated_functions,
            ..
        } => Some(generated_functions),
        _ => None,
    }) {
        for function in generated {
            signatures.insert(
                function.name.clone(),
                function
                    .parameters
                    .iter()
                    .map(|parameter| parameter.name.clone())
                    .collect(),
            );
        }
    }
    for item in items {
        match item {
            Item::Function(function) => {
                for (index, statement) in function.body.iter_mut().enumerate() {
                    normalize_call_statement(statement, &signatures).map_err(|error| {
                        let key = (function.name.clone(), index);
                        statement_expressions
                            .get(&key)
                            .map(|expression| call_normalization_span(expression, &error))
                            .or_else(|| statement_spans.get(&key).copied())
                            .map_or(error.clone().into(), |span| {
                                attach_span_to_source_error(error, span, source_files)
                            })
                    })?;
                }
            }
            Item::Let { name, value, .. } | Item::Static { name, value, .. } => {
                normalize_call_expr(value, &signatures).map_err(|error| {
                    declaration_expressions
                        .get(name)
                        .map(|expression| call_normalization_span(expression, &error))
                        .or_else(|| declaration_spans.get(name).copied())
                        .map_or(error.clone().into(), |span| {
                            attach_span_to_source_error(error, span, source_files)
                        })
                })?;
            }
            _ => {}
        }
    }
    Ok(())
}

/// Find a value use, excluding declarations, types, field names, and argument
/// labels. Async branch-scope diagnostics must underline the escaped use,
/// not its earlier declaration or an unrelated same-spelled field.
fn source_value_symbol_span(expression: &SpannedExpr, name: &str) -> Option<Span> {
    if matches!(&expression.expr, Expr::Symbol(symbol) if symbol == name) {
        return Some(expression.span);
    }
    let children = &expression.children;
    let head = match &expression.expr {
        Expr::List(items) => items.first().and_then(|item| match item {
            Expr::Symbol(head) => Some(head.as_str()),
            _ => None,
        }),
        _ => None,
    };
    let visit = |index: usize| {
        children
            .get(index)
            .and_then(|child| source_value_symbol_span(child, name))
    };
    match head {
        Some("#quote" | "#quasiquote" | "#literal") => None,
        Some("#let" | "#let-mut") => visit(3),
        Some("#let-else") => visit(4).or_else(|| visit(3)),
        Some("#fn" | "#unsafe-fn") => children
            .iter()
            .skip(4)
            .rev()
            .find_map(|child| source_value_symbol_span(child, name)),
        Some("#get" | "#get-payload") => visit(1),
        Some("#await") => children
            .last()
            .and_then(|child| source_value_symbol_span(child, name)),
        Some("#call") => children.get(2).and_then(|arguments| {
            arguments.children.iter().rev().find_map(|pair| {
                pair.children
                    .get(1)
                    .and_then(|value| source_value_symbol_span(value, name))
            })
        }),
        Some("#struct-literal") => children.get(2).and_then(|fields| {
            fields.children.iter().rev().find_map(|pair| {
                pair.children
                    .get(1)
                    .and_then(|value| source_value_symbol_span(value, name))
            })
        }),
        Some("#case") => children
            .iter()
            .skip(2)
            .rev()
            .find_map(|child| source_value_symbol_span(child, name)),
        _ => children
            .iter()
            .skip(usize::from(head.is_some()))
            .rev()
            .find_map(|child| source_value_symbol_span(child, name)),
    }
}

fn collect_source_symbol_spans(expression: &SpannedExpr, name: &str, spans: &mut Vec<Span>) {
    if matches!(&expression.expr, Expr::Symbol(symbol) if symbol == name) {
        spans.push(expression.span);
    }
    for child in &expression.children {
        collect_source_symbol_spans(child, name, spans);
    }
}

fn source_symbol_span(expression: &SpannedExpr, name: &str, last: bool) -> Option<Span> {
    let mut spans = Vec::new();
    collect_source_symbol_spans(expression, name, &mut spans);
    if last {
        spans.into_iter().max_by_key(|span| span.start)
    } else {
        spans.into_iter().min_by_key(|span| span.start)
    }
}

fn source_type_name_span(expression: &SpannedExpr, name: &str) -> Option<Span> {
    if let Expr::Symbol(symbol) = &expression.expr {
        if symbol == name || symbol.starts_with(&format!("{name}<")) {
            return Some(expression.span);
        }
    }
    expression
        .children
        .iter()
        .find_map(|child| source_type_name_span(child, name))
}

fn specialization_error_span(expression: &SpannedExpr, error: &str) -> Option<Span> {
    if let Some(name) = error
        .split_once("generic type '")
        .and_then(|(_, rest)| rest.split('\'').next())
    {
        return source_type_name_span(expression, name);
    }
    error
        .rsplit('\'')
        .nth(1)
        .and_then(|name| source_symbol_span(expression, name, false))
}

fn source_form_head_span(expression: &SpannedExpr, names: &[&str]) -> Option<Span> {
    if let Expr::List(items) = &expression.expr {
        if matches!(items.first(), Some(Expr::Symbol(name)) if names.contains(&name.as_str())) {
            return expression.children.first().map(|head| head.span);
        }
    }
    expression
        .children
        .iter()
        .find_map(|child| source_form_head_span(child, names))
}

fn source_form_head_span_nth(
    expression: &SpannedExpr,
    names: &[&str],
    index: usize,
) -> Option<Span> {
    fn collect(expression: &SpannedExpr, names: &[&str], spans: &mut Vec<Span>) {
        if matches!(
            &expression.expr,
            Expr::List(items)
                if matches!(items.first(), Some(Expr::Symbol(name)) if names.contains(&name.as_str()))
        ) {
            if let Some(head) = expression.children.first() {
                spans.push(head.span);
            }
        }
        for child in &expression.children {
            collect(child, names, spans);
        }
    }

    let mut spans = Vec::new();
    collect(expression, names, &mut spans);
    spans.get(index).copied()
}

fn source_form_child_span(
    expression: &SpannedExpr,
    names: &[&str],
    child_index: usize,
) -> Option<Span> {
    if let Expr::List(items) = &expression.expr {
        if matches!(items.first(), Some(Expr::Symbol(name)) if names.contains(&name.as_str())) {
            return expression.children.get(child_index).map(|child| child.span);
        }
    }
    expression
        .children
        .iter()
        .find_map(|child| source_form_child_span(child, names, child_index))
}

fn call_normalization_span(expression: &SpannedExpr, error: &str) -> Span {
    if error.starts_with("#println") {
        fn find(expression: &SpannedExpr, bad_arity: bool) -> Option<Span> {
            if matches!(&expression.expr, Expr::List(items)
                if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#println")
                    && (!bad_arity || items.len() != 2))
            {
                return expression.children.first().map(|head| head.span);
            }
            expression
                .children
                .iter()
                .find_map(|child| find(child, bad_arity))
        }
        if let Some(span) = find(expression, error.contains("exactly one")) {
            return span;
        }
    }
    if error.contains("more than once") {
        if let Some(span) = duplicate_call_parameter_span(expression) {
            return span;
        }
    }
    if let Some(target) = error.rsplit('\'').nth(1) {
        if let Some(span) = source_symbol_span(expression, target, error.contains("more than once"))
        {
            return span;
        }
    }
    source_form_head_span(expression, &["#call", "call", "#println"])
        .unwrap_or_else(|| source_value_span(expression))
}

fn duplicate_call_parameter_span(expression: &SpannedExpr) -> Option<Span> {
    if let Expr::List(items) = &expression.expr {
        if matches!(items.first(), Some(Expr::Symbol(name)) if name == "#call" || name == "call") {
            let arguments = expression.children.get(2)?;
            let mut seen = HashSet::new();
            for argument in &arguments.children {
                let Expr::List(parts) = &argument.expr else {
                    continue;
                };
                let Some(Expr::Symbol(parameter)) = parts.first() else {
                    continue;
                };
                if !seen.insert(parameter.as_str()) {
                    return argument.children.first().map(|parameter| parameter.span);
                }
            }
        }
    }
    expression
        .children
        .iter()
        .find_map(duplicate_call_parameter_span)
}

fn attach_span_to_source_error(
    error: String,
    span: Span,
    source_files: &[SourceFile],
) -> SourceError {
    attach_span_to_source_error_kind(error, span, source_files, "type error: ")
}

fn attach_span_to_source_error_kind(
    error: String,
    span: Span,
    source_files: &[SourceFile],
    prefix: &str,
) -> SourceError {
    let code = match prefix {
        "lex error: " => DiagnosticCode::Lex,
        "parse error: " => DiagnosticCode::Parse,
        _ => DiagnosticCode::Type,
    };
    SourceError::new(error, code).at(span).attach(source_files)
}

fn normalize_call_statement(
    statement: &mut Statement,
    signatures: &HashMap<String, Vec<String>>,
) -> Result<(), String> {
    match statement {
        Statement::Let { value, .. }
        | Statement::Destructure { value, .. }
        | Statement::LetElse { value, .. }
        | Statement::Assign { value, .. }
        | Statement::FieldAssign { value, .. }
        | Statement::TupleAssign { value, .. }
        | Statement::EnumPayloadAssign { value, .. }
        | Statement::BreakValue(value)
        | Statement::BreakToValue { value, .. }
        | Statement::Return(Some(value))
        | Statement::Expr(value) => normalize_call_expr(value, signatures)?,
        Statement::ArrayAssign { index, value, .. } => {
            normalize_call_expr(index, signatures)?;
            normalize_call_expr(value, signatures)?;
        }
        Statement::While { condition, body } => {
            normalize_call_expr(condition, signatures)?;
            for statement in body {
                normalize_call_statement(statement, signatures)?;
            }
        }
        Statement::Loop { body } => {
            for statement in body {
                normalize_call_statement(statement, signatures)?;
            }
        }
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            normalize_call_statement(init, signatures)?;
            normalize_call_expr(condition, signatures)?;
            normalize_call_statement(step, signatures)?;
            for statement in body {
                normalize_call_statement(statement, signatures)?;
            }
        }
        Statement::Labeled { statement, .. } => normalize_call_statement(statement, signatures)?,
        Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_)
        | Statement::Return(None) => {}
    }
    if let Statement::LetElse { else_body, .. } = statement {
        for statement in else_body {
            normalize_call_statement(statement, signatures)?;
        }
    }
    Ok(())
}

fn normalize_call_expr(
    expression: &mut Expr,
    signatures: &HashMap<String, Vec<String>>,
) -> Result<(), String> {
    match expression {
        Expr::List(items) => {
            if matches!(items.first(), Some(Expr::Symbol(name)) if name == "println") {
                if items.len() != 2 {
                    return Err("#println requires exactly one shared String reference".into());
                }
                if !signatures.contains_key("std-println") {
                    return Err("#println requires the standard IO library; add (#std)".into());
                }
                normalize_call_expr(&mut items[1], signatures)?;
                // Preserve the source shape and reuse the checked operand;
                // this is only call sugar, not a new emission primitive.
                items[0] = Expr::Function("std-println".into());
                return Ok(());
            }
            if matches!(items.first(), Some(Expr::Symbol(name)) if name == "call") {
                if items.len() != 3 {
                    return Err("#call requires a function name and named arguments".into());
                }
                let Expr::Symbol(function) = &items[1] else {
                    return Err("#call requires a function name".into());
                };
                let function = function.clone();
                let parameters = signatures
                    .get(&function)
                    .ok_or_else(|| format!("#call refers to unknown function '{function}'"))?;
                let Expr::List(argument_form) = &mut items[2] else {
                    return Err("#call arguments must be a named argument list".into());
                };
                let mut arguments = HashMap::new();
                for argument in argument_form.iter_mut() {
                    let Expr::List(pair) = argument else {
                        return Err(
                            "each named argument must have the form (parameter value)".into()
                        );
                    };
                    if pair.len() != 2 {
                        return Err(
                            "each named argument must have the form (parameter value)".into()
                        );
                    }
                    let Expr::Symbol(name) = &pair[0] else {
                        return Err("named argument labels must be identifiers".into());
                    };
                    let name = name.clone();
                    if !parameters.contains(&name) {
                        return Err(format!("function '{function}' has no parameter '{name}'"));
                    }
                    normalize_call_expr(&mut pair[1], signatures)?;
                    if arguments.insert(name.clone(), pair[1].clone()).is_some() {
                        return Err(format!(
                            "#call to '{function}' provides parameter '{name}' more than once"
                        ));
                    }
                }
                let mut lowered = Vec::with_capacity(parameters.len() + 1);
                lowered.push(Expr::Function(function.clone()));
                for parameter in parameters {
                    lowered.push(arguments.remove(parameter).ok_or_else(|| {
                        format!("#call to '{function}' is missing parameter '{parameter}'")
                    })?);
                }
                *expression = Expr::List(lowered);
                return Ok(());
            }
            if let Some(Expr::Symbol(name)) = items.first() {
                if signatures.contains_key(name) && !is_builtin_head(name) {
                    return Err(format!(
                        "function '{name}' must be called with (#call {name} (: parameter value ...))"
                    ));
                }
                if name == "match" {
                    if let Some(scrutinee) = items.get_mut(1) {
                        normalize_call_expr(scrutinee, signatures)?;
                    }
                    for arm in items.iter_mut().skip(2) {
                        let Expr::List(parts) = arm else { continue };
                        for part in parts.iter_mut().skip(1) {
                            normalize_call_expr(part, signatures)?;
                        }
                    }
                    return Ok(());
                }
                if matches!(name.as_str(), "if-let" | "while-let") {
                    for (index, child) in items.iter_mut().enumerate().skip(1) {
                        if index != 1 {
                            normalize_call_expr(child, signatures)?;
                        }
                    }
                    return Ok(());
                }
            }
            for item in items {
                normalize_call_expr(item, signatures)?;
            }
        }
        Expr::Block(statements) | Expr::Loop(statements) => {
            for statement in statements {
                normalize_call_statement(statement, signatures)?;
            }
        }
        Expr::Labeled { expression, .. }
        | Expr::Quote(expression)
        | Expr::QuasiQuote(expression)
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => normalize_call_expr(expression, signatures)?,
        _ => {}
    }
    Ok(())
}

/// Lower keyed struct literals to the positional aggregate representation used
/// internally by the type checker and backends. Source-level type-name calls
/// are rejected separately, so this representation is never user syntax.
fn normalize_struct_literals(
    items: &mut [Item],
    statement_spans: &HashMap<(String, usize), Span>,
    statement_expressions: &HashMap<(String, usize), SpannedExpr>,
    declaration_spans: &HashMap<String, Span>,
    declaration_expressions: &HashMap<String, SpannedExpr>,
    source_files: &[SourceFile],
) -> Result<(), SourceError> {
    let structs = items
        .iter()
        .filter_map(|item| match item {
            Item::Struct { name, fields, .. } => Some((name.clone(), fields.clone())),
            _ => None,
        })
        .collect::<HashMap<_, _>>();

    for item in items {
        match item {
            Item::Function(function) => {
                for (index, statement) in function.body.iter_mut().enumerate() {
                    normalize_struct_statement(statement, &structs).map_err(|error| {
                        let key = (function.name.clone(), index);
                        statement_expressions
                            .get(&key)
                            .map(|expression| struct_normalization_span(expression, &error))
                            .or_else(|| statement_spans.get(&key).copied())
                            .map_or(error.clone().into(), |span| {
                                attach_span_to_source_error(error, span, source_files)
                            })
                    })?;
                }
            }
            Item::Let { name, value, .. } | Item::Static { name, value, .. } => {
                normalize_struct_expr(value, &structs).map_err(|error| {
                    declaration_expressions
                        .get(name)
                        .map(|expression| struct_normalization_span(expression, &error))
                        .or_else(|| declaration_spans.get(name).copied())
                        .map_or(error.clone().into(), |span| {
                            attach_span_to_source_error(error, span, source_files)
                        })
                })?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn struct_normalization_span(expression: &SpannedExpr, error: &str) -> Span {
    if error.contains("missing field") {
        if let Some(span) =
            source_form_child_span(expression, &["#struct-literal", "struct-literal"], 2)
        {
            return span;
        }
    } else if let Some(target) = error.rsplit('\'').nth(1) {
        if let Some(span) =
            source_symbol_span(expression, target, error.contains("duplicate field"))
        {
            return span;
        }
    }
    source_form_head_span(expression, &["#struct-literal", "struct-literal"])
        .unwrap_or_else(|| source_value_span(expression))
}

fn normalize_struct_statement(
    statement: &mut Statement,
    structs: &HashMap<String, Vec<Field>>,
) -> Result<(), String> {
    match statement {
        Statement::Let { value, .. }
        | Statement::Destructure { value, .. }
        | Statement::LetElse { value, .. }
        | Statement::Assign { value, .. }
        | Statement::FieldAssign { value, .. }
        | Statement::TupleAssign { value, .. }
        | Statement::EnumPayloadAssign { value, .. }
        | Statement::BreakValue(value)
        | Statement::BreakToValue { value, .. }
        | Statement::Return(Some(value))
        | Statement::Expr(value) => normalize_struct_expr(value, structs)?,
        Statement::ArrayAssign { index, value, .. } => {
            normalize_struct_expr(index, structs)?;
            normalize_struct_expr(value, structs)?;
        }
        Statement::While { condition, body } => {
            normalize_struct_expr(condition, structs)?;
            for statement in body {
                normalize_struct_statement(statement, structs)?;
            }
        }
        Statement::Loop { body } => {
            for statement in body {
                normalize_struct_statement(statement, structs)?;
            }
        }
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            normalize_struct_statement(init, structs)?;
            normalize_struct_expr(condition, structs)?;
            normalize_struct_statement(step, structs)?;
            for statement in body {
                normalize_struct_statement(statement, structs)?;
            }
        }
        Statement::Labeled { statement, .. } => normalize_struct_statement(statement, structs)?,
        Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_)
        | Statement::Return(None) => {}
    }
    if let Statement::LetElse { else_body, .. } = statement {
        for statement in else_body {
            normalize_struct_statement(statement, structs)?;
        }
    }
    Ok(())
}

fn normalize_struct_expr(
    expression: &mut Expr,
    structs: &HashMap<String, Vec<Field>>,
) -> Result<(), String> {
    if let Expr::List(items) = expression {
        if matches!(items.first(), Some(Expr::Symbol(name)) if name == "struct-literal") {
            if items.len() != 3 {
                return Err(
                    "struct-literal requires (#struct-literal Type ((field value) ...))".into(),
                );
            }
            let Expr::Symbol(struct_name) = &items[1] else {
                return Err("struct-literal requires a struct type name".into());
            };
            let struct_name = struct_name.clone();
            let fields = structs
                .get(&struct_name)
                .ok_or_else(|| format!("unknown struct '{struct_name}'"))?;
            let Expr::List(entries) = &mut items[2] else {
                return Err("struct-literal fields must be a list of (name value) pairs".into());
            };
            let mut values = HashMap::new();
            for entry in entries.iter_mut() {
                let Expr::List(pair) = entry else {
                    return Err("struct-literal fields must have the form (name value)".into());
                };
                if pair.len() != 2 {
                    return Err("struct-literal fields must have the form (name value)".into());
                }
                let Expr::Symbol(field_name) = &pair[0] else {
                    return Err("struct-literal field names must be symbols".into());
                };
                let field_name = field_name.clone();
                normalize_struct_expr(&mut pair[1], structs)?;
                if values.insert(field_name.clone(), pair[1].clone()).is_some() {
                    return Err(format!(
                        "struct-literal '{struct_name}' contains duplicate field '{field_name}'"
                    ));
                }
            }
            for field in fields {
                if !values.contains_key(&field.name) {
                    return Err(format!(
                        "struct-literal '{struct_name}' is missing field '{}'",
                        field.name
                    ));
                }
            }
            if let Some(field_name) = values
                .keys()
                .find(|name| !fields.iter().any(|field| &field.name == *name))
            {
                return Err(format!(
                    "struct-literal '{struct_name}' has unknown field '{field_name}'"
                ));
            }
            let mut lowered = Vec::with_capacity(fields.len() + 1);
            lowered.push(Expr::Symbol(struct_name.clone()));
            lowered.extend(
                fields
                    .iter()
                    .map(|field| values.remove(&field.name).expect("checked struct field")),
            );
            *expression = Expr::List(lowered);
            return Ok(());
        }
        if let Some(Expr::Symbol(name)) = items.first() {
            if structs.contains_key(name) {
                return Err(format!(
                    "'{name}' is a type, not a constructor function; use #struct-literal or a named constructor function"
                ));
            }
            if name == "match" {
                if let Some(scrutinee) = items.get_mut(1) {
                    normalize_struct_expr(scrutinee, structs)?;
                }
                for arm in items.iter_mut().skip(2) {
                    let Expr::List(parts) = arm else { continue };
                    // Struct-shaped forms in arm position are patterns.
                    for part in parts.iter_mut().skip(1) {
                        normalize_struct_expr(part, structs)?;
                    }
                }
                return Ok(());
            }
            if matches!(name.as_str(), "if-let" | "while-let") {
                for (index, child) in items.iter_mut().enumerate().skip(1) {
                    if index != 1 {
                        normalize_struct_expr(child, structs)?;
                    }
                }
                return Ok(());
            }
        }
        for item in items {
            normalize_struct_expr(item, structs)?;
        }
    } else {
        match expression {
            Expr::Block(statements) | Expr::Loop(statements) => {
                for statement in statements {
                    normalize_struct_statement(statement, structs)?;
                }
            }
            Expr::Labeled { expression, .. } => normalize_struct_expr(expression, structs)?,
            Expr::Quote(_) | Expr::QuasiQuote(_) | Expr::Unquote(_) | Expr::UnquoteSplicing(_) => {}
            _ => {}
        }
    }
    Ok(())
}

fn rename_shadowed_locals(
    items: &mut [Item],
    statement_spans: &HashMap<(String, usize), Span>,
    declaration_spans: &HashMap<String, Span>,
    source_files: &[SourceFile],
    syntax_bundles: &HashMap<String, SpannedExpr>,
) -> Result<(), SourceError> {
    let globals = items
        .iter()
        .filter_map(|item| match item {
            Item::Let { name, .. } | Item::Static { name, .. } => Some(name.clone()),
            _ => None,
        })
        .chain(syntax_bundles.keys().cloned())
        .collect::<HashSet<_>>();
    let variants = items
        .iter()
        .filter_map(|item| match item {
            Item::Enum { variants, .. } => Some(variants),
            _ => None,
        })
        .flat_map(|variants| variants.iter().map(|variant| variant.name.clone()))
        .collect::<HashSet<_>>();
    for item in items {
        if let Item::Function(function) = item {
            let shadow = rename_function_locals(function, &globals, &variants);
            if let Some((name, statement_index)) = shadow {
                let span = statement_index
                    .and_then(|index| {
                        statement_spans
                            .get(&(function.name.clone(), index))
                            .copied()
                    })
                    .or_else(|| declaration_spans.get(&function.name).copied())
                    .and_then(|span| shadow_binding_span(span, &name, source_files));
                let error = SourceError::new(
                    format!(
                        "binding '{name}' shadows an existing binding; shadowing is not allowed"
                    ),
                    DiagnosticCode::Type,
                );
                return Err(span
                    .map_or(error.clone(), |span| error.at(span))
                    .attach(source_files));
            }
        }
    }
    Ok(())
}

fn shadow_binding_span(span: Span, name: &str, source_files: &[SourceFile]) -> Option<Span> {
    let source = &source_files.get(span.source_id as usize)?.source;
    let form = source.get(span.start..span.end)?;
    let (offset, _) = form.match_indices(name).find(|(offset, _)| {
        let before = form[..*offset].chars().next_back();
        let after = form[*offset + name.len()..].chars().next();
        !before.is_some_and(is_identifier_character) && !after.is_some_and(is_identifier_character)
    })?;
    let start = span.start + offset;
    let prefix = &source[..start];
    let line = prefix.bytes().filter(|byte| *byte == b'\n').count() + 1;
    let column = prefix
        .rsplit_once('\n')
        .map_or(prefix, |(_, tail)| tail)
        .chars()
        .count()
        + 1;
    Some(Span {
        start,
        end: start + name.len(),
        line,
        column,
        source_id: span.source_id,
    })
}

fn async_function_statement_source(
    expression: &SpannedExpr,
    statement_index: usize,
) -> Option<&SpannedExpr> {
    if matches!(
        &expression.expr,
        Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#fn" || head == "fn")
    ) {
        return expression.children.get(4 + statement_index);
    }
    expression
        .children
        .iter()
        .find_map(|child| async_function_statement_source(child, statement_index))
}

fn async_lowering_statement_index(error: &str) -> Option<usize> {
    let marker = "async statement ";
    let start = error.find(marker)? + marker.len();
    let rest = &error[start..];
    let end = rest.find(':')?;
    rest[..end].parse().ok()
}

fn is_identifier_character(character: char) -> bool {
    character.is_alphanumeric() || matches!(character, '_' | '-' | '.')
}

fn rename_function_locals(
    function: &mut Function,
    globals: &HashSet<String>,
    variants: &HashSet<String>,
) -> Option<(String, Option<usize>)> {
    let mut bindings = function
        .parameters
        .iter()
        .map(|parameter| (parameter.name.clone(), parameter.name.clone()))
        .collect::<HashMap<_, _>>();
    let mut used = bindings.values().cloned().collect::<HashSet<_>>();
    for parameter in &function.parameters {
        if globals.contains(&parameter.name) {
            used.insert(format!("\0lim-shadow:-1:{}", parameter.name));
        }
    }
    let mut next_id = 0usize;
    for (statement_index, statement) in function.body.iter_mut().enumerate() {
        used.insert(format!("\0lim-current:{statement_index}"));
        rename_statement(
            statement,
            &mut bindings,
            &mut used,
            &mut next_id,
            globals,
            variants,
        );
        used.retain(|entry| !entry.starts_with("\0lim-current:"));
    }
    used.iter()
        .filter_map(|entry| {
            let rest = entry.strip_prefix("\0lim-shadow:")?;
            let (index, name) = rest.split_once(':')?;
            let index = index.parse::<isize>().ok()?;
            Some((index, name))
        })
        .min_by_key(|(index, name)| (*index, *name))
        .map(|(index, name)| (name.to_owned(), (index >= 0).then_some(index as usize)))
}

/// Validate lexical shadowing in the source async function before lowering
/// splits it into helpers and omits dead locals from later states.
pub(crate) fn validate_async_function_shadowing(expression: &Expr) -> Result<(), String> {
    if let Some((name, _)) = async_function_shadowing(expression)? {
        return Err(format!(
            "binding '{name}' shadows an existing binding; shadowing is not allowed"
        ));
    }
    Ok(())
}

pub(crate) fn async_function_shadowing(
    expression: &Expr,
) -> Result<Option<(String, Option<usize>)>, String> {
    let normalized = normalize_keywords(expression.clone());
    let Item::Function(mut function) = parse_item(&normalized)? else {
        return Err("@async-fn source must be a function declaration".into());
    };
    Ok(rename_function_locals(
        &mut function,
        &HashSet::new(),
        &HashSet::new(),
    ))
}

fn fresh_binding(
    name: &str,
    bindings: &HashMap<String, String>,
    used: &mut HashSet<String>,
    next_id: &mut usize,
    globals: &HashSet<String>,
) -> String {
    if bindings.contains_key(name) || globals.contains(name) {
        let statement_index = used
            .iter()
            .find_map(|entry| entry.strip_prefix("\0lim-current:"))
            .unwrap_or("-1");
        used.insert(format!("\0lim-shadow:{statement_index}:{name}"));
    }
    if !bindings.contains_key(name) && !globals.contains(name) && !used.contains(name) {
        used.insert(name.to_owned());
        return name.to_owned();
    }
    loop {
        let candidate = format!("__lim_shadow_{}_{}", *next_id, name);
        *next_id += 1;
        if !globals.contains(&candidate) && used.insert(candidate.clone()) {
            return candidate;
        }
    }
}

fn rename_symbol(name: &mut String, bindings: &HashMap<String, String>) {
    if let Some(resolved) = bindings.get(name) {
        *name = resolved.clone();
    }
}

fn rename_pattern_bindings(
    pattern: &mut Expr,
    bindings: &mut HashMap<String, String>,
    used: &mut HashSet<String>,
    next_id: &mut usize,
    globals: &HashSet<String>,
    variants: &HashSet<String>,
    new_bindings: &mut HashSet<String>,
) {
    match pattern {
        Expr::List(items) => {
            if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "literal" | "range" | "range-inclusive"))
            {
                return;
            }
            for item in items.iter_mut().skip(1) {
                rename_pattern_bindings(
                    item,
                    bindings,
                    used,
                    next_id,
                    globals,
                    variants,
                    new_bindings,
                );
            }
        }
        Expr::Symbol(name)
            if name != "_"
                && name != "true"
                && name != "false"
                && !variants.contains(name)
                && new_bindings.insert(name.clone()) =>
        {
            let original = name.clone();
            let resolved = fresh_binding(&original, bindings, used, next_id, globals);
            bindings.insert(original, resolved.clone());
            *name = resolved;
        }
        _ => {}
    }
}

fn rename_statements(
    statements: &mut [Statement],
    bindings: &mut HashMap<String, String>,
    used: &mut HashSet<String>,
    next_id: &mut usize,
    globals: &HashSet<String>,
    variants: &HashSet<String>,
) {
    for statement in statements {
        rename_statement(statement, bindings, used, next_id, globals, variants);
    }
}

fn rename_statement(
    statement: &mut Statement,
    bindings: &mut HashMap<String, String>,
    used: &mut HashSet<String>,
    next_id: &mut usize,
    globals: &HashSet<String>,
    variants: &HashSet<String>,
) {
    match statement {
        Statement::Let { name, value, .. } => {
            rename_expression(value, bindings, used, next_id, globals, variants);
            let original = name.clone();
            let resolved = fresh_binding(&original, bindings, used, next_id, globals);
            bindings.insert(original, resolved.clone());
            *name = resolved;
        }
        Statement::Destructure { pattern, value, .. } => {
            rename_expression(value, bindings, used, next_id, globals, variants);
            let mut new_bindings = HashSet::new();
            rename_pattern_bindings(
                pattern,
                bindings,
                used,
                next_id,
                globals,
                variants,
                &mut new_bindings,
            );
        }
        Statement::LetElse {
            pattern,
            value,
            else_body,
            ..
        } => {
            rename_expression(value, bindings, used, next_id, globals, variants);
            let mut else_bindings = bindings.clone();
            rename_statements(
                else_body,
                &mut else_bindings,
                used,
                next_id,
                globals,
                variants,
            );
            let mut new_bindings = HashSet::new();
            rename_pattern_bindings(
                pattern,
                bindings,
                used,
                next_id,
                globals,
                variants,
                &mut new_bindings,
            );
        }
        Statement::Assign { name, value }
        | Statement::ArrayAssign { name, value, .. }
        | Statement::FieldAssign { name, value, .. }
        | Statement::TupleAssign { name, value, .. }
        | Statement::EnumPayloadAssign { name, value, .. } => {
            rename_symbol(name, bindings);
            rename_expression(value, bindings, used, next_id, globals, variants);
            if let Statement::ArrayAssign { index, .. } = statement {
                rename_expression(index, bindings, used, next_id, globals, variants);
            }
        }
        Statement::While { condition, body } => {
            rename_expression(condition, bindings, used, next_id, globals, variants);
            let mut body_bindings = bindings.clone();
            rename_statements(body, &mut body_bindings, used, next_id, globals, variants);
        }
        Statement::Loop { body } => {
            let mut body_bindings = bindings.clone();
            rename_statements(body, &mut body_bindings, used, next_id, globals, variants);
        }
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            let mut loop_bindings = bindings.clone();
            rename_statement(init, &mut loop_bindings, used, next_id, globals, variants);
            rename_expression(
                condition,
                &mut loop_bindings,
                used,
                next_id,
                globals,
                variants,
            );
            rename_statement(step, &mut loop_bindings, used, next_id, globals, variants);
            rename_statements(body, &mut loop_bindings, used, next_id, globals, variants);
        }
        Statement::Labeled { statement, .. } => {
            rename_statement(statement, bindings, used, next_id, globals, variants);
        }
        Statement::BreakValue(value) | Statement::Return(Some(value)) | Statement::Expr(value) => {
            rename_expression(value, bindings, used, next_id, globals, variants);
        }
        Statement::BreakToValue { value, .. } => {
            rename_expression(value, bindings, used, next_id, globals, variants);
        }
        Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_)
        | Statement::Return(None) => {}
    }
}

fn rename_expression(
    expression: &mut Expr,
    bindings: &mut HashMap<String, String>,
    used: &mut HashSet<String>,
    next_id: &mut usize,
    globals: &HashSet<String>,
    variants: &HashSet<String>,
) {
    match expression {
        Expr::Function(_) => {}
        Expr::Symbol(name) => rename_symbol(name, bindings),
        Expr::List(items) => {
            let Some(Expr::Symbol(operator)) = items.first() else {
                for item in items {
                    rename_expression(item, bindings, used, next_id, globals, variants);
                }
                return;
            };
            let operator = operator.clone();
            match operator.as_str() {
                "match" if items.len() >= 2 => {
                    rename_expression(&mut items[1], bindings, used, next_id, globals, variants);
                    for arm in items.iter_mut().skip(2) {
                        let Expr::List(arm_items) = arm else { continue };
                        if arm_items.is_empty() {
                            continue;
                        }
                        let mut arm_bindings = bindings.clone();
                        let mut new_bindings = HashSet::new();
                        rename_pattern_bindings(
                            &mut arm_items[0],
                            &mut arm_bindings,
                            used,
                            next_id,
                            globals,
                            variants,
                            &mut new_bindings,
                        );
                        for item in arm_items.iter_mut().skip(1) {
                            rename_expression(
                                item,
                                &mut arm_bindings,
                                used,
                                next_id,
                                globals,
                                variants,
                            );
                        }
                    }
                }
                "if-let" if items.len() >= 4 => {
                    rename_expression(&mut items[2], bindings, used, next_id, globals, variants);
                    let mut branch_bindings = bindings.clone();
                    let mut new_bindings = HashSet::new();
                    rename_pattern_bindings(
                        &mut items[1],
                        &mut branch_bindings,
                        used,
                        next_id,
                        globals,
                        variants,
                        &mut new_bindings,
                    );
                    for item in items.iter_mut().skip(3) {
                        rename_expression(
                            item,
                            &mut branch_bindings,
                            used,
                            next_id,
                            globals,
                            variants,
                        );
                    }
                }
                "as" | "size-of" | "align-of" | "offset-of" => {
                    for item in items
                        .iter_mut()
                        .skip(1)
                        .take(if operator == "as" { 1 } else { 0 })
                    {
                        rename_expression(item, bindings, used, next_id, globals, variants);
                    }
                }
                "get" => {
                    if let Some(value) = items.get_mut(1) {
                        rename_expression(value, bindings, used, next_id, globals, variants);
                    }
                }
                "pin-set-field" => {
                    if let Some(reference) = items.get_mut(1) {
                        rename_expression(reference, bindings, used, next_id, globals, variants);
                    }
                    if let Some(value) = items.get_mut(3) {
                        rename_expression(value, bindings, used, next_id, globals, variants);
                    }
                }
                "array" | "array-repeat" => {
                    for item in items.iter_mut().skip(2) {
                        rename_expression(item, bindings, used, next_id, globals, variants);
                    }
                }
                "tuple" => {
                    let value_start = items
                        .get(1)
                        .and_then(|item| parse_type(Some(item)).ok())
                        .filter(|ty| matches!(ty, Type::Tuple(_)))
                        .map_or(1, |_| 2);
                    for item in items.iter_mut().skip(value_start) {
                        rename_expression(item, bindings, used, next_id, globals, variants);
                    }
                }
                _ => {
                    for item in items.iter_mut().skip(1) {
                        rename_expression(item, bindings, used, next_id, globals, variants);
                    }
                }
            }
        }
        Expr::Block(statements) | Expr::Loop(statements) => {
            let mut block_bindings = bindings.clone();
            rename_statements(
                statements,
                &mut block_bindings,
                used,
                next_id,
                globals,
                variants,
            );
        }
        Expr::Labeled { expression, .. } => {
            rename_expression(expression, bindings, used, next_id, globals, variants);
        }
        Expr::Quote(_)
        | Expr::QuasiQuote(_)
        | Expr::Unquote(_)
        | Expr::UnquoteSplicing(_)
        | Expr::Integer(_)
        | Expr::UnsignedInteger(_)
        | Expr::Float(_)
        | Expr::Char(_)
        | Expr::String(_)
        | Expr::At => {}
    }
}

fn validate_prefixed_forms(expression: &Expr) -> Result<(), String> {
    let Expr::List(items) = expression else {
        return Ok(());
    };
    if matches!(items.first(), Some(Expr::At)) {
        let normalized = normalize_builtin_generator_invocation(expression)?;
        if normalized != *expression {
            if let Expr::List(values) = normalized {
                for value in values.iter().skip(2) {
                    validate_prefixed_forms(value)?;
                }
            }
            return Ok(());
        }
    }
    if matches!(items.first(), Some(Expr::Symbol(name)) if name == "#fn" || name == "#unsafe-fn" || name == "#extern-fn")
    {
        let parameter_index = if matches!(items.first(), Some(Expr::Symbol(name)) if name == "#extern-fn")
        {
            3
        } else {
            2
        };
        if let Some(Expr::List(parameters)) = items.get(parameter_index) {
            for parameter in parameters {
                if let Expr::List(parts) = parameter {
                    if matches!(parts.first(), Some(Expr::Symbol(name)) if name == "mut") {
                        return Err(
                            "builtin 'mut' must use its '#' prefix in prefixed syntax".into()
                        );
                    }
                    if let Some(ty) = parts.last() {
                        validate_prefixed_forms(ty)?;
                    }
                }
            }
            for (index, item) in items.iter().enumerate() {
                if index != parameter_index {
                    validate_prefixed_forms(item)?;
                }
            }
            return Ok(());
        }
    }
    if matches!(items.first(), Some(Expr::Symbol(name)) if name == "#call") {
        if let Some(Expr::List(arguments)) = items.get(2) {
            for argument in arguments {
                if let Expr::List(pair) = argument {
                    if let Some(value) = pair.get(1) {
                        validate_prefixed_forms(value)?;
                    }
                }
            }
            return Ok(());
        }
    }
    if let Some(Expr::Symbol(name)) = items.first() {
        if !name.starts_with('#') && (is_builtin_form(name) || is_operator_symbol(name)) {
            return Err(format!(
                "builtin '{name}' must use its '#' prefix in prefixed syntax"
            ));
        }
        if let Some(operator) = name.strip_prefix('#') {
            if requires_explicit_operator_type(operator) {
                return Err(format!(
                    "operator '{name}' must use an explicit type qualifier"
                ));
            }
        }
    }
    for item in items {
        validate_prefixed_forms(item)?;
    }
    Ok(())
}

fn normalize_match_cases_expr(expression: &mut Expr) {
    let Expr::List(items) = expression else {
        match expression {
            Expr::Labeled { expression, .. }
            | Expr::Quote(expression)
            | Expr::QuasiQuote(expression)
            | Expr::Unquote(expression)
            | Expr::UnquoteSplicing(expression) => normalize_match_cases_expr(expression),
            _ => {}
        }
        return;
    };
    if matches!(items.first(), Some(Expr::Symbol(head)) if head == "match") {
        for arm in items.iter_mut().skip(2) {
            if let Expr::List(parts) = arm {
                if matches!(parts.first(), Some(Expr::Symbol(head)) if head == "case") {
                    parts.remove(0);
                }
                for part in parts {
                    normalize_match_cases_expr(part);
                }
            }
        }
        if let Some(scrutinee) = items.get_mut(1) {
            normalize_match_cases_expr(scrutinee);
        }
        return;
    }
    for item in items {
        normalize_match_cases_expr(item);
    }
}

fn normalize_match_case_forms(expression: &mut SpannedExpr) -> Result<(), (String, Span)> {
    let Expr::List(items) = &mut expression.expr else {
        for child in &mut expression.children {
            normalize_match_case_forms(child)?;
        }
        return Ok(());
    };
    let head = match items.first() {
        Some(Expr::Symbol(name)) => name.as_str(),
        _ => "",
    };
    if head == "#case" || head == "case" {
        return Err((
            "#case is only valid as an arm of #match".to_owned(),
            expression.span,
        ));
    }
    if head == "#match" || head == "match" {
        if expression.children.len() < 3 {
            return Err((
                "#match requires a scrutinee and at least one #case".into(),
                expression.span,
            ));
        }
        normalize_match_case_forms(&mut expression.children[1])?;
        for arm in expression.children.iter_mut().skip(2) {
            let Expr::List(parts) = &arm.expr else {
                return Err(("#match arms must use (#case pattern body)".into(), arm.span));
            };
            if !matches!(parts.first(), Some(Expr::Symbol(head)) if head == "#case") {
                return Err(("each #match arm must use #case".into(), arm.span));
            }
            if !matches!(parts.len(), 3 | 4) {
                return Err((
                    "#case must have a pattern and body, with an optional #when guard".into(),
                    arm.span,
                ));
            }
            let Expr::List(normalized_parts) = &mut arm.expr else {
                unreachable!();
            };
            normalized_parts.remove(0);
            arm.children.remove(0);
            for child in &mut arm.children {
                normalize_match_case_forms(child)?;
            }
        }
        return Ok(());
    }
    for child in &mut expression.children {
        normalize_match_case_forms(child)?;
    }
    Ok(())
}

fn is_builtin_form(name: &str) -> bool {
    matches!(
        name,
        "type"
            | "fn"
            | "unsafe-fn"
            | "call"
            | "extern-fn"
            | "struct"
            | "enum"
            | "let"
            | "let-else"
            | "const"
            | "static"
            | "unsafe-impl"
            | "linear"
            | "opaque"
            | "thread-task"
            | "thread-task-spawn"
            | "thread-task-join"
            | "if"
            | "if-let"
            | "while"
            | "while-let"
            | "await"
            | "for"
            | "for-range"
            | "loop"
            | "label"
            | "break"
            | "break-to"
            | "continue"
            | "continue-to"
            | "return"
            | "set"
            | "set-index"
            | "set-field"
            | "set-payload"
            | "block"
            | "match"
            | "case"
            | "when"
            | "range"
            | "or"
            | "as"
            | "array"
            | "array-repeat"
            | "slice"
            | "slice-mut"
            | "slice-of"
            | "slice-mut-of"
            | "slice-len"
            | "slice-mut-len"
            | "slice-idx"
            | "slice-mut-idx"
            | "slice-range"
            | "slice-mut-split"
            | "atomic"
            | "atomic-init"
            | "atomic-load"
            | "atomic-store"
            | "atomic-fetch-add"
            | "atomic-exchange"
            | "atomic-compare-exchange"
            | "atomic-compare-exchange-weak"
            | "memory-relaxed"
            | "memory-acquire"
            | "memory-release"
            | "memory-acq-rel"
            | "memory-seq-cst"
            | "tuple"
            | "index"
            | "get"
            | "get-payload"
            | "variant-is"
            | "pin-get-payload"
            | "pin-get-payload-mut"
            | "size-of"
            | "align-of"
            | "offset-of"
            | "assert"
            | "debug-assert"
            | "panic"
            | "unreachable"
            | "literal"
            | "borrow"
            | "borrow-mut"
            | "pin-borrow"
            | "pin-borrow-mut"
            | "pin-own"
            | "pin-own-of"
            | "pin-own-borrow"
            | "pin-own-borrow-mut"
            | "pin-release"
            | "pin-read"
            | "pin-write"
            | "pin-set-field"
            | "ref"
            | "ref-mut"
            | "pin-ref"
            | "pin-ref-mut"
            | "pin-ptr-borrow"
            | "pin-ptr-borrow-mut"
            | "deref"
            | "deref-set"
            | "mut"
            | "unsafe"
            | "asm"
            | "linux-syscall"
            | "addr-of"
            | "addr-of-mut"
            | "ptr-read"
            | "ptr-address"
            | "ptr-null"
            | "ptr-is-null"
            | "ptr-borrow"
            | "ptr-borrow-mut"
            | "ptr-write"
            | "ptr-offset"
            | "clone"
            | "drop"
            | "forget"
            | "ptr"
            | "ptr-mut"
            | "gn"
            | "syntax-distribute"
            | "capability"
            | "import"
            | "import-external"
            | "std"
            | "println"
            | "cfg-if"
            | "cfg-else"
            | "cfg-and"
            | "cfg-or"
            | "cfg-is"
            | "cfg-not"
            | "gn-if"
            | "gn-fn"
            | "gn-call"
            | "gn-equal"
            | "gn-symbol?"
            | "gn-list?"
            | "gn-list"
            | "gn-symbol"
            | "gn-gensym"
            | "gn-symbol-append"
            | "gn-get"
            | "gn-first"
            | "gn-rest"
            | "gn-for-each"
            | "gn-error"
    )
}

fn is_operator_symbol(name: &str) -> bool {
    matches!(
        name,
        "+" | "-"
            | "*"
            | "/"
            | "%"
            | "&"
            | "|"
            | "^"
            | "<<"
            | ">>"
            | "<"
            | "<="
            | ">"
            | ">="
            | "=="
            | "!="
            | "!"
            | "&&"
            | "||"
    )
}

/// Classify builtin heads, never user-call targets. Qualified numeric spelling
/// stays builtin even when its overflow suffix is invalid (for diagnostics).
fn is_builtin_head(name: &str) -> bool {
    let name = name.strip_prefix('#').unwrap_or(name);
    is_builtin_form(name)
        || is_operator_symbol(name)
        || name.split_once('.').is_some_and(|(ty, rest)| {
            matches!(
                ty,
                "bool"
                    | "char"
                    | "i8"
                    | "i16"
                    | "i32"
                    | "i64"
                    | "i128"
                    | "isize"
                    | "u8"
                    | "u16"
                    | "u32"
                    | "u64"
                    | "u128"
                    | "usize"
                    | "f32"
                    | "f64"
            ) && is_operator_symbol(rest.split('.').next().unwrap_or(rest))
        })
}

fn requires_explicit_operator_type(name: &str) -> bool {
    matches!(
        name,
        "+" | "-"
            | "*"
            | "/"
            | "%"
            | "&"
            | "|"
            | "^"
            | "<<"
            | ">>"
            | "<"
            | "<="
            | ">"
            | ">="
            | "=="
            | "!="
            | "!"
    )
}

pub(crate) fn normalize_keywords(expression: Expr) -> Expr {
    match expression {
        // New intrinsic spelling stays distinct from a user function with
        // the same unprefixed name throughout ordinary call lowering.
        Expr::Symbol(name) if name == "#variant-is" => Expr::Symbol(name),
        Expr::Symbol(name) => Expr::Symbol(if let Some(keyword) = name.strip_prefix('#') {
            keyword.to_owned()
        } else {
            name
        }),
        Expr::List(mut items) => {
            // Keep the source distinction between the array type `#array` and
            // its value constructor `#array-of`, while sharing the established
            // internal array-constructor implementation.
            if matches!(items.first(), Some(Expr::Symbol(name)) if name == "#array-of") {
                items[0] = Expr::Symbol("array".to_owned());
            }
            Expr::List(items.into_iter().map(normalize_keywords).collect())
        }
        Expr::Block(statements) => Expr::Block(statements),
        Expr::Labeled { label, expression } => Expr::Labeled {
            label,
            expression: Box::new(normalize_keywords(*expression)),
        },
        Expr::Quote(value) => Expr::Quote(Box::new(normalize_keywords(*value))),
        Expr::QuasiQuote(value) => Expr::QuasiQuote(Box::new(normalize_keywords(*value))),
        Expr::Unquote(value) => Expr::Unquote(Box::new(normalize_keywords(*value))),
        Expr::UnquoteSplicing(value) => Expr::UnquoteSplicing(Box::new(normalize_keywords(*value))),
        other => other,
    }
}

fn load_imports_with_sources(
    source: &str,
    base: &Path,
    source_path: Option<&Path>,
    config: &CompileConfig,
) -> Result<(Vec<SpannedExpr>, Vec<SourceFile>), SourceError> {
    let mut active = Vec::new();
    let mut loaded = HashSet::new();
    let root_path = source_path.map_or_else(
        || base.join("<memory>"),
        |path| fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf()),
    );
    active.push(root_path.clone());
    let mut source_ids = HashMap::from([(root_path.clone(), 0u32)]);
    let mut source_files = vec![SourceFile {
        path: root_path,
        source: source.to_owned(),
    }];
    if source.len() > MAX_IMPORTED_SOURCE_BYTES {
        return Err(format!(
            "compilation sources exceed maximum total size of {MAX_IMPORTED_SOURCE_BYTES} bytes"
        )
        .into());
    }
    let mut budget = ImportBudget {
        import_count: 0,
        total_source_bytes: source.len(),
        max_import_count: MAX_IMPORT_COUNT,
        max_total_source_bytes: MAX_IMPORTED_SOURCE_BYTES,
        max_import_depth: MAX_IMPORT_DEPTH,
    };
    let forms = load_imports_inner(
        source,
        base,
        0,
        &mut active,
        &mut loaded,
        &mut source_ids,
        &mut source_files,
        &mut budget,
        config,
    )?;
    Ok((forms, source_files))
}

struct ImportBudget {
    import_count: usize,
    total_source_bytes: usize,
    max_import_count: usize,
    max_total_source_bytes: usize,
    max_import_depth: usize,
}

fn cfg_value(expression: &Expr) -> Result<String, String> {
    match expression {
        Expr::Symbol(value) => Ok(value.strip_prefix('#').unwrap_or(value).to_owned()),
        Expr::String(value) => Ok(value.clone()),
        Expr::Integer(value) => Ok(value.to_string()),
        Expr::UnsignedInteger(value) => Ok(value.to_string()),
        _ => Err("cfg values must be symbols, strings, or integer literals".into()),
    }
}

fn eval_cfg(expression: &SpannedExpr, config: &CompileConfig) -> Result<bool, SourceError> {
    let at = |message: String, index: Option<usize>| {
        SourceError::new(message, DiagnosticCode::Type).at(index
            .and_then(|index| expression.children.get(index))
            .map_or(expression.span, |child| child.span))
    };
    let Expr::List(items) = &expression.expr else {
        return Err(at("cfg condition must be a (#cfg-...) form".into(), None));
    };
    let Some(Expr::Symbol(operator)) = items.first() else {
        return Err(at(
            "cfg condition must start with a #cfg-* operator".into(),
            Some(0),
        ));
    };
    match operator.as_str() {
        "#cfg-is" if items.len() == 3 => {
            let Expr::Symbol(key) = &items[1] else {
                return Err(at(
                    "#cfg-is key must be a keyword such as #platform".into(),
                    Some(1),
                ));
            };
            let key = key.strip_prefix('#').unwrap_or(key);
            let actual = config
                .values
                .get(key)
                .ok_or_else(|| at(format!("unknown cfg key '#{key}'"), Some(1)))?;
            Ok(actual == &cfg_value(&items[2]).map_err(|error| at(error, Some(2)))?)
        }
        "#cfg-and" if items.len() >= 2 => expression.children[1..]
            .iter()
            .try_fold(true, |result, item| Ok(result && eval_cfg(item, config)?)),
        "#cfg-or" if items.len() >= 2 => expression.children[1..]
            .iter()
            .try_fold(false, |result, item| Ok(result || eval_cfg(item, config)?)),
        "#cfg-not" if items.len() == 2 => Ok(!eval_cfg(&expression.children[1], config)?),
        "#cfg-is" => Err(at("#cfg-is requires a key and a value".into(), Some(0))),
        "#cfg-and" | "#cfg-or" => Err(at(
            format!("{operator} requires at least one condition"),
            Some(0),
        )),
        "#cfg-not" => Err(at(
            "#cfg-not requires exactly one condition".into(),
            Some(0),
        )),
        _ => Err(at(
            format!("unsupported cfg condition '{operator}'"),
            Some(0),
        )),
    }
}

fn expand_cfg_forms(
    forms: Vec<SpannedExpr>,
    config: &CompileConfig,
) -> Result<Vec<SpannedExpr>, SourceError> {
    let mut expanded = Vec::new();
    for form in forms {
        let at_form = |error: SourceError| error.at(form.span);
        let Expr::List(items) = &form.expr else {
            expanded.push(form);
            continue;
        };
        if !matches!(items.first(), Some(Expr::Symbol(name)) if name == "#cfg-if") {
            if matches!(items.first(), Some(Expr::Symbol(name)) if name == "#cfg-else") {
                return Err(at_form(
                    "#cfg-else is only valid as the final branch of #cfg-if".into(),
                ));
            }
            expanded.push(form);
            continue;
        }
        if items.len() < 3 {
            return Err(at_form(
                "#cfg-if requires a condition and at least one form".into(),
            ));
        }
        let condition = eval_cfg(&form.children[1], config)?;
        let mut else_forms = None;
        let mut then_forms = Vec::new();
        for branch in &items[2..] {
            if let Expr::List(branch_items) = branch {
                if matches!(branch_items.first(), Some(Expr::Symbol(name)) if name == "#cfg-else") {
                    if else_forms.is_some() || branch_items.len() < 2 {
                        return Err(at_form(
                            "#cfg-else must occur once and contain at least one form".into(),
                        ));
                    }
                    else_forms = Some(branch_items[1..].to_vec());
                    continue;
                }
            }
            if else_forms.is_some() {
                return Err(at_form("#cfg-else must be the final #cfg-if branch".into()));
            }
            then_forms.push(branch.clone());
        }
        let selected = if condition {
            then_forms
        } else {
            else_forms.unwrap_or_default()
        };
        let selected = selected
            .into_iter()
            .map(|expr| SpannedExpr {
                expr,
                span: form.span,
                children: Vec::new(),
            })
            .collect();
        expanded.extend(expand_cfg_forms(selected, config).map_err(&at_form)?);
    }
    Ok(expanded)
}

fn load_imports_inner(
    source: &str,
    base: &Path,
    source_id: u32,
    active: &mut Vec<PathBuf>,
    loaded: &mut HashSet<String>,
    source_ids: &mut HashMap<PathBuf, u32>,
    source_files: &mut Vec<SourceFile>,
    budget: &mut ImportBudget,
    config: &CompileConfig,
) -> Result<Vec<SpannedExpr>, SourceError> {
    let tokens = lex(source).map_err(|error| {
        let mut span = error.span;
        span.source_id = source_id;
        let error =
            attach_span_to_source_error_kind(error.message, span, source_files, "lex error: ");
        attach_generator_source(error, source_files)
    })?;
    for token in &tokens {
        if matches!(&token.kind, TokenKind::Symbol(name) if gensym::reserved(name)) {
            let mut span = token.span;
            span.source_id = source_id;
            return Err(attach_span_to_source_error_kind(
                "identifiers beginning with 'lim.gensym.' are reserved for compiler-generated symbols".into(),
                span,
                source_files,
                "parse error: ",
            ));
        }
    }
    let mut expressions = Parser::new(&tokens).run().map_err(|error| {
        let mut span = error.span;
        span.source_id = source_id;
        let error =
            attach_span_to_source_error_kind(error.message, span, source_files, "parse error: ");
        attach_generator_source(error, source_files)
    })?;
    for expression in &mut expressions {
        set_source_id(expression, source_id);
    }
    let expressions = expand_cfg_forms(expressions, config)
        .map_err(|error| attach_generator_source(error, source_files))?;
    let mut result = Vec::new();
    for expression in expressions {
        let Some(specification) = import_form(&expression.expr)
            .map_err(|error| attach_span_to_source_error(error, expression.span, source_files))?
        else {
            result.push(expression);
            continue;
        };
        let unresolved_paths = std::iter::once(base.join(specification.path))
            .chain(
                config
                    .module_paths
                    .iter()
                    .map(|root| root.join(specification.path)),
            )
            .collect::<Vec<_>>();
        let unresolved_path = unresolved_paths
            .iter()
            .find(|candidate| standard_library::source(candidate).is_some() || candidate.is_file())
            .cloned()
            .unwrap_or_else(|| unresolved_paths[0].clone());
        let path = if standard_library::source(&unresolved_path).is_some() {
            Ok(unresolved_path.clone())
        } else {
            fs::canonicalize(&unresolved_path)
        }
        .map_err(|error| {
            let path_span = expression
                .children
                .get(1)
                .map_or(expression.span, |path| path.span);
            attach_span_to_source_error(
                format!(
                    "cannot resolve import '{}': {error}",
                    unresolved_path.display()
                ),
                path_span,
                source_files,
            )
        })?;
        if active.contains(&path) {
            let mut cycle = active
                .iter()
                .map(|entry| entry.display().to_string())
                .collect::<Vec<_>>();
            cycle.push(path.display().to_string());
            let path_span = expression
                .children
                .get(1)
                .map_or(expression.span, |path| path.span);
            return Err(attach_span_to_source_error(
                format!("import cycle: {}", cycle.join(" -> ")),
                path_span,
                source_files,
            ));
        }
        let path_span = expression
            .children
            .get(1)
            .map_or(expression.span, |path| path.span);
        if active.len() >= budget.max_import_depth {
            return Err(attach_span_to_source_error(
                format!(
                    "import nesting exceeds maximum depth of {}",
                    budget.max_import_depth
                ),
                path_span,
                source_files,
            ));
        }
        let key = format!(
            "{}:{}:{}",
            path.display(),
            if specification.external {
                "external"
            } else {
                "internal"
            },
            specification.prefix.unwrap_or("")
        );
        if !loaded.insert(key) {
            continue;
        }
        if budget.import_count >= budget.max_import_count {
            return Err(attach_span_to_source_error(
                format!(
                    "project exceeds maximum of {} imports",
                    budget.max_import_count
                ),
                path_span,
                source_files,
            ));
        }
        let embedded_source = standard_library::source(&path);
        let source_size = if let Some(source) = embedded_source {
            source.len()
        } else {
            usize::try_from(
                fs::metadata(&path)
                    .map_err(|error| {
                        format!("cannot inspect import '{}': {error}", path.display())
                    })?
                    .len(),
            )
            .unwrap_or(usize::MAX)
        };
        let next_total = budget
            .total_source_bytes
            .checked_add(source_size)
            .filter(|total| *total <= budget.max_total_source_bytes)
            .ok_or_else(|| {
                attach_span_to_source_error(
                    format!(
                        "compilation sources exceed maximum total size of {} bytes",
                        budget.max_total_source_bytes
                    ),
                    path_span,
                    source_files,
                )
            })?;
        let imported_source = embedded_source
            .map(|source| Ok(source.to_owned()))
            .unwrap_or_else(|| fs::read_to_string(&path))
            .map_err(|error| {
                attach_span_to_source_error(
                    format!("cannot read import '{}': {error}", path.display()),
                    expression.span,
                    source_files,
                )
            })?;
        budget.import_count += 1;
        budget.total_source_bytes = next_total;
        let imported_source_id = *source_ids.entry(path.clone()).or_insert_with(|| {
            let id = source_files.len() as u32;
            source_files.push(SourceFile {
                path: path.clone(),
                source: imported_source.clone(),
            });
            id
        });
        active.push(path.clone());
        let mut imported = load_imports_inner(
            &imported_source,
            path.parent().unwrap_or_else(|| Path::new(".")),
            imported_source_id,
            active,
            loaded,
            source_ids,
            source_files,
            budget,
            config,
        )?;
        active.pop();
        if let Some(prefix) = specification.prefix {
            let generator_names = imported
                .iter()
                .filter_map(|form| match &form.expr {
                    Expr::List(items)
                        if matches!(items.first(), Some(Expr::Symbol(keyword)) if keyword == "#gn" || keyword == "#gn-fn") =>
                    {
                        items.get(1).and_then(|name| match name {
                            Expr::Symbol(name) => Some(name.clone()),
                            _ => None,
                        })
                    }
                    _ => None,
                })
                .collect::<HashSet<_>>();
            for form in &mut imported {
                prefix_expression(&mut form.expr, prefix, &generator_names);
                if gensym::contains_reserved(&form.expr) {
                    let prefix_span = expression
                        .children
                        .get(2)
                        .map_or(expression.span, |node| node.span);
                    return Err(attach_span_to_source_error_kind(
                        "external import prefix cannot create compiler-reserved 'lim.gensym.' identifiers".into(),
                        prefix_span,
                        source_files,
                        "parse error: ",
                    ));
                }
            }
        }
        result.extend(imported);
    }
    Ok(result)
}

/// Collect every cfg key referenced by a source file and all of its imports.
/// Imports and cfg branches are scanned regardless of which branch is active.
pub fn collect_cfg_keys_from_path(source_path: &Path) -> Result<Vec<String>, String> {
    fn scan_file(
        path: &Path,
        visited: &mut HashSet<PathBuf>,
        keys: &mut BTreeSet<String>,
    ) -> Result<(), String> {
        let path = if standard_library::source(path).is_some() {
            Ok(path.to_owned())
        } else {
            fs::canonicalize(path)
        }
        .map_err(|error| format!("cannot resolve source '{}': {error}", path.display()))?;
        if !visited.insert(path.clone()) {
            return Ok(());
        }
        let source = standard_library::source(&path)
            .map(|source| Ok(source.to_owned()))
            .unwrap_or_else(|| fs::read_to_string(&path))
            .map_err(|error| format!("cannot read source '{}': {error}", path.display()))?;
        let expressions = parse(&source).map_err(|error| format!("{}: {error}", path.display()))?;
        for expression in expressions {
            scan_expr(&expression.expr, &path, visited, keys)?;
        }
        Ok(())
    }

    fn scan_expr(
        expression: &Expr,
        source_path: &Path,
        visited: &mut HashSet<PathBuf>,
        keys: &mut BTreeSet<String>,
    ) -> Result<(), String> {
        let Expr::List(items) = expression else {
            match expression {
                Expr::Block(statements) | Expr::Loop(statements) => {
                    for statement in statements {
                        scan_statement(statement, source_path, visited, keys)?;
                    }
                }
                Expr::Labeled { expression, .. }
                | Expr::Quote(expression)
                | Expr::QuasiQuote(expression)
                | Expr::Unquote(expression)
                | Expr::UnquoteSplicing(expression) => {
                    scan_expr(expression, source_path, visited, keys)?;
                }
                _ => {}
            }
            return Ok(());
        };
        if matches!(items.first(), Some(Expr::Symbol(name)) if name == "#cfg-is") {
            if items.len() != 3 {
                return Err(format!(
                    "{}: #cfg-is requires a key and a value",
                    source_path.display()
                ));
            }
            let Some(Expr::Symbol(key)) = items.get(1) else {
                return Err(format!(
                    "{}: #cfg-is key must be a keyword such as #platform",
                    source_path.display()
                ));
            };
            keys.insert(format!("#{}", key.strip_prefix('#').unwrap_or(key)));
        }
        if let Some(specification) = import_form(expression)? {
            let imported = source_path
                .parent()
                .unwrap_or_else(|| Path::new("."))
                .join(specification.path);
            scan_file(&imported, visited, keys)?;
        }
        for item in items {
            scan_expr(item, source_path, visited, keys)?;
        }
        Ok(())
    }

    fn scan_statement(
        statement: &Statement,
        source_path: &Path,
        visited: &mut HashSet<PathBuf>,
        keys: &mut BTreeSet<String>,
    ) -> Result<(), String> {
        match statement {
            Statement::Let { value, .. }
            | Statement::Destructure { value, .. }
            | Statement::Assign { value, .. }
            | Statement::FieldAssign { value, .. }
            | Statement::TupleAssign { value, .. }
            | Statement::EnumPayloadAssign { value, .. }
            | Statement::BreakValue(value)
            | Statement::BreakToValue { value, .. }
            | Statement::Return(Some(value))
            | Statement::Expr(value) => scan_expr(value, source_path, visited, keys)?,
            Statement::ArrayAssign { index, value, .. } => {
                scan_expr(index, source_path, visited, keys)?;
                scan_expr(value, source_path, visited, keys)?;
            }
            Statement::While { condition, body } => {
                scan_expr(condition, source_path, visited, keys)?;
                for statement in body {
                    scan_statement(statement, source_path, visited, keys)?;
                }
            }
            Statement::Loop { body } => {
                for statement in body {
                    scan_statement(statement, source_path, visited, keys)?;
                }
            }
            Statement::For {
                init,
                condition,
                step,
                body,
            } => {
                scan_statement(init, source_path, visited, keys)?;
                scan_expr(condition, source_path, visited, keys)?;
                scan_statement(step, source_path, visited, keys)?;
                for statement in body {
                    scan_statement(statement, source_path, visited, keys)?;
                }
            }
            Statement::Labeled { statement, .. } => {
                scan_statement(statement, source_path, visited, keys)?
            }
            Statement::LetElse {
                value, else_body, ..
            } => {
                scan_expr(value, source_path, visited, keys)?;
                for statement in else_body {
                    scan_statement(statement, source_path, visited, keys)?;
                }
            }
            Statement::Break
            | Statement::BreakTo(_)
            | Statement::Continue
            | Statement::ContinueTo(_)
            | Statement::Return(None) => {}
        }
        Ok(())
    }

    let mut visited = HashSet::new();
    let mut keys = BTreeSet::new();
    scan_file(source_path, &mut visited, &mut keys)?;
    Ok(keys.into_iter().collect())
}

struct ImportSpec<'a> {
    external: bool,
    path: &'a str,
    prefix: Option<&'a str>,
}

fn import_form(expression: &Expr) -> Result<Option<ImportSpec<'_>>, String> {
    let Expr::List(items) = expression else {
        return Ok(None);
    };
    let Some(Expr::Symbol(operator)) = items.first() else {
        return Ok(None);
    };
    match operator.as_str() {
        "#std" => {
            if items.len() != 1 {
                return Err("#std takes no arguments".into());
            }
            Ok(Some(ImportSpec {
                external: false,
                path: standard_library::ROOT,
                prefix: None,
            }))
        }
        "#import" => {
            if items.len() != 2 {
                return Err("#import requires one string path".into());
            }
            match items.get(1) {
                Some(Expr::String(path)) => Ok(Some(ImportSpec {
                    external: false,
                    path,
                    prefix: None,
                })),
                _ => Err("#import path must be a string literal".into()),
            }
        }
        "#import-external" => {
            if items.len() != 3 {
                return Err("#import-external requires a string path and symbol prefix".into());
            }
            let path = match items.get(1) {
                Some(Expr::String(path)) => path,
                _ => return Err("#import-external path must be a string literal".into()),
            };
            let prefix = match items.get(2) {
                Some(Expr::Symbol(prefix)) if !prefix.is_empty() && !prefix.starts_with('#') => {
                    prefix.as_str()
                }
                _ => return Err("#import-external prefix must be an identifier prefix".into()),
            };
            Ok(Some(ImportSpec {
                external: true,
                path,
                prefix: Some(prefix),
            }))
        }
        _ => Ok(None),
    }
}

fn prefix_expression(expression: &mut Expr, prefix: &str, generator_names: &HashSet<String>) {
    match expression {
        Expr::Function(_) => unreachable!("imports are prefixed before call normalization"),
        Expr::Symbol(name) => {
            if !name.starts_with('#') && !is_unprefixed_builtin_name(name) {
                *name = format!("{prefix}{name}");
            }
        }
        Expr::List(items) => {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "#gn-symbol") {
                for item in items.iter_mut().skip(1) {
                    match item {
                        Expr::String(name)
                            if !name.starts_with('#') && !is_unprefixed_builtin_name(name) =>
                        {
                            *name = format!("{prefix}{name}");
                        }
                        other => prefix_expression(other, prefix, generator_names),
                    }
                }
                return;
            }
            let is_generated_call = matches!(items.first(), Some(Expr::At));
            for (index, item) in items.iter_mut().enumerate() {
                if is_generated_call && index == 1 {
                    if let Expr::Symbol(name) = item {
                        if generator_names.contains(name) {
                            *name = format!("{prefix}{name}");
                        }
                    }
                } else {
                    prefix_expression(item, prefix, generator_names);
                }
            }
        }
        Expr::Quote(value)
        | Expr::QuasiQuote(value)
        | Expr::Unquote(value)
        | Expr::UnquoteSplicing(value) => prefix_expression(value, prefix, generator_names),
        Expr::Block(_)
        | Expr::Loop(_)
        | Expr::Labeled { .. }
        | Expr::Integer(_)
        | Expr::UnsignedInteger(_)
        | Expr::Float(_)
        | Expr::Char(_)
        | Expr::String(_)
        | Expr::At => {}
    }
}

fn is_unprefixed_builtin_name(name: &str) -> bool {
    // Keywords are always #-prefixed. An unprefixed spelling such as
    // `panic` is an ordinary identifier and must follow external imports.
    matches!(
        name,
        "true"
            | "false"
            | "_"
            | "()"
            | "!"
            | "bool"
            | "char"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "f32"
            | "f64"
    )
}

/// Materialize built-in generated declarations as source files.
///
/// Expansion remains part of parse_program; this helper gives command-line
/// builds an inspectable cache of generated Lim source under .lim/cache/.
pub fn write_generated_sources(source: &str, directory: &Path) -> Result<(), String> {
    let base =
        env::current_dir().map_err(|error| format!("cannot get current directory: {error}"))?;
    Ok(write_generated_sources_in_directory(
        source,
        &base,
        None,
        directory,
        &CompileConfig::default(),
        None,
    )?)
}

/// Materialize generated source while resolving imports relative to `source_path`.
pub fn write_generated_sources_from_path(
    source: &str,
    source_path: &Path,
    directory: &Path,
) -> Result<(), String> {
    let base = source_path.parent().unwrap_or_else(|| Path::new("."));
    Ok(write_generated_sources_in_directory(
        source,
        base,
        Some(source_path),
        directory,
        &CompileConfig::default(),
        None,
    )?)
}

/// Materialize generated source using the same cfg values as compilation.
pub fn write_generated_sources_from_path_with_config(
    source: &str,
    source_path: &Path,
    directory: &Path,
    config: &CompileConfig,
) -> Result<(), String> {
    let base = source_path.parent().unwrap_or_else(|| Path::new("."));
    write_generated_sources_in_directory(source, base, Some(source_path), directory, config, None)
        .map_err(String::from)
}

/// Materialize generated source using cfg values and a persistent generator cache.
pub fn write_generated_sources_from_path_with_config_and_cache(
    source: &str,
    source_path: &Path,
    directory: &Path,
    config: &CompileConfig,
    cache_directory: &Path,
) -> Result<(), String> {
    let base = source_path.parent().unwrap_or_else(|| Path::new("."));
    Ok(write_generated_sources_in_directory(
        source,
        base,
        Some(source_path),
        directory,
        config,
        Some(cache_directory),
    )?)
}

/// Diagnostic-returning variant of generated-source materialization.
pub fn write_generated_sources_diagnostic(
    source: &str,
    source_path: &Path,
    directory: &Path,
    config: &CompileConfig,
    cache_directory: &Path,
) -> Result<(), Diagnostic> {
    write_generated_sources_in_directory(
        source,
        source_path.parent().unwrap_or(Path::new(".")),
        Some(source_path),
        directory,
        config,
        Some(cache_directory),
    )
    .map_err(|error| generator_diagnostic(error, source_path, source))
}

fn write_generated_sources_in_directory(
    source: &str,
    base: &Path,
    source_path: Option<&Path>,
    directory: &Path,
    config: &CompileConfig,
    cache_directory: Option<&Path>,
) -> Result<(), SourceError> {
    let prepared = prepare_program_syntax(source, base, source_path, config, cache_directory)?;
    let has_async = prepared.expressions.iter().any(|expression| matches!(&expression.expr,
        Expr::List(items) if matches!(items.first(), Some(Expr::At))
            && matches!(items.get(1), Some(Expr::Symbol(kind)) if matches!(kind.as_str(), "async-fn" | "async-fn-pinned"))));
    let plans = if has_async {
        parse_prepared_program_with_capture_plans(&prepared)?.1
    } else {
        AsyncCapturePlans::new()
    };
    write_prepared_generated_sources(&prepared, directory, cache_directory, &plans)
}

fn write_prepared_generated_sources(
    prepared: &PreparedProgramSyntax,
    directory: &Path,
    cache_directory: Option<&Path>,
    async_plans: &AsyncCapturePlans,
) -> Result<(), SourceError> {
    let expanded = &prepared.expressions;
    let user_generated = &prepared.user_generated;
    let dependency_context = &prepared.dependency_context;
    let worker_functions = &prepared.worker_functions;
    let copy_types = &prepared.async_copy_types;
    let async_types = &prepared.async_types;
    let generated_cache = cache_directory
        .map(Path::to_path_buf)
        .unwrap_or_else(|| directory.join("cache"));
    for expression in expanded {
        if !matches!(&expression.expr, Expr::List(items) if matches!(items.first(), Some(Expr::At)))
        {
            continue;
        }
        let capture_key = (
            expression.span.source_id,
            expression.span.start,
            expression.span.end,
        );
        let capture_plan = async_plans.get(&capture_key);
        let invocation = expression_source(&expression.expr)?;
        let original = normalize_builtin_generator_invocation(&expression.expr)?;
        let Expr::List(forms) = normalize_keywords(original.clone()) else {
            continue;
        };
        if !matches!(forms.first(), Some(Expr::At)) {
            continue;
        }
        let kind = expect_symbol(forms.get(1), "generated declaration name")?;
        if !matches!(
            kind,
            "thread-spawn"
                | "vec"
                | "vec-alloc"
                | "vec-sort"
                | "optional"
                | "result"
                | "async-fn"
                | "async-fn-pinned"
        ) {
            continue;
        }
        let key = format!(
            "lim-inspectable-generated-source-v4\ncompiler={}\nimplementation={}\ntarget=x86_64-sysv\ndependency-context={}\nasync-capture-plan={}\nasync-copy-types={}\nasync-type-environment={}\ninvocation={invocation}",
            env!("CARGO_PKG_VERSION"),
            env!("LIM_BUILD_FINGERPRINT"),
            dependency_context,
            async_capture_plan_identity(capture_plan),
            async_copy_type_identity(&copy_types),
            async_type_environment_identity(&async_types),
        );
        generator::cached_generated_source(&generated_cache, &key, || {
            if matches!(kind, "async-fn" | "async-fn-pinned") {
                let source = async_fn::generated_source_with_environment(
                    &original,
                    capture_plan,
                    &copy_types,
                    &async_types,
                )?;
                async_dispatch::collapse(&source, &async_types)
            } else {
                materialize_builtin_generated_source(&kind, &forms, &worker_functions)
            }
        })?;
    }
    if !user_generated.is_empty() {
        let source = user_generated
            .iter()
            .map(expression_source)
            .collect::<Result<Vec<_>, _>>()?
            .join("\n");
        let key = format!(
            "lim-inspectable-user-generator-source-v2\ncompiler={}\ntarget={}-{}\ndependency-context={}\nsource={source}",
            env!("CARGO_PKG_VERSION"),
            std::env::consts::ARCH,
            std::env::consts::OS,
            dependency_context,
        );
        generator::cached_generated_source(&generated_cache, &key, || Ok(source))?;
    }
    Ok(())
}

fn generator_dependency_context(expressions: &[SpannedExpr], config: &CompileConfig) -> String {
    let mut values = config
        .values
        .iter()
        .map(|(key, value)| format!("{key}={value}"))
        .collect::<Vec<_>>();
    values.sort();
    // Hash syntax once rather than duplicating a multi-megabyte debug dump in
    // every invocation key. Spans remain part of the dependency identity: cached
    // diagnostics must not retain locations from a differently laid-out source.
    let mut identity = Vec::new();
    for expression in expressions {
        let syntax = expression_source(&expression.expr).expect("loaded syntax is printable");
        identity.extend_from_slice(&(syntax.len() as u64).to_le_bytes());
        identity.extend_from_slice(syntax.as_bytes());
        append_dependency_spans(expression, &mut identity);
    }
    format!(
        "dependency-v2\ncfg={values:?}\nloaded-hash={:032x}",
        generator::stable_hash(&identity)
    )
}

fn is_thread_spawn_invocation(expression: &SpannedExpr) -> bool {
    matches!(&expression.expr, Expr::List(items)
        if matches!(items.first(), Some(Expr::At))
        && matches!(items.get(1), Some(Expr::Symbol(kind)) if kind == "thread-spawn"))
}

fn is_async_invocation(expression: &SpannedExpr) -> bool {
    matches!(&expression.expr, Expr::List(items)
        if matches!(items.first(), Some(Expr::At))
        && matches!(items.get(1), Some(Expr::Symbol(kind)) if matches!(kind.as_str(), "async-fn" | "async-fn-pinned")))
}

fn append_dependency_spans(expression: &SpannedExpr, identity: &mut Vec<u8>) {
    let span = expression.span;
    for value in [
        span.start,
        span.end,
        span.line,
        span.column,
        span.source_id as usize,
        expression.children.len(),
    ] {
        identity.extend_from_slice(&(value as u64).to_le_bytes());
    }
    for child in &expression.children {
        append_dependency_spans(child, identity);
    }
}

fn materialize_builtin_generated_source(
    kind: &str,
    forms: &[Expr],
    worker_functions: &HashMap<String, Function>,
) -> Result<String, String> {
    if kind == "thread-spawn" {
        let task = expect_symbol(forms.get(2), "thread task type name")?;
        let worker = expect_symbol(forms.get(3), "thread worker function")?;
        let worker_function = worker_functions.get(worker).ok_or_else(|| {
            format!("cannot materialize @thread-spawn: worker '{worker}' is not defined")
        })?;
        return Ok(thread_task_generated_source(task, worker, worker_function));
    }
    if kind == "vec" {
        return generated_vec_source(forms)
            .map_err(|error| format!("{error} while materializing @vec {forms:?}"));
    }
    if kind == "vec-alloc" {
        return generated_vec_allocator_source(forms)
            .map_err(|error| format!("{error} while materializing @vec-alloc {forms:?}"));
    }
    if kind == "vec-sort" {
        return generated_vec_sort_source(forms);
    }

    let item = parse_generated_item(forms)
        .map_err(|error| format!("{error} while materializing @{kind} {forms:?}"))?;
    let Item::Enum { name, variants, .. } = item else {
        return Err(format!("@{kind} did not produce an enum"));
    };
    let first = variants
        .first()
        .and_then(|variant| variant.fields.first())
        .ok_or_else(|| format!("{kind} expansion has no payload type"))?;
    let first_name = variants
        .first()
        .map(|variant| variant.name.as_str())
        .ok_or_else(|| format!("{kind} expansion has no payload constructor"))?;
    let second_name = variants
        .get(1)
        .map(|variant| variant.name.as_str())
        .unwrap_or("none");
    let first_source = type_source(first);
    if kind == "optional" {
        Ok(format!(
            "(#enum {name} (({first_name} {first_source}) {second_name}))\n(#fn {name}-construct ((value {first_source})) {name} (#return ({first_name} value)))\n(#fn {name}-is-some ((value {name})) bool (#return (#match value (#case ({first_name} _) true) (#case {second_name} false))))\n(#fn {name}-unwrap-or ((value {name}) (fallback {first_source})) {first_source} (#return (#match value (#case ({first_name} payload) payload) (#case {second_name} fallback))))\n"
        ))
    } else if kind == "result" {
        let second = variants
            .get(1)
            .and_then(|variant| variant.fields.first())
            .ok_or_else(|| "result expansion has no error payload type".to_owned())?;
        let second_source = type_source(second);
        Ok(format!(
            "(#enum {name} (({first_name} {first_source}) ({second_name} {second_source})))\n(#fn {name}-ok ((value {first_source})) {name} (#return ({first_name} value)))\n(#fn {name}-err ((error {second_source})) {name} (#return ({second_name} error)))\n(#fn {name}-is-ok ((value {name})) bool (#return (#match value (#case ({first_name} _) true) (#case ({second_name} _) false))))\n(#fn {name}-unwrap-or ((value {name}) (fallback {first_source})) {first_source} (#return (#match value (#case ({first_name} payload) payload) (#case ({second_name} _) fallback))))\n(#fn {name}-unwrap-err-or ((value {name}) (fallback {second_source})) {second_source} (#return (#match value (#case ({first_name} _) fallback) (#case ({second_name} error) error))))\n"
        ))
    } else {
        Err(format!("unknown builtin generated declaration '@{kind}'"))
    }
}

/// Turn a built-in generator's named syntax arguments into its internal
/// declaration order. User-defined generators continue to receive literals.
fn normalize_builtin_generator_invocation(expression: &Expr) -> Result<Expr, String> {
    let Expr::List(items) = expression else {
        return Ok(expression.clone());
    };
    if !matches!(items.first(), Some(Expr::At)) {
        return Ok(expression.clone());
    }
    let Some(Expr::Symbol(kind)) = items.get(1) else {
        return Ok(expression.clone());
    };
    let keys: &[&str] = match kind.as_str() {
        "optional" => &["type", "name"],
        "result" => &["ok", "error", "name"],
        "thread-spawn" => &["task", "worker"],
        "vec" => &["element", "allocator", "name"],
        "vec-alloc" => &[
            "element",
            "allocator",
            "vector",
            "alloc-result",
            "alloc-error",
            "alloc",
            "grow",
            "dealloc",
            "destroy",
        ],
        "vec-sort" => &["element", "vector", "comparator"],
        "async-fn" | "async-fn-pinned" => &["names", "waker", "function", "cancel"],
        _ => return Ok(expression.clone()),
    };
    let Some(Expr::List(arguments)) = items.get(2) else {
        return Err(format!(
            "@{kind} requires a named argument list (: key value : ...)"
        ));
    };
    if items.len() != 3 {
        return Err(format!("@{kind} requires exactly one named argument list"));
    }
    let mut values = HashMap::new();
    for argument in arguments {
        let Expr::List(pair) = argument else {
            return Err(format!("@{kind} arguments must be (: key value : ...)"));
        };
        let [Expr::Symbol(key), value] = pair.as_slice() else {
            return Err(format!("@{kind} arguments must be (: key value : ...)"));
        };
        if !keys.contains(&key.as_str()) {
            return Err(format!("@{kind} has no argument '{key}'"));
        }
        if values.insert(key.as_str(), value.clone()).is_some() {
            return Err(format!("@{kind} repeats argument '{key}'"));
        }
    }
    let mut normalized = vec![Expr::At, Expr::Symbol(kind.clone())];
    let optional_async_cancel = matches!(kind.as_str(), "async-fn" | "async-fn-pinned");
    for key in keys {
        if optional_async_cancel && *key == "cancel" && !values.contains_key(key) {
            continue;
        }
        normalized.push(
            values
                .remove(key)
                .ok_or_else(|| format!("@{kind} is missing argument '{key}'"))?,
        );
    }
    Ok(Expr::List(normalized))
}

pub(crate) fn expression_source(expression: &Expr) -> Result<String, String> {
    match expression {
        Expr::List(items) => Ok(format!(
            "({})",
            items
                .iter()
                .map(expression_source)
                .collect::<Result<Vec<_>, _>>()?
                .join(" ")
        )),
        Expr::Symbol(name) | Expr::Function(name) => Ok(name.clone()),
        Expr::Integer(value) => Ok(value.to_string()),
        Expr::UnsignedInteger(value) => Ok(value.to_string()),
        Expr::Float(value) => Ok(value.clone()),
        Expr::Char(value) => Ok(match value {
            ' ' => "#\\space".into(),
            '\n' => "#\\newline".into(),
            '\t' => "#\\tab".into(),
            '\r' => "#\\return".into(),
            '\0' => "#\\null".into(),
            value
                if value.is_whitespace()
                    || matches!(value, '(' | ')' | '\'' | '`' | ',' | '"' | '@' | '#' | ';') =>
            {
                format!("#\\u{{{:x}}}", u32::from(*value))
            }
            value => format!("#\\{value}"),
        }),
        Expr::String(value) => {
            let mut source = String::from("\"");
            for character in value.chars() {
                match character {
                    '\n' => source.push_str("\\n"),
                    '\r' => source.push_str("\\r"),
                    '\t' => source.push_str("\\t"),
                    '\\' => source.push_str("\\\\"),
                    '"' => source.push_str("\\\""),
                    value if value.is_control() => {
                        source.push_str(&format!("\\u{{{:x}}}", u32::from(value)));
                    }
                    value => source.push(value),
                }
            }
            source.push('"');
            Ok(source)
        }
        Expr::At => Ok("@".into()),
        Expr::Quote(value) => Ok(format!("'{}", expression_source(value)?)),
        Expr::QuasiQuote(value) => Ok(format!("`{}", expression_source(value)?)),
        Expr::Unquote(value) => Ok(format!(",{}", expression_source(value)?)),
        Expr::UnquoteSplicing(value) => Ok(format!(",@{}", expression_source(value)?)),
        Expr::Block(_) | Expr::Loop(_) | Expr::Labeled { .. } => {
            Err("cannot serialize this generated syntax form yet".into())
        }
    }
}

fn type_source(ty: &Type) -> String {
    match ty {
        Type::Unit => "()".into(),
        Type::Never => "!".into(),
        Type::Bool => "bool".into(),
        Type::Char => "char".into(),
        Type::I8 => "i8".into(),
        Type::I16 => "i16".into(),
        Type::I32 => "i32".into(),
        Type::I64 => "i64".into(),
        Type::I128 => "i128".into(),
        Type::Isize => "isize".into(),
        Type::U8 => "u8".into(),
        Type::U16 => "u16".into(),
        Type::U32 => "u32".into(),
        Type::U64 => "u64".into(),
        Type::U128 => "u128".into(),
        Type::Usize => "usize".into(),
        Type::F32 => "f32".into(),
        Type::F64 => "f64".into(),
        Type::Reference { mutable, target } => format!(
            "(#{} {})",
            if *mutable { "ref-mut" } else { "ref" },
            type_source(target)
        ),
        Type::PinnedReference { mutable, target } => format!(
            "(#{} {})",
            if *mutable { "pin-ref-mut" } else { "pin-ref" },
            type_source(target)
        ),
        Type::PinOwned(target) => format!("(#pin-own {})", type_source(target)),
        Type::RawPointer { mutable, target } => format!(
            "(#{} {})",
            if *mutable { "ptr-mut" } else { "ptr" },
            type_source(target)
        ),
        Type::Slice(target) => format!("(#slice {})", type_source(target)),
        Type::MutableSlice(target) => format!("(#slice-mut {})", type_source(target)),
        Type::Atomic(target) => format!("(#atomic {})", type_source(target)),
        Type::Generic(name) => name.clone(),
        Type::Named(name) => name.clone(),
        Type::Tuple(fields) => format!(
            "(#tuple {})",
            fields.iter().map(type_source).collect::<Vec<_>>().join(" ")
        ),
        Type::Array(element, length) => format!("(#array {} {})", type_source(element), length),
    }
}

fn applied_type_parts(name: &str) -> Option<(String, Vec<String>)> {
    let open = name.find('<')?;
    if open == 0 || !name.ends_with('>') {
        return None;
    }
    let mut depth = 0usize;
    let mut start = open + 1;
    let mut arguments = Vec::new();
    for (index, character) in name.char_indices().skip(open + 1) {
        match character {
            '<' => depth += 1,
            '>' if depth > 0 => depth -= 1,
            ',' if depth == 0 => {
                arguments.push(name[start..index].trim().to_owned());
                start = index + character.len_utf8();
            }
            _ => {}
        }
    }
    let end = name.len() - 1;
    arguments.push(name[start..end].trim().to_owned());
    if arguments.iter().any(String::is_empty) {
        return None;
    }
    Some((name[..open].to_owned(), arguments))
}

fn specialized_type_name(base: &str, arguments: &[Type]) -> String {
    format!(
        "{}${}",
        base,
        arguments
            .iter()
            .map(type_source)
            .map(|name| name.replace(['(', ')', ' ', ','], "_"))
            .collect::<Vec<_>>()
            .join("$")
    )
}

fn specialize_type(
    ty: &Type,
    substitutions: &HashMap<String, Type>,
    templates: &HashMap<String, Item>,
    names: &mut HashMap<String, String>,
    generated: &mut Vec<Item>,
) -> Result<Type, String> {
    match ty {
        Type::Generic(name) => Ok(substitutions
            .get(name)
            .cloned()
            .unwrap_or_else(|| ty.clone())),
        Type::Array(element, length) => Ok(Type::Array(
            Box::new(specialize_type(
                element,
                substitutions,
                templates,
                names,
                generated,
            )?),
            *length,
        )),
        Type::Tuple(fields) => Ok(Type::Tuple(
            fields
                .iter()
                .map(|field| specialize_type(field, substitutions, templates, names, generated))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        Type::Named(name) => {
            let Some((base, argument_names)) = applied_type_parts(name) else {
                return Ok(Type::Named(name.clone()));
            };
            let Some(template) = templates.get(&base).cloned() else {
                return Ok(Type::Named(name.clone()));
            };
            let (parameters, _) = match &template {
                Item::Struct {
                    type_parameters,
                    fields,
                    ..
                } => (type_parameters.clone(), fields.len()),
                Item::Enum {
                    type_parameters,
                    variants,
                    ..
                } => (type_parameters.clone(), variants.len()),
                Item::TypeAlias {
                    type_parameters, ..
                } => (type_parameters.clone(), 0),
                _ => return Ok(Type::Named(name.clone())),
            };
            if parameters.len() != argument_names.len() {
                return Err(format!(
                    "generic type '{base}' expects {} type arguments, got {}",
                    parameters.len(),
                    argument_names.len()
                ));
            }
            let arguments = argument_names
                .iter()
                .map(|argument| {
                    let parsed = substitutions
                        .get(argument)
                        .cloned()
                        .unwrap_or_else(|| Type::from_name(argument));
                    specialize_type(&parsed, substitutions, templates, names, generated)
                })
                .collect::<Result<Vec<_>, _>>()?;
            if arguments
                .iter()
                .any(|argument| matches!(argument, Type::Generic(_)))
            {
                return Ok(Type::Named(name.clone()));
            }
            if let Some(specialized) = names.get(name) {
                return Ok(Type::Named(specialized.clone()));
            }
            let specialized = specialized_type_name(&base, &arguments);
            names.insert(name.clone(), specialized.clone());
            let mut type_substitutions = HashMap::new();
            for (parameter, argument) in parameters.iter().zip(arguments) {
                type_substitutions.insert(parameter.clone(), argument);
            }
            let concrete = match template {
                Item::Struct {
                    name: _,
                    representation,
                    fields,
                    ..
                } => Item::Struct {
                    name: specialized.clone(),
                    representation,
                    type_parameters: Vec::new(),
                    fields: fields
                        .iter()
                        .map(|field| {
                            Ok(Field {
                                name: field.name.clone(),
                                ty: specialize_type(
                                    &field.ty,
                                    &type_substitutions,
                                    templates,
                                    names,
                                    generated,
                                )?,
                            })
                        })
                        .collect::<Result<Vec<_>, String>>()?,
                },
                Item::Enum {
                    name: _,
                    representation,
                    variants,
                    ..
                } => Item::Enum {
                    name: specialized.clone(),
                    representation,
                    type_parameters: Vec::new(),
                    variants: variants
                        .iter()
                        .map(|variant| {
                            Ok(EnumVariant {
                                name: variant.name.clone(),
                                fields: variant
                                    .fields
                                    .iter()
                                    .map(|field| {
                                        specialize_type(
                                            field,
                                            &type_substitutions,
                                            templates,
                                            names,
                                            generated,
                                        )
                                    })
                                    .collect::<Result<Vec<_>, _>>()?,
                                discriminant: variant.discriminant,
                            })
                        })
                        .collect::<Result<Vec<_>, String>>()?,
                },
                Item::TypeAlias { target, .. } => {
                    return specialize_type(
                        &target,
                        &type_substitutions,
                        templates,
                        names,
                        generated,
                    );
                }
                _ => unreachable!("generic type template is not an aggregate"),
            };
            generated.push(concrete);
            Ok(Type::Named(specialized))
        }
        _ => Ok(ty.clone()),
    }
}

fn specialize_expr(
    expression: &Expr,
    substitutions: &HashMap<String, Type>,
    templates: &HashMap<String, Item>,
    names: &mut HashMap<String, String>,
    generated: &mut Vec<Item>,
) -> Result<Expr, String> {
    match expression {
        Expr::List(items) => Ok(Expr::List(
            items
                .iter()
                .enumerate()
                .map(|(index, item)| {
                    if index == 0 {
                        if let Expr::Symbol(name) = item {
                            if let Type::Named(ty) = specialize_type(
                                &Type::Named(name.clone()),
                                substitutions,
                                templates,
                                names,
                                generated,
                            )? {
                                return Ok(Expr::Symbol(ty));
                            }
                        }
                    }
                    specialize_expr(item, substitutions, templates, names, generated)
                })
                .collect::<Result<Vec<_>, String>>()?,
        )),
        Expr::Block(statements) => Ok(Expr::Block(
            statements
                .iter()
                .map(|statement| {
                    specialize_statement(statement, substitutions, templates, names, generated)
                })
                .collect::<Result<Vec<_>, _>>()?,
        )),
        Expr::Loop(statements) => Ok(Expr::Loop(
            statements
                .iter()
                .map(|statement| {
                    specialize_statement(statement, substitutions, templates, names, generated)
                })
                .collect::<Result<Vec<_>, _>>()?,
        )),
        Expr::Labeled { label, expression } => Ok(Expr::Labeled {
            label: label.clone(),
            expression: Box::new(specialize_expr(
                expression,
                substitutions,
                templates,
                names,
                generated,
            )?),
        }),
        Expr::Quote(value) => Ok(Expr::Quote(Box::new(specialize_expr(
            value,
            substitutions,
            templates,
            names,
            generated,
        )?))),
        Expr::QuasiQuote(value) => Ok(Expr::QuasiQuote(Box::new(specialize_expr(
            value,
            substitutions,
            templates,
            names,
            generated,
        )?))),
        Expr::Unquote(value) => Ok(Expr::Unquote(Box::new(specialize_expr(
            value,
            substitutions,
            templates,
            names,
            generated,
        )?))),
        Expr::UnquoteSplicing(value) => Ok(Expr::UnquoteSplicing(Box::new(specialize_expr(
            value,
            substitutions,
            templates,
            names,
            generated,
        )?))),
        _ => Ok(expression.clone()),
    }
}

fn specialize_statement(
    statement: &Statement,
    substitutions: &HashMap<String, Type>,
    templates: &HashMap<String, Item>,
    names: &mut HashMap<String, String>,
    generated: &mut Vec<Item>,
) -> Result<Statement, String> {
    Ok(match statement {
        Statement::Let {
            name,
            ty,
            value,
            mutable,
        } => Statement::Let {
            name: name.clone(),
            ty: specialize_type(ty, substitutions, templates, names, generated)?,
            value: specialize_expr(value, substitutions, templates, names, generated)?,
            mutable: *mutable,
        },
        Statement::Destructure {
            pattern,
            ty,
            value,
            mutable,
        } => Statement::Destructure {
            pattern: pattern.clone(),
            ty: specialize_type(ty, substitutions, templates, names, generated)?,
            value: specialize_expr(value, substitutions, templates, names, generated)?,
            mutable: *mutable,
        },
        Statement::LetElse {
            pattern,
            ty,
            value,
            else_body,
        } => Statement::LetElse {
            pattern: pattern.clone(),
            ty: specialize_type(ty, substitutions, templates, names, generated)?,
            value: specialize_expr(value, substitutions, templates, names, generated)?,
            else_body: else_body
                .iter()
                .map(|statement| {
                    specialize_statement(statement, substitutions, templates, names, generated)
                })
                .collect::<Result<Vec<_>, _>>()?,
        },
        Statement::Assign { name, value } => Statement::Assign {
            name: name.clone(),
            value: specialize_expr(value, substitutions, templates, names, generated)?,
        },
        Statement::ArrayAssign { name, index, value } => Statement::ArrayAssign {
            name: name.clone(),
            index: specialize_expr(index, substitutions, templates, names, generated)?,
            value: specialize_expr(value, substitutions, templates, names, generated)?,
        },
        Statement::FieldAssign { name, field, value } => Statement::FieldAssign {
            name: name.clone(),
            field: field.clone(),
            value: specialize_expr(value, substitutions, templates, names, generated)?,
        },
        Statement::TupleAssign { name, index, value } => Statement::TupleAssign {
            name: name.clone(),
            index: *index,
            value: specialize_expr(value, substitutions, templates, names, generated)?,
        },
        Statement::EnumPayloadAssign {
            name,
            variant,
            index,
            value,
        } => Statement::EnumPayloadAssign {
            name: name.clone(),
            variant: variant.clone(),
            index: *index,
            value: specialize_expr(value, substitutions, templates, names, generated)?,
        },
        Statement::While { condition, body } => Statement::While {
            condition: specialize_expr(condition, substitutions, templates, names, generated)?,
            body: body
                .iter()
                .map(|statement| {
                    specialize_statement(statement, substitutions, templates, names, generated)
                })
                .collect::<Result<Vec<_>, _>>()?,
        },
        Statement::Loop { body } => Statement::Loop {
            body: body
                .iter()
                .map(|statement| {
                    specialize_statement(statement, substitutions, templates, names, generated)
                })
                .collect::<Result<Vec<_>, _>>()?,
        },
        Statement::For {
            init,
            condition,
            step,
            body,
        } => Statement::For {
            init: Box::new(specialize_statement(
                init,
                substitutions,
                templates,
                names,
                generated,
            )?),
            condition: specialize_expr(condition, substitutions, templates, names, generated)?,
            step: Box::new(specialize_statement(
                step,
                substitutions,
                templates,
                names,
                generated,
            )?),
            body: body
                .iter()
                .map(|statement| {
                    specialize_statement(statement, substitutions, templates, names, generated)
                })
                .collect::<Result<Vec<_>, _>>()?,
        },
        Statement::Labeled { label, statement } => Statement::Labeled {
            label: label.clone(),
            statement: Box::new(specialize_statement(
                statement,
                substitutions,
                templates,
                names,
                generated,
            )?),
        },
        Statement::Return(value) => Statement::Return(
            value
                .as_ref()
                .map(|value| specialize_expr(value, substitutions, templates, names, generated))
                .transpose()?,
        ),
        Statement::Expr(value) => Statement::Expr(specialize_expr(
            value,
            substitutions,
            templates,
            names,
            generated,
        )?),
        Statement::BreakValue(value) => Statement::BreakValue(specialize_expr(
            value,
            substitutions,
            templates,
            names,
            generated,
        )?),
        Statement::BreakToValue { label, value } => Statement::BreakToValue {
            label: label.clone(),
            value: specialize_expr(value, substitutions, templates, names, generated)?,
        },
        Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_) => statement.clone(),
    })
}

fn specialize_generic_types(
    mut items: Vec<Item>,
    statement_spans: &HashMap<(String, usize), Span>,
    statement_expressions: &HashMap<(String, usize), SpannedExpr>,
    declaration_spans: &HashMap<String, Span>,
    declaration_expressions: &HashMap<String, SpannedExpr>,
    source_files: &[SourceFile],
) -> Result<Vec<Item>, SourceError> {
    for item in &items {
        let Item::UnsafeThreadAnnotation {
            property,
            type_name,
        } = item
        else {
            continue;
        };
        let declaration = items.iter().find(|candidate| match candidate {
            Item::Struct { name, .. } | Item::Enum { name, .. } | Item::TypeAlias { name, .. } => {
                name == type_name
            }
            _ => false,
        });
        let Some(declaration) = declaration else {
            let error = format!(
                "unsafe {:?} annotation refers to undeclared type '{type_name}'",
                property
            );
            let key = format!("$unsafe-impl:{property:?}:{type_name}");
            let precise = declaration_expressions
                .get(&key)
                .and_then(|expression| source_symbol_span(expression, type_name, false));
            return Err(precise
                .or_else(|| declaration_spans.get(&key).copied())
                .map_or(error.clone().into(), |span| {
                    attach_span_to_source_error(error, span, source_files)
                }));
        };
        let is_generic = match declaration {
            Item::Struct {
                type_parameters, ..
            }
            | Item::Enum {
                type_parameters, ..
            }
            | Item::TypeAlias {
                type_parameters, ..
            } => !type_parameters.is_empty(),
            _ => false,
        };
        if matches!(declaration, Item::TypeAlias { .. }) {
            let error = format!(
                "unsafe {:?} annotations require a nominal struct or enum type, not alias '{type_name}'",
                property
            );
            let key = format!("$unsafe-impl:{property:?}:{type_name}");
            let precise = declaration_expressions
                .get(&key)
                .and_then(|expression| source_symbol_span(expression, type_name, false));
            return Err(precise
                .or_else(|| declaration_spans.get(&key).copied())
                .map_or(error.clone().into(), |span| {
                    attach_span_to_source_error(error, span, source_files)
                }));
        }
        if is_generic {
            let error = format!(
                "unsafe {:?} annotation for generic type '{type_name}' is not supported",
                property
            );
            let key = format!("$unsafe-impl:{property:?}:{type_name}");
            let precise = declaration_expressions
                .get(&key)
                .and_then(|expression| source_symbol_span(expression, type_name, false));
            return Err(precise
                .or_else(|| declaration_spans.get(&key).copied())
                .map_or(error.clone().into(), |span| {
                    attach_span_to_source_error(error, span, source_files)
                }));
        }
    }
    let templates = items
        .iter()
        .filter_map(|item| match item {
            Item::Struct {
                name,
                type_parameters,
                ..
            }
            | Item::Enum {
                name,
                type_parameters,
                ..
            }
            | Item::TypeAlias {
                name,
                type_parameters,
                ..
            } if !type_parameters.is_empty() => Some((name.clone(), item.clone())),
            _ => None,
        })
        .collect::<HashMap<_, _>>();
    if templates.is_empty() {
        return Ok(items);
    }
    let mut names = HashMap::new();
    let mut generated = Vec::new();
    for item in &mut items {
        let current_name = item_declared_names(item).into_iter().next();
        let is_generic = matches!(
            item,
            Item::TypeAlias { type_parameters, .. }
                | Item::Struct { type_parameters, .. }
                | Item::Enum { type_parameters, .. }
                if !type_parameters.is_empty()
        );
        if is_generic {
            continue;
        }
        let result = (|| -> Result<(), String> {
            match item {
                Item::TypeAlias { target, .. } => {
                    *target = specialize_type(
                        target,
                        &HashMap::new(),
                        &templates,
                        &mut names,
                        &mut generated,
                    )?;
                }
                Item::Function(function) => {
                    for parameter in &mut function.parameters {
                        parameter.ty = specialize_type(
                            &parameter.ty,
                            &HashMap::new(),
                            &templates,
                            &mut names,
                            &mut generated,
                        )?;
                    }
                    function.return_type = specialize_type(
                        &function.return_type,
                        &HashMap::new(),
                        &templates,
                        &mut names,
                        &mut generated,
                    )?;
                    function.body = function
                        .body
                        .iter()
                        .enumerate()
                        .map(|(index, statement)| {
                            specialize_statement(
                                statement,
                                &HashMap::new(),
                                &templates,
                                &mut names,
                                &mut generated,
                            )
                            .map_err(|error| {
                                let key = (function.name.clone(), index);
                                statement_expressions
                                    .get(&key)
                                    .and_then(|expression| {
                                        specialization_error_span(expression, &error)
                                            .or_else(|| Some(source_value_span(expression)))
                                    })
                                    .or_else(|| statement_spans.get(&key).copied())
                                    .map_or(error.clone().into(), |span| {
                                        attach_span_to_source_error(error, span, source_files)
                                    })
                            })
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                }
                Item::Struct { fields, .. } => {
                    for field in fields {
                        field.ty = specialize_type(
                            &field.ty,
                            &HashMap::new(),
                            &templates,
                            &mut names,
                            &mut generated,
                        )?;
                    }
                }
                Item::Enum { variants, .. } => {
                    for variant in variants {
                        for field in &mut variant.fields {
                            *field = specialize_type(
                                field,
                                &HashMap::new(),
                                &templates,
                                &mut names,
                                &mut generated,
                            )?;
                        }
                    }
                }
                Item::Let { ty, value, .. } => {
                    *ty = specialize_type(
                        ty,
                        &HashMap::new(),
                        &templates,
                        &mut names,
                        &mut generated,
                    )?;
                    *value = specialize_expr(
                        value,
                        &HashMap::new(),
                        &templates,
                        &mut names,
                        &mut generated,
                    )?;
                }
                Item::Static { ty, value, .. } => {
                    *ty = specialize_type(
                        ty,
                        &HashMap::new(),
                        &templates,
                        &mut names,
                        &mut generated,
                    )?;
                    *value = specialize_expr(
                        value,
                        &HashMap::new(),
                        &templates,
                        &mut names,
                        &mut generated,
                    )?;
                }
                Item::UnsafeThreadAnnotation { .. }
                | Item::LinearAnnotation { .. }
                | Item::OpaqueAnnotation { .. } => {}
                Item::ThreadTask { .. } => {}
            }
            Ok(())
        })();
        result.map_err(|error| {
            current_name
                .as_ref()
                .and_then(|name| {
                    declaration_expressions
                        .get(name)
                        .and_then(|expression| specialization_error_span(expression, &error))
                        .or_else(|| declaration_spans.get(name).copied())
                })
                .map_or(error.clone().into(), |span| {
                    attach_span_to_source_error(error, span, source_files)
                })
        })?;
    }
    items.retain(|item| {
        !matches!(
            item,
            Item::TypeAlias { type_parameters, .. }
                | Item::Struct { type_parameters, .. }
                | Item::Enum { type_parameters, .. }
                if !type_parameters.is_empty()
        )
    });
    items.extend(generated);
    Ok(items)
}

fn parse_item(expression: &Expr) -> Result<Item, String> {
    let items = expect_list(expression, "top-level declaration")?;
    if matches!(items.first(), Some(Expr::At)) {
        return parse_generated_item(items);
    }
    let keyword = expect_symbol(items.first(), "declaration keyword")?;
    match keyword {
        "type" => {
            let (type_parameters, target_index) = parse_type_parameters(items, 2)?;
            if items.len() != target_index + 1 {
                return Err("type requires a name and target type".into());
            }
            Ok(Item::TypeAlias {
                name: expect_symbol(items.get(1), "type alias name")?.to_owned(),
                type_parameters: type_parameters.clone(),
                target: replace_generic_types(
                    &parse_type(items.get(target_index))?,
                    &type_parameters,
                ),
            })
        }
        "fn" | "unsafe-fn" => Ok(Item::Function(parse_function(items, false)?)),
        "extern-fn" => Ok(Item::Function(parse_function(items, true)?)),
        "thread-task" => {
            if !matches!(items.len(), 3 | 5) {
                return Err("#thread-task requires a task type, worker function, and optionally spawn/join signature declarations".into());
            }
            let generated_functions = if items.len() == 5 {
                vec![
                    parse_thread_task_function_signature(items.get(3), "thread-task-spawn")?,
                    parse_thread_task_function_signature(items.get(4), "thread-task-join")?,
                ]
            } else {
                Vec::new()
            };
            Ok(Item::ThreadTask {
                name: expect_symbol(items.get(1), "thread task type name")?.to_owned(),
                worker: expect_symbol(items.get(2), "thread worker function")?.to_owned(),
                generated_functions,
            })
        }
        "struct" => {
            let representation = if matches!(items.get(2), Some(Expr::Symbol(name)) if name == "repr-c")
            {
                Representation::C
            } else {
                Representation::Lim
            };
            let declaration_index = if representation == Representation::C {
                3
            } else {
                2
            };
            let (type_parameters, field_index) = parse_type_parameters(items, declaration_index)?;
            Ok(Item::Struct {
                name: expect_symbol(items.get(1), "struct name")?.to_owned(),
                representation,
                type_parameters: type_parameters.clone(),
                fields: parse_struct_fields_at(items, field_index, &type_parameters)?,
            })
        }
        "enum" => {
            let representation = if matches!(items.get(2), Some(Expr::Symbol(name)) if name == "repr-c")
            {
                Representation::C
            } else {
                Representation::Lim
            };
            let declaration_index = if representation == Representation::C {
                3
            } else {
                2
            };
            let (type_parameters, variant_index) = parse_type_parameters(items, declaration_index)?;
            Ok(Item::Enum {
                name: expect_symbol(items.get(1), "enum name")?.to_owned(),
                representation,
                type_parameters: type_parameters.clone(),
                variants: parse_enum_variants_at(items, variant_index, &type_parameters)?,
            })
        }
        "let" | "let-mut" => {
            let binding = parse_let(items)?;
            Ok(Item::Let {
                name: binding.name,
                ty: binding.ty,
                value: binding.value,
                mutable: binding.mutable,
            })
        }
        "const" => {
            let binding = parse_const(items)?;
            Ok(Item::Let {
                name: binding.name,
                ty: binding.ty,
                value: binding.value,
                mutable: false,
            })
        }
        "static" => {
            if items.len() != 4 {
                return Err("static requires the form (#static name Type value)".into());
            }
            Ok(Item::Static {
                name: expect_symbol(items.get(1), "static name")?.to_owned(),
                ty: parse_type(items.get(2))?,
                value: lower_expr(&items[3])?,
            })
        }
        "linear" => {
            if items.len() != 2 {
                return Err("#linear requires one struct or enum type name".into());
            }
            Ok(Item::LinearAnnotation {
                type_name: expect_symbol(items.get(1), "linear type name")?.to_owned(),
            })
        }
        "opaque" => {
            if items.len() != 2 {
                return Err("#opaque requires one concrete struct type name".into());
            }
            Ok(Item::OpaqueAnnotation {
                type_name: expect_symbol(items.get(1), "opaque type name")?.to_owned(),
            })
        }
        "unsafe-impl" => {
            if items.len() != 3 {
                return Err("unsafe-impl requires (#unsafe-impl #send-or-sync Type)".into());
            }
            let property = match expect_symbol(items.get(1), "thread property name")? {
                "send" => ThreadProperty::Send,
                "sync" => ThreadProperty::Sync,
                other => return Err(format!("unsupported unsafe thread property '{other}'")),
            };
            let type_name = expect_symbol(items.get(2), "thread property type")?.to_owned();
            Ok(Item::UnsafeThreadAnnotation {
                property,
                type_name,
            })
        }
        other => Err(format!("unknown top-level form '{other}'")),
    }
}

fn parse_thread_task_function_signature(
    expression: Option<&Expr>,
    expected_builtin: &str,
) -> Result<GeneratedFunctionSignature, String> {
    let items = expect_list(
        expression.ok_or_else(|| format!("#thread-task requires #{expected_builtin}"))?,
        "generated thread function signature",
    )?;
    if items.len() != 4
        || !matches!(items.first(), Some(Expr::Symbol(name)) if name == expected_builtin)
    {
        return Err(format!(
            "expected (#{expected_builtin} name parameters return-type)"
        ));
    }
    let name = expect_symbol(items.get(1), "generated thread function name")?.to_owned();
    let parameter_items = expect_list(
        items.get(2).unwrap(),
        "generated thread function parameters",
    )?;
    let mut parameters = Vec::with_capacity(parameter_items.len());
    for parameter in parameter_items {
        let parts = expect_list(parameter, "generated thread function parameter")?;
        let mutable = matches!(parts.first(), Some(Expr::Symbol(name)) if name == "mut");
        let (name_index, type_index) = if mutable { (1, 2) } else { (0, 1) };
        if parts.len() != type_index + 1 {
            return Err(
                "generated thread parameters must have form (name Type) or (#mut name Type)".into(),
            );
        }
        parameters.push(Parameter {
            name: expect_symbol(parts.get(name_index), "generated thread parameter name")?
                .to_owned(),
            ty: parse_type(parts.get(type_index))?,
            mutable,
        });
    }
    Ok(GeneratedFunctionSignature {
        name,
        parameters,
        return_type: parse_type(items.get(3))?,
    })
}

fn parse_generated_item(items: &[Expr]) -> Result<Item, String> {
    if !matches!(items.first(), Some(Expr::At)) {
        return Err("generated declaration must start with '@'".into());
    }
    let kind = expect_symbol(items.get(1), "generated declaration name")?;
    match kind {
        "optional" => {
            if items.len() != 4 {
                return Err(
                    "generated declaration must have the form (@optional (: type Type : name OptionalType))".into(),
                );
            }
            let payload = parse_type(items.get(2))?;
            let name = expect_symbol(items.get(3), "generated optional type name")?.to_owned();
            Ok(Item::Enum {
                name: name.clone(),
                representation: Representation::Lim,
                type_parameters: Vec::new(),
                variants: vec![
                    EnumVariant {
                        name: format!("{name}-some"),
                        fields: vec![payload],
                        discriminant: 0,
                    },
                    EnumVariant {
                        name: format!("{name}-none"),
                        fields: Vec::new(),
                        discriminant: 1,
                    },
                ],
            })
        }
        "result" => {
            if items.len() != 5 {
                return Err(
                    "generated declaration must have the form (@result (: ok OkType : error ErrType : name ResultType))"
                        .into(),
                );
            }
            let ok = parse_type(items.get(2))?;
            let error = parse_type(items.get(3))?;
            let name = expect_symbol(items.get(4), "generated result type name")?.to_owned();
            Ok(Item::Enum {
                name: name.clone(),
                representation: Representation::Lim,
                type_parameters: Vec::new(),
                variants: vec![
                    EnumVariant {
                        name: format!("{name}-ok-value"),
                        fields: vec![ok],
                        discriminant: 0,
                    },
                    EnumVariant {
                        name: format!("{name}-err-value"),
                        fields: vec![error],
                        discriminant: 1,
                    },
                ],
            })
        }
        "thread-spawn" => {
            if items.len() != 4 {
                return Err(
                    "generated declaration must have the form (@thread-spawn (: task TaskType : worker worker-function))".into(),
                );
            }
            Ok(Item::ThreadTask {
                name: expect_symbol(items.get(2), "thread task type name")?.to_owned(),
                worker: expect_symbol(items.get(3), "thread worker function")?.to_owned(),
                generated_functions: Vec::new(),
            })
        }
        "vec" => {
            if items.len() != 5 {
                return Err(
                    "generated declaration must have the form (@vec (: element Element : allocator Allocator : name VecType))"
                        .into(),
                );
            }
            let element = parse_type(items.get(2))?;
            let allocator = expect_symbol(items.get(3), "vector allocator type")?.to_owned();
            let name = expect_symbol(items.get(4), "generated vector type name")?.to_owned();
            Ok(Item::Struct {
                name,
                representation: Representation::Lim,
                type_parameters: Vec::new(),
                fields: vec![
                    Field {
                        name: "allocator".into(),
                        ty: Type::Reference {
                            mutable: false,
                            target: Box::new(Type::Named(allocator)),
                        },
                    },
                    Field {
                        name: "pointer".into(),
                        ty: Type::RawPointer {
                            mutable: true,
                            target: Box::new(element),
                        },
                    },
                    Field {
                        name: "length".into(),
                        ty: Type::Usize,
                    },
                    Field {
                        name: "capacity".into(),
                        ty: Type::Usize,
                    },
                ],
            })
        }
        "vec-sort" => {
            if items.len() != 5 {
                return Err(
                    "generated declaration must have the form (@vec-sort (: element Element : vector VecType : comparator Comparator))"
                        .into(),
                );
            }
            let element = type_source(&parse_type(items.get(2))?);
            let name = expect_symbol(items.get(3), "vector sort type")?;
            let comparator = expect_symbol(items.get(4), "vector comparator")?;
            generated_vec_sort_source_parts(&element, name, comparator)
                .and_then(|source| parse_generated_source_items(&source))
                .and_then(|mut items| {
                    if items.len() == 1 {
                        Ok(items.remove(0))
                    } else {
                        Err("vector sort expansion produced an invalid item count".into())
                    }
                })
        }
        other => Err(format!("unknown generated declaration '@{other}'")),
    }
}

fn parse_generated_items(items: &[Expr]) -> Result<Vec<Item>, String> {
    let kind = expect_symbol(items.get(1), "generated declaration name")?;
    if kind == "result" {
        return parse_generated_result_items(items);
    }
    if kind == "thread-spawn" {
        let task = parse_generated_item(items)?;
        return Ok(vec![task]);
    }
    if kind == "vec" {
        return parse_generated_source_items(&generated_vec_source(items)?);
    }
    if kind == "vec-alloc" {
        return parse_generated_source_items(&generated_vec_allocator_source(items)?);
    }
    if kind == "vec-sort" {
        return parse_generated_source_items(&generated_vec_sort_source(items)?);
    }
    let generated = parse_generated_item(items)?;
    let Item::Enum { name, variants, .. } = &generated else {
        unreachable!("optional expansion always produces an enum")
    };
    let name = name.clone();
    let payload = variants
        .first()
        .and_then(|variant| variant.fields.first())
        .cloned()
        .expect("optional expansion has a payload variant");
    let some = variants
        .first()
        .map(|variant| variant.name.clone())
        .expect("optional expansion has a some variant");
    let none = variants
        .get(1)
        .map(|variant| variant.name.clone())
        .expect("optional expansion has a none variant");
    let optional_type = Type::Named(name.clone());
    let is_some_body = optional_match(
        "value",
        &some,
        &none,
        "_",
        Expr::Symbol("true".into()),
        Expr::Symbol("false".into()),
    );
    let unwrap_or_body = optional_match(
        "value",
        &some,
        &none,
        "payload",
        Expr::Symbol("payload".into()),
        Expr::Symbol("fallback".into()),
    );
    let payload_for_construct = payload.clone();
    let payload_for_unwrap = payload.clone();
    Ok(vec![
        generated,
        Item::Function(Function {
            name: format!("{name}-construct"),
            external: false,
            unsafe_call: false,
            calling_convention: CallingConvention::Lim,
            type_parameters: Vec::new(),
            parameters: vec![Parameter {
                name: "value".into(),
                ty: payload_for_construct,
                mutable: false,
            }],
            return_type: optional_type.clone(),
            body: vec![Statement::Return(Some(Expr::List(vec![
                Expr::Symbol(some),
                Expr::Symbol("value".into()),
            ])))],
        }),
        Item::Function(Function {
            name: format!("{name}-is-some"),
            external: false,
            unsafe_call: false,
            calling_convention: CallingConvention::Lim,
            type_parameters: Vec::new(),
            parameters: vec![Parameter {
                name: "value".into(),
                ty: optional_type.clone(),
                mutable: false,
            }],
            return_type: Type::Bool,
            body: vec![Statement::Return(Some(is_some_body))],
        }),
        Item::Function(Function {
            name: format!("{name}-unwrap-or"),
            external: false,
            unsafe_call: false,
            calling_convention: CallingConvention::Lim,
            type_parameters: Vec::new(),
            parameters: vec![
                Parameter {
                    name: "value".into(),
                    ty: optional_type,
                    mutable: false,
                },
                Parameter {
                    name: "fallback".into(),
                    ty: payload_for_unwrap,
                    mutable: false,
                },
            ],
            return_type: payload,
            body: vec![Statement::Return(Some(unwrap_or_body))],
        }),
    ])
}

fn generated_vec_source(items: &[Expr]) -> Result<String, String> {
    let Item::Struct { name, fields, .. } = parse_generated_item(items)? else {
        unreachable!("vec expansion always produces a struct")
    };
    let allocator = type_source(&fields[0].ty);
    let pointer = type_source(&fields[1].ty);
    Ok(format!(
        "(#struct {name} ((allocator {allocator}) (pointer {pointer}) (length usize) (capacity usize)))\n(#fn {name}-new-with-storage ((allocator {allocator}) (pointer {pointer}) (capacity usize)) {name} (#return (#struct-literal {name} ((allocator allocator) (pointer pointer) (length 0) (capacity capacity)))))\n(#fn {name}-len ((vector (#ref {name}))) usize (#return (#get vector length)))\n(#fn {name}-capacity ((vector (#ref {name}))) usize (#return (#get vector capacity)))\n"
    ))
}

fn generated_vec_allocator_source(items: &[Expr]) -> Result<String, String> {
    if items.len() != 11 {
        return Err("generated declaration must have the form (@vec-alloc (: element Element : allocator Allocator : vector Vec : alloc-result AllocResult : alloc-error AllocError : alloc alloc : grow grow : dealloc dealloc : destroy destroy))".into());
    }
    let element = type_source(&parse_type(items.get(2))?);
    let allocator = expect_symbol(items.get(3), "vector allocator type")?;
    let name = expect_symbol(items.get(4), "generated vector type name")?;
    let allocation_result = expect_symbol(items.get(5), "allocator result type")?;
    let allocation_error = expect_symbol(items.get(6), "allocator error type")?;
    let alloc = expect_symbol(items.get(7), "allocator allocation function")?;
    let grow = expect_symbol(items.get(8), "allocator growth function")?;
    let dealloc = expect_symbol(items.get(9), "allocator deallocation function")?;
    let destroy = expect_symbol(items.get(10), "element destruction function")?;
    let _ = (dealloc, destroy);
    Ok(format!(
        r#"
(#enum {name}-ReserveError
  (({name}-ReserveAllocationError {allocation_error})
   {name}-ReserveCapacityOverflow))
(#enum {name}-PushError
  (({name}-PushReserveError {name}-ReserveError {element})
   ({name}-PushCapacityOverflow {element})))
(#enum {name}-SetError (({name}-SetOutOfBounds {element})))
(#enum {name}-ReserveResult
  (({name}-ReserveResult-ok-value ())
   ({name}-ReserveResult-err-value {name}-ReserveError)))
(#enum {name}-PushResult
  (({name}-PushResult-ok-value ())
   ({name}-PushResult-err-value {name}-PushError)))
(#enum {name}-SetResult
  (({name}-SetResult-ok-value ())
   ({name}-SetResult-err-value {name}-SetError)))
(#enum {name}-PopResult
  (({name}-PopResult-some {element}) {name}-PopResult-none))
(#enum {name}-GetResult
  (({name}-GetResult-some (#ref {element})) {name}-GetResult-none))
(#enum {name}-GetMutResult
  (({name}-GetMutResult-some (#ref-mut {element})) {name}-GetMutResult-none))
(#fn {name}-new
  ((allocator (#ref {allocator})))
  {name}
  (#return (#struct-literal {name} ((allocator allocator) (pointer (#ptr-null (#ptr-mut {element}))) (length 0usize) (capacity 0usize)))))
(#fn {name}-reserve-fields
  ((allocator (#ref {allocator}))
   (pointer-slot (#ref-mut (#ptr-mut {element})))
   (capacity-slot (#ref-mut usize))
   (requested usize))
  {name}-ReserveResult
  (#let capacity usize (#deref capacity-slot))
  (#let element-size usize (#size-of {element}))
  (#return
    (#if (#usize.<= requested capacity)
      ({name}-ReserveResult-ok-value ())
      (#if (#usize.== element-size 0usize)
        (#block
          (#deref-set capacity-slot requested)
          ({name}-ReserveResult-ok-value ()))
        (#block
          (#let doubled usize (#usize.*.saturate capacity 2usize))
          (#let new-capacity usize
            (#if (#usize.> requested doubled) requested doubled))
          (#let old-layout usize (#usize.*.wrap capacity element-size))
          (#let new-layout usize (#usize.*.wrap new-capacity element-size))
          (#if
            (#&&
              (#usize.== (#usize./.wrap new-layout element-size) new-capacity)
              (#usize.== (#usize./.wrap old-layout element-size) capacity))
            (#block
              (#let allocation-result {allocation_result}
                (#if (#usize.== capacity 0usize)
                  (#call {alloc} (: allocator (#clone allocator) : layout new-layout : alignment (#align-of {element})))
                  (#call {grow} (: allocator (#clone allocator) : pointer (#clone (#deref pointer-slot)) : old-layout old-layout : new-layout new-layout : alignment (#align-of {element})))))
              (#match allocation-result
                (#case ({allocation_result}-ok-value new-pointer)
                  (#block
                    (#deref-set pointer-slot new-pointer)
                    (#deref-set capacity-slot new-capacity)
                    ({name}-ReserveResult-ok-value ())))
                (#case ({allocation_result}-err-value error)
                  ({name}-ReserveResult-err-value
                    ({name}-ReserveAllocationError error)))))
            ({name}-ReserveResult-err-value
              {name}-ReserveCapacityOverflow)))))))
(#fn {name}-reserve
  ((vector (#ref-mut {name})) (requested usize))
  {name}-ReserveResult
  (#return
    (#call {name}-reserve-fields (: allocator (#clone (#get vector allocator)) : pointer-slot (#borrow-mut (#get vector pointer)) : capacity-slot (#borrow-mut (#get vector capacity)) : requested requested))))
(#fn {name}-push
  ((vector (#ref-mut {name})) (element {element}))
  {name}-PushResult
  (#let length usize (#get vector length))
  (#let requested usize (#usize.+.saturate length 1usize))
  (#return
    (#if (#usize.== requested length)
      ({name}-PushResult-err-value ({name}-PushCapacityOverflow element))
      (#match
        (#call {name}-reserve-fields (: allocator (#clone (#get vector allocator)) : pointer-slot (#borrow-mut (#get vector pointer)) : capacity-slot (#borrow-mut (#get vector capacity)) : requested requested))
        (#case ({name}-ReserveResult-ok-value _)
          (#block
            (#let pointer (#ptr-mut {element})
              (#clone (#get vector pointer)))
            (#let destination (#ptr-mut {element})
              (#unsafe (#ptr-offset pointer length)))
            (#unsafe (#ptr-write destination element))
            (#forget element)
            (#deref-set
              (#borrow-mut (#get vector length))
              (#usize.+.wrap length 1usize))
            ({name}-PushResult-ok-value ())))
        (#case ({name}-ReserveResult-err-value error)
          ({name}-PushResult-err-value
            ({name}-PushReserveError error element)))))))
(#fn {name}-get
  ((vector (#ref {name})) (index usize))
  {name}-GetResult
  (#let length usize (#get vector length))
  (#let pointer (#ptr-mut {element}) (#clone (#get vector pointer)))
  (#return
    (#if (#usize.< index length)
      ({name}-GetResult-some
        (#unsafe (#ptr-borrow vector (#ptr-offset pointer index))))
      (#block (#forget pointer) {name}-GetResult-none))))
(#fn {name}-get-mut
  ((vector (#ref-mut {name})) (index usize))
  {name}-GetMutResult
  (#let length usize (#get vector length))
  (#let pointer (#ptr-mut {element}) (#clone (#get vector pointer)))
  (#return
    (#if (#usize.< index length)
      ({name}-GetMutResult-some
        (#unsafe (#ptr-borrow-mut vector (#ptr-offset pointer index))))
      (#block (#forget pointer) {name}-GetMutResult-none))))
(#fn {name}-set
  ((vector (#ref-mut {name})) (index usize) (value {element}))
  {name}-SetResult
  (#let length usize (#get vector length))
  (#return
    (#if (#usize.< index length)
      (#block
        (#let pointer (#ptr-mut {element}) (#clone (#get vector pointer)))
        (#let destination (#ptr-mut {element})
          (#unsafe (#ptr-offset pointer index)))
        (#let previous {element} (#unsafe (#ptr-read destination)))
        (#call {destroy} (: allocator (#clone (#get vector allocator)) : value previous))
        (#unsafe (#ptr-write destination value))
        (#forget destination)
        (#forget value)
        ({name}-SetResult-ok-value ()))
      ({name}-SetResult-err-value ({name}-SetOutOfBounds value)))))
(#fn {name}-pop
  ((vector (#ref-mut {name})))
  {name}-PopResult
  (#let length usize (#get vector length))
  (#return
    (#if (#usize.== length 0usize)
      {name}-PopResult-none
      (#block
        (#let new-length usize (#usize.-.wrap length 1usize))
        (#let pointer (#ptr-mut {element}) (#clone (#get vector pointer)))
        (#let destination (#ptr-mut {element})
          (#unsafe (#ptr-offset pointer new-length)))
        (#let value {element} (#unsafe (#ptr-read destination)))
        (#forget destination)
        (#deref-set (#borrow-mut (#get vector length)) new-length)
        ({name}-PopResult-some value)))))
(#fn {name}-free ((vector {name})) ()
  (#let allocator (#ref {allocator}) (#clone (#get vector allocator)))
  (#let pointer (#ptr-mut {element}) (#clone (#get vector pointer)))
  (#let length usize (#get vector length))
  (#let capacity usize (#get vector capacity))
  (#let element-size usize (#size-of {element}))
  (#let-mut index usize 0usize)
  (#while (#usize.< index length)
    (#let element-pointer (#ptr-mut {element})
      (#unsafe (#ptr-offset (#clone pointer) index)))
    (#let element-value {element} (#unsafe (#ptr-read element-pointer)))
    (#forget element-pointer)
    (#call {destroy} (: allocator (#clone allocator) : value element-value))
    (#set index (#usize.+.wrap index 1usize)))
  (#if
    (#&& (#usize.!= element-size 0usize) (#usize.!= capacity 0usize))
    (#block
      (#call {dealloc} (: allocator (#clone allocator) : pointer (#clone pointer) : layout (#usize.*.wrap capacity element-size) : alignment (#align-of {element})))
      (#forget pointer)
      ())
    (#block (#forget pointer) ()))
  (#forget vector)
  (#return ()))
"#
    ))
}

fn generated_vec_sort_source(items: &[Expr]) -> Result<String, String> {
    if items.len() != 5 {
        return Err(
            "generated declaration must have the form (@vec-sort (: element Element : vector VecType : comparator Comparator))"
                .into(),
        );
    }
    let element = type_source(&parse_type(items.get(2))?);
    let vector = expect_symbol(items.get(3), "vector sort type")?;
    let comparator = expect_symbol(items.get(4), "vector comparator")?;
    generated_vec_sort_source_parts(&element, vector, comparator)
}

fn generated_vec_sort_source_parts(
    element: &str,
    vector: &str,
    comparator: &str,
) -> Result<String, String> {
    Ok(format!(
        r#"
(#fn {vector}-sort ((vector (#ref-mut {vector}))) ()
  (#let length usize (#get vector length))
  (#let element-size usize (#size-of {element}))
  (#if
    (#&& (#usize.> length 1usize) (#usize.!= element-size 0usize))
    (#block
      (#let pointer (#ptr-mut {element}) (#clone (#get vector pointer)))
      (#let-mut index usize 1usize)
      (#while (#usize.< index length)
        (#let current-pointer (#ptr-mut {element})
          (#unsafe (#ptr-offset (#clone pointer) index)))
        (#let current {element} (#unsafe (#ptr-read current-pointer)))
        (#let-mut cursor usize index)
        (#let-mut shifting bool true)
        (#while (#&& (#usize.> cursor 0usize) shifting)
          (#let previous-index usize (#usize.-.wrap cursor 1usize))
          (#let previous-pointer (#ptr-mut {element})
            (#unsafe (#ptr-offset (#clone pointer) previous-index)))
          (#let move-previous bool
            (#call {comparator}
              (: left (#borrow current) : right (#unsafe (#ptr-borrow vector previous-pointer)))))
          (#if move-previous
            (#block
              (#let previous {element} (#unsafe (#ptr-read
                (#unsafe (#ptr-offset (#clone pointer) previous-index)))))
              (#unsafe (#ptr-write
                (#unsafe (#ptr-offset (#clone pointer) cursor)) previous))
              (#set cursor previous-index))
            (#block (#set shifting false) ())))
        (#unsafe (#ptr-write
          (#unsafe (#ptr-offset (#clone pointer) cursor)) current))
        (#set index (#usize.+.wrap index 1usize)))
      (#forget pointer)
      ())
    ())
  (#return ()))
"#
    ))
}

fn parse_generated_source_items(source: &str) -> Result<Vec<Item>, String> {
    let mut items = Vec::new();
    for mut spanned in parse(source)? {
        normalize_match_case_forms(&mut spanned).map_err(|(error, _)| error)?;
        let mut expression = normalize_keywords(spanned.expr);
        normalize_match_cases_expr(&mut expression);
        if let Expr::List(forms) = &expression {
            if matches!(forms.first(), Some(Expr::At)) {
                items.extend(parse_generated_items(forms)?);
                continue;
            }
        }
        items.push(parse_item(&expression).map_err(|error| {
            format!(
                "{error} while parsing generated declaration {}",
                expression_source(&expression).unwrap_or_else(|_| "<?>".into())
            )
        })?);
    }
    Ok(items)
}

fn parse_generated_result_items(items: &[Expr]) -> Result<Vec<Item>, String> {
    let generated = parse_generated_item(items)?;
    let (name, variants) = match &generated {
        Item::Enum { name, variants, .. } => (name.clone(), variants.clone()),
        _ => unreachable!("result expansion always produces an enum"),
    };
    let ok = variants
        .first()
        .and_then(|variant| variant.fields.first())
        .cloned()
        .ok_or_else(|| "result expansion has no success payload".to_owned())?;
    let error = variants
        .get(1)
        .and_then(|variant| variant.fields.first())
        .cloned()
        .ok_or_else(|| "result expansion has no error payload".to_owned())?;
    let ok_name = variants[0].name.clone();
    let err_name = variants[1].name.clone();
    let result_type = Type::Named(name.clone());
    let is_ok = optional_match(
        "value",
        &ok_name,
        &err_name,
        "_",
        Expr::Symbol("true".into()),
        Expr::Symbol("false".into()),
    );
    let unwrap_or = optional_match(
        "value",
        &ok_name,
        &err_name,
        "payload",
        Expr::Symbol("payload".into()),
        Expr::Symbol("fallback".into()),
    );
    let unwrap_err_or = Expr::List(vec![
        Expr::Symbol("match".into()),
        Expr::Symbol("value".into()),
        Expr::List(vec![
            Expr::List(vec![
                Expr::Symbol(ok_name.clone()),
                Expr::Symbol("_".into()),
            ]),
            Expr::Symbol("fallback".into()),
        ]),
        Expr::List(vec![
            Expr::List(vec![
                Expr::Symbol(err_name.clone()),
                Expr::Symbol("error".into()),
            ]),
            Expr::Symbol("error".into()),
        ]),
    ]);
    Ok(vec![
        generated,
        Item::Function(Function {
            name: format!("{name}-ok"),
            external: false,
            unsafe_call: false,
            calling_convention: CallingConvention::Lim,
            type_parameters: Vec::new(),
            parameters: vec![Parameter {
                name: "value".into(),
                ty: ok.clone(),
                mutable: false,
            }],
            return_type: result_type.clone(),
            body: vec![Statement::Return(Some(Expr::List(vec![
                Expr::Symbol(ok_name),
                Expr::Symbol("value".into()),
            ])))],
        }),
        Item::Function(Function {
            name: format!("{name}-err"),
            external: false,
            unsafe_call: false,
            calling_convention: CallingConvention::Lim,
            type_parameters: Vec::new(),
            parameters: vec![Parameter {
                name: "error".into(),
                ty: error.clone(),
                mutable: false,
            }],
            return_type: result_type.clone(),
            body: vec![Statement::Return(Some(Expr::List(vec![
                Expr::Symbol(err_name),
                Expr::Symbol("error".into()),
            ])))],
        }),
        Item::Function(Function {
            name: format!("{name}-is-ok"),
            external: false,
            unsafe_call: false,
            calling_convention: CallingConvention::Lim,
            type_parameters: Vec::new(),
            parameters: vec![Parameter {
                name: "value".into(),
                ty: result_type.clone(),
                mutable: false,
            }],
            return_type: Type::Bool,
            body: vec![Statement::Return(Some(is_ok))],
        }),
        Item::Function(Function {
            name: format!("{name}-unwrap-or"),
            external: false,
            unsafe_call: false,
            calling_convention: CallingConvention::Lim,
            type_parameters: Vec::new(),
            parameters: vec![
                Parameter {
                    name: "value".into(),
                    ty: result_type,
                    mutable: false,
                },
                Parameter {
                    name: "fallback".into(),
                    ty: ok.clone(),
                    mutable: false,
                },
            ],
            return_type: ok,
            body: vec![Statement::Return(Some(unwrap_or))],
        }),
        Item::Function(Function {
            name: format!("{name}-unwrap-err-or"),
            external: false,
            unsafe_call: false,
            calling_convention: CallingConvention::Lim,
            type_parameters: Vec::new(),
            parameters: vec![
                Parameter {
                    name: "value".into(),
                    ty: Type::Named(name.clone()),
                    mutable: false,
                },
                Parameter {
                    name: "fallback".into(),
                    ty: error.clone(),
                    mutable: false,
                },
            ],
            return_type: error,
            body: vec![Statement::Return(Some(unwrap_err_or))],
        }),
    ])
}

fn optional_match(
    value: &str,
    some: &str,
    none: &str,
    some_binding: &str,
    some_result: Expr,
    none_result: Expr,
) -> Expr {
    Expr::List(vec![
        Expr::Symbol("match".into()),
        Expr::Symbol(value.into()),
        Expr::List(vec![
            Expr::List(vec![
                Expr::Symbol(some.into()),
                Expr::Symbol(some_binding.into()),
            ]),
            some_result,
        ]),
        Expr::List(vec![Expr::Symbol(none.into()), none_result]),
    ])
}
fn parse_type_parameters(items: &[Expr], index: usize) -> Result<(Vec<String>, usize), String> {
    if items.len() <= index + 1 {
        return Ok((Vec::new(), index));
    }
    let Some(Expr::List(parameters)) = items.get(index) else {
        return Ok((Vec::new(), index));
    };
    if parameters.is_empty()
        || !parameters
            .iter()
            .all(|item| matches!(item, Expr::Symbol(_)))
    {
        return Ok((Vec::new(), index));
    }
    let mut result = Vec::with_capacity(parameters.len());
    for parameter in parameters {
        let parameter = expect_symbol(Some(parameter), "type parameter")?.to_owned();
        if result.iter().any(|existing| existing == &parameter) {
            return Err(format!("duplicate generic type parameter '{parameter}'"));
        }
        result.push(parameter);
    }
    Err(
        "generic declarations are not supported; use a concrete generated declaration instead"
            .into(),
    )
}

fn parse_struct_fields_at(
    items: &[Expr],
    field_index: usize,
    type_parameters: &[String],
) -> Result<Vec<Field>, String> {
    if items.len() != field_index + 1 {
        return Err("struct requires a name and field list".into());
    }
    let fields = expect_list(items.get(field_index).unwrap(), "struct fields")?;
    let mut result = Vec::with_capacity(fields.len());
    for field in fields {
        let fields = expect_list(field, "struct field")?;
        if fields.len() != 2 {
            return Err("struct fields must have the form (name Type)".into());
        }
        result.push(Field {
            name: expect_symbol(fields.first(), "field name")?.to_owned(),
            ty: replace_generic_types(&parse_type(fields.get(1))?, type_parameters),
        });
    }
    Ok(result)
}

fn parse_enum_variants_at(
    items: &[Expr],
    variant_index: usize,
    type_parameters: &[String],
) -> Result<Vec<EnumVariant>, String> {
    if items.len() != variant_index + 1 {
        return Err("enum requires a name and variant list".into());
    }
    let variants = expect_list(items.get(variant_index).unwrap(), "enum variants")?;
    if variants.is_empty() {
        return Err("enum requires at least one variant".into());
    }
    let mut result = Vec::with_capacity(variants.len());
    let mut next_discriminant = Some(0u64);
    for variant in variants {
        let (name, fields, discriminant) = match variant {
            Expr::Symbol(name) => (
                name.clone(),
                Vec::new(),
                next_discriminant.ok_or_else(|| "enum discriminant overflowed".to_owned())?,
            ),
            Expr::List(items) => {
                if items.is_empty() {
                    return Err("enum variant cannot be empty".into());
                }
                let name = expect_symbol(items.first(), "enum variant name")?.to_owned();
                let explicit = items.get(1).and_then(enum_discriminant);
                let field_start = if explicit.is_some() { 2 } else { 1 };
                let fields = items[field_start..]
                    .iter()
                    .map(|field| {
                        parse_type(Some(field))
                            .map(|ty| replace_generic_types(&ty, type_parameters))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                (
                    name,
                    fields,
                    explicit
                        .or(next_discriminant)
                        .ok_or_else(|| "enum discriminant overflowed".to_owned())?,
                )
            }
            _ => return Err("enum variant must be a symbol or (name Type ...)".into()),
        };
        if result
            .iter()
            .any(|existing: &EnumVariant| existing.name == name)
        {
            return Err(format!("duplicate enum variant '{name}'"));
        }
        if result
            .iter()
            .any(|existing: &EnumVariant| existing.discriminant == discriminant)
        {
            return Err(format!(
                "duplicate discriminant {discriminant} for enum variant '{name}'"
            ));
        }
        result.push(EnumVariant {
            name,
            fields,
            discriminant,
        });
        next_discriminant = discriminant.checked_add(1);
    }
    Ok(result)
}

fn enum_discriminant(expression: &Expr) -> Option<u64> {
    match expression {
        Expr::Integer(value) if *value >= 0 => (*value).try_into().ok(),
        Expr::UnsignedInteger(value) => (*value).try_into().ok(),
        _ => None,
    }
}

pub(crate) fn parse_function(items: &[Expr], external: bool) -> Result<Function, String> {
    parse_function_parts(items, external, true)
}

fn parse_function_parts(
    items: &[Expr],
    external: bool,
    parse_body: bool,
) -> Result<Function, String> {
    let name_index = if external { 2 } else { 1 };
    if external && !matches!(items.get(1), Some(Expr::Symbol(name)) if name == "abi-c") {
        return Err("extern-fn requires an explicit #abi-c calling convention".into());
    }
    if items.len() < name_index + 3 {
        return Err("fn requires a name, parameter list, return type, and body".into());
    }
    let name = expect_symbol(items.get(name_index), "function name")?.to_owned();
    let (type_parameters, parameter_index, return_index, body_index) =
        if let Some(Expr::List(generic_items)) = items.get(name_index + 1) {
            if !generic_items.is_empty()
                && generic_items
                    .iter()
                    .all(|item| matches!(item, Expr::Symbol(_)))
            {
                return Err(
                    "generic functions are not supported; use a concrete generated function instead"
                        .into(),
                );
            } else {
                (Vec::new(), name_index + 1, name_index + 2, name_index + 3)
            }
        } else {
            (Vec::new(), name_index + 1, name_index + 2, name_index + 3)
        };
    if items.len() <= return_index {
        return Err("fn requires a name, parameter list, return type, and body".into());
    }
    let parameter_items = expect_list(items.get(parameter_index).unwrap(), "function parameters")?;
    let mut parameters = Vec::with_capacity(parameter_items.len());
    for parameter in parameter_items {
        let fields = expect_list(parameter, "function parameter")?;
        let mutable = matches!(fields.first(), Some(Expr::Symbol(name)) if name == "mut");
        let expected_len = if mutable { 3 } else { 2 };
        if fields.len() != expected_len {
            return Err(
                "function parameters must have the form (name Type) or (#mut name Type)".into(),
            );
        }
        let name_index = if mutable { 1 } else { 0 };
        let type_index = if mutable { 2 } else { 1 };
        let ty = replace_generic_types(&parse_type(fields.get(type_index))?, &type_parameters);
        parameters.push(Parameter {
            name: expect_symbol(fields.get(name_index), "parameter name")?.to_owned(),
            ty,
            mutable,
        });
    }

    let return_type =
        replace_generic_types(&parse_type(items.get(return_index))?, &type_parameters);
    let mut body = Vec::with_capacity(items.len().saturating_sub(body_index));
    if external {
        if !type_parameters.is_empty() || items.len() != body_index {
            return Err("extern-fn requires a non-generic signature without a body".into());
        }
    } else if parse_body {
        for expression in &items[body_index..] {
            body.push(replace_generic_statement(
                &parse_statement(expression)?,
                &type_parameters,
            ));
        }
    }
    if parse_body && !external && !matches!(body.last(), Some(Statement::Return(Some(_)))) {
        return Err(
            "functions require an explicit (#return value) as their final statement".into(),
        );
    }
    Ok(Function {
        name,
        external,
        unsafe_call: external
            || matches!(items.first(), Some(Expr::Symbol(head)) if head == "unsafe-fn"),
        calling_convention: if external {
            CallingConvention::C
        } else {
            CallingConvention::Lim
        },
        type_parameters,
        parameters,
        return_type,
        body,
    })
}

fn replace_generic_types(ty: &Type, parameters: &[String]) -> Type {
    match ty {
        Type::Named(name) if parameters.iter().any(|parameter| parameter == name) => {
            Type::Generic(name.clone())
        }
        Type::Array(element, length) => Type::Array(
            Box::new(replace_generic_types(element, parameters)),
            *length,
        ),
        Type::Tuple(fields) => Type::Tuple(
            fields
                .iter()
                .map(|field| replace_generic_types(field, parameters))
                .collect(),
        ),
        _ => ty.clone(),
    }
}

fn replace_generic_statement(statement: &Statement, parameters: &[String]) -> Statement {
    match statement {
        Statement::Let {
            name,
            ty,
            value,
            mutable,
        } => Statement::Let {
            name: name.clone(),
            ty: replace_generic_types(ty, parameters),
            value: value.clone(),
            mutable: *mutable,
        },
        Statement::Destructure {
            pattern,
            ty,
            value,
            mutable,
        } => Statement::Destructure {
            pattern: pattern.clone(),
            ty: replace_generic_types(ty, parameters),
            value: value.clone(),
            mutable: *mutable,
        },
        Statement::LetElse {
            pattern,
            ty,
            value,
            else_body,
        } => Statement::LetElse {
            pattern: pattern.clone(),
            ty: replace_generic_types(ty, parameters),
            value: value.clone(),
            else_body: else_body
                .iter()
                .map(|statement| replace_generic_statement(statement, parameters))
                .collect(),
        },
        Statement::Assign { .. }
        | Statement::ArrayAssign { .. }
        | Statement::FieldAssign { .. }
        | Statement::TupleAssign { .. }
        | Statement::EnumPayloadAssign { .. }
        | Statement::Break
        | Statement::BreakValue(_)
        | Statement::BreakTo(_)
        | Statement::BreakToValue { .. }
        | Statement::Continue
        | Statement::ContinueTo(_)
        | Statement::Return(None)
        | Statement::Return(Some(_))
        | Statement::Expr(_) => statement.clone(),
        Statement::While { condition, body } => Statement::While {
            condition: condition.clone(),
            body: body
                .iter()
                .map(|statement| replace_generic_statement(statement, parameters))
                .collect(),
        },
        Statement::Loop { body } => Statement::Loop {
            body: body
                .iter()
                .map(|statement| replace_generic_statement(statement, parameters))
                .collect(),
        },
        Statement::For {
            init,
            condition,
            step,
            body,
        } => Statement::For {
            init: Box::new(replace_generic_statement(init, parameters)),
            condition: condition.clone(),
            step: Box::new(replace_generic_statement(step, parameters)),
            body: body
                .iter()
                .map(|statement| replace_generic_statement(statement, parameters))
                .collect(),
        },
        Statement::Labeled { label, statement } => Statement::Labeled {
            label: label.clone(),
            statement: Box::new(replace_generic_statement(statement, parameters)),
        },
    }
}

fn lower_expr(expression: &Expr) -> Result<Expr, String> {
    if let Expr::List(items) = expression {
        if is_form(expression, "std") {
            return Err("#std is only valid as a top-level declaration".into());
        }
        if is_form(expression, "for-range") {
            if items.len() < 5 {
                return Err(
                    "for-range requires (name Type), start, end, and at least one body statement"
                        .into(),
                );
            }
            let binding = expect_list(
                items
                    .get(1)
                    .ok_or_else(|| "for-range is missing its binding".to_owned())?,
                "for-range binding",
            )?;
            if binding.len() != 2 {
                return Err("for-range binding must have the form (name Type)".into());
            }
            let name = expect_symbol(binding.first(), "for-range binding name")?.to_owned();
            let ty = binding.get(1).cloned().unwrap();
            let counter = format!("__lim_range_counter_{name}");
            let start = lower_expr(&items[2])?;
            let end = lower_expr(&items[3])?;
            let mut lowered = vec![
                Expr::Symbol("for".into()),
                Expr::List(vec![
                    Expr::Symbol("let-mut".into()),
                    Expr::Symbol(counter.clone()),
                    ty.clone(),
                    start,
                ]),
                Expr::List(vec![
                    Expr::Symbol("<".into()),
                    Expr::List(vec![
                        Expr::Symbol("clone".into()),
                        Expr::Symbol(counter.clone()),
                    ]),
                    end,
                ]),
                Expr::List(vec![
                    Expr::Symbol("set".into()),
                    Expr::Symbol(counter.clone()),
                    Expr::List(vec![
                        Expr::Symbol("+".into()),
                        Expr::List(vec![
                            Expr::Symbol("clone".into()),
                            Expr::Symbol(counter.clone()),
                        ]),
                        Expr::Integer(1),
                    ]),
                ]),
            ];
            lowered.push(Expr::List(vec![
                Expr::Symbol("let".into()),
                Expr::Symbol(name),
                ty,
                Expr::List(vec![Expr::Symbol("clone".into()), Expr::Symbol(counter)]),
            ]));
            lowered.extend(items[4..].iter().cloned());
            return lower_expr(&Expr::List(lowered));
        }
    }
    match expression {
        Expr::List(items) if is_form(expression, "label") => {
            if items.len() != 3 {
                return Err("label requires a name and one value loop expression".into());
            }
            let label = expect_symbol(items.get(1), "loop label")?.to_owned();
            let expression = lower_expr(&items[2])?;
            if !matches!(expression, Expr::Loop(_)) {
                return Err("expression label must wrap a value-producing loop".into());
            }
            Ok(Expr::Labeled {
                label,
                expression: Box::new(expression),
            })
        }
        Expr::List(items) if is_form(expression, "loop") => {
            if items.len() < 2 {
                return Err("loop requires a body".into());
            }
            let body = items[1..]
                .iter()
                .map(parse_statement)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Expr::Loop(body))
        }
        Expr::List(items) if is_form(expression, "while") => {
            if items.len() < 2 {
                return Err("while requires a condition and body".into());
            }
            let mut lowered = Vec::with_capacity(items.len());
            lowered.push(Expr::Symbol("while".into()));
            lowered.push(lower_expr(&items[1])?);
            lowered.extend(items[2..].iter().cloned());
            Ok(Expr::List(lowered))
        }
        Expr::List(items) if is_form(expression, "for") => {
            if items.len() < 5 {
                return Err("for requires init, condition, step, and body".into());
            }
            let mut lowered = Vec::with_capacity(items.len());
            lowered.push(Expr::Symbol("for".into()));
            lowered.push(items[1].clone());
            lowered.push(lower_expr(&items[2])?);
            lowered.push(items[3].clone());
            lowered.extend(items[4..].iter().cloned());
            Ok(Expr::List(lowered))
        }
        Expr::List(items) if is_form(expression, "while-let") => {
            if items.len() < 4 {
                return Err(
                    "while-let requires a pattern, value, and at least one body statement".into(),
                );
            }
            // Preserve the complete pattern. Enum payload bindings are harmless
            // in the boolean guard, while aggregate patterns need their literal
            // fields checked to avoid turning every tuple/struct guard into an
            // unconditional loop.
            let condition_pattern = items[1].clone();
            let repeated_value = Expr::List(vec![Expr::Symbol("clone".into()), items[2].clone()]);
            let mut body = vec![Expr::Symbol("block".into())];
            body.extend(items[3..].iter().cloned());
            let then_value = Expr::List(body);
            lower_expr(&Expr::List(vec![
                Expr::Symbol("while".into()),
                Expr::List(vec![
                    Expr::Symbol("match".into()),
                    repeated_value.clone(),
                    Expr::List(vec![condition_pattern, Expr::Symbol("true".into())]),
                    Expr::List(vec![Expr::Symbol("_".into()), Expr::Symbol("false".into())]),
                ]),
                Expr::List(vec![
                    Expr::Symbol("if-let".into()),
                    items[1].clone(),
                    repeated_value,
                    then_value,
                ]),
            ]))
        }
        Expr::List(items) if is_form(expression, "if-let") => {
            if items.len() != 4 && items.len() != 5 {
                return Err(
                    "if-let requires a pattern, value, then expression, and optional else expression".into(),
                );
            }
            let pattern = items[1].clone();
            let value = lower_expr(&items[2])?;
            let then_value = lower_expr(&items[3])?;
            let fallback = if items.len() == 5 {
                lower_expr(&items[4])?
            } else {
                Expr::List(Vec::new())
            };
            Ok(Expr::List(vec![
                Expr::Symbol("match".into()),
                value,
                Expr::List(vec![pattern, then_value]),
                Expr::List(vec![Expr::Symbol("_".into()), fallback]),
            ]))
        }
        Expr::List(items) if is_form(expression, "block") => {
            let mut statements = Vec::with_capacity(items.len().saturating_sub(1));
            for item in &items[1..] {
                statements.push(parse_statement(item)?);
            }
            Ok(Expr::Block(statements))
        }
        Expr::List(items) => Ok(Expr::List(
            items
                .iter()
                .map(lower_expr)
                .collect::<Result<Vec<_>, _>>()?,
        )),
        _ => Ok(expression.clone()),
    }
}

struct LetBinding {
    name: String,
    ty: Type,
    value: Expr,
    mutable: bool,
}

fn parse_let(items: &[Expr]) -> Result<LetBinding, String> {
    let keyword = match items.first() {
        Some(Expr::Symbol(keyword)) => keyword.as_str(),
        _ => "",
    };
    if !matches!(keyword, "let" | "let-mut") || items.len() != 4 {
        return Err("let requires the form (#let or #let-mut name Type value)".into());
    }
    let mutable = keyword == "let-mut";
    if !mutable && matches!(items.get(1), Some(Expr::Symbol(keyword)) if keyword == "mut") {
        return Err("mutable bindings must use #let-mut".into());
    }
    let name_index = 1;
    let type_index = name_index + 1;
    let value_index = type_index + 1;
    if mutable && items.len() != 4 {
        return Err("mutable let requires the form (#let-mut name Type value)".into());
    }
    Ok(LetBinding {
        name: expect_symbol(items.get(name_index), "binding name")?.to_owned(),
        ty: parse_type(items.get(type_index))?,
        value: lower_expr(&items[value_index])?,
        mutable,
    })
}

fn parse_const(items: &[Expr]) -> Result<LetBinding, String> {
    if !matches!(items.first(), Some(Expr::Symbol(keyword)) if keyword == "const")
        || items.len() != 4
    {
        return Err("const requires the form (#const name Type value)".into());
    }
    Ok(LetBinding {
        name: expect_symbol(items.get(1), "constant name")?.to_owned(),
        ty: parse_type(items.get(2))?,
        value: lower_expr(&items[3])?,
        mutable: false,
    })
}

fn parse_statement(expression: &Expr) -> Result<Statement, String> {
    if is_form(expression, "loop") && !loop_has_value_break(expression) {
        let items = expect_list(expression, "loop statement")?;
        if items.len() < 2 {
            return Err("loop requires a body".into());
        }
        let mut body = Vec::with_capacity(items.len() - 1);
        for expression in &items[1..] {
            body.push(parse_statement(expression)?);
        }
        return Ok(Statement::Loop { body });
    }
    if is_form(expression, "label") {
        let items = expect_list(expression, "labeled loop")?;
        if items.len() != 3 {
            return Err("label requires a name and one loop statement".into());
        }
        let label = expect_symbol(items.get(1), "loop label")?.to_owned();
        if is_form(&items[2], "loop") && labeled_loop_has_value_break(&items[2], &label) {
            return Ok(Statement::Expr(lower_expr(expression)?));
        }
        let statement = parse_statement(&items[2])?;
        if let Statement::Expr(Expr::Loop(body)) = statement {
            return Ok(Statement::Expr(Expr::Labeled {
                label,
                expression: Box::new(Expr::Loop(body)),
            }));
        }
        if !matches!(
            statement,
            Statement::While { .. } | Statement::Loop { .. } | Statement::For { .. }
        ) {
            return Err("label must wrap a while, loop, or for statement".into());
        }
        return Ok(Statement::Labeled {
            label,
            statement: Box::new(statement),
        });
    }
    let lowered = lower_expr(expression)?;
    let expression = &lowered;
    if is_form(expression, "let") || is_form(expression, "let-mut") {
        let items = expect_list(expression, "let statement")?;
        let mutable = is_form(expression, "let-mut");
        let name_index = 1;
        let type_index = name_index + 1;
        let value_index = type_index + 1;
        if items.len() != value_index + 1 {
            return Err("let requires the form (#let or #let-mut name Type value)".into());
        }
        if !mutable && matches!(items.get(1), Some(Expr::Symbol(keyword)) if keyword == "mut") {
            return Err("mutable bindings must use #let-mut".into());
        }
        if !matches!(items.get(name_index), Some(Expr::Symbol(_))) {
            return Ok(Statement::Destructure {
                pattern: items[name_index].clone(),
                ty: parse_type(items.get(type_index))?,
                value: lower_expr(&items[value_index])?,
                mutable,
            });
        }
        let binding = parse_let(items)?;
        return Ok(Statement::Let {
            name: binding.name,
            ty: binding.ty,
            value: binding.value,
            mutable: binding.mutable,
        });
    }
    if is_form(expression, "let-else") {
        let items = expect_list(expression, "let-else statement")?;
        if items.len() < 5 {
            return Err(
                "let-else requires (#let-else pattern Type value else-statement ...)".into(),
            );
        }
        let mut else_body = Vec::with_capacity(items.len() - 4);
        for expression in &items[4..] {
            else_body.push(parse_statement(expression)?);
        }
        return Ok(Statement::LetElse {
            pattern: items[1].clone(),
            ty: parse_type(items.get(2))?,
            value: lower_expr(&items[3])?,
            else_body,
        });
    }
    if is_form(expression, "const") {
        let binding = parse_const(expect_list(expression, "const statement")?)?;
        return Ok(Statement::Let {
            name: binding.name,
            ty: binding.ty,
            value: binding.value,
            mutable: false,
        });
    }
    if is_form(expression, "set") {
        let items = expect_list(expression, "assignment")?;
        if items.len() != 3 {
            return Err("set requires the form (#set name value)".into());
        }
        return Ok(Statement::Assign {
            name: expect_symbol(items.get(1), "assignment name")?.to_owned(),
            value: items[2].clone(),
        });
    }
    if is_form(expression, "set-index") {
        let items = expect_list(expression, "array assignment")?;
        if items.len() != 4 {
            return Err("set-index requires the form (#set-index array index value)".into());
        }
        return Ok(Statement::ArrayAssign {
            name: expect_symbol(items.get(1), "array name")?.to_owned(),
            index: items[2].clone(),
            value: items[3].clone(),
        });
    }
    if is_form(expression, "set-field") {
        let items = expect_list(expression, "field assignment")?;
        if items.len() != 4 {
            return Err("set-field requires the form (#set-field struct field value)".into());
        }
        let name = expect_symbol(items.get(1), "struct or tuple name")?.to_owned();
        if let Some(Expr::Integer(index)) = items.get(2) {
            if *index < 0 {
                return Err("tuple field index must be non-negative".into());
            }
            return Ok(Statement::TupleAssign {
                name,
                index: usize::try_from(*index)
                    .map_err(|_| "tuple field index is too large".to_owned())?,
                value: items[3].clone(),
            });
        }
        return Ok(Statement::FieldAssign {
            name,
            field: expect_symbol(items.get(2), "field name")?.to_owned(),
            value: items[3].clone(),
        });
    }
    if is_form(expression, "set-payload") {
        let items = expect_list(expression, "enum payload assignment")?;
        if items.len() != 5 {
            return Err(
                "set-payload requires the form (#set-payload enum variant index value)".into(),
            );
        }
        let index = match items.get(3) {
            Some(Expr::Integer(index)) if *index >= 0 => usize::try_from(*index)
                .map_err(|_| "enum payload field index is too large".to_owned())?,
            Some(Expr::Integer(_)) => {
                return Err("enum payload field index must be non-negative".into())
            }
            _ => return Err("enum payload field index must be an integer".into()),
        };
        return Ok(Statement::EnumPayloadAssign {
            name: expect_symbol(items.get(1), "enum name")?.to_owned(),
            variant: expect_symbol(items.get(2), "enum variant")?.to_owned(),
            index,
            value: items[4].clone(),
        });
    }
    if is_form(expression, "while") {
        let items = expect_list(expression, "while statement")?;
        if items.len() < 2 {
            return Err("while requires a condition and body".into());
        }
        let mut body = Vec::with_capacity(items.len() - 2);
        for expression in &items[2..] {
            body.push(parse_statement(expression)?);
        }
        return Ok(Statement::While {
            condition: items[1].clone(),
            body,
        });
    }
    if is_form(expression, "for") {
        let items = expect_list(expression, "for statement")?;
        if items.len() < 5 {
            return Err("for requires init, condition, step, and body".into());
        }
        let mut body = Vec::with_capacity(items.len() - 4);
        for expression in &items[4..] {
            body.push(parse_statement(expression)?);
        }
        return Ok(Statement::For {
            init: Box::new(parse_statement(&items[1])?),
            condition: items[2].clone(),
            step: Box::new(parse_statement(&items[3])?),
            body,
        });
    }
    if is_form(expression, "break") {
        let items = expect_list(expression, "break statement")?;
        if items.len() == 2 {
            return Ok(Statement::BreakValue(items[1].clone()));
        }
        if items.len() != 1 {
            return Err("break takes zero or one argument".into());
        }
        return Ok(Statement::Break);
    }
    if is_form(expression, "continue") {
        if expect_list(expression, "continue statement")?.len() != 1 {
            return Err("continue takes no arguments".into());
        }
        return Ok(Statement::Continue);
    }
    if is_form(expression, "break-to") {
        let items = expect_list(expression, "labeled break statement")?;
        if items.len() == 3 {
            return Ok(Statement::BreakToValue {
                label: expect_symbol(items.get(1), "break label")?.to_owned(),
                value: items[2].clone(),
            });
        }
        if items.len() != 2 {
            return Err("break-to requires a label and optional value".into());
        }
        return Ok(Statement::BreakTo(
            expect_symbol(items.get(1), "break label")?.to_owned(),
        ));
    }
    if is_form(expression, "continue-to") {
        let items = expect_list(expression, "labeled continue statement")?;
        if items.len() != 2 {
            return Err("continue-to requires exactly one label".into());
        }
        return Ok(Statement::ContinueTo(
            expect_symbol(items.get(1), "continue label")?.to_owned(),
        ));
    }
    if is_form(expression, "return") {
        let items = expect_list(expression, "return statement")?;
        if items.len() != 2 {
            return Err("return requires exactly one expression; use () for void".into());
        }
        return Ok(Statement::Return(Some(items[1].clone())));
    }
    Ok(Statement::Expr(expression.clone()))
}

fn loop_has_value_break(expression: &Expr) -> bool {
    let Expr::List(items) = expression else {
        return false;
    };
    items[1..].iter().any(loop_body_has_value_break)
}

fn labeled_loop_has_value_break(expression: &Expr, label: &str) -> bool {
    let Expr::List(items) = expression else {
        return false;
    };
    if is_form(expression, "break-to")
        && items.len() == 3
        && matches!(&items[1], Expr::Symbol(target) if target == label)
    {
        return true;
    }
    if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "quote" | "quasiquote"))
    {
        return false;
    }
    // Named transfers can cross nested loops; unnamed breaks cannot.
    items
        .iter()
        .skip(1)
        .any(|value| labeled_loop_has_value_break(value, label))
}

fn loop_body_has_value_break(expression: &Expr) -> bool {
    match expression {
        Expr::List(items) => {
            if (is_form(expression, "break") && items.len() == 2)
                || (is_form(expression, "break-to") && items.len() == 3)
            {
                return true;
            }
            if matches!(
                items.first(),
                Some(Expr::Symbol(name))
                    if matches!(name.as_str(), "loop" | "while" | "while-let" | "for" | "for-range")
            ) {
                return false;
            }
            items.iter().any(loop_body_has_value_break)
        }
        Expr::Block(statements) => statements.iter().any(statement_has_value_break),
        _ => false,
    }
}

fn statement_has_value_break(statement: &Statement) -> bool {
    match statement {
        Statement::BreakValue(_) | Statement::BreakToValue { .. } => true,
        Statement::Expr(expression) => loop_body_has_value_break(expression),
        Statement::Labeled { statement, .. } => statement_has_value_break(statement),
        Statement::While { .. } | Statement::Loop { .. } | Statement::For { .. } => false,
        _ => false,
    }
}

pub(crate) fn parse_type(expression: Option<&Expr>) -> Result<Type, String> {
    if matches!(expression, Some(Expr::List(items)) if items.is_empty()) {
        return Ok(Type::Unit);
    }
    if let Some(Expr::List(items)) = expression {
        if items.len() == 2 && matches!(&items[0], Expr::Symbol(name) if name == "pin-own") {
            return Ok(Type::PinOwned(Box::new(parse_type(items.get(1))?)));
        }
        if items.len() >= 2 && matches!(&items[0], Expr::Symbol(name) if name == "tuple") {
            let fields = items[1..]
                .iter()
                .map(|field| parse_type(Some(field)))
                .collect::<Result<Vec<_>, _>>()?;
            return Ok(Type::Tuple(fields));
        }
        if items.len() == 3 && matches!(&items[0], Expr::Symbol(name) if name == "array") {
            let element = parse_type(items.get(1))?;
            let length = match items.get(2) {
                Some(Expr::Integer(value)) if *value >= 0 => {
                    usize::try_from(*value).map_err(|_| "array length is too large".to_owned())?
                }
                _ => return Err("array length must be a non-negative integer".into()),
            };
            return Ok(Type::Array(Box::new(element), length));
        }
        if items.len() == 2 && matches!(&items[0], Expr::Symbol(name) if name == "ref") {
            return Ok(Type::Reference {
                mutable: false,
                target: Box::new(parse_type(items.get(1))?),
            });
        }
        if items.len() == 2 && matches!(&items[0], Expr::Symbol(name) if name == "ref-mut") {
            return Ok(Type::Reference {
                mutable: true,
                target: Box::new(parse_type(items.get(1))?),
            });
        }
        if items.len() == 2 && matches!(&items[0], Expr::Symbol(name) if name == "pin-ref") {
            return Ok(Type::PinnedReference {
                mutable: false,
                target: Box::new(parse_type(items.get(1))?),
            });
        }
        if items.len() == 2 && matches!(&items[0], Expr::Symbol(name) if name == "pin-ref-mut") {
            return Ok(Type::PinnedReference {
                mutable: true,
                target: Box::new(parse_type(items.get(1))?),
            });
        }
        if items.len() == 2 && matches!(&items[0], Expr::Symbol(name) if name == "slice") {
            return Ok(Type::Slice(Box::new(parse_type(items.get(1))?)));
        }
        if items.len() == 2 && matches!(&items[0], Expr::Symbol(name) if name == "slice-mut") {
            return Ok(Type::MutableSlice(Box::new(parse_type(items.get(1))?)));
        }
        if items.len() == 2 && matches!(&items[0], Expr::Symbol(name) if name == "atomic") {
            return Ok(Type::Atomic(Box::new(parse_type(items.get(1))?)));
        }
        if items.len() == 2 && matches!(&items[0], Expr::Symbol(name) if name == "ptr") {
            return Ok(Type::RawPointer {
                mutable: false,
                target: Box::new(parse_type(items.get(1))?),
            });
        }
        if items.len() == 2 && matches!(&items[0], Expr::Symbol(name) if name == "ptr-mut") {
            return Ok(Type::RawPointer {
                mutable: true,
                target: Box::new(parse_type(items.get(1))?),
            });
        }
    }
    let name = expect_symbol(expression, "type")?;
    if name.contains('<') || name.contains('>') {
        return Err(
            "angle-bracket generic types are not supported; use a concrete generated type".into(),
        );
    }
    Ok(Type::from_name(name))
}

fn expect_list<'a>(expression: &'a Expr, context: &str) -> Result<&'a [Expr], String> {
    match expression {
        Expr::List(items) => Ok(items),
        _ => Err(format!("expected list for {context}")),
    }
}

fn expect_symbol<'a>(expression: Option<&'a Expr>, context: &str) -> Result<&'a str, String> {
    match expression {
        Some(Expr::Symbol(value)) => Ok(value),
        _ => Err(format!("expected symbol for {context}")),
    }
}

fn is_form(expression: &Expr, name: &str) -> bool {
    matches!(expression, Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(keyword)) if keyword == name))
}

struct Parser<'a> {
    tokens: &'a [Token],
    index: usize,
    depth: usize,
}

const MAX_PARSE_NESTING: usize = 256;
const MAX_IMPORT_DEPTH: usize = 128;
const MAX_IMPORT_COUNT: usize = 4096;
const MAX_IMPORTED_SOURCE_BYTES: usize = 64 * 1024 * 1024;

impl<'a> Parser<'a> {
    fn new(tokens: &'a [Token]) -> Self {
        Self {
            tokens,
            index: 0,
            depth: 0,
        }
    }

    fn run(mut self) -> Result<Vec<SpannedExpr>, ParseError> {
        let mut expressions = Vec::new();
        while self.index < self.tokens.len() {
            expressions.push(self.expression()?);
        }
        Ok(expressions)
    }

    fn expression(&mut self) -> Result<SpannedExpr, ParseError> {
        if self.depth >= MAX_PARSE_NESTING {
            let span = self
                .tokens
                .get(self.index)
                .map_or_else(|| self.eof_span(), |token| token.span);
            return Err(self.error(
                &format!("expression nesting exceeds maximum of {MAX_PARSE_NESTING}"),
                span,
            ));
        }
        self.depth += 1;
        let result = self.expression_inner();
        self.depth -= 1;
        result
    }

    fn expression_inner(&mut self) -> Result<SpannedExpr, ParseError> {
        let token = self
            .tokens
            .get(self.index)
            .ok_or_else(|| self.error("expected expression", self.eof_span()))?;
        match &token.kind {
            TokenKind::LParen => self.list(),
            TokenKind::RParen => {
                Err(self.error("unexpected ')'; expected an expression", token.span))
            }
            TokenKind::Colon => {
                Err(self.error("':' must be the first token inside its list", token.span))
            }
            TokenKind::Quote => {
                self.index += 1;
                let quoted = self
                    .expression()
                    .map_err(|_| self.error("expected expression after quote", token.span))?;
                let inner = quoted.expr.clone();
                Ok(SpannedExpr {
                    expr: Expr::Quote(Box::new(inner)),
                    span: Span::new(
                        token.span.start,
                        quoted.span.end,
                        token.span.line,
                        token.span.column,
                    ),
                    children: vec![quoted],
                })
            }
            TokenKind::QuasiQuote | TokenKind::Unquote | TokenKind::UnquoteSplicing => {
                self.index += 1;
                let nested = self.expression().map_err(|_| {
                    self.error(
                        "expected expression after syntax template marker",
                        token.span,
                    )
                })?;
                let nested_expr = nested.expr.clone();
                let expr = match token.kind {
                    TokenKind::QuasiQuote => Expr::QuasiQuote(Box::new(nested_expr.clone())),
                    TokenKind::Unquote => Expr::Unquote(Box::new(nested_expr.clone())),
                    TokenKind::UnquoteSplicing => Expr::UnquoteSplicing(Box::new(nested_expr)),
                    _ => unreachable!(),
                };
                Ok(SpannedExpr {
                    expr,
                    span: Span::new(
                        token.span.start,
                        nested.span.end,
                        token.span.line,
                        token.span.column,
                    ),
                    children: vec![nested],
                })
            }
            TokenKind::At => {
                self.index += 1;
                Ok(SpannedExpr {
                    expr: Expr::At,
                    span: token.span,
                    children: Vec::new(),
                })
            }
            TokenKind::Symbol(value) => {
                self.index += 1;
                if let Some((literal, ty)) = parse_typed_integer_atom(value) {
                    return Ok(SpannedExpr {
                        expr: Expr::List(vec![
                            Expr::Symbol("#literal".into()),
                            Expr::Symbol(ty.into()),
                            literal,
                        ]),
                        span: token.span,
                        children: Vec::new(),
                    });
                }
                if let Some((literal, ty)) = parse_typed_float_atom(value) {
                    return Ok(SpannedExpr {
                        expr: Expr::List(vec![
                            Expr::Symbol("#literal".into()),
                            Expr::Symbol(ty.into()),
                            literal,
                        ]),
                        span: token.span,
                        children: Vec::new(),
                    });
                }
                Ok(SpannedExpr {
                    expr: Expr::Symbol(value.clone()),
                    span: token.span,
                    children: Vec::new(),
                })
            }
            TokenKind::Integer(value) => {
                self.index += 1;
                Ok(SpannedExpr {
                    expr: Expr::Integer(*value),
                    span: token.span,
                    children: Vec::new(),
                })
            }
            TokenKind::UnsignedInteger(value) => {
                self.index += 1;
                Ok(SpannedExpr {
                    expr: Expr::UnsignedInteger(*value),
                    span: token.span,
                    children: Vec::new(),
                })
            }
            TokenKind::Float(value) => {
                self.index += 1;
                Ok(SpannedExpr {
                    expr: Expr::Float(value.clone()),
                    span: token.span,
                    children: Vec::new(),
                })
            }
            TokenKind::Char(value) => {
                self.index += 1;
                Ok(SpannedExpr {
                    expr: Expr::Char(*value),
                    span: token.span,
                    children: Vec::new(),
                })
            }
            TokenKind::String(value) => {
                self.index += 1;
                Ok(SpannedExpr {
                    expr: Expr::String(value.clone()),
                    span: token.span,
                    children: Vec::new(),
                })
            }
        }
    }

    fn list(&mut self) -> Result<SpannedExpr, ParseError> {
        let start = self.tokens[self.index].span;
        self.index += 1;
        if matches!(
            self.tokens.get(self.index).map(|token| &token.kind),
            Some(TokenKind::Colon)
        ) {
            return self.colon_list(start);
        }
        let mut items = Vec::new();
        let mut children = Vec::new();
        loop {
            match self.tokens.get(self.index) {
                Some(Token {
                    kind: TokenKind::RParen,
                    span,
                }) => {
                    let end = span.end;
                    self.index += 1;
                    return Ok(SpannedExpr {
                        expr: Expr::List(items),
                        span: Span::new(start.start, end, start.line, start.column),
                        children,
                    });
                }
                Some(_) => {
                    let child = self.expression()?;
                    items.push(child.expr.clone());
                    children.push(child);
                }
                None => return Err(self.error("unterminated list; expected ')'", self.eof_span())),
            }
        }
    }

    fn colon_list(&mut self, start: Span) -> Result<SpannedExpr, ParseError> {
        let mut separator = self.tokens[self.index].span;
        self.index += 1;
        let mut groups = Vec::new();
        let mut children = Vec::new();
        let mut segment = Vec::new();
        loop {
            match self.tokens.get(self.index) {
                Some(Token {
                    kind: TokenKind::Colon,
                    span,
                }) => {
                    if segment.is_empty() {
                        return Err(self.error("empty ':' group", *span));
                    }
                    let group = Self::colon_group(separator, std::mem::take(&mut segment));
                    groups.push(group.expr.clone());
                    children.push(group);
                    separator = *span;
                    self.index += 1;
                }
                Some(Token {
                    kind: TokenKind::RParen,
                    span,
                }) => {
                    let end = span.end;
                    if !segment.is_empty() {
                        let group = Self::colon_group(separator, segment);
                        groups.push(group.expr.clone());
                        children.push(group);
                    } else if !groups.is_empty() {
                        return Err(self.error("trailing ':' group", separator));
                    }
                    self.index += 1;
                    return Ok(SpannedExpr {
                        expr: Expr::List(groups),
                        span: Span::new(start.start, end, start.line, start.column),
                        children,
                    });
                }
                Some(_) => segment.push(self.expression()?),
                None => return Err(self.error("unterminated list; expected ')'", self.eof_span())),
            }
        }
    }

    fn colon_group(separator: Span, children: Vec<SpannedExpr>) -> SpannedExpr {
        let end = children
            .last()
            .map_or(separator.end, |child| child.span.end);
        let items = children.iter().map(|child| child.expr.clone()).collect();
        SpannedExpr {
            expr: Expr::List(items),
            span: Span::new(separator.start, end, separator.line, separator.column),
            children,
        }
    }

    fn eof_span(&self) -> Span {
        self.tokens
            .last()
            .map(|token| {
                Span::new(
                    token.span.end,
                    token.span.end,
                    token.span.line,
                    token.span.column + (token.span.end - token.span.start),
                )
            })
            .unwrap_or(Span::new(0, 0, 1, 1))
    }

    fn error(&self, message: &str, span: Span) -> ParseError {
        ParseError {
            message: message.to_owned(),
            span,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pinned_reference_type_metadata_preserves_mutability_and_target() {
        let shared = Type::PinnedReference {
            mutable: false,
            target: Box::new(Type::U64),
        };
        let exclusive = Type::PinnedReference {
            mutable: true,
            target: Box::new(Type::U64),
        };
        assert_ne!(shared, exclusive);
        assert_eq!(type_source(&shared), "(#pin-ref u64)");
        assert_eq!(type_source(&exclusive), "(#pin-ref-mut u64)");
    }

    fn structured_type_error(program: &Program) -> Diagnostic {
        let (message, code, span, labels) = typecheck::check_types_with_span(program).unwrap_err();
        analysis_diagnostic(message, code, span, labels, program)
    }

    fn read_cached_generated_source(directory: &Path, contains: &str) -> (PathBuf, String) {
        let cache = directory.join("cache");
        for entry in std::fs::read_dir(cache).unwrap() {
            let path = entry.unwrap().path();
            if path.extension().is_some_and(|extension| extension == "lim") {
                let source = std::fs::read_to_string(&path).unwrap();
                if source.contains(contains) {
                    return (path, source);
                }
            }
        }
        panic!("no cached generated source contains {contains:?}");
    }

    #[test]
    fn structured_diagnostics_have_stable_codes_and_notes() {
        let diagnostic = Diagnostic::new(DiagnosticCode::Borrow, "conflicting borrow")
            .with_span(Span {
                start: 4,
                end: 9,
                line: 2,
                column: 3,
                source_id: 0,
            })
            .note("borrowed here");
        assert_eq!(diagnostic.code_string(), "E4100");
        assert_eq!(diagnostic.span.unwrap().line, 2);
        assert_eq!(diagnostic.notes, vec!["borrowed here"]);
    }

    #[test]
    fn compile_and_link_apis_return_structured_diagnostics() {
        let cache = env::temp_dir().join(format!("lim-diagnostic-cache-{}", std::process::id()));
        let syntax = compile_source_to_assembly(
            "(#fn main () u64 (#return 0u64)",
            Path::new("example.lim"),
            &CompileConfig::default(),
            &cache,
            TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert_eq!(syntax.code, DiagnosticCode::Parse);
        assert!(syntax.span.is_some());

        let types = compile_source_to_assembly(
            "(#fn main () u64 (#return missing))",
            Path::new("example.lim"),
            &CompileConfig::default(),
            &cache,
            TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert_eq!(types.code, DiagnosticCode::Type);
        assert!(types.span.is_some());

        let generator_source = "(#gn fail () (#gn-error \"unsupported\"))\n(@fail)";
        let generator = compile_source_to_assembly(
            generator_source,
            Path::new("example.lim"),
            &CompileConfig::default(),
            &cache,
            TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert_eq!(generator.code, DiagnosticCode::Generator);
        let generator_span = generator.span.unwrap();
        assert_eq!(
            &generator.source_text.as_deref().unwrap()[generator_span.start..generator_span.end],
            "(@fail)"
        );

        let backend_source = "(#const First u64 (#u64.+.wrap Second 1))\n(#const Second u64 (#u64.+.wrap First 1))\n(#fn main () u64 (#return First))";
        let backend = compile_source_to_assembly(
            backend_source,
            Path::new("example.lim"),
            &CompileConfig::default(),
            &cache,
            TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert_eq!(backend.code, DiagnosticCode::Codegen);
        let backend_span = backend.span.unwrap();
        assert_eq!(
            &backend.source_text.as_deref().unwrap()[backend_span.start..backend_span.end],
            "Second"
        );

        let nested_static_source = "(#fn get-value () u64 (#return 1u64))\n(#static VALUE u64 (#u64.+.wrap 1u64 (#call get-value (:))))\n(#fn main () u64 (#return (#unsafe VALUE)))";
        let nested_static = compile_source_to_assembly(
            nested_static_source,
            Path::new("example.lim"),
            &CompileConfig::default(),
            &cache,
            TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert_eq!(nested_static.code, DiagnosticCode::Codegen);
        let nested_static_span = nested_static.span.unwrap();
        assert_eq!(
            &nested_static.source_text.as_deref().unwrap()
                [nested_static_span.start..nested_static_span.end],
            "(#call get-value (:))"
        );

        let linking = link_native_binary(
            "invalid assembly instruction !",
            Path::new("unused"),
            &[],
            &[],
            TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert_eq!(linking.code, DiagnosticCode::Link);
        let _ = fs::remove_dir_all(cache);
    }

    #[test]
    fn diagnostic_renderer_shows_and_underlines_source_lines() {
        let source = "first line\n  missing_name\n";
        let rendered = render_error(
            source,
            "example.lim",
            "2:3: unknown variable 'missing_name'",
        );
        assert!(rendered.contains("error[E2000]: unknown variable 'missing_name'"));
        assert!(rendered.contains("--> example.lim:2:3"));
        assert!(rendered.contains("2 |   missing_name"));
        assert!(rendered.contains("^^^ here"));

        let type_error = render_error(source, "example.lim", "unknown variable 'missing_name'");
        assert!(type_error.contains("error[E4000]: unknown variable 'missing_name'"));
        assert!(type_error.contains("missing_name"));
    }

    #[test]
    fn diagnostic_renderer_expands_tabs_before_aligning_underlines() {
        let source = "a\tb";
        let diagnostic =
            Diagnostic::new(DiagnosticCode::Type, "bad value").with_span(Span::new(2, 3, 1, 3));
        let rendered = render_diagnostic(&diagnostic, source, "tabs.lim");
        assert!(rendered.contains("1 | a   b"), "{rendered}");
        assert!(rendered.contains("1 | a   b\n  |     ^ here"), "{rendered}");
    }

    #[test]
    fn diagnostic_renderer_bounds_extremely_long_source_lines() {
        let prefix = "a".repeat(200_000);
        let source = format!("{prefix}TARGET{}\n", "z".repeat(200_000));
        let start = prefix.len();
        let diagnostic = Diagnostic::new(DiagnosticCode::Type, "invalid token")
            .with_span(Span::new(start, start + 6, 1, prefix.chars().count() + 1));
        let rendered = render_diagnostic(&diagnostic, &source, "large.lim");
        assert!(rendered.len() < 2_000, "rendered {} bytes", rendered.len());
        let source_row = rendered
            .lines()
            .find(|line| line.contains("TARGET"))
            .unwrap();
        let underline_row = rendered.lines().find(|line| line.contains('^')).unwrap();
        assert_eq!(
            source_row.chars().position(|character| character == 'T'),
            underline_row.chars().position(|character| character == '^')
        );
        assert!(source_row.contains('…'));
    }

    #[test]
    fn diagnostic_renderer_accounts_for_wide_and_combining_characters() {
        let source = "界e\u{301}bad";
        let diagnostic =
            Diagnostic::new(DiagnosticCode::Type, "bad value").with_span(Span::new(6, 9, 1, 4));
        let rendered = render_diagnostic(&diagnostic, source, "unicode.lim");
        assert!(rendered.contains("1 | 界e\u{301}bad"), "{rendered}");
        assert!(rendered.contains("  |    ^^^ here"), "{rendered}");
    }

    #[test]
    fn lexer_columns_render_unicode_tokens_at_their_display_position() {
        let source = "界 missing";
        let tokens = lex(source).unwrap();
        let token = tokens
            .iter()
            .find(|token| matches!(&token.kind, TokenKind::Symbol(name) if name == "missing"))
            .unwrap();
        assert_eq!(token.span.column, 3);
        let diagnostic =
            Diagnostic::new(DiagnosticCode::Type, "unknown name").with_span(token.span);
        let rendered = render_diagnostic(&diagnostic, source, "unicode.lim");
        assert!(rendered.contains("  |    ^^^^^^^ here"), "{rendered}");
    }

    #[test]
    fn borrow_errors_render_both_source_sites() {
        let source = "borrow owner\nmutate owner\n";
        let mut diagnostic = Diagnostic::new(DiagnosticCode::Borrow, "cannot mutate 'owner'")
            .with_span(Span::new(13, 25, 2, 1))
            .with_source("borrow.lim", source);
        diagnostic.labels.push(DiagnosticLabel {
            message: "borrow begins here".into(),
            span: Span::new(7, 12, 1, 8),
            source_name: Some("borrow.lim".into()),
            source_text: Some(source.into()),
        });
        let rendered = render_diagnostic(&diagnostic, source, "borrow.lim");
        assert!(rendered.contains("error[E4100]"));
        assert!(rendered.contains("--> borrow.lim:2:1"));
        assert!(rendered.contains("--> borrow.lim:1:8"), "{rendered}");
        assert!(rendered.contains("borrow begins here"));
    }

    #[test]
    fn borrow_errors_point_at_conflicting_reads() {
        let source = "(#fn main () u64\n  (#let-mut value u64 1u64)\n  (#let reference (#ref-mut u64) (#borrow-mut value))\n  (#return value)\n)";
        let program = parse_program(source).unwrap();
        let diagnostic = structured_type_error(&program);
        let rendered = render_diagnostic(&diagnostic, source, "borrow-read.lim");
        assert!(rendered.contains("E4100"), "{rendered}");
        assert!(rendered.contains(":4:12"), "{rendered}");
    }

    #[test]
    fn borrow_errors_point_at_conflicting_writes() {
        let source = "(#fn main () u64\n  (#let-mut value u64 1u64)\n  (#let reference (#ref u64) (#borrow value))\n  (#set value 2u64)\n  (#return 0u64)\n)";
        let program = parse_program(source).unwrap();
        let diagnostic = structured_type_error(&program);
        let rendered = render_diagnostic(&diagnostic, source, "borrow-write.lim");
        assert!(rendered.contains("E4100"), "{rendered}");
        assert!(rendered.contains(":4:4"), "{rendered}");
        assert!(rendered.contains(":3:31"), "{rendered}");
    }

    #[test]
    fn range_loop_borrow_diagnostics_preserve_original_body_sources() {
        for body in [
            "(#set value 2u64)",
            "(#let other u64 0u64) (#set value 2u64)",
            "(#for-range (j u64) 0u64 1u64 (#set value 2u64))",
        ] {
            let source = format!(
                "(#fn main () u64\n  (#let-mut value u64 1u64)\n  (#let reference (#ref u64) (#borrow value))\n  (#for-range (i u64) 0u64 1u64 {body})\n  (#return (#deref reference)))"
            );
            let diagnostic = structured_type_error(&parse_program(&source).unwrap());
            assert!(diagnostic.message.contains("borrow"), "{diagnostic:?}");
            let span = diagnostic.span.expect("range body mutation has a span");
            assert_eq!(&source[span.start..span.end], "#set", "{diagnostic:?}");
            assert_eq!(span.start, source.find("#set value").unwrap());
        }
    }

    #[test]
    fn escaping_borrow_errors_highlight_the_return_and_label_the_referent() {
        let source = "(#fn bad () (#ref u64)\n  (#let value u64 42)\n  (#return (#borrow value)))";
        let program = parse_program(source).unwrap();
        let diagnostic = structured_type_error(&program);
        let span = diagnostic.span.expect("escaping borrow has a primary span");
        assert_eq!(&source[span.start..span.end], "(#return (#borrow value))");
        assert_eq!(diagnostic.labels.len(), 1);
        let origin = diagnostic.labels[0].span;
        assert_eq!(&source[origin.start..origin.end], "(#borrow value)");
    }

    #[test]
    fn projected_borrow_errors_keep_both_operator_spans() {
        let source = "(#struct Point ((x u64) (y u64)))\n(#fn main () u64\n  (#let-mut point Point (#struct-literal Point ((x 1u64) (y 2u64))))\n  (#let point-ref (#ref-mut Point) (#borrow-mut point))\n  (#let reference (#ref u64) (#borrow (#get point-ref x)))\n  (#set-field point x 3u64)\n  (#return 0u64)\n)";
        let program = parse_program(source).unwrap();
        let diagnostic = structured_type_error(&program);
        let rendered = render_diagnostic(&diagnostic, source, "borrow-field.lim");
        assert!(rendered.contains("E4100"), "{rendered}");
        assert!(rendered.contains(":6:4"), "{rendered}");
        assert!(rendered.contains(":5:31"), "{rendered}");
    }

    #[test]
    fn parsed_program_preserves_exact_function_statement_spans() {
        let source = "(#fn main () u64\n  (#let x u64 1)\n  (#return missing)\n)";
        let program = parse_program(source).unwrap();
        let span = program.statement_spans.get(&("main".into(), 1)).unwrap();
        assert_eq!(&source[span.start..span.end], "(#return missing)");
        assert_eq!((span.line, span.column), (3, 3));
    }

    #[test]
    fn type_errors_pinpoint_an_unknown_identifier() {
        let source = "(#fn main () u64\n  (#let value u64 1u64)\n  (#return missing)\n)";
        let program = parse_program(source).unwrap();
        let diagnostic = structured_type_error(&program);
        let rendered = render_diagnostic(&diagnostic, source, "type-error.lim");
        assert!(rendered.contains("unknown variable or enum variant 'missing'"));
        assert!(rendered.contains(":3:12"), "{rendered}");
        assert!(rendered.contains("^^^^^^^ here"), "{rendered}");
        assert!(rendered.contains("(#return missing)"), "{rendered}");
    }

    #[test]
    fn type_errors_preserve_the_offending_nested_expression_span() {
        let source = "(#fn main () u64\n  (#return (#u64.+.wrap 1u64 missing))\n)";
        let program = parse_program(source).unwrap();
        let diagnostic = structured_type_error(&program);
        let span = diagnostic.span.expect("unknown nested argument has a span");
        assert_eq!(&source[span.start..span.end], "missing");
    }

    #[test]
    fn type_mismatch_inside_nested_expression_highlights_the_bad_operand() {
        for source in [
            "(#fn main () u64 (#return (#u64.+.wrap 1u64 false)))",
            "(#fn main () u64 (#return (#u64.+.wrap false 1u64)))",
            "(#fn main () u64 (#return (#u64.+.wrap 1u64 2i8)))",
        ] {
            let program = parse_program(source).unwrap();
            let diagnostic = structured_type_error(&program);
            let span = diagnostic.span.expect("bad operand has a span");
            assert!(
                matches!(&source[span.start..span.end], "false" | "2i8"),
                "wrong highlighted operand: {:?}",
                &source[span.start..span.end]
            );
        }
    }

    #[test]
    fn formatter_normalizes_nested_syntax() {
        let formatted = format_source("(#fn main () u64 (#return (#u64.+.wrap 40 2)))").unwrap();
        assert!(formatted.contains("#fn\n"));
        assert!(formatted.contains("#return"));
        assert_eq!(format_source(&formatted).unwrap(), formatted);
    }

    #[test]
    fn project_formatter_formats_transitive_internal_imports_only() {
        let directory = std::env::temp_dir().join(format!(
            "lim-format-project-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir_all(&directory).unwrap();
        let root = directory.join("root.lim");
        let first = directory.join("first.lim");
        let second = directory.join("second.lim");
        fs::write(
            &root,
            "(#import \"first.lim\") (#import-external \"missing.lim\" ext-)",
        )
        .unwrap();
        fs::write(&first, "(#import \"second.lim\")").unwrap();
        fs::write(&second, "(#type Number u64)").unwrap();

        let formatted = format_project_from_path(&root).unwrap();
        assert_eq!(formatted.len(), 3);
        for path in [&root, &first, &second] {
            let source = fs::read_to_string(path).unwrap();
            assert_eq!(format_source(&source).unwrap(), source);
        }
        assert!(!directory.join("missing.lim").exists());
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn formatter_does_not_treat_semicolons_inside_strings_as_comments() {
        let source = "(#fn main () () (#print \"semi;colon\") (#return ()))";
        let formatted = format_source(source).unwrap();
        assert_ne!(formatted, source);
        assert!(formatted.contains("semi;colon"));
    }

    #[test]
    fn duplicate_call_argument_span_is_found_from_source_structure() {
        let source = "(#fn take ((arg u64)) () (#return ())) (#fn main () () (#call take (: arg 1u64 : arg 2u64)) (#return ()))";
        let forms = parse(source).unwrap();
        let span = duplicate_call_parameter_span(&forms[1]).unwrap();
        assert_eq!(&source[span.start..span.end], "arg");
        assert_eq!(source.rfind(": arg").unwrap() + 2, span.start);
    }

    #[test]
    fn formatter_preserves_comments_and_is_idempotent_for_generator_templates() {
        let commented = "; module note\n(#fn main () u64\n  (#let value u64 0u64)\n  ; return the named value\n  (#return value)) ; trailing note\n";
        let formatted = format_source(commented).unwrap();
        assert_ne!(formatted, commented);
        assert!(formatted.contains("; module note\n"));
        assert!(formatted.contains("; return the named value\n"));
        assert!(formatted.contains("; trailing note\n"), "{formatted}");
        let original_program = parse_program(commented).unwrap();
        let formatted_program = parse_program(&formatted).unwrap();
        assert!(check_types(&original_program).is_ok());
        assert!(check_types(&formatted_program).is_ok());
        assert_eq!(format_source(&formatted).unwrap(), formatted);

        let template = "(@generator make ((name syntax))\n  ; keep generated type readable\n  (gn-emit `(#type ,name u64)))\n(#fn empty () () (#return ()))";
        let formatted = format_source(template).unwrap();
        assert!(formatted.contains("; keep generated type readable"));
        assert!(formatted.contains("`(#type ,name u64)"));
        assert!(formatted.contains("()"));
        assert_eq!(format_source(&formatted).unwrap(), formatted);
    }

    #[test]
    fn lexes_function_and_generated_forms() {
        let tokens =
            lex("(#fn add ((left i32) (right i32)) i32 (#return (#u64.+.wrap  left right)))")
                .unwrap();
        assert_eq!(tokens[0].kind, TokenKind::LParen);
        assert_eq!(tokens[1].kind, TokenKind::Symbol("#fn".into()));
        assert_eq!(tokens[6].kind, TokenKind::Symbol("i32".into()));

        let generated = lex("(@optional (: type MyType : name MyType?))").unwrap();
        assert_eq!(generated[1].kind, TokenKind::At);
        assert_eq!(generated[9].kind, TokenKind::Symbol("MyType?".into()));
    }

    #[test]
    fn lexes_prefixed_keywords_and_typed_operators() {
        let tokens = lex("(#fn main () u32 (#return (#u32.+.wrap 20 22)))").unwrap();
        assert_eq!(tokens[1].kind, TokenKind::Symbol("#fn".into()));
        assert!(tokens
            .iter()
            .any(|token| token.kind == TokenKind::Symbol("#u32.+.wrap".into())));
        let program = parse_program("(#fn main () u32 (#return (#u32.+.wrap 20 22)))").unwrap();
        assert!(check_types(&program).is_ok(), "{:?}", check_types(&program));
        assert!(generate_assembly(&program).unwrap().contains("add"));
        let plain = parse_program("(#fn main () u32 (#return (#u32.+ 20 22)))").unwrap();
        assert!(check_types(&plain).is_err());
        let bare_keyword = parse_program("(#fn main () u32 (#return (if true 42 0)))").unwrap_err();
        assert!(bare_keyword.contains("must use its '#' prefix"));
        let bare_operator = parse_program("(#fn main () u32 (#return (+ 20 22)))").unwrap_err();
        assert!(bare_operator.contains("must use its '#' prefix"));
        let bare_division =
            parse_program("(#fn main () u128 (#return (/ 100u128 7u128)))").unwrap_err();
        assert!(bare_division.contains("must use its '#' prefix"));
        let qualified_division =
            parse_program("(#fn main () u128 (#return (#u128./.wrap 100u128 7u128)))");
        assert!(qualified_division.is_ok());
        let qualified_remainder =
            parse_program("(#fn main () u128 (#return (#u128.%.wrap 100u128 7u128)))");
        assert!(qualified_remainder.is_ok());
        assert_eq!(
            lex("(#&& true false)").unwrap()[1].kind,
            TokenKind::Symbol("#&&".into())
        );
    }

    #[test]
    fn native_target_matrix_accepts_only_linux_x86_64_system_v() {
        for alias in ["x86_64-sysv", "x86_64-unknown-linux-gnu"] {
            let target = TargetDescription::parse(alias).unwrap();
            assert_eq!(target, TargetDescription::X86_64_SYSTEM_V);
            let program = parse_program("(#fn main () u64 (#return 42))").unwrap();
            assert!(generate_assembly_for_target(&program, target).is_ok());
        }
        for unsupported in [
            "aarch64-unknown-linux-gnu",
            "x86_64-apple-darwin",
            "x86_64-pc-windows-msvc",
        ] {
            assert!(TargetDescription::parse(unsupported)
                .unwrap_err()
                .contains("supported targets: x86_64-sysv"));
        }
        let program = parse_program("(#fn main () u64 (#return 42))").unwrap();
        assert!(generate_assembly_for_target(&program, TargetDescription::X86_64_SYSTEM_V).is_ok());
    }

    #[test]
    fn inline_assembly_is_typed_and_requires_unsafe() {
        let source = "(#fn main () i64\n\
          (#return (#unsafe (#asm i64 ((rax 39i64)) \"syscall\"))))";
        let program = parse_program(source).unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("    mov rax, QWORD PTR [rsp+0]"));
        assert!(assembly.contains("    syscall\n"));
        assert!(assembly.contains("    pop rbx\n"));

        let outside_unsafe = "(#fn main () i64 (#return (#asm i64 ((rax 39i64)) \"syscall\")))";
        let outside_unsafe = parse_program(&outside_unsafe).unwrap();
        let error = check_types(&outside_unsafe).unwrap_err();
        assert!(
            error.contains("requires an enclosing (#unsafe ...) block"),
            "unexpected unsafe diagnostic: {error}"
        );

        let invalid_register = source.replace("(rax 39i64)", "(rsp 39i64)");
        let invalid_register = parse_program(&invalid_register).unwrap();
        let error = check_types(&invalid_register).unwrap_err();
        assert!(error.contains("unsupported #asm register 'rsp'"));
    }

    #[test]
    fn automatic_cfg_values_select_target_specific_assembly() {
        let source = "(#cfg-if (#cfg-and\
          (#cfg-is #os linux)\
          (#cfg-is #arch x86_64)\
          (#cfg-is #target x86_64-unknown-linux-gnu))\
          (#fn main () u64 (#return 42u64))\
          (#cfg-else (#fn main () u64 (#return 0u64))))";
        let program = parse_program(source).unwrap();
        assert!(check_types(&program).is_ok());
        assert_eq!(program.items.len(), 1);
    }

    #[test]
    fn raw_linux_syscalls_are_unsafe_and_enforce_the_register_limit() {
        let outside_unsafe =
            parse_program("(#fn main () i64 (#return (#linux-syscall i64 39usize ())))").unwrap();
        let error = check_types(&outside_unsafe).unwrap_err();
        assert!(error.contains("requires an enclosing (#unsafe ...) block"));

        let too_many_arguments = parse_program(
            "(#fn main () i64 (#return (#unsafe (#linux-syscall i64 39usize (0usize 0usize 0usize 0usize 0usize 0usize 0usize)))))",
        )
        .unwrap();
        let error = check_types(&too_many_arguments).unwrap_err();
        assert!(error.contains("at most six arguments"));
    }

    #[test]
    fn lexes_quasiquote_unquote_and_splicing() {
        let tokens = lex("`(item ,name ,@items)").unwrap();
        assert_eq!(tokens[0].kind, TokenKind::QuasiQuote);
        assert_eq!(tokens[2].kind, TokenKind::Symbol("item".into()));
        assert_eq!(tokens[3].kind, TokenKind::Unquote);
        assert_eq!(tokens[5].kind, TokenKind::UnquoteSplicing);
    }

    #[test]
    fn compile_time_cfg_selects_only_the_active_forms() {
        let source = "(#cfg-if (#cfg-and (#cfg-is #platform test-os) (#cfg-not (#cfg-is #feature slow))) (#fn main () u64 (#return 42u64)) (#cfg-else (#fn main () u64 (#return missing-name))))";
        let mut config = CompileConfig::default();
        config.set("platform", "test-os");
        config.set("feature", "fast");
        let program = parse_program_with_config(source, &config).unwrap();
        assert_eq!(program.items.len(), 1);
        assert!(check_types(&program).is_ok());

        config.set("feature", "slow");
        let program = parse_program_with_config(source, &config).unwrap();
        assert!(check_types(&program).is_err());
    }

    #[test]
    fn compile_time_cfg_reports_unknown_keys_and_malformed_predicates() {
        let unknown =
            parse_program("(#cfg-if (#cfg-is #missing yes) (#fn main () () (#return ())))")
                .unwrap_err();
        assert!(unknown.contains("unknown cfg key '#missing'"));
        let malformed =
            parse_program("(#cfg-if (#cfg-not true) (#fn main () () (#return ())))").unwrap_err();
        assert!(malformed.contains("cfg condition must be a (#cfg-...) form"));
    }

    #[test]
    fn expands_pure_user_generators_over_literal_syntax() {
        let program = parse_program(
            "(#gn aliases (pairs) (#gn-for-each pair pairs (#gn-list (#gn-symbol \"#type\") (#gn-first pair) (#gn-first (#gn-rest pair))))) (@aliases ((Byte u8) (Word u16))) (@aliases ((Byte u8) (Word u16))) (#fn main () u64 (#return 42))",
        )
        .unwrap();
        assert!(program
            .items
            .iter()
            .any(|item| matches!(item, Item::TypeAlias { name, .. } if name == "Byte")));
        assert!(program
            .items
            .iter()
            .any(|item| matches!(item, Item::TypeAlias { name, .. } if name == "Word")));
        assert_eq!(
            program
                .items
                .iter()
                .filter(|item| matches!(item, Item::TypeAlias { name, .. } if name == "Byte"))
                .count(),
            1,
            "identical generator invocations should emit declarations once"
        );
        assert!(check_types(&program).is_ok());
    }

    #[test]
    fn generator_functions_compose_and_reject_recursion() {
        let source = "(#gn-fn make-type-form (name target) (#gn-list (#gn-symbol \"#type\") name target)) (#gn-fn make-alias (name target) (#gn-call make-type-form name target)) (#gn aliases (pairs) (#gn-for-each pair pairs (#gn-call make-alias (#gn-first pair) (#gn-first (#gn-rest pair))))) (@aliases ((Byte u8) (Word u16))) (#fn main () u64 (#return 42))";
        let program = parse_program(source).unwrap();
        assert_eq!(program.items.len(), 3);

        let recursive = parse_program(
            "(#gn-fn first (x) (#gn-call second x)) (#gn-fn second (x) (#gn-call first x)) (#gn make (x) (#gn-call first x)) (@make value)",
        )
        .unwrap_err();
        assert!(recursive.contains("recursive generator function calls are not allowed"));
    }

    #[test]
    fn generators_require_explicit_capabilities_for_concrete_types() {
        let valid = parse_program(
            "(#fn u64-less ((left (#ref u64)) (right (#ref u64))) bool (#return true)) (#capability sortable u64 ((u64-less ((#ref u64) (#ref u64)) bool))) (#gn emit ((element sortable)) (#gn-list)) (@emit u64)",
        )
        .unwrap();
        assert!(check_types(&valid).is_ok());

        let missing = parse_program(
            "(#gn emit ((element sortable)) (#gn-list (#gn-list (#gn-symbol \"#type\") Generated element))) (@emit u64)",
        )
        .unwrap_err();
        assert!(missing.contains("requires capability 'sortable'"));

        let wrong_type = parse_program(
            "(#fn u64-less ((left (#ref u64)) (right (#ref u64))) bool (#return true)) (#capability sortable u64 ((u64-less ((#ref u64) (#ref u64)) bool))) (#gn emit ((element sortable)) (#gn-list)) (@emit UserType)",
        )
        .unwrap_err();
        assert!(wrong_type.contains("for type 'UserType'"));

        let wrong_signature = parse_program(
            "(#fn u64-less ((left u64) (right u64)) bool (#return true)) (#capability sortable u64 ((u64-less ((#ref u64) (#ref u64)) bool))) (#gn emit ((element sortable)) (#gn-list)) (@emit u64)",
        )
        .unwrap_err();
        assert!(wrong_signature.contains("contract requires"));

        let missing_operation = parse_program(
            "(#capability sortable u64 ((u64-less ((#ref u64) (#ref u64)) bool))) (#gn emit ((element sortable)) (#gn-list)) (@emit u64)",
        )
        .unwrap_err();
        assert!(missing_operation.contains("requires operation function 'u64-less'"));
    }

    #[test]
    fn generator_functions_return_syntax_not_predicate_values() {
        let error = parse_program(
            "(#gn-fn invalid (value) (#gn-symbol? value)) (#gn make () (#gn-call invalid name)) (@make)",
        )
        .unwrap_err();
        assert!(error.contains("must return a syntax value"));
    }

    #[test]
    fn generator_quasiquote_unquotes_and_splices_syntax() {
        let source = "(#gn-fn emit-alias (name) `(#type ,name u64)) (#gn aliases (names) `(,@(#gn-for-each name names (#gn-call emit-alias name)))) (@aliases (First Second)) (#fn main () u64 (#return 42))";
        let program = parse_program(source).unwrap();
        let aliases = program
            .items
            .iter()
            .filter_map(|item| match item {
                Item::TypeAlias { name, .. } => Some(name.as_str()),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(aliases, ["First", "Second"]);

        let non_list =
            parse_program("(#gn bad () `((#type X u64) ,@not-a-list)) (@bad)").unwrap_err();
        assert!(non_list.contains("unquote-splicing requires list syntax"));
        let outside_template = parse_program("(#gn bad (x) ,x) (@bad value)").unwrap_err();
        assert!(outside_template.contains("only valid inside a backtick syntax template"));
    }

    #[test]
    fn generator_errors_and_recursion_are_reported() {
        let error =
            parse_program("(#gn fail () (#gn-error \"unsupported input\")) (@fail)").unwrap_err();
        assert!(error.contains("generator error: unsupported input"));

        let recursive =
            parse_program("(#gn repeat () (#gn-list (@repeat))) (@repeat)").unwrap_err();
        assert!(recursive.contains("recursive generator expansion is not allowed"));

        let unknown = parse_program("(#gn typo () (#gn-unknown 1))\n(@typo)").unwrap_err();
        assert!(unknown.contains("unknown generator builtin '#gn-unknown'"));
        assert!(unknown.contains("defined at 1:1"));
        assert!(unknown.contains("2:1: generator expansion"));

        let argument_error =
            parse_program("(#gn fail (value) (#gn-error \"unsupported input\"))\n(@fail u64)")
                .unwrap_err();
        assert!(argument_error.contains("argument 0="));
        assert!(argument_error.contains("invocation at 2:1"));
    }

    #[test]
    fn loads_internal_and_prefixes_external_imports() {
        let directory = std::env::temp_dir().join(format!("lim-imports-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        let module_path = directory.join("definitions.lim");
        std::fs::write(
            &module_path,
            "(#struct Thing ((value u64))) (#fn read-value ((thing Thing)) u64 (#return (#get thing value))) (#gn make-alias (alias target) (#gn-list (#gn-list (#gn-symbol \"#type\") alias target))) (@make-alias GeneratedAlias u64)",
        )
        .unwrap();
        let root_path = directory.join("root.lim");
        let program_source = "(#import \"definitions.lim\") (#import-external \"definitions.lim\" ext-) (#import-external \"definitions.lim\" ext-) (#fn main () u64 (#return (#u64.+.wrap (#call read-value (: thing (#struct-literal Thing ((value 20))))) (#call ext-read-value (: ext-thing (#struct-literal ext-Thing ((ext-value 22))))))))";
        let program = parse_program_from_path(program_source, &root_path).unwrap();
        assert!(check_types(&program).is_ok());
        assert!(program
            .items
            .iter()
            .any(|item| matches!(item, Item::TypeAlias { name, .. } if name == "GeneratedAlias")));
        assert!(program.items.iter().any(
            |item| matches!(item, Item::TypeAlias { name, .. } if name == "ext-GeneratedAlias")
        ));
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains(".globl read_x2d_value"));
        assert!(assembly.contains(".globl ext_x2d_read_x2d_value"));
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn imported_diagnostics_keep_their_own_source_file_and_offsets() {
        let directory = std::env::temp_dir().join(format!("lim-source-map-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        let module_path = directory.join("module.lim");
        let module_source = "(#fn broken () u64\n  (#return missing))";
        std::fs::write(&module_path, module_source).unwrap();
        let root_path = directory.join("root.lim");
        let root_source = "(#import \"module.lim\") (#fn main () u64 (#return 0u64))";
        let program = parse_program_from_path(root_source, &root_path).unwrap();
        let (message, code, span, labels) = typecheck::check_types_with_span(&program).unwrap_err();
        assert!(!message.contains("source span "));
        let diagnostic = analysis_diagnostic(message, code, span, labels, &program);
        let span = diagnostic.span.unwrap();
        assert_eq!(span.source_id, 1);
        assert_eq!(
            &diagnostic.source_text.as_deref().unwrap()[span.start..span.end],
            "missing"
        );
        let rendered = render_diagnostic(&diagnostic, root_source, "root.lim");
        assert!(rendered.contains("--> "));
        assert!(rendered.contains("module.lim:2:12"), "{rendered}");
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn function_type_diagnostics_carry_the_span_without_message_metadata() {
        let source = "(#fn main () u64 (#return false))";
        let program = parse_program(source).unwrap();
        let (message, code, span, labels) = typecheck::check_types_with_span(&program).unwrap_err();
        assert!(!message.contains("source span "));
        let span = span.expect("mismatched return has a structured source span");
        assert_eq!(&source[span.start..span.end], "false");
        let compatibility_message = check_types(&program).unwrap_err();
        assert!(!compatibility_message.contains("source span "));

        let diagnostic = analysis_diagnostic(message, code, Some(span), labels, &program);
        assert_eq!(diagnostic.span, Some(span));
        assert_eq!(diagnostic.code, DiagnosticCode::Type);

        let global_source = "(#let total u64 false)";
        let global_program = parse_program(global_source).unwrap();
        let (message, _, span, _) = typecheck::check_types_with_span(&global_program).unwrap_err();
        assert!(!message.contains("source span "));
        let span = span.expect("mismatched global initializer has a structured span");
        assert_eq!(&global_source[span.start..span.end], "false");

        let unsafe_source = "(#static VALUE u64 1u64) (#fn main () u64 (#return VALUE))";
        let unsafe_program = parse_program(unsafe_source).unwrap();
        let (message, _, span, _) = typecheck::check_types_with_span(&unsafe_program).unwrap_err();
        assert!(!message.contains("source span "));
        let span = span.expect("unsafe static access has a structured span");
        assert_eq!(&unsafe_source[span.start..span.end], "VALUE");

        let linear_source = "(#struct Resource ((value u64))) (#linear Resource) (#fn main () u64 (#let resource Resource (#struct-literal Resource ((value 1u64)))) (#return 0u64))";
        let linear_program = parse_program(linear_source).unwrap();
        let (message, _, span, _) = typecheck::check_types_with_span(&linear_program).unwrap_err();
        assert!(!message.contains("source span "));
        let span = span.expect("unconsumed linear local has a structured span");
        assert_eq!(&linear_source[span.start..span.end], "resource");
    }

    #[test]
    fn function_declaration_validation_errors_carry_the_name_span() {
        let source = "(#fn invalid () u64 (#return 0u64))";
        let mut program = parse_program(source).unwrap();
        let function = program
            .items
            .iter_mut()
            .find_map(|item| match item {
                Item::Function(function) => Some(function),
                _ => None,
            })
            .unwrap();
        function.external = true;
        let (_, _, span, _) = typecheck::check_types_with_span(&program).unwrap_err();
        let span = span.expect("invalid function declaration has a structured span");
        assert_eq!(&source[span.start..span.end], "invalid");
    }

    #[test]
    fn imported_parser_diagnostics_highlight_the_full_offending_token() {
        let directory =
            std::env::temp_dir().join(format!("lim-import-parser-span-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        let root_path = directory.join("root.lim");
        let root_source = "(#fn main () u64\n  (#return \"bad token)\n)";
        let diagnostic = write_generated_sources_diagnostic(
            root_source,
            &root_path,
            &directory.join("generated"),
            &CompileConfig::default(),
            &directory.join("cache"),
        )
        .unwrap_err();
        let span = diagnostic.span.unwrap();
        assert_eq!(
            &diagnostic.source_text.as_deref().unwrap()[span.start..span.end],
            "\"bad token)\n)"
        );
        assert_eq!(
            diagnostic.source_name.as_deref(),
            Some(root_path.to_str().unwrap())
        );

        let module_path = directory.join("module.lim");
        let module_source = r#"(#fn broken () u64
  (#return "bad \" token)
)"#;
        std::fs::write(&module_path, module_source).unwrap();
        let import_source = "(#import \"module.lim\")\n(#fn main () u64 (#return 0u64))";
        let diagnostic = compile_source_to_assembly(
            import_source,
            &root_path,
            &CompileConfig::default(),
            &directory.join("cache"),
            TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        let span = diagnostic.span.unwrap();
        assert_eq!(
            &diagnostic.source_text.as_deref().unwrap()[span.start..span.end],
            "\"bad \\\" token)\n)"
        );
        assert_eq!(span.source_id, 1);
        assert_eq!(
            diagnostic.source_name.as_deref(),
            Some(module_path.to_str().unwrap())
        );
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn cached_generator_semantic_errors_keep_generated_and_invocation_spans() {
        let directory = std::env::temp_dir().join(format!(
            "lim-cached-generator-diagnostic-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory).unwrap();
        let source = "(#gn bad (name) `((#fn ,name () u64 (#return false))))\n(@bad generated)\n";
        let input = directory.join("input.lim");
        let assembly = directory.join("output.s");
        std::fs::write(&input, source).unwrap();
        let cache = directory.join("cache");
        let compile = || {
            compile_source_to_assembly(
                source,
                &input,
                &CompileConfig::default(),
                &cache,
                TargetDescription::X86_64_SYSTEM_V,
            )
            .unwrap_err()
        };
        let first = compile();
        assert!(first.message.contains("return"), "{}", first.message);
        let second = compile();
        let invocation_start = source.find("(@bad generated)").unwrap();
        assert!(first.span.is_some(), "{first:?}");
        assert_eq!(first.span, second.span);
        let generated_span = first.span.unwrap();
        assert_eq!(
            &first.source_text.as_deref().unwrap()[generated_span.start..generated_span.end],
            "false"
        );
        assert_eq!(first.labels.len(), 1);
        let invocation = &first.labels[0];
        assert_eq!(invocation.span.start, invocation_start);
        assert_eq!(
            invocation.span.end,
            invocation_start + "(@bad generated)".len()
        );
        assert_eq!(
            &invocation.source_text.as_deref().unwrap()[invocation.span.start..invocation.span.end],
            "(@bad generated)"
        );
        assert_eq!(first.span, second.span);
        assert_eq!(first.labels, second.labels);
        assert!(!assembly.exists());
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn imported_generator_errors_keep_the_invocation_source_span() {
        let directory =
            std::env::temp_dir().join(format!("lim-import-generator-span-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        let module_path = directory.join("module.lim");
        let module_source = "(#gn fail () (#gn-error \"unsupported\"))\n(@fail)";
        std::fs::write(&module_path, module_source).unwrap();
        let root_path = directory.join("root.lim");
        let root_source = "(#import \"module.lim\")";
        let diagnostic = compile_source_to_assembly(
            root_source,
            &root_path,
            &CompileConfig::default(),
            &directory.join("cache"),
            TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert_eq!(diagnostic.code, DiagnosticCode::Generator);
        let span = diagnostic.span.unwrap();
        assert_eq!(span.source_id, 1);
        assert_eq!(
            &diagnostic.source_text.as_deref().unwrap()[span.start..span.end],
            "(@fail)"
        );
        assert!(diagnostic
            .source_name
            .as_deref()
            .unwrap()
            .ends_with("module.lim"));
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn resolves_imports_from_configured_module_paths() {
        let directory =
            std::env::temp_dir().join(format!("lim-module-path-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(directory.join("shared.lim"), "(#type Imported u64)").unwrap();
        let root = std::env::temp_dir().join(format!("lim-module-root-{}.lim", std::process::id()));
        let mut config = CompileConfig::default();
        config.add_module_path(&directory);
        let program = parse_program_from_path_with_config(
            "(#import \"shared.lim\") (#fn main () u64 (#return 42))",
            &root,
            &config,
        )
        .unwrap();
        assert!(program.items.iter().any(|item| matches!(
            item,
            Item::TypeAlias { name, .. } if name == "Imported"
        )));
        std::fs::remove_file(root).ok();
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn reads_project_manifest_module_paths() {
        let directory = std::env::temp_dir().join(format!("lim-project-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::create_dir_all(directory.join("modules")).unwrap();
        std::fs::write(directory.join("support.o"), "test-object").unwrap();
        let manifest = directory.join("lim.project");
        std::fs::write(
            &manifest,
            "schema-version = 1\nname = \"demo\"\nsource-root = \"src\"\noutput-dir = \"artifacts\"\nmodule-path = \"modules\"\ntarget = \"x86_64-sysv\"\nlink-lib = \"m\"\nlink-object = \"support.o\"\n",
        )
        .unwrap();
        std::fs::create_dir_all(directory.join("src")).unwrap();
        let project = read_project(&manifest).unwrap();
        assert_eq!(project.schema_version, 1);
        assert_eq!(project.name, "demo");
        assert_eq!(
            project.source_root,
            directory.join("src").canonicalize().unwrap()
        );
        assert_eq!(project.output_directory, directory.join("artifacts"));
        assert_eq!(
            project.module_paths,
            vec![directory.join("modules").canonicalize().unwrap()]
        );
        assert_eq!(project.target, Some(TargetDescription::X86_64_SYSTEM_V));
        assert_eq!(project.link_libraries, ["m"]);
        assert_eq!(
            project.link_objects,
            vec![directory.join("support.o").canonicalize().unwrap()]
        );

        std::fs::write(
            &manifest,
            "schema-version = 1\nname = \"demo\"\nmodule-path = \"modules\"\nmodule-path = \"./modules\"\n",
        )
        .unwrap();
        assert!(read_project(&manifest)
            .unwrap_err()
            .contains("duplicate project module root"));
        std::fs::write(&manifest, "schema-version = 2\nname = \"demo\"\n").unwrap();
        assert!(read_project(&manifest)
            .unwrap_err()
            .contains("unsupported schema-version"));
        std::fs::write(
            &manifest,
            "schema-version = 1\nname = \"demo\"\nmodule-path = \"missing\"\n",
        )
        .unwrap();
        assert!(read_project(&manifest)
            .unwrap_err()
            .contains("not an existing directory"));
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn collects_cfg_keys_from_all_imports_and_inactive_branches() {
        let directory =
            std::env::temp_dir().join(format!("lim-cfg-collect-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(
            directory.join("linux.lim"),
            "(#cfg-if (#cfg-is #backend asm) (#fn from-linux () () (#return ())))",
        )
        .unwrap();
        std::fs::write(
            directory.join("other.lim"),
            "(#cfg-if (#cfg-is #feature fast) (#fn from-other () () (#return ())))",
        )
        .unwrap();
        let root_path = directory.join("root.lim");
        std::fs::write(
            &root_path,
            "(#cfg-if (#cfg-is #platform linux) (#import \"linux.lim\") (#cfg-else (#import \"other.lim\"))) (#cfg-if (#cfg-not (#cfg-is #debug enabled)) (#fn root () () (#return ())))",
        )
        .unwrap();

        assert_eq!(
            collect_cfg_keys_from_path(&root_path).unwrap(),
            vec!["#backend", "#debug", "#feature", "#platform"]
        );
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn rejects_import_cycles_and_malformed_imports() {
        let directory =
            std::env::temp_dir().join(format!("lim-import-cycle-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(directory.join("a.lim"), "(#import \"b.lim\")").unwrap();
        std::fs::write(directory.join("b.lim"), "(#import \"a.lim\")").unwrap();
        let error =
            parse_program_from_path("(#import \"b.lim\")", &directory.join("a.lim")).unwrap_err();
        assert!(error.contains("import cycle"));
        assert!(parse_program("(#import-external \"module.lim\")").is_err());
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn import_loader_enforces_depth_count_and_source_byte_budgets() {
        let directory =
            std::env::temp_dir().join(format!("lim-import-budgets-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory).unwrap();
        let root = directory.join("root.lim");
        let root_source = "(#import \"m0.lim\")";
        std::fs::write(&root, root_source).unwrap();
        std::fs::write(directory.join("m0.lim"), "(#import \"m1.lim\")").unwrap();
        std::fs::write(directory.join("m1.lim"), "(#import \"m2.lim\")").unwrap();
        std::fs::write(directory.join("m2.lim"), "(#fn helper () () (#return ()))").unwrap();

        let load_with_budget = |max_depth, max_import_count, max_total_source_bytes| {
            let canonical_root = std::fs::canonicalize(&root).unwrap();
            let mut active = vec![canonical_root.clone()];
            let mut loaded = HashSet::new();
            let mut source_ids = HashMap::from([(canonical_root.clone(), 0u32)]);
            let mut source_files = vec![SourceFile {
                path: canonical_root,
                source: root_source.to_owned(),
            }];
            let mut budget = ImportBudget {
                import_count: 0,
                total_source_bytes: root_source.len(),
                max_import_count,
                max_total_source_bytes,
                max_import_depth: max_depth,
            };
            load_imports_inner(
                root_source,
                &directory,
                0,
                &mut active,
                &mut loaded,
                &mut source_ids,
                &mut source_files,
                &mut budget,
                &CompileConfig::default(),
            )
        };
        assert!(load_with_budget(2, usize::MAX, usize::MAX)
            .unwrap_err()
            .contains("maximum depth of 2"));
        assert!(load_with_budget(usize::MAX, 1, usize::MAX)
            .unwrap_err()
            .contains("maximum of 1 imports"));
        assert!(
            load_with_budget(usize::MAX, usize::MAX, root_source.len() + 1)
                .unwrap_err()
                .contains("maximum total size")
        );
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn enforces_one_compilation_wide_type_name_space() {
        let program = parse_program("(#type Shared u64) (#struct Shared ())").unwrap();
        assert!(check_types(&program)
            .unwrap_err()
            .contains("duplicate type name 'Shared'"));
    }

    #[test]
    fn requires_explicit_returns_in_prefixed_functions() {
        let missing = parse_program("(#fn main () u64 42)").unwrap_err();
        assert!(missing.contains("explicit"));
        let unit = parse_program("(#fn main () () (#return ()))").unwrap();
        assert!(check_types(&unit).is_ok());
        let no_value = parse_program("(#fn main () () (#return))").unwrap_err();
        assert!(no_value.contains("exactly one expression"));
        let old_mut =
            parse_program("(#fn main () u64 (#let mut value u64 1) (#return value))").unwrap_err();
        assert!(old_mut.contains("#let-mut"));
    }

    #[test]
    fn checks_inferred_lexical_borrows() {
        let shared = parse_program(
            "(#fn main () u64 (#let value u64 40) (#return (#borrow value (#u64.+.wrap value 2))))",
        )
        .unwrap();
        assert!(check_types(&shared).is_ok());
        assert!(generate_assembly(&shared).is_ok());

        let mutable = parse_program(
            "(#fn main () u64 (#let-mut value u64 40) (#return (#borrow-mut value (#block (#set value 42) value))))",
        )
        .unwrap();
        assert!(check_types(&mutable).is_ok());

        let nested_shared = parse_program(
            "(#fn main () u64 (#let value u64 40) (#return (#borrow value (#borrow value value))))",
        )
        .unwrap();
        assert!(check_types(&nested_shared).is_ok());

        let shared_then_mutable = parse_program(
            "(#fn main () u64 (#let-mut value u64 40) (#return (#borrow value (#borrow-mut value value))))",
        )
        .unwrap();
        assert!(check_types(&shared_then_mutable)
            .unwrap_err()
            .contains("borrow 'value' mutably"));

        let overlapping_mutable = parse_program(
            "(#fn main () u64 (#let-mut value u64 40) (#return (#borrow-mut value (#borrow value value))))",
        )
        .unwrap();
        assert!(check_types(&overlapping_mutable)
            .unwrap_err()
            .contains("already borrowed mutably"));

        let diagnostic_source = "(#fn main () u64\n  (#let-mut value u64 40)\n  (#return (#borrow value (#borrow-mut value value))))";
        let diagnostic_program = parse_program(diagnostic_source).unwrap();
        let (structured_message, code, _, _) =
            typecheck::check_types_with_span(&diagnostic_program).unwrap_err();
        assert_eq!(code, DiagnosticCode::Borrow);
        assert!(!structured_message.contains('\0'));
        let compatibility_message = check_types(&diagnostic_program).unwrap_err();
        assert!(!compatibility_message.contains("conflicting span"));
        assert!(!compatibility_message.contains("source span"));
        let (message, code, primary, labels) =
            typecheck::check_types_with_span(&diagnostic_program).unwrap_err();
        assert!(!message.contains("conflicting span"));
        let primary = primary.expect("borrow conflict has a structured primary span");
        assert_eq!(
            &diagnostic_source[primary.start..primary.end],
            "#borrow-mut"
        );
        assert_eq!(labels.len(), 1);
        assert_eq!(
            &diagnostic_source[labels[0].0.start..labels[0].0.end],
            "#borrow"
        );
        let structured_diagnostic =
            analysis_diagnostic(message, code, Some(primary), labels, &diagnostic_program);
        let rendered = render_diagnostic(&structured_diagnostic, diagnostic_source, "borrow.lim");
        assert!(rendered.contains("borrow begins here"), "{rendered}");
        assert_eq!(rendered.matches("\n  --> ").count(), 2, "{rendered}");

        let shared_write = parse_program(
            "(#fn main () u64 (#let-mut value u64 40) (#return (#borrow value (#block (#set value 42) value))))",
        )
        .unwrap();
        assert!(check_types(&shared_write)
            .unwrap_err()
            .contains("immutably borrowed"));
    }

    #[test]
    fn soundness_audit_tracks_raw_pointer_borrows_through_returned_tuples() {
        let program = parse_program(
            "(#fn expose ((anchor (#ref u64)) (pointer (#ptr u64))) (#tuple (#ref u64) u64) (#let reference (#ref u64) (#unsafe (#ptr-borrow anchor pointer))) (#forget pointer) (#return (#tuple (#tuple (#ref u64) u64) reference 1u64))) (#fn bad () u64 (#let-mut value u64 41u64) (#let pointer (#ptr u64) (#unsafe (#addr-of value))) (#let result (#tuple (#ref u64) u64) (#call expose (: anchor (#borrow value) : pointer pointer))) (#set value 42u64) (#return (#deref (#get result 0))))",
        )
        .unwrap();
        let error = check_types(&program).unwrap_err();
        assert!(
            error.contains("cannot mutate 'value' while it is immutably borrowed"),
            "a reference derived from an unsafe pointer must keep its anchor loan through aggregate return: {error}"
        );
    }

    #[test]
    fn soundness_audit_keeps_enum_payload_borrows_live_across_match() {
        let program = parse_program(
            "(#enum HeldRef ((Held (#ref u64)) Empty)) (#fn hold ((source (#ref u64))) HeldRef (#return (Held source))) (#fn bad () u64 (#let-mut value u64 41u64) (#let held HeldRef (#call hold (: source (#borrow value)))) (#set value 42u64) (#return (#match held (#case (Held reference) (#deref reference)) (#case Empty 0u64))))",
        )
        .unwrap();
        let error = check_types(&program).unwrap_err();
        assert!(
            error.contains("cannot mutate 'value' while it is immutably borrowed"),
            "enum payload borrows must remain live until the matching branch consumes the enum: {error}"
        );
    }

    #[test]
    fn supports_generated_interior_mutable_cells() {
        let prefix = format!(
            "{} (@cell u64 CellU64 CellU64-create CellU64-get CellU64-set)",
            include_str!("../library/cell.lim")
        );
        let program = parse_program(&format!(
            "{prefix} (#fn main () u64
              (#let counter CellU64 (#call CellU64-create (: value 40u64)))
              (#call CellU64-set (: cell (#borrow counter) : value (#u64.+.wrap
                  (#call CellU64-get (: cell (#borrow counter))) 2u64)))
              (#let result u64 (#call CellU64-get (: cell (#borrow counter))))
              (#forget counter) (#return result))"
        ))
        .unwrap();
        assert!(check_types(&program).is_ok(), "{:?}", check_types(&program));
        assert!(generate_assembly(&program).is_ok());

        let invalid = parse_program(&format!(
            "{prefix} (#fn main () u64
              (#let counter CellU64 (#call CellU64-create (: value 40u64)))
              (#call CellU64-set (: cell (#borrow counter) : value true))
              (#forget counter) (#return 0u64))"
        ))
        .unwrap();
        assert!(check_types(&invalid).is_err());

        assert!(parse_program("(#fn main () (#cell u64) (#return (#cell 0u64)))").is_err());
    }

    #[test]
    fn supports_shared_references_to_aggregate_allocator_state() {
        let prefix = format!(
            "{} (@cell u64 CellU64 CellU64-create CellU64-get CellU64-set)",
            include_str!("../library/cell.lim")
        );
        let program = parse_program(&format!(
            "{prefix} (#struct ArenaState ((cursor CellU64)))
             (#fn ArenaState-advance ((arena (#ref ArenaState))) u64
               (#let cell (#ref CellU64) (#borrow (#get arena cursor)))
               (#call CellU64-set (: cell (#clone cell) : value (#u64.+.wrap
                   (#call CellU64-get (: cell (#clone cell))) 1u64)))
               (#return (#call CellU64-get (: cell cell))))
             (#fn main () u64 (#return 0u64))"
        ))
        .unwrap();
        assert!(check_types(&program).is_ok(), "{:?}", check_types(&program));
        assert!(generate_assembly(&program).is_ok());

        let runnable = parse_program(&format!(
            "{prefix} (#struct ArenaState ((cursor CellU64)))
             (#fn main () u64
               (#let arena ArenaState (#struct-literal ArenaState ((cursor
                 (#call CellU64-create (: value 40u64))))))
               (#let allocator (#ref ArenaState) (#borrow arena))
               (#let cell (#ref CellU64) (#borrow (#get allocator cursor)))
               (#call CellU64-set (: cell (#clone cell) : value (#u64.+.wrap
                   (#call CellU64-get (: cell (#clone cell))) 2u64)))
               (#let result u64 (#call CellU64-get (: cell cell)))
               (#drop allocator) (#forget arena) (#return result))"
        ))
        .unwrap();
        assert!(
            check_types(&runnable).is_ok(),
            "{:?}",
            check_types(&runnable)
        );
        assert!(generate_assembly(&runnable).is_ok());

        let reference_to_global = parse_program(
            "(#struct Point ((x u64) (y u64))) (#static Origin Point (#struct-literal Point ((x 20) (y 22)))) (#fn origin () (#ref Point) (#return (#unsafe (#borrow Origin)))) (#fn main () u64 (#return (#get (#call origin (:)) x)))",
        )
        .unwrap();
        assert!(check_types(&reference_to_global).is_ok());
        assert!(generate_assembly(&reference_to_global).is_ok());

        let aggregate_deref = parse_program(
            "(#struct Point ((x u64))) (#fn main () u64 (#let-mut point Point (#struct-literal Point ((x 42)))) (#return (#get (#deref (#borrow point)) x)))",
        )
        .unwrap();
        // The borrow is only an address operand for a local value load. The
        // returned scalar does not retain a reference to the local Point.
        check_types(&aggregate_deref).unwrap();
        generate_assembly(&aggregate_deref).unwrap();

        let stored = parse_program(
            "(#struct Allocator ((cursor u64))) (#struct VecWithAllocator ((allocator (#ref Allocator)) (length u64))) (#fn main () u64 (#let-mut allocator Allocator (#struct-literal Allocator ((cursor 0)))) (#let-mut vector VecWithAllocator (#struct-literal VecWithAllocator ((allocator (#borrow allocator)) (length 0)))) (#set-field allocator cursor 1) (#return 0))",
        )
        .unwrap();
        assert!(check_types(&stored)
            .unwrap_err()
            .contains("immutably borrowed"));

        let escaping = parse_program(
            "(#struct Allocator ((cursor u64))) (#struct VecWithAllocator ((allocator (#ref Allocator)) (length u64))) (#fn make () VecWithAllocator (#let-mut allocator Allocator (#struct-literal Allocator ((cursor 0)))) (#let vector VecWithAllocator (#struct-literal VecWithAllocator ((allocator (#borrow allocator)) (length 0)))) (#return vector))",
        )
        .unwrap();
        assert!(check_types(&escaping)
            .unwrap_err()
            .contains("cannot return a value retaining a reference to local 'allocator'"));

        let immutable_reference_field = parse_program(
            "(#struct Allocator ((cursor u64))) (#struct VecWithAllocator ((allocator (#ref Allocator)))) (#fn replace ((#mut vector VecWithAllocator) (allocator (#ref Allocator))) () (#set-field vector allocator allocator) (#return ()))",
        )
        .unwrap();
        assert!(check_types(&immutable_reference_field)
            .unwrap_err()
            .contains("reference field 'allocator'"));
    }

    #[test]
    fn derives_send_and_sync_and_accepts_explicit_unsafe_overrides() {
        let program = parse_program(&format!(
            "{} (@cell u64 CellU64 CellU64-create CellU64-get CellU64-set)
             (#struct Plain ((value u64))) (#struct HasCell ((value CellU64)))
             (#struct HasPointer ((value (#ptr u64))))
             (#struct HasSharedReference ((value (#ref Plain))))
             (#struct PromisedSend ((value (#ptr u64))))
             (#struct PromisedSync ((value (#ptr u64))))
             (#unsafe-impl #send PromisedSend) (#unsafe-impl #sync PromisedSync)",
            include_str!("../library/cell.lim")
        ))
        .unwrap();
        check_types(&program).unwrap();
        let has = |name: &str, property: ThreadProperty| {
            type_has_thread_property(&program, &Type::Named(name.to_owned()), property).unwrap()
        };

        assert!(has("Plain", ThreadProperty::Send));
        assert!(has("Plain", ThreadProperty::Sync));
        assert!(has("HasCell", ThreadProperty::Send));
        assert!(has("HasCell", ThreadProperty::Sync));
        assert!(!has("HasPointer", ThreadProperty::Send));
        assert!(!has("HasPointer", ThreadProperty::Sync));
        assert!(has("HasSharedReference", ThreadProperty::Send));
        assert!(has("HasSharedReference", ThreadProperty::Sync));
        assert!(has("PromisedSend", ThreadProperty::Send));
        assert!(!has("PromisedSend", ThreadProperty::Sync));
        assert!(has("PromisedSync", ThreadProperty::Sync));

        assert!(type_has_thread_property(
            &program,
            &Type::Reference {
                mutable: false,
                target: Box::new(Type::Named("Plain".to_owned())),
            },
            ThreadProperty::Send,
        )
        .unwrap());
        assert!(type_has_thread_property(
            &program,
            &Type::Reference {
                mutable: false,
                target: Box::new(Type::Named("HasCell".to_owned())),
            },
            ThreadProperty::Send,
        )
        .unwrap());
        assert!(type_has_thread_property(
            &program,
            &Type::Reference {
                mutable: true,
                target: Box::new(Type::Named("Plain".to_owned())),
            },
            ThreadProperty::Send,
        )
        .unwrap());
        assert!(type_has_thread_property(
            &program,
            &Type::Reference {
                mutable: true,
                target: Box::new(Type::Named("HasCell".to_owned())),
            },
            ThreadProperty::Sync,
        )
        .unwrap());

        let duplicate = parse_program(
            "(#struct Value ((value u64))) (#unsafe-impl #send Value) (#unsafe-impl #send Value)",
        )
        .unwrap();
        assert!(check_types(&duplicate)
            .unwrap_err()
            .contains("duplicate unsafe Send annotation"));
        let duplicate_source =
            "(#struct Value ((value u64))) (#unsafe-impl #send Value) (#unsafe-impl #send Value)";
        let (_, _, span, _) = typecheck::check_types_with_span(&duplicate).unwrap_err();
        let span = span.expect("duplicate unsafe annotation has its type span");
        assert_eq!(&duplicate_source[span.start..span.end], "Value");
        assert_eq!(duplicate_source[..span.start].matches("Value").count(), 2);

        assert!(parse_program("(#unsafe-impl #send Unknown)")
            .unwrap_err()
            .contains("undeclared type 'Unknown'"));

        let generic_override =
            parse_program("(#struct Box (T) ((value T))) (#unsafe-impl #sync Box)").unwrap_err();
        assert!(generic_override.contains("generic declarations are not supported"));

        let alias_override =
            parse_program("(#type Resource (#ptr u8)) (#unsafe-impl #send Resource)").unwrap_err();
        assert!(alias_override.contains("require a nominal struct or enum type"));
    }

    #[test]
    fn thread_spawn_generator_requires_send_worker_inputs_and_output() {
        let valid = parse_program(
            "(#fn increment ((value u64)) u64 (#return (#u64.+.wrap value 1))) (@thread-spawn (: task IncrementTask : worker increment))",
        )
        .unwrap();
        assert!(check_types(&valid).is_ok(), "{:?}", check_types(&valid));
        assert!(valid.items.iter().any(|item| matches!(
            item,
            Item::ThreadTask { name, worker, .. }
                if name == "IncrementTask" && worker == "increment"
        )));
        let assembly = generate_assembly(&valid).unwrap();
        assert!(!assembly.contains("pthread"));
        assert!(!assembly.contains(".extern malloc"));
        assert!(assembly.contains("mov eax, 56\n    syscall"));
        assert!(assembly.contains("mov eax, 202\n    syscall"));
        assert!(assembly.contains(".Llim_thread_entry_IncrementTask"));

        let api = parse_program(
            "(#fn increment ((value u64)) u64 (#return (#u64.+.wrap value 1))) (@thread-spawn (: task IncrementTask : worker increment)) (#fn main () u64 (#return (#match (#call IncrementTask-spawn (: value 41)) (#case (IncrementTask-spawn-ok task) (#match (#call IncrementTask-join (: task task)) (#case (IncrementTask-join-ok value) value) (#case (IncrementTask-join-error (#tuple retry error)) (#panic)))) (#case (IncrementTask-spawn-error error) (#panic)))))",
        )
        .unwrap();
        assert!(check_types(&api).is_ok(), "{:?}", check_types(&api));
        let api_assembly = generate_assembly(&api).unwrap();
        assert!(api_assembly.contains(".Llim_thread_join_fail_IncrementTask"));
        assert!(api_assembly.contains("ud2"));

        let non_send_input = parse_program(
            "(#fn inspect ((pointer (#ptr u64))) u64 (#return (#unsafe (#ptr-read pointer)))) (@thread-spawn (: task PointerTask : worker inspect))",
        )
        .unwrap();
        assert!(check_types(&non_send_input)
            .unwrap_err()
            .contains("parameter 'pointer' does not implement Send"));

        let unsafe_send_input = parse_program(
            "(#struct NativeToken ((pointer (#ptr u64)))) (#unsafe-impl #send NativeToken) (#fn inspect ((token NativeToken)) u64 (#return 0)) (@thread-spawn (: task TokenTask : worker inspect))",
        )
        .unwrap();
        assert!(check_types(&unsafe_send_input).is_ok());

        let unsafe_sync_reference = parse_program(
            "(#struct NativeShared ((pointer (#ptr u64)))) (#unsafe-impl #sync NativeShared) (#fn inspect ((value (#ref NativeShared))) u64 (#return 0)) (@thread-spawn (: task InspectTask : worker inspect))",
        )
        .unwrap();
        assert!(check_types(&unsafe_sync_reference).is_ok());

        let missing_sync_reference = parse_program(
            "(#struct NativeShared ((pointer (#ptr u64)))) (#fn inspect ((value (#ref NativeShared))) u64 (#return 0)) (@thread-spawn (: task InspectTask : worker inspect))",
        )
        .unwrap();
        assert!(check_types(&missing_sync_reference)
            .unwrap_err()
            .contains("parameter 'value' does not implement Send"));

        let reference_return = parse_program(
            "(#fn identity ((value (#ref u64))) (#ref u64) (#return value)) (@thread-spawn (: task IdentityTask : worker identity))",
        )
        .unwrap();
        assert!(check_types(&reference_return)
            .unwrap_err()
            .contains("cannot return reference-containing values"));

        let forgotten_spawn_result = parse_program(
            "(#fn work ((value u64)) u64 (#return value)) (@thread-spawn (: task WorkTask : worker work)) (#fn main () u64 (#let result WorkTask-spawn-result (#call WorkTask-spawn (: value 1))) (#forget result) (#return 0))",
        )
        .unwrap();
        assert!(check_types(&forgotten_spawn_result)
            .unwrap_err()
            .contains("cannot be dropped or forgotten; match and join them"));

        let forgotten_nested_spawn_result = parse_program(
            "(#fn work ((value u64)) u64 (#return value)) (@thread-spawn (: task WorkTask : worker work)) (#fn main () u64 (#let result WorkTask-spawn-result (#call WorkTask-spawn (: value 1))) (#forget (#tuple (#tuple WorkTask-spawn-result u64) result 0)) (#return 0))",
        )
        .unwrap();
        assert!(check_types(&forgotten_nested_spawn_result)
            .unwrap_err()
            .contains("cannot be dropped or forgotten; match and join them"));

        let discarded_spawn_handle = parse_program(
            "(#fn work ((value u64)) u64 (#return value)) (@thread-spawn (: task WorkTask : worker work)) (#fn main () u64 (#let result WorkTask-spawn-result (#call WorkTask-spawn (: value 1))) (#return (#match result (#case _ 0))))",
        )
        .unwrap();
        assert!(check_types(&discarded_spawn_handle)
            .unwrap_err()
            .contains("must explicitly handle variant 'WorkTask-spawn-ok'"));

        let discarded_join_error_handle = parse_program(
            "(#fn work ((value u64)) u64 (#return value)) (@thread-spawn (: task WorkTask : worker work)) (#fn main () u64 (#return (#match (#call WorkTask-spawn (: value 1)) (#case (WorkTask-spawn-ok task) (#match (#call WorkTask-join (: task task)) (#case (WorkTask-join-ok value) value) (#case (WorkTask-join-error (#tuple _ error)) (#panic)))) (#case (WorkTask-spawn-error error) (#panic)))))",
        )
        .unwrap();
        assert!(check_types(&discarded_join_error_handle)
            .unwrap_err()
            .contains("must bind its task handle instead of discarding it"));

        let forged_task = parse_program(
            "(#fn work ((value u64)) u64 (#return value)) (@thread-spawn (: task WorkTask : worker work)) (#fn main () u64 (#let task WorkTask (WorkTask (#ptr-null (#ptr-mut ())))) (#return 0))",
        )
        .unwrap();
        assert!(check_types(&forged_task)
            .unwrap_err()
            .contains("thread task type 'WorkTask' is opaque"));

        let unknown_worker =
            parse_program("(@thread-spawn (: task MissingTask : worker missing-worker))").unwrap();
        assert!(check_types(&unknown_worker)
            .unwrap_err()
            .contains("unknown worker function 'missing-worker'"));
    }

    #[test]
    fn failed_thread_join_keeps_captured_borrows_active() {
        let program = parse_program(
            r#"(#struct Shared ((value u64)))
(#fn read ((value (#ref Shared))) u64 (#return (#get value value)))
(@thread-spawn (: task ReadTask : worker read))
(#fn main () u64
  (#let-mut shared Shared (#struct-literal Shared ((value 1))))
  (#let spawned ReadTask-spawn-result (#call ReadTask-spawn (: value (#borrow shared))))
  (#return
    (#match spawned
      (#case (ReadTask-spawn-ok task)
        (#match (#call ReadTask-join (: task task))
          (#case (ReadTask-join-ok value) (#block (#set-field shared value 2) value))
          (#case (ReadTask-join-error (#tuple retry error))
            (#block (#set-field shared value 3) 0))))
      (#case (ReadTask-spawn-error error) (#block (#set-field shared value 4) 0)))))"#,
        )
        .unwrap();
        let error = crate::borrowcheck::check_program(&program)
            .unwrap_err()
            .message;
        assert!(
            error.contains("cannot mutate 'shared' while it is immutably borrowed"),
            "{error}"
        );
    }

    #[test]
    fn failed_thread_join_keeps_exclusive_captures_active() {
        let program = parse_program(
            r#"(#struct Shared ((value u64)))
(#fn read-mut ((value (#ref-mut Shared))) u64 (#return (#get value value)))
(@thread-spawn (: task MutTask : worker read-mut))
(#fn main () u64
  (#let-mut shared Shared (#struct-literal Shared ((value 1))))
  (#let spawned MutTask-spawn-result (#call MutTask-spawn (: value (#borrow-mut shared))))
  (#return
    (#match spawned
      (#case (MutTask-spawn-ok task)
        (#match (#call MutTask-join (: task task))
          (#case (MutTask-join-ok value) (#block (#set-field shared value 2) value))
          (#case (MutTask-join-error (#tuple retry error))
            (#block (#let copy Shared shared) 0))))
      (#case (MutTask-spawn-error error) (#block (#let copy Shared shared) 0)))))"#,
        )
        .unwrap();
        let error = crate::borrowcheck::check_program(&program)
            .unwrap_err()
            .message;
        assert!(
            error.contains("cannot access 'shared' while it is mutably borrowed"),
            "{error}"
        );
    }

    #[test]
    fn returns_and_dereferences_references() {
        let program = parse_program(
            "(#let answer u64 42) (#fn identity ((value (#ref u64))) (#ref u64) (#return value)) (#fn get-answer () (#ref u64) (#return (#borrow answer))) (#fn main () u64 (#return (#deref (#call identity (: value (#call get-answer (:)))))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());

        let local_escape =
            parse_program("(#fn bad () (#ref u64) (#let value u64 42) (#return (#borrow value)))")
                .unwrap();
        assert!(check_types(&local_escape)
            .unwrap_err()
            .contains("retaining a reference to local 'value'"));

        let bad_deref = parse_program("(#fn main () u64 (#return (#deref 42)))").unwrap();
        assert!(check_types(&bad_deref)
            .unwrap_err()
            .contains("deref requires a reference"));
    }

    #[test]
    fn writes_through_mutable_references_and_borrows_struct_fields() {
        let write_through_reference = parse_program(
            "(#fn main () u64 (#let-mut value u64 40) (#let reference (#ref-mut u64) (#borrow-mut value)) (#deref-set reference 42) (#return (#deref reference)))",
        )
        .unwrap();
        assert!(
            check_types(&write_through_reference).is_ok(),
            "{:?}",
            check_types(&write_through_reference)
        );
        assert!(generate_assembly(&write_through_reference).is_ok());

        let immutable_write = parse_program(
            "(#fn main () () (#let value u64 40) (#let reference (#ref u64) (#borrow value)) (#deref-set reference 42) (#return ()))",
        )
        .unwrap();
        assert!(check_types(&immutable_write)
            .unwrap_err()
            .contains("deref-set requires a mutable reference"));

        let owner_write_while_mutably_borrowed = parse_program(
            "(#fn main () () (#let-mut value u64 40) (#let reference (#ref-mut u64) (#borrow-mut value)) (#set value 42) (#return ()))",
        )
        .unwrap();
        assert!(check_types(&owner_write_while_mutably_borrowed)
            .unwrap_err()
            .contains("while it is mutably borrowed"));

        let derived_field = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn main () u64 (#let-mut point Point (#struct-literal Point ((x 1) (y 2)))) (#let point-ref (#ref-mut Point) (#borrow-mut point)) (#let x-ref (#ref-mut u64) (#borrow-mut (#get point-ref x))) (#deref-set x-ref 42) (#return (#deref x-ref)))",
        )
        .unwrap();
        assert!(
            check_types(&derived_field).is_ok(),
            "{:?}",
            check_types(&derived_field)
        );
        assert!(generate_assembly(&derived_field).is_ok());

        let suspended_parent = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn main () u64 (#let-mut point Point (#struct-literal Point ((x 1) (y 2)))) (#let point-ref (#ref-mut Point) (#borrow-mut point)) (#let x-ref (#ref-mut u64) (#borrow-mut (#get point-ref x))) (#return (#get point-ref y)))",
        )
        .unwrap();
        assert!(
            check_types(&suspended_parent).is_ok(),
            "{:?}",
            check_types(&suspended_parent)
        );

        let overlapping_field = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn main () u64 (#let-mut point Point (#struct-literal Point ((x 1) (y 2)))) (#let point-ref (#ref-mut Point) (#borrow-mut point)) (#let x-ref (#ref-mut u64) (#borrow-mut (#get point-ref x))) (#return (#get point-ref x)))",
        )
        .unwrap();
        assert!(check_types(&overlapping_field)
            .unwrap_err()
            .contains("cannot access 'point.x' while it is mutably borrowed"));

        let dropped_field_reference = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn main () u64 (#let-mut point Point (#struct-literal Point ((x 1) (y 2)))) (#let point-ref (#ref-mut Point) (#borrow-mut point)) (#let x-ref (#ref-mut u64) (#borrow-mut (#get point-ref x))) (#drop x-ref) (#let y-ref (#ref-mut u64) (#borrow-mut (#get point-ref y))) (#return (#deref y-ref)))",
        )
        .unwrap();
        assert!(
            check_types(&dropped_field_reference).is_ok(),
            "{:?}",
            check_types(&dropped_field_reference)
        );

        let tuple_field_borrow = parse_program(
            "(#fn main () u64 (#let-mut pair (#tuple u64 u64) (#tuple 1 2)) (#let pair-ref (#ref-mut (#tuple u64 u64)) (#borrow-mut pair)) (#let first-ref (#ref-mut u64) (#borrow-mut (#get pair-ref 0))) (#return (#get pair-ref 1)))",
        )
        .unwrap();
        assert!(check_types(&tuple_field_borrow).is_ok());

        let overlapping_tuple_field = parse_program(
            "(#fn main () u64 (#let-mut pair (#tuple u64 u64) (#tuple 1 2)) (#let pair-ref (#ref-mut (#tuple u64 u64)) (#borrow-mut pair)) (#let first-ref (#ref-mut u64) (#borrow-mut (#get pair-ref 0))) (#return (#get pair-ref 0)))",
        )
        .unwrap();
        assert!(check_types(&overlapping_tuple_field)
            .unwrap_err()
            .contains("cannot access 'pair.0' while it is mutably borrowed"));

        let nested_tuple_field = parse_program(
            "(#fn main () u64 (#let-mut pair (#tuple (#tuple u64 u64) u64) (#tuple (#tuple 1 2) 3)) (#let pair-ref (#ref-mut (#tuple (#tuple u64 u64) u64)) (#borrow-mut pair)) (#let first-ref (#ref-mut u64) (#borrow-mut (#get (#get pair-ref 0) 1))) (#return (#get pair-ref 1)))",
        )
        .unwrap();
        assert!(check_types(&nested_tuple_field).is_ok());

        let array_element_borrow = parse_program(
            "(#fn main () u64 (#let-mut values (#array u64 2) (#array 1 2)) (#let values-ref (#ref-mut (#array u64 2)) (#borrow-mut values)) (#let first-ref (#ref-mut u64) (#borrow-mut (#index values-ref 0))) (#return (#index values-ref 1)))",
        )
        .unwrap();
        assert!(
            check_types(&array_element_borrow).is_ok(),
            "{:?}",
            check_types(&array_element_borrow)
        );

        let overlapping_array_element = parse_program(
            "(#fn main () u64 (#let-mut values (#array u64 2) (#array 1 2)) (#let values-ref (#ref-mut (#array u64 2)) (#borrow-mut values)) (#let first-ref (#ref-mut u64) (#borrow-mut (#index values-ref 0))) (#return (#index values-ref 0)))",
        )
        .unwrap();
        assert!(check_types(&overlapping_array_element)
            .unwrap_err()
            .contains("cannot access 'values.0' while it is mutably borrowed"));

        let dynamic_array_element = parse_program(
            "(#fn main ((idx u64)) u64 (#let-mut values (#array u64 2) (#array 1 2)) (#let values-ref (#ref-mut (#array u64 2)) (#borrow-mut values)) (#let element-ref (#ref-mut u64) (#borrow-mut (#index values-ref idx))) (#return (#index values-ref 0)))",
        )
        .unwrap();
        assert!(check_types(&dynamic_array_element)
            .unwrap_err()
            .contains("cannot access 'values.0' while it is mutably borrowed"));

        let multiple_field_borrows = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn main () u64 (#let-mut point Point (#struct-literal Point ((x 1) (y 2)))) (#let point-ref (#ref-mut Point) (#borrow-mut point)) (#let x-ref (#ref-mut u64) (#borrow-mut (#get point-ref x))) (#let y-ref (#ref-mut u64) (#borrow-mut (#get point-ref y))) (#drop x-ref) (#drop y-ref) (#let z-ref (#ref-mut u64) (#borrow-mut (#get point-ref y))) (#return (#deref z-ref)))",
        )
        .unwrap();
        assert!(
            check_types(&multiple_field_borrows).is_ok(),
            "{:?}",
            check_types(&multiple_field_borrows)
        );

        let branch_field_borrow = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn main ((choose bool)) u64 (#let-mut point Point (#struct-literal Point ((x 1) (y 2)))) (#let point-ref (#ref-mut Point) (#borrow-mut point)) (#if choose (#block (#let x-ref (#ref-mut u64) (#borrow-mut (#get point-ref x))) 0) (#block (#let y-ref (#ref-mut u64) (#borrow-mut (#get point-ref y))) 0)) (#return (#get point-ref y)))",
        )
        .unwrap();
        assert!(
            check_types(&branch_field_borrow).is_ok(),
            "{:?}",
            check_types(&branch_field_borrow)
        );

        let enum_payload_borrow = parse_program(
            "(#enum Message ((Move u64 u64) Empty)) (#fn main () u64 (#let-mut message Message (Move 1 2)) (#let message-ref (#ref-mut Message) (#borrow-mut message)) (#return (#borrow-mut (#get-payload message-ref Move 0) (#get-payload message-ref Move 1))))",
        )
        .unwrap();
        assert!(
            check_types(&enum_payload_borrow).is_ok(),
            "{:?}",
            check_types(&enum_payload_borrow)
        );
        assert!(generate_assembly(&enum_payload_borrow).is_ok());

        let overlapping_enum_payload = parse_program(
            "(#enum Message ((Move u64 u64) Empty)) (#fn main () u64 (#let-mut message Message (Move 1 2)) (#let message-ref (#ref-mut Message) (#borrow-mut message)) (#return (#borrow-mut (#get-payload message-ref Move 0) (#get-payload message-ref Move 0))))",
        )
        .unwrap();
        assert!(check_types(&overlapping_enum_payload)
            .unwrap_err()
            .contains("cannot access 'message.Move.0' while it is mutably borrowed"));

        let nested_reference_aggregate = parse_program(
            "(#struct Inner ((data (#ref-mut u64)))) (#struct Outer ((inner (#ref-mut Inner)))) (#fn main () u64 (#let-mut value u64 40) (#let-mut inner Inner (#struct-literal Inner ((data (#borrow-mut value))))) (#let outer Outer (#struct-literal Outer ((inner (#borrow-mut inner))))) (#deref-set (#get (#get outer inner) data) 42) (#return (#deref (#get (#get outer inner) data))))",
        )
        .unwrap();
        assert!(
            check_types(&nested_reference_aggregate).is_ok(),
            "{:?}",
            check_types(&nested_reference_aggregate)
        );
        assert!(generate_assembly(&nested_reference_aggregate).is_ok());

        let tuple_reference_aggregate = parse_program(
            "(#fn main () u64 (#let-mut value u64 40) (#let refs (#tuple (#ref-mut u64)) (#tuple (#borrow-mut value))) (#deref-set (#get refs 0) 42) (#return (#deref (#get refs 0))))",
        )
        .unwrap();
        assert!(check_types(&tuple_reference_aggregate).is_ok());
        assert!(generate_assembly(&tuple_reference_aggregate).is_ok());

        let nested_reference_owner_write = parse_program(
            "(#struct Inner ((data (#ref-mut u64)))) (#struct Outer ((inner (#ref-mut Inner)))) (#fn main () u64 (#let-mut value u64 40) (#let-mut inner Inner (#struct-literal Inner ((data (#borrow-mut value))))) (#let outer Outer (#struct-literal Outer ((inner (#borrow-mut inner))))) (#set value 41) (#return 0))",
        )
        .unwrap();
        assert!(check_types(&nested_reference_owner_write)
            .unwrap_err()
            .contains("cannot mutate 'value' while it is mutably borrowed"));

        let original_owner_suspended = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn main () u64 (#let-mut point Point (#struct-literal Point ((x 1) (y 2)))) (#let point-ref (#ref-mut Point) (#borrow-mut point)) (#return (#get point y)))",
        )
        .unwrap();
        assert!(check_types(&original_owner_suspended)
            .unwrap_err()
            .contains("while it is mutably borrowed"));

        let immutable_derived_field = parse_program(
            "(#struct Point ((x u64))) (#fn main () () (#let point Point (#struct-literal Point ((x 1)))) (#let point-ref (#ref Point) (#borrow point)) (#let x-ref (#ref-mut u64) (#borrow-mut (#get point-ref x))) (#return ()))",
        )
        .unwrap();
        assert!(check_types(&immutable_derived_field)
            .unwrap_err()
            .contains("cannot mutably borrow through an immutable reference"));

        let returned_field_reference = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn point-x ((point (#ref Point))) (#ref u64) (#return (#borrow (#get point x)))) (#fn main () u64 (#let-mut point Point (#struct-literal Point ((x 40) (y 2)))) (#return (#deref (#call point-x (: point (#borrow point))))))",
        )
        .unwrap();
        assert!(check_types(&returned_field_reference).is_ok());
        assert!(generate_assembly(&returned_field_reference).is_ok());

        let escaping_field_reference = parse_program(
            "(#struct Point ((x u64))) (#fn bad () (#ref u64) (#let-mut point Point (#struct-literal Point ((x 42)))) (#let point-ref (#ref Point) (#borrow point)) (#return (#borrow (#get point-ref x))))",
        )
        .unwrap();
        assert!(check_types(&escaping_field_reference)
            .unwrap_err()
            .contains("retaining a reference to local 'point'"));

        let cloned_local_reference = parse_program(
            "(#fn bad () (#ref u64) (#let value u64 42) (#let reference (#ref u64) (#borrow value)) (#return (#clone reference)))",
        )
        .unwrap();
        assert!(check_types(&cloned_local_reference)
            .unwrap_err()
            .contains("cannot return a value retaining a reference to local 'value'"));

        let matched_local_reference = parse_program(
            "(#fn bad () (#ref u64) (#let value u64 42) (#let reference (#ref u64) (#borrow value)) (#return (#match true (#case true (#clone reference)) (#case _ (#clone reference)))))",
        )
        .unwrap();
        assert!(check_types(&matched_local_reference)
            .unwrap_err()
            .contains("cannot return a value retaining a reference to local 'value'"));

        let block_scoped_reference = parse_program(
            "(#fn main () u64 (#let-mut value u64 1) (#block (#let reference (#ref u64) (#borrow value)) 2) (#set value 3) (#return value))",
        )
        .unwrap();
        assert!(check_types(&block_scoped_reference).is_ok());

        let loop_scoped_reference = parse_program(
            "(#fn main () u64 (#let-mut value u64 1) (#while false (#let reference (#ref u64) (#borrow value))) (#set value 3) (#return value))",
        )
        .unwrap();
        assert!(check_types(&loop_scoped_reference).is_ok());

        let dropped_reference = parse_program(
            "(#fn main () u64 (#let-mut value u64 1) (#let reference (#ref-mut u64) (#borrow-mut value)) (#drop reference) (#set value 3) (#return value))",
        )
        .unwrap();
        assert!(check_types(&dropped_reference).is_ok());

        let mutable_reference_struct = parse_program(
            "(#struct MutView ((data (#ref-mut u64)))) (#fn make ((data (#ref-mut u64))) MutView (#return (#struct-literal MutView ((data data))))) (#fn main () u64 (#let-mut value u64 40) (#let view MutView (#call make (: data (#borrow-mut value)))) (#deref-set (#get view data) 42) (#return (#deref (#get view data))))",
        )
        .unwrap();
        assert!(
            check_types(&mutable_reference_struct).is_ok(),
            "{:?}",
            check_types(&mutable_reference_struct)
        );
        assert!(generate_assembly(&mutable_reference_struct).is_ok());

        let destructured_mutable_reference = parse_program(
            "(#struct MutView ((data (#ref-mut u64)))) (#fn main () u64 (#let-mut value u64 40) (#let view MutView (#struct-literal MutView ((data (#borrow-mut value))))) (#let (MutView reference) MutView view) (#deref-set reference 42) (#return (#deref reference)))",
        )
        .unwrap();
        assert!(
            check_types(&destructured_mutable_reference).is_ok(),
            "{:?}",
            check_types(&destructured_mutable_reference)
        );
        assert!(generate_assembly(&destructured_mutable_reference).is_ok());

        let destructured_disjoint_mutable_references = parse_program(
            "(#struct Pair ((left (#ref-mut u64)) (right (#ref-mut u64)))) (#fn main () u64 (#let-mut left-value u64 20) (#let-mut right-value u64 22) (#let pair Pair (#struct-literal Pair ((left (#borrow-mut left-value)) (right (#borrow-mut right-value))))) (#let (Pair left right) Pair pair) (#deref-set left 21) (#deref-set right 23) (#return (#u64.+.wrap (#deref left) (#deref right))))",
        )
        .unwrap();
        assert!(
            check_types(&destructured_disjoint_mutable_references).is_ok(),
            "{:?}",
            check_types(&destructured_disjoint_mutable_references)
        );
        assert!(generate_assembly(&destructured_disjoint_mutable_references).is_ok());

        let duplicate_mutable_reference_fields = parse_program(
            "(#struct Pair ((left (#ref-mut u64)) (right (#ref-mut u64)))) (#fn main () u64 (#let-mut value u64 20) (#let pair Pair (#struct-literal Pair ((left (#borrow-mut value)) (right (#borrow-mut value))))) (#return 0u64))",
        )
        .unwrap();
        assert!(check_types(&duplicate_mutable_reference_fields)
            .unwrap_err()
            .contains("overlapping borrows"));

        let destructured_enum_payload_references = parse_program(
            "(#enum PairOrEmpty ((Pair (#ref-mut u64) (#ref-mut u64)) Empty)) (#fn main () u64 (#let-mut left-value u64 20) (#let-mut right-value u64 22) (#let choice PairOrEmpty (Pair (#borrow-mut left-value) (#borrow-mut right-value))) (#let-else (Pair left right) PairOrEmpty choice (#return 0u64)) (#deref-set left 21) (#deref-set right 23) (#return (#u64.+.wrap (#deref left) (#deref right))))",
        )
        .unwrap();
        assert!(
            check_types(&destructured_enum_payload_references).is_ok(),
            "{:?}",
            check_types(&destructured_enum_payload_references)
        );
        assert!(generate_assembly(&destructured_enum_payload_references).is_ok());

        let destructured_array_references = parse_program(
            "(#fn main () u64 (#let-mut left-value u64 20) (#let-mut right-value u64 22) (#let references (#array (#ref-mut u64) 2) (#array (#array (#ref-mut u64) 2) (#borrow-mut left-value) (#borrow-mut right-value))) (#let (#array left right) (#array (#ref-mut u64) 2) references) (#deref-set left 21) (#deref-set right 23) (#return (#u64.+.wrap (#deref left) (#deref right))))",
        )
        .unwrap();
        assert!(check_types(&destructured_array_references).is_ok());
        assert!(generate_assembly(&destructured_array_references).is_ok());

        let destructured_tuple_references = parse_program(
            "(#fn main () u64 (#let-mut left-value u64 20) (#let-mut right-value u64 22) (#let references (#tuple (#ref-mut u64) (#ref-mut u64)) (#tuple (#tuple (#ref-mut u64) (#ref-mut u64)) (#borrow-mut left-value) (#borrow-mut right-value))) (#let (#tuple left right) (#tuple (#ref-mut u64) (#ref-mut u64)) references) (#deref-set left 21) (#deref-set right 23) (#return (#u64.+.wrap (#deref left) (#deref right))))",
        )
        .unwrap();
        assert!(check_types(&destructured_tuple_references).is_ok());
        assert!(generate_assembly(&destructured_tuple_references).is_ok());

        let destructured_returnable_reference = parse_program(
            "(#struct View ((data (#ref u64)))) (#fn wrap ((source (#ref u64))) View (#return (#struct-literal View ((data source))))) (#fn unwrap ((source (#ref u64))) (#ref u64) (#let view View (#call wrap (: source source))) (#let (View reference) View view) (#return reference))",
        )
        .unwrap();
        assert!(check_types(&destructured_returnable_reference).is_ok());
        assert!(generate_assembly(&destructured_returnable_reference).is_ok());

        let destructured_reference_escape = parse_program(
            "(#struct View ((data (#ref u64)))) (#fn bad () (#ref u64) (#let value u64 40) (#let view View (#struct-literal View ((data (#borrow value))))) (#let (View reference) View view) (#return reference))",
        )
        .unwrap();
        assert!(check_types(&destructured_reference_escape)
            .unwrap_err()
            .contains("cannot return a value retaining a reference to local 'value'"));

        let mutable_reference_struct_escape = parse_program(
            "(#struct MutView ((data (#ref-mut u64)))) (#fn make ((data (#ref-mut u64))) MutView (#return (#struct-literal MutView ((data data))))) (#fn bad () MutView (#let-mut value u64 40) (#return (#call make (: data (#borrow-mut value)))))",
        )
        .unwrap();
        assert!(check_types(&mutable_reference_struct_escape)
            .unwrap_err()
            .contains("cannot return a value retaining a reference to local 'value'"));

        let mutable_reference_struct_clone = parse_program(
            "(#struct MutView ((data (#ref-mut u64)))) (#fn main () () (#let-mut value u64 40) (#let view MutView (#struct-literal MutView ((data (#borrow-mut value))))) (#let duplicate MutView (#clone view)) (#return ()))",
        )
        .unwrap();
        assert!(check_types(&mutable_reference_struct_clone)
            .unwrap_err()
            .contains("a mutable reference cannot be cloned"));
    }

    #[test]
    fn checks_raw_pointers_and_unsafe_blocks() {
        let null_pointer_program =
            parse_program("(#fn make-null () (#ptr-mut u64) (#return (#ptr-null (#ptr-mut u64))))")
                .unwrap();
        assert!(check_types(&null_pointer_program).is_ok());
        let null_assembly = generate_assembly(&null_pointer_program).unwrap();
        assert!(null_assembly.contains("xor eax, eax"));

        let pointer_null_test = parse_program(
            "(#fn main () bool (#let pointer (#ptr u64) (#ptr-null (#ptr u64))) (#return (#ptr-is-null pointer)))",
        )
        .unwrap();
        assert!(check_types(&pointer_null_test).is_ok());
        assert!(generate_assembly(&pointer_null_test)
            .unwrap()
            .contains("sete al"));

        let pointer_address = parse_program(
            "(#fn main () usize (#let pointer (#ptr u8) (#ptr-null (#ptr u8))) (#return (#ptr-address pointer)))",
        )
        .unwrap();
        assert!(check_types(&pointer_address).is_ok());
        assert!(generate_assembly(&pointer_address).is_ok());
        let invalid_address =
            parse_program("(#fn main () usize (#return (#ptr-address 1usize)))").unwrap();
        assert!(check_types(&invalid_address)
            .unwrap_err()
            .contains("ptr-address requires a raw pointer"));

        let untyped_null_pointer =
            parse_program("(#fn bad () (#ptr u64) (#return (#ptr-null u64)))").unwrap();
        assert!(check_types(&untyped_null_pointer)
            .unwrap_err()
            .contains("ptr-null requires an explicit raw-pointer type"));

        let pointer_program = parse_program(
            "(#fn main () u64 (#let-mut value u64 40) (#return (#unsafe (#block (#let p (#ptr-mut u64) (#addr-of-mut value)) (#ptr-write p 42) (#ptr-read p)))))",
        )
        .unwrap();
        assert!(check_types(&pointer_program).is_ok());
        assert!(generate_assembly(&pointer_program).is_ok());

        let safe_pointer_use = parse_program(
            "(#fn bad () u64 (#let value u64 42) (#return (#ptr-read (#addr-of value))))",
        )
        .unwrap();
        assert!(check_types(&safe_pointer_use)
            .unwrap_err()
            .contains("requires an enclosing (#unsafe ...) block"));

        let immutable_pointer_write = parse_program(
            "(#fn bad () u64 (#let value u64 42) (#let p (#ptr u64) (#unsafe (#addr-of value))) (#unsafe (#ptr-write p 1)) (#return value))",
        )
        .unwrap();
        assert!(check_types(&immutable_pointer_write)
            .unwrap_err()
            .contains("mutable raw pointer"));

        let pointer_offset = parse_program(
            "(#fn main () u64 (#let-mut value u64 42u64) (#let pointer (#ptr-mut u64) (#unsafe (#addr-of-mut value))) (#return (#unsafe (#ptr-read (#ptr-offset pointer 0usize)))))",
        )
        .unwrap();
        assert!(check_types(&pointer_offset).is_ok());
        let assembly = generate_assembly(&pointer_offset).unwrap();
        assert!(assembly.contains("mul rcx"));
        assert!(assembly.contains("pointer_offset_overflow"));

        let wrong_index_type = parse_program(
            "(#fn bad ((pointer (#ptr u64))) (#ptr u64) (#return (#unsafe (#ptr-offset pointer 0u64))))",
        )
        .unwrap();
        assert!(check_types(&wrong_index_type)
            .unwrap_err()
            .contains("expected Usize"));

        let missing_unsafe = parse_program(
            "(#fn bad ((pointer (#ptr u64))) (#ptr u64) (#return (#ptr-offset pointer 1usize)))",
        )
        .unwrap();
        assert!(check_types(&missing_unsafe)
            .unwrap_err()
            .contains("requires an enclosing (#unsafe ...) block"));

        let unsafe_span_source =
            "(#fn bad ((pointer (#ptr u64))) (#ptr u64)\n  (#return (#ptr-offset pointer 1usize)))";
        let unsafe_span_program = parse_program(unsafe_span_source).unwrap();
        let unsafe_diagnostic = structured_type_error(&unsafe_span_program);
        let span = unsafe_diagnostic
            .span
            .expect("unsafe pointer operation has a structured span");
        assert_eq!(&unsafe_span_source[span.start..span.end], "#ptr-offset");

        let return_borrow_from_raw_pointer = parse_program(
            "(#fn expose ((anchor (#ref u64)) (pointer (#ptr u64))) (#ref u64) (#let reference (#ref u64) (#unsafe (#ptr-borrow anchor pointer))) (#forget pointer) (#return reference)) (#fn bad () u64 (#let-mut value u64 41) (#let pointer (#ptr u64) (#unsafe (#addr-of value))) (#let reference (#ref u64) (#call expose (: anchor (#borrow value) : pointer pointer))) (#set value 42) (#return (#deref reference)))",
        )
        .unwrap();
        let error = check_types(&return_borrow_from_raw_pointer).unwrap_err();
        assert!(
            error.contains("cannot mutate 'value' while it is immutably borrowed"),
            "{error}"
        );

        let valid_return_borrow_from_raw_pointer = parse_program(
            "(#fn expose ((anchor (#ref u64)) (pointer (#ptr u64))) (#ref u64) (#let reference (#ref u64) (#unsafe (#ptr-borrow anchor pointer))) (#forget pointer) (#return reference)) (#fn main () u64 (#let-mut value u64 41) (#let pointer (#ptr u64) (#unsafe (#addr-of value))) (#let reference (#ref u64) (#call expose (: anchor (#borrow value) : pointer pointer))) (#return (#deref reference)))",
        )
        .unwrap();
        let checked = check_types(&valid_return_borrow_from_raw_pointer);
        assert!(checked.is_ok(), "{checked:?}");
        assert!(generate_assembly(&valid_return_borrow_from_raw_pointer).is_ok());

        let mutable_borrow_with_immutable_anchor = parse_program(
            "(#fn bad ((anchor (#ref u64)) (pointer (#ptr-mut u64))) (#ref-mut u64) (#return (#unsafe (#ptr-borrow-mut anchor pointer))))",
        )
        .unwrap();
        assert!(check_types(&mutable_borrow_with_immutable_anchor)
            .unwrap_err()
            .contains("requires a mutable reference anchor"));
    }

    #[test]
    fn rejects_legacy_forms() {
        let missing_prefix = parse_program("(fn main () u64 (#return 42))").unwrap_err();
        assert!(missing_prefix.contains("must use its '#' prefix"));
        let missing_return = parse_program("(#fn main () u64 42)").unwrap_err();
        assert!(missing_return.contains("explicit"));
        let unqualified_arithmetic =
            parse_program("(#fn main () u64 (#return (#+ 40 2)))").unwrap_err();
        assert!(unqualified_arithmetic.contains("explicit type qualifier"));
        let unqualified_comparison =
            parse_program("(#fn main () bool (#return (#== 40 2)))").unwrap_err();
        assert!(unqualified_comparison.contains("explicit type qualifier"));
        assert!(parse_program("(#fn main () bool (#return (#u64.== 40 2)))").is_ok());
        let missing_match_case =
            parse_program("(#fn main () u64 (#return (#match true (true 1u64) (#case _ 0u64))))")
                .unwrap_err();
        assert!(missing_match_case.contains("each #match arm must use #case"));
        let valid = parse_program("(#fn main () u64 (#return (#u64.+.wrap 40 2)))");
        assert!(valid.is_ok());
        let external = parse_program(
            "(#extern-fn #abi-c abs ((value i32)) i32) (#fn main () u64 (#return (#as (#unsafe (#call abs (: value -42))) u64)))",
        )
        .unwrap();
        assert!(check_types(&external).is_ok());
        let external_assembly = generate_assembly(&external).unwrap();
        assert!(external_assembly.contains(".extern abs"));
        assert!(external_assembly.contains("call abs"));
        let unsafe_boundary = parse_program(
            "(#extern-fn #abi-c abs ((value i32)) i32) (#fn main () u64 (#return (#as (#call abs (: value -42)) u64)))",
        )
        .unwrap();
        assert!(check_types(&unsafe_boundary)
            .unwrap_err()
            .contains("call to external function 'abs' requires"));
    }

    #[test]
    fn treats_dotted_names_as_ordinary_identifiers() {
        let tokens = lex("a.b.c - . #u64.+.wrap").unwrap();
        assert_eq!(tokens[0].kind, TokenKind::Symbol("a.b.c".into()));
        assert_eq!(tokens[1].kind, TokenKind::Symbol("-".into()));
        assert_eq!(tokens[2].kind, TokenKind::Symbol(".".into()));
        assert_eq!(tokens[3].kind, TokenKind::Symbol("#u64.+.wrap".into()));
        let program = parse_program(
            "(#fn util.add-one () u64 (#return 42))
             (#fn main () u64
               (#let-mut value.local u64 (#call util.add-one (:)))
               (#set value.local 84u64)
               (#return value.local))
             (#fn wide.value () i128
               (#let-mut wide.local i128 12)
               (#set wide.local 15)
               (#return wide.local))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("util_x2e_add_x2d_one"));
    }

    #[test]
    fn parses_nested_lists_quotes_and_comments() {
        let expressions = parse("# header\n'(#fn main () i32 42) ; tail\n").unwrap();
        assert!(matches!(expressions[0].expr, Expr::Quote(_)));
    }

    #[test]
    fn colon_groups_expand_to_lists_and_require_a_prefix() {
        let shorthand = "(: text (#slice char) : control u32)";
        let parsed = parse(shorthand).unwrap();
        assert_eq!(
            parsed[0].expr,
            parse("((text (#slice char)) (control u32))").unwrap()[0].expr
        );
        assert_eq!(parsed[0].children.len(), 2);
        assert_eq!(
            &shorthand[parsed[0].children[1].span.start..parsed[0].children[1].span.end],
            ": control u32"
        );
        assert_eq!(parse("(:)").unwrap()[0].expr, Expr::List(vec![]));
        for invalid in ["(name : value)", "(: x : : y)", "(: x :)", ":"] {
            assert!(parse(invalid).is_err(), "{invalid}");
        }
        let invalid = "(name : value)";
        let error = Parser::new(&lex(invalid).unwrap()).run().unwrap_err();
        assert_eq!(&invalid[error.span.start..error.span.end], ":");
        assert!(parse("(: outer (: inner value) : other 1)").is_ok());
        assert_eq!(lex("#\\:").unwrap()[0].kind, TokenKind::Char(':'));
    }

    #[test]
    fn colon_groups_work_in_signatures_and_named_calls() {
        let source = "(#fn sum (: index u32 : right u32) u32
          (#return (#u32.+.wrap index right)))
          (#fn main () u32
            (#return (#call sum (: right 2u32 : index 40u32))))";
        let program = parse_program(source).unwrap();
        assert!(check_types(&program).is_ok(), "{:?}", check_types(&program));
        assert!(generate_assembly(&program).is_ok());
        let empty = parse_program(
            "(#fn answer (:) u32 (#return 42u32))
             (#fn main (:) u32 (#return (#call answer (:))))",
        )
        .unwrap();
        assert!(check_types(&empty).is_ok());
        assert!(parse_program("(#extern-fn #abi-c abs (: value i32) i32)").is_ok());
        let missing = parse_program(
            "(#fn take (: left u32 : right u32) u32 (#return left))
             (#fn main () u32 (#return (#call take (: left 1u32))))",
        )
        .unwrap_err();
        assert!(missing.contains("missing parameter"), "{missing}");

        let duplicate = "(#fn take (: left u32) u32 (#return left))
          (#fn main () u32 (#return (#call take (: left 1u32 : left 2u32))))";
        let cache =
            std::env::temp_dir().join(format!("lim-colon-duplicate-cache-{}", std::process::id()));
        let error = compile_source_to_assembly(
            duplicate,
            Path::new("colon-duplicate.lim"),
            &CompileConfig::default(),
            &cache,
            TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert!(error.message.contains("more than once"), "{error:?}");
        let span = error.span.expect("duplicate argument has a source span");
        assert_eq!(&duplicate[span.start..span.end], "left");
        let obsolete = parse_program(
            "(#fn take (: value u32) u32 (#return value))
             (#fn main () u32 (#return (#call take (#fn-args (value 1u32)))))",
        )
        .unwrap_err();
        assert!(obsolete.contains("named argument"), "{obsolete}");
    }

    #[test]
    fn formatter_keeps_colon_group_spelling() {
        let source = "(#fn take (: left u32 : right u32) u32 (#return left))
          (#fn main () u32 (#return (#call take (: right 2u32 : left 40u32))))";
        let formatted = format_source(source).unwrap();
        assert!(formatted.contains("(: left u32 : right u32)"));
        assert!(formatted.contains("(: right 2u32 : left 40u32)"));
        assert_eq!(format_source(&formatted).unwrap(), formatted);
    }

    #[test]
    fn parser_rejects_excessive_nesting_with_a_spanned_error() {
        let within_limit = format!(
            "{}value{}",
            "(".repeat(MAX_PARSE_NESTING - 1),
            ")".repeat(MAX_PARSE_NESTING - 1)
        );
        assert!(parse(&within_limit).is_ok());

        let over_limit = format!(
            "{}value{}",
            "(".repeat(MAX_PARSE_NESTING),
            ")".repeat(MAX_PARSE_NESTING)
        );
        let tokens = lex(&over_limit).unwrap();
        let error = Parser::new(&tokens).run().unwrap_err();
        assert!(error.message.contains("expression nesting exceeds maximum"));
        assert!(error.span.start < over_limit.len());
    }

    #[test]
    fn parses_strings_and_signed_integers() {
        let expressions = parse("(say \"line\\n\" -42)").unwrap();
        let Expr::List(items) = &expressions[0].expr else {
            panic!()
        };
        assert_eq!(items[1], Expr::String("line\n".into()));
        assert_eq!(items[2], Expr::Integer(-42));
        let minimum = parse("(-170141183460469231731687303715884105728)").unwrap();
        assert_eq!(minimum[0].expr, Expr::List(vec![Expr::Integer(i128::MIN)]));
        let literals = parse("(0xff 0o10 0b1010 1_000)").unwrap();
        assert_eq!(
            literals[0].expr,
            Expr::List(vec![
                Expr::Integer(255),
                Expr::Integer(8),
                Expr::Integer(10),
                Expr::Integer(1000),
            ])
        );
    }

    #[test]
    fn parses_lisp_character_literals() {
        let expressions = parse("(#\\a #\\space #\\newline)").unwrap();
        assert_eq!(
            expressions[0].expr,
            Expr::List(vec![Expr::Char('a'), Expr::Char(' '), Expr::Char('\n')])
        );
        let unicode = parse("(#\\u{03bb} \"A\\u{1f600}\")").unwrap();
        assert_eq!(
            unicode[0].expr,
            Expr::List(vec![Expr::Char('λ'), Expr::String("A😀".into())])
        );
        assert!(parse("#\\u{d800}").is_err());
        assert!(parse("\"bad\\u{110000}\"").is_err());
    }

    #[test]
    fn reports_unterminated_list() {
        let error = parse("(#fn missing").unwrap_err();
        assert!(error.contains("unterminated list"));
    }

    #[test]
    fn parses_typed_lets_and_functions() {
        let program = parse_program(
            "(#fn add ((left u32) (right u64)) u64 (#let total u64 (#u64.+.wrap  left right)) (#return total))",
        )
        .unwrap();
        let Item::Function(function) = &program.items[0] else {
            panic!()
        };
        assert_eq!(function.name, "add");
        assert_eq!(function.parameters[0].ty, Type::U32);
        assert_eq!(function.parameters[1].ty, Type::U64);
        assert_eq!(function.return_type, Type::U64);
        assert!(matches!(
            function.body[0],
            Statement::Let { ty: Type::U64, .. }
        ));
        assert!(matches!(
            function.body[1],
            Statement::Return(Some(Expr::Symbol(ref name))) if name == "total"
        ));
        let local_const = parse_program(
            "(#fn main () u64 (#const Answer u64 40) (#return (#u64.+.wrap  Answer 2)))",
        )
        .unwrap();
        assert!(check_types(&local_const).is_ok());
        assert!(generate_assembly(&local_const).is_ok());
        let mutable_const = parse_program(
            "(#fn main () u64 (#const Answer u64 40) (#set Answer 42) (#return Answer))",
        )
        .unwrap();
        assert!(check_types(&mutable_const)
            .unwrap_err()
            .contains("immutable variable 'Answer'"));
        let generic =
            parse_program("(#fn identity (T) ((value T)) T (#return value))").unwrap_err();
        assert!(generic.contains("generic functions are not supported"));
        let instantiated = parse_program("(#fn main () u64 (#return (identity<u64> 42)))").unwrap();
        assert!(check_types(&instantiated)
            .unwrap_err()
            .contains("angle-bracket generic calls are not supported"));
        let concrete = parse_program(
            "(#fn identity-u64 ((value u64)) u64 (#return value)) (#fn main () u64 (#return (#call identity-u64 (: value 42))))",
        )
        .unwrap();
        assert!(check_types(&concrete).is_ok());
        assert!(generate_assembly(&concrete).is_ok());
    }

    #[test]
    fn parses_all_builtin_scalar_types_and_named_types() {
        let program = parse_program(
            "(#fn types ((a u8) (b u16) (c u32) (d u64) (e u128) (f usize) (g i8) (h i16) (i i32) (j i64) (k i128) (l isize) (m f32) (n f64) (o bool) (p char) (q UserId)) () (#return ()))",
        )
        .unwrap();
        let Item::Function(function) = &program.items[0] else {
            panic!()
        };
        assert_eq!(function.parameters.len(), 17);
        assert_eq!(function.parameters[16].ty, Type::Named("UserId".into()));
        assert_eq!(function.return_type, Type::Unit);
    }

    #[test]
    fn parses_and_checks_typed_constants() {
        let program = parse_program(
            "(#const Answer u64 (#u64.+.wrap  40 2)) (#fn main () u64 (#return Answer))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("Answer:"));
    }

    #[test]
    fn evaluates_typed_float_constants() {
        let program = parse_program(
            "(#const Scale f32 (#f32.* Base 2.0)) (#const Base f32 1.5) (#const Pi f64 (#f64.+ 3.0 0.25)) (#fn main () u64 (#return (#if (#bool.&& (#f32.> Scale 2.9) (#f64.> Pi 3.2)) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("Scale:\n    .long 1077936128"));
        assert!(assembly.contains("Pi:"));
    }

    #[test]
    fn parses_and_checks_immutable_statics() {
        let program = parse_program(
            "(#static BuildId u64 7) (#fn main () u64 (#return (#u64.+.wrap  (#unsafe BuildId) 35)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let safe_read =
            parse_program("(#static BuildId u64 7) (#fn main () u64 (#return BuildId))").unwrap();
        assert!(check_types(&safe_read)
            .unwrap_err()
            .contains("access to static 'BuildId' requires"));
        assert!(generate_assembly(&program).unwrap().contains("BuildId:"));
    }

    #[test]
    fn lowers_aggregate_statics_for_index_and_field_reads() {
        let program = parse_program(
            "(#struct Point ((x u64) (y u64))) (#static Values (#array u64 3) (#array (#array u64 3) 10 20 30)) (#static Origin Point (#struct-literal Point ((x 7) (y 9)))) (#static Pair (#tuple u64 f64) (#tuple (#tuple u64 f64) 4 2.5)) (#enum Maybe ((Some u64) None)) (#static Choice Maybe (Some 12)) (#fn take ((values (#array u64 3)) (point Point)) u64 (#return (#u64.+.wrap (#index values 1) (#get point y)))) (#fn return-values () (#array u64 3) (#return (#unsafe Values))) (#fn read-choice ((choice Maybe)) u64 (#return (#match choice (#case (Some value) value) (#case None 0)))) (#fn return-choice () Maybe (#return (#unsafe Choice))) (#fn main () u64 (#let copied (#array u64 3) (#unsafe Values)) (#let copied-choice Maybe (#unsafe Choice)) (#return (#u64.+.wrap (#index copied 0) (#u64.+.wrap (#index (#call return-values (:)) 2) (#u64.+.wrap (#call take (: values (#unsafe Values) : point (#unsafe Origin))) (#u64.+.wrap (#call read-choice (: choice copied-choice)) (#call read-choice (: choice (#call return-choice (:))))))))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program);
        assert!(assembly.is_ok(), "{assembly:?}");
    }

    #[test]
    fn evaluates_floating_remainder_constants() {
        let program = parse_program(
            "(#const Remainder f64 (#f64.% 7.5 2.5)) (#fn main () u64 (#return (#if (#f64.== Remainder 0.0) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program);
        assert!(assembly.is_ok(), "{assembly:?}");
    }

    #[test]
    fn rejects_malformed_let_and_functions() {
        assert!(parse_program("(#let value u32)")
            .unwrap_err()
            .contains("let requires"));
        assert!(parse_program("(#fn broken ((value u32)) u32)")
            .unwrap_err()
            .contains("explicit"));
        assert!(parse_program("(unknown form)")
            .unwrap_err()
            .contains("unknown top-level"));
        assert!(parse_program("(#fn empty () ())")
            .unwrap_err()
            .contains("explicit"));
        assert!(parse_program("(#fn missing () u64)")
            .unwrap_err()
            .contains("explicit"));
    }

    #[test]
    fn generates_native_integer_assembly() {
        let program = parse_program("(#fn main () i64 (#return (#i64.+.wrap  20 22)))").unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains(".globl main"));
        assert!(assembly.contains("add rax, rcx"));
        assert!(assembly.contains("# lim frame size:"));
        assert!(assembly.contains("ret"));
        assert!(assembly.contains(".note.GNU-stack"));
    }

    #[test]
    fn type_checks_variables_calls_and_returns() {
        let program =
            parse_program("(#fn inc ((value u32)) u32 (#return (#u32.+.wrap  value 1))) (#fn main () u32 (#return (#call inc (: value 41))))")
                .unwrap();
        assert!(check_types(&program).is_ok());
        let mismatch = parse_program("(#fn main () u32 (#return true))").unwrap();
        assert!(check_types(&mismatch).unwrap_err().contains("expected U32"));
        let unknown = parse_program("(#fn main () u32 (#return missing))").unwrap();
        assert!(check_types(&unknown)
            .unwrap_err()
            .contains("unknown variable"));
    }

    #[test]
    fn rejects_shadowed_local_bindings() {
        let program = parse_program(
            "(#fn main () u64 (#let value u64 40) (#let value u64 (#u64.+.wrap value 1)) (#return (#u64.+.wrap value (#block (#let value u64 1) (#u64.+.wrap value 1)))))",
        )
        .unwrap_err();
        assert!(program.contains("binding 'value' shadows an existing binding"));
    }

    #[test]
    fn rejects_parameters_that_shadow_globals() {
        let error = parse_program(
            "(#let value u64 10) (#fn read ((value u64)) u64 (#return value)) (#fn main () u64 (#return (#call read (: value 42))))",
        )
        .unwrap_err();
        assert!(error.contains("binding 'value' shadows an existing binding"));
    }

    #[test]
    fn rejects_match_bindings_that_shadow_outer_locals() {
        let error = parse_program(
            "(#enum Maybe ((Some u64) None)) (#fn main () u64 (#let value u64 40) (#return (#match (Some 1) (#case (Some value) (#u64.+.wrap value 1)) (#case None value))))",
        )
        .unwrap_err();
        assert!(error.contains("binding 'value' shadows an existing binding"));
    }

    #[test]
    fn preserves_type_descriptors_when_a_local_matches_a_type_name() {
        let program = parse_program(
            "(#fn main () u64 (#let u64 u64 40) (#return (#u64.+.wrap (#get (#tuple (#tuple u64 u64) u64 2) 0) 2)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn parses_mutable_while_statements() {
        let program =
            parse_program("(#fn count () u64 (#let-mut n u64 0) (#while (#u64.<  (#clone n) 3) (#set n (#u64.+.wrap  n 1))) (#return n))")
                .unwrap();
        let Item::Function(function) = &program.items[0] else {
            panic!()
        };
        assert!(matches!(
            function.body[0],
            Statement::Let { mutable: true, .. }
        ));
        assert!(matches!(function.body[1], Statement::While { .. }));
        assert!(check_types(&program).is_ok());
    }

    #[test]
    fn accepts_u64_literals_above_i64_range() {
        let program = parse_program("(#fn main () u64 (#return 18446744073709551615))").unwrap();
        assert!(check_types(&program).is_ok());
        let too_large = parse_program("(#fn main () u32 (#return 4294967296))").unwrap();
        assert!(check_types(&too_large)
            .unwrap_err()
            .contains("does not fit"));
    }

    #[test]
    fn checks_break_and_continue_scope() {
        let valid = parse_program(
            "(#fn main () u64 (#let-mut n u64 0) (#while (#u64.<  (#clone n) 3) (#set n (#u64.+.wrap  n 1)) (#continue)) (#return n))",
        )
        .unwrap();
        assert!(check_types(&valid).is_ok());
        let invalid = parse_program("(#fn main () () (#break) (#return ()))").unwrap();
        assert!(check_types(&invalid)
            .unwrap_err()
            .contains("outside a loop"));
    }

    #[test]
    fn scopes_loop_value_breaks_to_their_own_loop() {
        let nested_statement =
            parse_program("(#fn main () u64 (#loop (#loop (#break 7))) (#return 42))").unwrap();
        assert!(check_types(&nested_statement).is_ok());
        let Item::Function(function) = &nested_statement.items[0] else {
            panic!("expected a function");
        };
        assert!(matches!(function.body[0], Statement::Loop { .. }));

        let mismatched =
            parse_program("(#fn main () u64 (#return (#loop (#loop (#break true)) (#break 42))))")
                .unwrap();
        assert!(check_types(&mismatched).is_ok());
    }

    #[test]
    fn checks_and_lowers_early_return() {
        let program = parse_program("(#fn main () u64 (#return 42) (#return 0))").unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("mov rax, 42"));
        assert!(assembly.contains("jmp .Lreturn_main"));
    }

    #[test]
    fn generates_integer_operator_family() {
        let program = parse_program(
            "(#fn main () i64 (#return (#i64.%.wrap  (#i64./.wrap  (#i64.^  20 1) 2) 3)))",
        )
        .unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("idiv rcx"));
        assert!(assembly.contains("xor rax, rcx"));
        assert!(assembly.contains("division_by_zero"));
    }

    #[test]
    fn emits_wide_division_by_zero_traps() {
        let program = parse_program("(#fn main () u128 (#return (#u128.%.wrap 1 0)))").unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("wide_division_by_zero"));
        assert!(assembly.contains("ud2"));
    }

    #[test]
    fn lowers_unsigned_division_and_remainder() {
        let program = parse_program(
            "(#fn main () u64 (#let left u64 20) (#let right u64 3) (#return (#u64.+.wrap  (#u64./.wrap  (#clone left) (#clone right)) (#u64.%.wrap  left right))))",
        )
        .unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("div rcx"));
        assert!(!assembly.contains("idiv rcx"));
    }

    #[test]
    fn lowers_float_values_inside_aggregates() {
        let program = parse_program(
            "(#struct Point ((x f64) (y f32))) (#fn main () u64 (#let point Point (#struct-literal Point ((x 1.5) (y 2.5)))) (#let x f64 (#get point x)) (#let values (#array f32 2) (#array 1.5 2.5)) (#let y f32 (#index values 1)) (#return (#if (#bool.&& (#f64.> x 1.0) (#f32.> y 2.0)) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("movss xmm0, DWORD PTR"));
        assert!(assembly.contains("movq xmm0, QWORD PTR"));
    }

    #[test]
    fn preserves_unsigned_comparisons_and_shifts() {
        let program =
            parse_program("(#fn main () u64 (#let value u64 1) (#return (#if (#u64.<  (#clone value) 2) (#u64.>>  value 1) 0)))")
                .unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("setb al"), "{assembly}");
        assert!(assembly.contains("shr rax, cl"));
    }

    #[test]
    fn checks_and_lowers_explicit_integer_casts() {
        let program = parse_program("(#fn main () u64 (#return (#as (#as 42 u32) u64)))").unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("mov rax, 42"));
        let invalid = parse_program("(#fn main () u64 (#return (#as 42 ())))").unwrap();
        assert!(check_types(&invalid).unwrap_err().contains("numeric"));
    }

    #[test]
    fn checks_and_lowers_numeric_casts() {
        let program = parse_program(
            "(#fn main () u64 (#let value f64 41.75) (#let whole u64 (#as value u64)) (#let small f32 (#as whole f32)) (#return (#as small u64)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("cvttsd2si rax, xmm0"));
        assert!(assembly.contains("cvtsi2ss xmm0, rax"));
        assert!(assembly.contains("cvttss2si rax, xmm0"));
    }

    #[test]
    fn checks_and_lowers_128_bit_casts() {
        let program = parse_program(
            "(#fn widen () u128 (#return (#as 42 u128))) (#fn main () u64 (#let value u128 (#call widen (:))) (#return (#as value u64)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("sar rdx, 63"));
        let signed =
            parse_program("(#fn main ((value i128)) i64 (#return (#as value i64)))").unwrap();
        assert!(check_types(&signed).is_ok());
        assert!(generate_assembly(&signed).is_ok());
    }

    #[test]
    fn passes_aggregate_values_with_mixed_float_parameters() {
        let program = parse_program(
            "(#struct Pair ((scale f32) (value u64))) (#fn consume ((pair Pair) (factor f32)) u64 (#return (#if (#f32.>  (#get pair scale) 1.0) (#u64.+.wrap (#get pair value) 1) 0))) (#fn main () u64 (#return (#call consume (: pair (#struct-literal Pair ((scale 1.5) (value 41))) : factor 2.0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("mov rdi, QWORD PTR"));
        assert!(assembly.contains("movd xmm0"));
    }

    #[test]
    fn passes_six_field_structs_through_functions() {
        let program = parse_program(
            "(#struct Values ((a u64) (b u64) (c u64) (d u64) (e u64) (f u64))) (#fn make () Values (#return (#struct-literal Values ((a 1) (b 2) (c 3) (d 4) (e 5) (f 6))))) (#fn sum ((value Values)) u64 (#return (#u64.+.wrap  (#u64.+.wrap  (#u64.+.wrap  (#u64.+.wrap  (#u64.+.wrap  (#get value a) (#get value b)) (#get value c)) (#get value d)) (#get value e)) (#get value f)))) (#fn main () u64 (#return (#call sum (: value (#call make (:))))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("pop rdi"));
        assert!(assembly.contains("[rbp-8], rdi"));
    }

    #[test]
    fn passes_mixed_f32_and_f64_parameters() {
        let program = parse_program(
            "(#fn blend ((small f32) (large f64)) f64 (#return (#f64.+ (#as small f64) large))) (#fn main () u64 (#return (#if (#f64.> (#call blend (: small 1.5 : large 2.5)) 4.0) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("movd xmm0"));
        assert!(assembly.contains("movq xmm1"));
    }

    #[test]
    fn passes_tuples_through_functions() {
        let program = parse_program(
            "(#fn make () (#tuple u64 f32) (#return (#tuple 40 2.5))) (#fn consume ((value (#tuple u64 f32))) u64 (#return (#u64.+.wrap (#get value 0) (#as (#get value 1) u64)))) (#fn main () u64 (#let value (#tuple u64 f32) (#call make (:))) (#return (#call consume (: value value))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("call make"));
        assert!(assembly.contains("call consume"));
    }

    #[test]
    fn mutates_tuple_fields() {
        let program = parse_program(
            "(#fn main () u64 (#let-mut value (#tuple u64 f32) (#tuple 1 2.5)) (#set-field value 0 40) (#return (#u64.+.wrap (#get value 0) 2)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program)
            .unwrap()
            .contains("QWORD PTR [rbp-8]"));
        let invalid = parse_program(
            "(#fn main () u64 (#let value (#tuple u64 f32) (#tuple 1 2.5)) (#set-field value 0 40) (#return 0))",
        )
        .unwrap();
        assert!(check_types(&invalid)
            .unwrap_err()
            .contains("immutable variable"));
    }

    #[test]
    fn normalizes_integer_width_after_arithmetic() {
        let program = parse_program(
            "(#fn main () u64 (#let value u8 (#u8.+.wrap (#as 255 u8) 1)) (#return (#if (#u8.== value 0) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program)
            .unwrap()
            .contains("movzx eax, al"));
    }

    #[test]
    fn normalizes_typed_global_constants() {
        let program =
            parse_program("(#let WRAPPED u8 (#u8.+.wrap 255 1)) (#fn main () u64 (#return (#if (#u8.== WRAPPED 0) 42 0)))")
                .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("WRAPPED:\n    .quad 0"));
    }

    #[test]
    fn evaluates_referenced_global_constants_and_integer_operators() {
        let program = parse_program(
            "(#const Base u64 40) (#const Answer u64 (#u64.+.wrap  (#u64.*.wrap  Base 2) 2)) (#fn main () u64 (#return (#if (#u64.&&  (#u64.==  Answer 82) (#u64.>=  (#u64.<<  1 6) 64)) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("Answer:\n    .quad 82"));
    }

    #[test]
    fn evaluates_integer_casts_in_global_constants() {
        let program = parse_program(
            "(#const Wrapped u8 (#as (#u8.+.wrap 255 1) u8)) (#fn main () u64 (#return (#if (#u8.== Wrapped 0) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program)
            .unwrap()
            .contains("Wrapped:\n    .quad 0"));
    }

    #[test]
    fn evaluates_forward_global_constant_references() {
        let program = parse_program(
            "(#const Answer u64 (#u64.+.wrap  Base 2)) (#const Base u64 40) (#fn main () u64 (#return Answer))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program)
            .unwrap()
            .contains("Answer:\n    .quad 42"));
        let recursive = parse_program(
            "(#const First u64 (#u64.+.wrap  Second 1)) (#const Second u64 (#u64.+.wrap  First 1)) (#fn main () u64 (#return First))",
        )
        .unwrap();
        let error = generate_assembly(&recursive).unwrap_err();
        assert!(error.contains("recursive"), "{error}");
    }

    #[test]
    fn rejects_recursive_function_calls() {
        let direct = parse_program(
            "(#fn recurse () u64 (#return (#call recurse (:)))) (#fn main () u64 (#return (#call recurse (:))))",
        )
        .unwrap();
        let error = check_types(&direct).unwrap_err();
        assert!(error.contains("recursive calls"), "{error}");

        let indirect = parse_program(
            "(#fn first () u64 (#return (#call second (:)))) (#fn second () u64 (#return (#call first (:)))) (#fn main () u64 (#return (#call first (:))))",
        )
        .unwrap();
        let error = check_types(&indirect).unwrap_err();
        assert!(
            error.contains("first") && error.contains("second"),
            "{error}"
        );
    }

    #[test]
    fn lowers_wide_integer_globals() {
        let program = parse_program(
            "(#let VALUE u128 42) (#fn main () u64 (#return (#if (#u128.==  VALUE 42) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("VALUE:\n    .quad 42\n    .quad 0"));
        assert!(
            assembly.contains("mov rdx, QWORD PTR [rip+VALUE_x2b_8]")
                || assembly.contains("mov rdx, QWORD PTR [rip+VALUE+8]")
        );
    }

    #[test]
    fn lowers_high_unsigned_wide_global_literals() {
        let program = parse_program(
            "(#let VALUE u128 340282366920938463463374607431768211455) (#fn main () u64 (#return (#if (#u128.==  VALUE (#as -1 u128)) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly
            .contains("VALUE:\n    .quad 18446744073709551615\n    .quad 18446744073709551615"));
    }

    #[test]
    fn preserves_float_width_across_control_flow() {
        let program = parse_program(
            "(#fn choose ((flag bool)) f32 (#return (#if flag 1.5 2.5))) (#fn main () u64 (#return (#if (#f32.>  (#call choose (: flag true)) 1.0) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("movd xmm0, eax"));
        let matched = parse_program(
            "(#enum MaybeF ((SomeF f32) None)) (#fn read ((value MaybeF)) f32 (#return (#match value (#case (SomeF payload) payload) (#case None 2.5)))) (#fn main () u64 (#return (#if (#f32.>  (#call read (: value None)) 2.0) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&matched).is_ok());
        assert!(generate_assembly(&matched)
            .unwrap()
            .contains("movd xmm0, eax"));
    }

    #[test]
    fn handles_nan_float_comparisons() {
        let program =
            parse_program("(#fn main () u64 (#return (#if (#f64.!= (#f64./ 0.0 0.0) 0.0) 42 0)))")
                .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("jp .Lfloat_unordered"));
    }

    #[test]
    fn checks_shift_counts_against_integer_width() {
        let program = parse_program("(#fn main () u64 (#return (#u64.<<  21 1)))").unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("shift_failure"));
        let invalid = parse_program("(#fn main () u8 (#return (#u8.<<  (#as 1 u8) 8)))").unwrap();
        assert!(check_types(&invalid)
            .unwrap_err()
            .contains("shift count 8 is out of range"));
        let wide = parse_program(
            "(#fn main ((count u128)) u128 (#return (#u128.<<  (#as 1 u128) count)))",
        )
        .unwrap();
        assert!(generate_assembly(&wide)
            .unwrap()
            .contains("wide_shift_failure"));
    }

    #[test]
    fn accepts_high_bit_u128_literals() {
        let program = parse_program(
            "(#fn make () u128 (#return 0x8000000000000000000000000000002a)) (#fn main () u64 (#return (#as (#call make (:)) u64)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("mov rdx, 0x8000000000000000"));
    }

    #[test]
    fn lowers_unit_functions_and_calls() {
        let program = parse_program(
            "(#fn noop () () (#return ())) (#fn main () u64 (#call noop (:)) (#return 42))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains(".globl noop"));
        assert!(assembly.contains("call noop"));
    }

    #[test]
    fn checks_and_lowers_mutable_parameters() {
        let program =
            parse_program("(#fn increment ((#mut value u64)) u64 (#set value (#u64.+.wrap  value 1)) (#return value))")
                .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program)
            .unwrap()
            .contains("add rax, rcx"));
        let invalid =
            parse_program("(#fn increment ((value u64)) u64 (#set value 1) (#return value))")
                .unwrap();
        assert!(check_types(&invalid).unwrap_err().contains("immutable"));
    }

    #[test]
    fn checks_and_lowers_f64_arithmetic() {
        let program = parse_program(
            "(#fn calculate () f64 (#let left f64 1.5) (#let right f64 2.25) (#return (#f64.+  left right)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("addsd xmm1, xmm0"));
        assert!(assembly.contains("movq xmm0"));
        let remainder =
            parse_program("(#fn main () u64 (#return (#if (#f64.== (#f64.% 5.5 2.0) 1.5) 42 0)))")
                .unwrap();
        assert!(check_types(&remainder).is_ok());
        assert!(generate_assembly(&remainder).unwrap().contains("fprem"));
        let narrow_remainder = parse_program(
            "(#fn main () u64 (#let left f32 5.5) (#let right f32 2.0) (#return (#if (#f32.==  (#f32.%  left right) 1.5) 42 0)))",
        )
        .unwrap();
        assert!(generate_assembly(&narrow_remainder)
            .unwrap()
            .contains("fprem"));
        let parameter = parse_program("(#fn calculate ((value f64)) f64 (#return value))").unwrap();
        assert!(generate_assembly(&parameter)
            .unwrap()
            .contains("movq QWORD PTR [rbp-8], xmm0"));
        let called = parse_program(
            "(#fn add ((left f64) (right f64)) f64 (#return (#f64.+  left right))) (#fn main () f64 (#return (#call add (: left 1.5 : right 2.5))))",
        )
        .unwrap();
        assert!(generate_assembly(&called).unwrap().contains("call add"));
        let mixed = parse_program(
            "(#fn choose ((value u64) (scale f64)) u64 (#return (#if (#f64.>  scale 1.0) value 0))) (#fn main () u64 (#return (#call choose (: value 42 : scale 2.0))))",
        )
        .unwrap();
        assert!(check_types(&mixed).is_ok());
        assert!(generate_assembly(&mixed).unwrap().contains("movq xmm0"));
    }

    #[test]
    fn checks_and_lowers_f32_arithmetic_and_calls() {
        let program = parse_program(
            "(#fn add ((left f32) (right f32)) f32 (#return (#f32.+  left right))) (#fn main () u64 (#return (#if (#f32.>  (#call add (: left 1.5 : right 2.5)) 3.0) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("addss xmm1, xmm0"));
        assert!(assembly.contains("ucomiss xmm1, xmm0"));
        assert!(assembly.contains("movd xmm0"));
        let parameter_assembly = generate_assembly(
            &parse_program("(#fn read ((value f32)) f32 (#return value))").unwrap(),
        )
        .unwrap();
        assert!(parameter_assembly.contains("movd DWORD PTR [rbp-8], xmm0"));
        let overflow_f32 = parse_program("(#fn main () f32 (#return 1e100))").unwrap();
        assert!(check_types(&overflow_f32)
            .unwrap_err()
            .contains("not finite for F32"));
        let overflow_f64 = parse_program("(#fn main () f64 (#return 1e400))").unwrap();
        assert!(check_types(&overflow_f64)
            .unwrap_err()
            .contains("not finite for F64"));
    }

    #[test]
    fn checks_and_lowers_char_values() {
        let program =
            parse_program("(#fn main () u64 (#return (#if (#char.== #\\a #\\a) 42 0)))").unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("mov rax, 97"));
    }

    #[test]
    fn async_scope_span_lookup_ignores_same_spelled_non_value_symbols() {
        let source = "(#block local (#let local u64 1u64) (#get value local) (#call work (: local value)) (#struct-literal Holder ((local value))))";
        let parsed = parse(source).unwrap();
        let span = source_value_symbol_span(&parsed[0], "local").unwrap();
        assert_eq!(span.start, source.find("local").unwrap());
        assert_eq!(&source[span.start..span.end], "local");
    }

    #[test]
    fn async_environment_identity_includes_declared_function_results() {
        let environment = |result| {
            async_type_environment(
                &parse(&format!(
                    "(#fn helper ((value u64)) {result} (#return (#unreachable)))"
                ))
                .unwrap(),
            )
        };
        let scalar = environment("u64");
        let boolean = environment("bool");
        assert_eq!(scalar.functions, boolean.functions);
        assert_ne!(
            async_type_environment_identity(&scalar),
            async_type_environment_identity(&boolean)
        );
        assert_eq!(
            async_type_environment_identity(&scalar),
            async_type_environment_identity(&environment("u64"))
        );
    }

    #[test]
    fn async_environment_identity_preserves_struct_pattern_field_order() {
        let environment = |fields| {
            async_type_environment(&parse(&format!("(#struct Values ({fields}))")).unwrap())
        };
        let first = environment("(z u16) (a u64)");
        let swapped = environment("(a u64) (z u16)");
        assert_eq!(first.struct_fields, swapped.struct_fields);
        assert_eq!(first.struct_field_order["Values"], ["z", "a"]);
        assert_ne!(
            async_type_environment_identity(&first),
            async_type_environment_identity(&swapped)
        );
        assert_eq!(
            async_type_environment_identity(&first),
            async_type_environment_identity(&environment("(z u16) (a u64)"))
        );
    }

    #[test]
    fn async_environment_identity_preserves_parameter_evaluation_order() {
        let environment = |parameters| {
            async_type_environment(
                &parse(&format!(
                    "(#fn helper ({parameters}) u64 (#return (#unreachable)))"
                ))
                .unwrap(),
            )
        };
        let first = environment("(first u64) (second u64)");
        let swapped = environment("(second u64) (first u64)");
        assert_eq!(first.functions, swapped.functions);
        assert_eq!(
            first.function_parameter_order["helper"],
            ["first", "second"]
        );
        assert_ne!(
            async_type_environment_identity(&first),
            async_type_environment_identity(&swapped)
        );
        assert_eq!(
            async_type_environment_identity(&first),
            async_type_environment_identity(&environment("(first u64) (second u64)"))
        );
        let foreign = async_type_environment(
            &parse("(#extern-fn #abi-c foreign ((second u64) (first u64)) u64)").unwrap(),
        );
        assert_eq!(
            foreign.function_parameter_order["foreign"],
            ["second", "first"]
        );
    }

    #[test]
    fn async_metadata_is_only_built_for_selected_async_users() {
        let declarations =
            "(#struct Value ((number u64))) (#fn ordinary ((value u64)) u64 (#return value))";
        let prepare = |source: &str| {
            prepare_program_syntax(
                source,
                Path::new("."),
                None,
                &CompileConfig::default(),
                None,
            )
            .unwrap()
        };
        let ordinary = prepare(declarations);
        assert!(ordinary.async_copy_types.is_empty());
        assert_eq!(
            ordinary.async_types,
            async_fn::AsyncTypeEnvironment::default()
        );

        for generator in ["async-fn", "async-fn-pinned"] {
            let source = format!(
                "{declarations} (@{generator} (: names (Frame Poll Pending Ready poll) : waker u64 : function (#fn work () u64 (#return 1u64))))"
            );
            let asynchronous = prepare(&source);
            assert_eq!(
                asynchronous.async_types.functions["ordinary"]["value"],
                "u64"
            );
            assert_eq!(asynchronous.async_types.function_results["ordinary"], "u64");
            assert_eq!(
                asynchronous.async_types.struct_fields["Value"]["number"],
                "u64"
            );
        }
    }

    #[test]
    fn expands_optional_generated_declarations() {
        let program = parse_program(
            "(@optional (: type u64 : name Maybe?)) (#fn main () u64 (#let value Maybe? (#call Maybe?-construct (: value 42))) (#return (#if (#call Maybe?-is-some (: value (#clone value))) (#call Maybe?-unwrap-or (: value value : fallback 0)) 0)))",
        )
        .unwrap();
        assert!(program.items.iter().any(|item| {
            matches!(item, Item::Function(function) if function.name == "Maybe?-construct")
        }));
        assert!(program.items.iter().any(|item| {
            matches!(item, Item::Function(function) if function.name == "Maybe?-is-some")
        }));
        assert!(program.items.iter().any(|item| {
            matches!(item, Item::Function(function) if function.name == "Maybe?-unwrap-or")
        }));
        let type_result = check_types(&program);
        assert!(type_result.is_ok(), "{type_result:?}");
        assert!(generate_assembly(&program)
            .unwrap()
            .contains(".globl Maybe_x3f__x2d_construct"));
    }

    #[test]
    fn builtin_generators_require_complete_named_arguments() {
        let cases = [
            (
                "(@optional (: name Maybe : type u64))",
                "(@ optional u64 Maybe)",
            ),
            (
                "(@result (: name Outcome : error u32 : ok u64))",
                "(@ result u64 u32 Outcome)",
            ),
            (
                "(@thread-spawn (: worker work : task Task))",
                "(@ thread-spawn Task work)",
            ),
            (
                "(@vec (: name VecU64 : allocator Arena : element u64))",
                "(@ vec u64 Arena VecU64)",
            ),
            (
                "(@vec-sort (: comparator less : vector VecU64 : element u64))",
                "(@ vec-sort u64 VecU64 less)",
            ),
            (
                "(@vec-alloc (: destroy drop-item : dealloc release : grow grow : alloc allocate : alloc-error AllocError : alloc-result AllocResult : vector VecU64 : allocator Arena : element u64))",
                "(@ vec-alloc u64 Arena VecU64 AllocResult AllocError allocate grow release drop-item)",
            ),
            (
                "(@async-fn (: function (#fn work () u64 (#return 1)) : waker Wake : names (Frame Poll Pending Ready poll)))",
                "(@ async-fn (Frame Poll Pending Ready poll) Wake (#fn work () u64 (#return 1)))",
            ),
        ];
        for (source, expected) in cases {
            let form = &parse(source).unwrap()[0].expr;
            let normalized = normalize_builtin_generator_invocation(form).unwrap();
            assert_eq!(expression_source(&normalized).unwrap(), expected);
        }
        let reordered = parse_program(
            "(@optional (: name Maybe : type u64))
             (#fn work () u64 (#return 1u64))
             (@thread-spawn (: worker work : task Work))",
        )
        .unwrap();
        assert!(reordered
            .items
            .iter()
            .any(|item| matches!(item, Item::Enum { name, .. } if name == "Maybe")));
        assert!(reordered
            .items
            .iter()
            .any(|item| matches!(item, Item::ThreadTask { name, .. } if name == "Work")));
        for (source, message) in [
            ("(@optional u64 Maybe)", "requires a named argument list"),
            ("(@optional (: type u64))", "missing argument 'name'"),
            (
                "(@optional (: type u64 : name Maybe : name Other))",
                "repeats argument 'name'",
            ),
            (
                "(@optional (: type u64 : renamed Maybe))",
                "has no argument 'renamed'",
            ),
        ] {
            let error = parse_program(source).unwrap_err();
            assert!(error.contains(message), "{source}: {error}");
        }
    }

    #[test]
    fn dependency_digest_is_compact_and_tracks_syntax_spans_and_cfg() {
        let source = "(#fn main () u64 (#return 42u64))";
        let expressions = parse(source).unwrap();
        let config = CompileConfig::default();
        let key = generator_dependency_context(&expressions, &config);
        assert!(key.len() < 512);
        assert_eq!(
            key,
            generator_dependency_context(&parse(source).unwrap(), &config)
        );
        assert_ne!(
            key,
            generator_dependency_context(&parse(&format!("\n{source}")).unwrap(), &config)
        );
        assert_ne!(
            key,
            generator_dependency_context(&parse(&source.replace("42", "43")).unwrap(), &config)
        );
        let mut changed = config.clone();
        changed.set("feature", "enabled");
        assert_ne!(key, generator_dependency_context(&expressions, &changed));
    }

    #[test]
    fn async_capture_cache_encoding_is_deterministic_and_rejects_malformed_plans() {
        let forms = parse("((0 1 2) ((1 ()) (0 (y x))))")
            .unwrap()
            .into_iter()
            .map(|form| form.expr)
            .collect::<Vec<_>>();
        let plans = decode_async_capture_plans(&forms).unwrap();
        let encoded = encode_async_capture_plans(&plans);
        assert_eq!(decode_async_capture_plans(&encoded), Some(plans));
        assert_eq!(
            expression_source(&encoded[0]).unwrap(),
            "((0 1 2) ((0 (x y)) (1 ())))"
        );
        for source in [
            "((0 1 2) ((0 (x x))))",
            "((0 1 2) ((0 ()) (0 ())))",
            "((0 2 1) ())",
            "((-1 1 2) ())",
            "((0 1 2) ((-1 ())))",
            "((0 1 2) ((0 (42))))",
            "((0 1 2) ()) ((0 1 2) ())",
            "malformed",
            "",
        ] {
            let forms = parse(source)
                .unwrap()
                .into_iter()
                .map(|form| form.expr)
                .collect::<Vec<_>>();
            assert!(decode_async_capture_plans(&forms).is_none(), "{source}");
        }
    }

    #[test]
    fn async_compilation_expands_generators_once_across_all_frontend_stages() {
        let directory =
            std::env::temp_dir().join(format!("lim-shared-frontend-{}", std::process::id()));
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/async_fn.lim");
        let source = fs::read_to_string(&path).unwrap();
        let cache = directory.join("cache");
        let config = CompileConfig::default();
        let compile = || {
            compile_source_with_generated_sources(
                &source,
                &path,
                &config,
                &cache,
                TargetDescription::X86_64_SYSTEM_V,
                None,
                &directory,
            )
            .unwrap()
        };
        typecheck::SEMANTIC_PASSES.with(|passes| passes.set(0));
        let (cold, cold_report) = with_cache_report(compile);
        typecheck::SEMANTIC_PASSES.with(|passes| assert_eq!(passes.get(), 2));
        typecheck::SEMANTIC_PASSES.with(|passes| passes.set(0));
        let (warm, warm_report) = with_cache_report(compile);
        typecheck::SEMANTIC_PASSES.with(|passes| assert_eq!(passes.get(), 1));
        assert_eq!(cold, warm);
        // The example invokes three user generators. Probe parsing, final
        // parsing and artifact writing must share those three expansions.
        assert_eq!(cold_report.matches("\"kind\":\"syntax\"").count(), 3);
        assert_eq!(warm_report.matches("\"kind\":\"syntax\"").count(), 3);
        assert!(!warm_report.contains("\"missing-entry\""));
        assert!(warm_report.contains("\"kind\":\"async-captures\""));
        let prepared = prepare_program_syntax(
            &source,
            path.parent().unwrap(),
            Some(&path),
            &config,
            Some(&cache),
        )
        .unwrap();
        let key = format!(
            "lim-async-captures-v1\nimplementation={}\n{}",
            env!("LIM_BUILD_FINGERPRINT"),
            prepared.dependency_context
        );
        let capture_path = generator::cache_path(&cache, &key);
        fs::write(&capture_path, b"damaged cache").unwrap();
        typecheck::SEMANTIC_PASSES.with(|passes| passes.set(0));
        assert_eq!(compile(), cold);
        typecheck::SEMANTIC_PASSES.with(|passes| assert_eq!(passes.get(), 2));
        // Even a checksummed but structurally invalid entry must be ignored.
        generator::write_cached_expansion(&cache, &key, &[Expr::Symbol("invalid".into())]);
        typecheck::SEMANTIC_PASSES.with(|passes| passes.set(0));
        assert_eq!(compile(), cold);
        typecheck::SEMANTIC_PASSES.with(|passes| assert_eq!(passes.get(), 2));
        let changed_config = {
            let mut config = config.clone();
            config.set("feature", "changed");
            config
        };
        typecheck::SEMANTIC_PASSES.with(|passes| passes.set(0));
        compile_source_with_generated_sources(
            &source,
            &path,
            &changed_config,
            &cache,
            TargetDescription::X86_64_SYSTEM_V,
            None,
            &directory,
        )
        .unwrap();
        typecheck::SEMANTIC_PASSES.with(|passes| assert_eq!(passes.get(), 2));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn combined_compilation_materializes_inspectable_source() {
        let directory =
            std::env::temp_dir().join(format!("lim-combined-compile-{}", std::process::id()));
        let cache = directory.join("cache");
        let path = directory.join("input.lim");
        let source = "(@optional (: type u64 : name Maybe)) (#fn main () u64 (#return 42u64))";
        let config = CompileConfig::default();
        let expected = compile_source_to_assembly(
            source,
            &path,
            &config,
            &cache,
            TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
        let actual = compile_source_with_generated_sources(
            source,
            &path,
            &config,
            &cache,
            TargetDescription::X86_64_SYSTEM_V,
            None,
            &directory,
        )
        .unwrap();
        assert_eq!(actual, expected);
        let (_, generated) = read_cached_generated_source(&directory, "Maybe-construct");
        assert!(generated.contains("Maybe-construct"));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn materializes_strict_optional_source_with_explicit_returns() {
        let directory =
            std::env::temp_dir().join(format!("lim-generated-optional-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        write_generated_sources("(@optional (: type u64 : name Maybe?))", &directory).unwrap();
        let (_, generated) = read_cached_generated_source(&directory, "Maybe?-construct");
        assert!(generated.contains("#enum"));
        assert!(generated.contains("#return"));
        assert!(generated.contains("(#case "));
        let program = parse_program(&generated).unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn materializes_result_generated_source() {
        let directory =
            std::env::temp_dir().join(format!("lim-generated-result-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        write_generated_sources("(@result (: ok u64 : error u32 : name Result))", &directory)
            .unwrap();
        let (_, generated) = read_cached_generated_source(&directory, "Result-ok-value");
        assert!(generated.contains("Result-ok-value"));
        assert!(generated.contains("Result-unwrap-or"));
        assert!(generated.contains("Result-unwrap-err-or"));
        assert!(generated.contains("(#case "));
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn materializes_user_generators_in_the_shared_hashed_cache() {
        let directory =
            std::env::temp_dir().join(format!("lim-generated-user-cache-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        let source = "(#gn emit (name) (#gn-list (#gn-list (#gn-symbol \"#type\") name u64))) (@emit CachedType)";
        write_generated_sources(source, &directory).unwrap();
        let (path, generated) = read_cached_generated_source(&directory, "CachedType");
        assert!(path
            .file_name()
            .unwrap()
            .to_string_lossy()
            .starts_with("generated-"));
        assert!(generated.contains("(#type CachedType u64)"));
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn materializes_thread_spawn_as_a_prefixed_builtin_declaration() {
        let directory =
            std::env::temp_dir().join(format!("lim-generated-thread-spawn-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        let source = "(#fn worker ((value u64)) u64 (#return value)) (@thread-spawn (: task Task : worker worker))";
        write_generated_sources(source, &directory).unwrap();
        let (path, generated) =
            read_cached_generated_source(&directory, "#thread-task Task worker");
        assert!(path
            .file_name()
            .unwrap()
            .to_string_lossy()
            .starts_with("generated-"));
        assert!(!directory.join("thread-spawn-0.lim").exists());
        assert!(generated.contains("(#thread-task Task worker"));
        assert!(
            generated.contains("(#thread-task-spawn Task-spawn ((value u64)) Task-spawn-result)")
        );
        assert!(generated.contains("(#thread-task-join Task-join ((task Task)) Task-join-result)"));
        assert!(generated.contains("Task-spawn-ok"));
        assert!(generated.contains("Task-spawn-error"));
        assert!(generated.contains("Task-join-ok"));
        assert!(generated.contains("Task-join-error"));

        let lowered = parse_program(&format!(
            "(#fn worker ((value u64)) u64 (#return value)) {generated}"
        ))
        .unwrap();
        let original = parse_program(source).unwrap();
        let generated_names = |program: &Program| {
            program
                .items
                .iter()
                .filter_map(|item| match item {
                    Item::Enum { name, .. } if name.starts_with("Task-") => Some(name.clone()),
                    _ => None,
                })
                .collect::<HashSet<_>>()
        };
        assert_eq!(generated_names(&original), generated_names(&lowered));
        assert_eq!(generated_names(&original).len(), 3);
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn expands_allocator_backed_vec_with_explicit_allocator_borrow() {
        let program = parse_program(
            "(#struct Arena ((cursor u64))) (@vec (: element u64 : allocator Arena : name VecU64)) (#fn main () usize (#let-mut arena Arena (#struct-literal Arena ((cursor 0)))) (#let-mut value u64 0) (#let vector VecU64 (#call VecU64-new-with-storage (: allocator (#borrow arena) : pointer (#unsafe (#addr-of-mut value)) : capacity 4))) (#return (#call VecU64-capacity (: vector (#borrow vector)))))",
        )
        .unwrap();
        assert!(program
            .items
            .iter()
            .any(|item| { matches!(item, Item::Struct { name, .. } if name == "VecU64") }));
        let type_result = check_types(&program);
        assert!(type_result.is_ok(), "{type_result:?}");
        let assembly = generate_assembly(&program);
        assert!(assembly.is_ok(), "{assembly:?}");
    }

    #[test]
    fn dereferences_and_writes_small_aggregate_references() {
        let read = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn main () u64 (#let-mut point Point (#struct-literal Point ((x 40) (y 2)))) (#let point-ref (#ref Point) (#borrow point)) (#let copy Point (#deref point-ref)) (#return (#u64.+.wrap (#get copy x) (#get copy y))))",
        )
        .unwrap();
        assert!(check_types(&read).is_ok());
        assert!(generate_assembly(&read).is_ok());

        let write = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn main () Point (#let-mut point Point (#struct-literal Point ((x 1) (y 2)))) (#let point-ref (#ref-mut Point) (#borrow-mut point)) (#deref-set point-ref (#struct-literal Point ((x 40) (y 2)))) (#return (#deref point-ref)))",
        )
        .unwrap();
        let write_types = check_types(&write);
        assert!(write_types.is_ok(), "{write_types:?}");
        assert!(generate_assembly(&write).is_ok());
    }

    #[test]
    fn copies_large_aggregate_dereferences_through_indirect_storage() {
        let program = parse_program(
            "(#struct Large ((a u64) (b u64) (c u64) (d u64) (e u64) (f u64) (g u64))) (#fn take-large ((value (#ref Large))) Large (#return (#deref value))) (#fn main () u64 (#let large Large (#struct-literal Large ((a 1) (b 2) (c 3) (d 4) (e 5) (f 6) (g 7)))) (#let copy Large (#call take-large (: value (#borrow large)))) (#return (#get copy g)))",
        )
        .unwrap();
        let type_result = check_types(&program);
        assert!(type_result.is_ok(), "{type_result:?}");
        let assembly = generate_assembly(&program);
        assert!(assembly.is_ok(), "{assembly:?}");
    }

    #[test]
    fn projects_large_fields_through_references_into_indirect_storage() {
        let program = parse_program(
            "(#struct Large ((a u64) (b u64) (c u64) (d u64) (e u64) (f u64) (g u64))) (#struct Outer ((large Large) (tail u64))) (#fn project ((outer (#ref Outer))) Large (#return (#get outer large))) (#fn main () u64 (#let outer Outer (#struct-literal Outer ((large (#struct-literal Large ((a 1) (b 2) (c 3) (d 4) (e 5) (f 6) (g 7)))) (tail 8)))) (#let result Large (#call project (: outer (#borrow outer)))) (#return (#get result g)))",
        )
        .unwrap();
        let type_result = check_types(&program);
        assert!(type_result.is_ok(), "{type_result:?}");
        let assembly = generate_assembly(&program);
        assert!(assembly.is_ok(), "{assembly:?}");
    }

    #[test]
    fn dropping_reference_aggregate_releases_each_field_loan() {
        let program = parse_program(
            "(#struct View ((left (#ref-mut u64)) (right (#ref-mut u64)))) (#fn main () u64 (#let-mut left u64 1) (#let-mut right u64 2) (#let view View (#struct-literal View ((left (#borrow-mut left)) (right (#borrow-mut right))))) (#drop view) (#set left 10) (#set right 20) (#return (#u64.+.wrap left right)))",
        )
        .unwrap();
        let type_result = check_types(&program);
        assert!(type_result.is_ok(), "{type_result:?}");
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn vec_sort_expansion_calls_and_typechecks_its_literal_comparator() {
        let valid = parse_program(
            "(#struct Arena ((cursor u64))) (@vec (: element u64 : allocator Arena : name VecU64)) (@vec-sort (: element u64 : vector VecU64 : comparator compare-u64)) (#fn compare-u64 ((left (#ref u64)) (right (#ref u64))) bool (#return (#u64.< (#deref left) (#deref right)))) (#fn main () u64 (#return 0u64))",
        )
        .unwrap();
        let checked = check_types(&valid);
        assert!(checked.is_ok(), "{checked:?}");
        assert!(generate_assembly(&valid).is_ok());

        let invalid = parse_program(
            "(#struct Arena ((cursor u64))) (@vec (: element u64 : allocator Arena : name VecU64)) (@vec-sort (: element u64 : vector VecU64 : comparator compare-u64)) (#fn compare-u64 ((left u64) (right u64)) bool (#return (#u64.< left right))) (#fn main () u64 (#return 0u64))",
        )
        .unwrap();
        let error = check_types(&invalid).unwrap_err();
        assert!(
            error.contains("expected") || error.contains("type"),
            "{error}"
        );
    }

    #[test]
    fn materializes_vec_generated_source() {
        let directory =
            std::env::temp_dir().join(format!("lim-generated-vec-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        write_generated_sources(
            "(@vec (: element u64 : allocator Arena : name VecU64))",
            &directory,
        )
        .unwrap();
        let (_, generated) = read_cached_generated_source(&directory, "VecU64-new-with-storage");
        assert!(generated.contains("(#struct VecU64"));
        assert!(generated.contains("VecU64-new-with-storage"));
        assert!(generated.contains("(#ref Arena)"));
        write_generated_sources(
            "(@vec-sort (: element u64 : vector VecU64 : comparator compare-u64))",
            &directory,
        )
        .unwrap();
        let (_, sort) = read_cached_generated_source(&directory, "VecU64-sort");
        assert!(sort.contains("VecU64-sort"));
        assert!(sort.contains("(#call compare-u64"));
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn expands_allocator_owned_vec_declarations() {
        let program = parse_program(
            r#"
(#struct Arena ((cursor u64)))
(#enum AllocError (OutOfMemory))
(@result (: ok (#ptr-mut u64) : error AllocError : name AllocResult))
(@vec (: element u64 : allocator Arena : name VecU64))
(@vec-alloc (: element u64 : allocator Arena : vector VecU64 : alloc-result AllocResult : alloc-error AllocError : alloc arena-alloc : grow arena-grow : dealloc arena-dealloc : destroy drop-u64))
(#fn arena-alloc ((allocator (#ref Arena)) (layout usize) (alignment usize)) AllocResult
  (#return (#call AllocResult-err (: error OutOfMemory))))
(#fn arena-grow
  ((allocator (#ref Arena)) (pointer (#ptr-mut u64)) (old-layout usize)
   (new-layout usize) (alignment usize))
  AllocResult
  (#forget pointer)
  (#return (#call AllocResult-err (: error OutOfMemory))))
(#fn arena-dealloc
  ((allocator (#ref Arena)) (pointer (#ptr-mut u64)) (layout usize)
   (alignment usize))
  ()
  (#forget pointer)
  (#return ()))
(#fn drop-u64 ((allocator (#ref Arena)) (value u64)) () (#return ()))
(#fn main () usize
  (#let-mut arena Arena (#struct-literal Arena ((cursor 0u64))))
  (#let-mut vector VecU64 (#call VecU64-new (: allocator (#borrow arena))))
  (#let reserve-result VecU64-ReserveResult
    (#call VecU64-reserve (: vector (#borrow-mut vector) : requested 4usize)))
  (#forget reserve-result)
  (#let push-result VecU64-PushResult
    (#call VecU64-push (: vector (#borrow-mut vector) : element 42u64)))
  (#forget push-result)
  (#let get-result VecU64-GetResult (#call VecU64-get (: vector (#borrow vector) : index 0usize)))
  (#forget get-result)
  (#let get-mut-result VecU64-GetMutResult
    (#call VecU64-get-mut (: vector (#borrow-mut vector) : index 0usize)))
  (#forget get-mut-result)
  (#let set-result VecU64-SetResult
    (#call VecU64-set (: vector (#borrow-mut vector) : index 0usize : value 7u64)))
  (#forget set-result)
  (#let pop-result VecU64-PopResult (#call VecU64-pop (: vector (#borrow-mut vector))))
  (#forget pop-result)
  (#call VecU64-free (: vector vector))
  (#return 0usize))
"#,
        )
        .unwrap();
        let checked = check_types(&program);
        assert!(checked.is_ok(), "{checked:?}");
        let assembly = generate_assembly(&program);
        assert!(assembly.is_ok(), "{assembly:?}");
    }

    #[test]
    fn parses_vec_allocator_example() {
        let source = include_str!("../examples/vec_allocator.lim");
        let path = std::path::Path::new("examples/vec_allocator.lim");
        let program = parse_program_from_path(source, path);
        let program = program.unwrap();
        let checked = check_types(&program);
        assert!(checked.is_ok(), "{checked:?}");
        let assembly = generate_assembly(&program);
        assert!(assembly.is_ok(), "{assembly:?}");
        let config = CompileConfig::default();
        let cache = std::env::temp_dir().join(format!("lim-vec-cache-{}", std::process::id()));
        let generated_dir =
            std::env::temp_dir().join(format!("lim-vec-source-{}", std::process::id()));
        write_generated_sources_from_path_with_config_and_cache(
            source,
            path,
            &generated_dir,
            &config,
            &cache,
        )
        .unwrap();
        let from_path =
            parse_program_from_path_with_config_and_cache(source, path, &config, &cache).unwrap();
        assert!(generate_assembly(&from_path).is_ok());
        let _ = std::fs::remove_dir_all(generated_dir);
        let _ = std::fs::remove_dir_all(cache);
    }

    #[test]
    fn rejects_allocator_backed_vector_outliving_its_allocator() {
        let program = parse_program(
            "(#struct Arena ((cursor u64))) (@vec (: element u64 : allocator Arena : name VecU64)) (#fn escape () VecU64 (#let arena Arena (#struct-literal Arena ((cursor 0u64)))) (#return (#call VecU64-new-with-storage (: allocator (#borrow arena) : pointer (#ptr-null (#ptr-mut u64)) : capacity 0usize))))",
        )
        .unwrap();
        let error = check_types(&program).unwrap_err();
        assert!(error.contains("local"), "{error}");
    }

    #[test]
    fn lowers_if_let_to_native_match() {
        let program = parse_program(
            "(@optional (: type u64 : name Maybe?)) (#fn main () u64 (#let value Maybe? (#call Maybe?-construct (: value 42))) (#return (#if-let (Maybe?-some payload) value payload 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn expands_result_generated_declarations() {
        let program = parse_program(
            "(@result (: ok u64 : error u32 : name Result)) (#fn classify ((value Result)) u64 (#return (#match value (#case (Result-ok-value 42) 1) (#case (Result-err-value _) 0)))) (#fn main () u64 (#let value Result (#call Result-ok (: value 42))) (#return (#call classify (: value value))))",
        )
        .unwrap();
        let type_result = check_types(&program);
        assert!(type_result.is_ok(), "{type_result:?}");
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn lowers_while_let_with_match_guard() {
        let program = parse_program(
            "(@optional (: type u64 : name Maybe?)) (#fn main () u64 (#let-mut value Maybe? (#call Maybe?-construct (: value 42))) (#let-mut total u64 0) (#while-let (Maybe?-some payload) value (#set total (#u64.+.wrap  total payload)) (#set value Maybe?-none)) (#return total))",
        )
        .unwrap();
        let type_result = check_types(&program);
        assert!(type_result.is_ok(), "{type_result:?}");
        let assembly_result = generate_assembly(&program);
        assert!(assembly_result.is_ok(), "{assembly_result:?}");
    }

    #[test]
    fn lowers_aggregate_if_let_and_while_let() {
        let program = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn point_value () u64 (#let point Point (#struct-literal Point ((x 40) (y 2)))) (#return (#if-let (Point 40 y) point y 0))) (#fn main () u64 (#let-mut value (#tuple u64 u64) (#tuple (#tuple u64 u64) 1 2)) (#let-mut total u64 0) (#while-let (#tuple 1 _) value (#set total (#u64.+.wrap total (#get value 1))) (#set-field value 0 0)) (#return (#u64.+.wrap total (#call point_value (:)))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn lowers_typed_tuple_and_struct_let_destructuring() {
        let program = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn sum_tuple ((value (#tuple u64 u64))) u64 (#let (#tuple first second) (#tuple u64 u64) value) (#return (#u64.+.wrap first second))) (#fn sum_point ((value Point)) u64 (#let (Point x y) Point value) (#return (#u64.+.wrap x y))) (#fn main () u64 (#return (#u64.+.wrap (#call sum_tuple (: value (#tuple (#tuple u64 u64) 20 10))) (#call sum_point (: value (#struct-literal Point ((x 7) (y 5))))))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn lowers_mutable_aggregate_let_destructuring() {
        let program = parse_program(
            "(#fn main () u64 (#let-mut (#tuple first second) (#tuple u64 u64) (#tuple (#tuple u64 u64) 20 22)) (#set first 40) (#return (#u64.+.wrap first second)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn lowers_array_let_destructuring() {
        let program = parse_program(
            "(#fn main () u64 (#let (#array first second third) (#array u64 3) (#array (#array u64 3) 10 20 12)) (#return (#u64.+.wrap first (#u64.+.wrap second third))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn lowers_array_match_patterns() {
        let program = parse_program(
            "(#fn classify ((value (#array u64 3))) u64 (#return (#match value (#case (#array 10 middle _) middle) (#case _ 0)))) (#fn main () u64 (#return (#call classify (: value (#array (#array u64 3) 10 32 12)))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn matches_empty_arrays() {
        let program = parse_program(
            "(#fn main () u64 (#return (#match (#array (#array u64 0)) (#case (#array) 42) (#case _ 0))))",
        )
        .unwrap();
        let type_result = check_types(&program);
        assert!(type_result.is_ok(), "{type_result:?}");
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn matches_direct_array_values() {
        let program = parse_program(
            "(#fn main () u64 (#return (#match (#array (#array u64 3) 10 32 12) (#case (#array 10 middle _) middle) (#case _ 0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn matches_direct_struct_values() {
        let program = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn main () u64 (#return (#match (#struct-literal Point ((x 10) (y 32))) (#case (Point 10 middle) middle) (#case _ 0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn matches_direct_tuple_values() {
        let program = parse_program(
            "(#fn main () u64 (#return (#match (#tuple (#tuple u64 u64) 10 32) (#case (#tuple 10 middle) middle) (#case _ 0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn returns_nested_direct_tuple_values() {
        let program = parse_program(
            "(#fn make () (#tuple (#tuple u64 u64) u64) (#return (#tuple (#tuple (#tuple u64 u64) 10 20) 32))) (#fn main () u64 (#return (#get (#call make (:)) 1)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn stores_and_reads_nested_tuple_locals() {
        let program = parse_program(
            "(#fn main () u64 (#let value (#tuple (#tuple u64 u64) u64) (#tuple (#tuple (#tuple u64 u64) 10 20) 32)) (#return (#get value 1)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn stores_and_indexes_nested_array_locals() {
        let program = parse_program(
            "(#fn main () u64 (#let value (#array (#array u64 2) 2) (#array (#array (#array u64 2) 2) (#array (#array u64 2) 10 20) (#array (#array u64 2) 30 40))) (#return (#index (#index value 1) 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn stores_and_reads_nested_struct_locals() {
        let program = parse_program(
            "(#struct Inner ((left u64) (right u64))) (#struct Outer ((inner Inner) (tail u64))) (#fn main () u64 (#let value Outer (#struct-literal Outer ((inner (#struct-literal Inner ((left 10) (right 20)))) (tail 32)))) (#return (#get value tail)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn destructures_nested_struct_locals() {
        let program = parse_program(
            "(#struct Inner ((left u64) (right u64))) (#struct Outer ((inner Inner) (tail u64))) (#fn main () u64 (#let (Outer inner tail) Outer (#struct-literal Outer ((inner (#struct-literal Inner ((left 10) (right 20)))) (tail 32)))) (#return tail))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn matches_nested_direct_tuple_values() {
        let program = parse_program(
            "(#fn main () u64 (#return (#match (#tuple (#tuple (#tuple u64 u64) u64) (#tuple (#tuple u64 u64) 10 20) 32) (#case _ 32))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn matches_nested_tuple_patterns_and_binds_flattened_values() {
        let program = parse_program(
            "(#fn main () u64 (#return (#match (#tuple (#tuple (#tuple u64 u64) u64) (#tuple (#tuple u64 u64) 10 20) 32) (#case (#tuple (#tuple _ inner) tail) (#u64.+.wrap inner tail)) (#case _ 0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn passes_nested_tuple_parameters_through_native_calls() {
        let program = parse_program(
            "(#fn add-inner-and-tail ((value (#tuple (#tuple u64 u64) u64))) u64 (#return (#u64.+.wrap (#u64.+.wrap (#get (#get value 0) 1) (#get value 1)) (#get (#get value 0) 0)))) (#fn main () u64 (#return (#call add-inner-and-tail (: value (#tuple (#tuple (#tuple u64 u64) u64) (#tuple (#tuple u64 u64) 10 20) 32)))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn returns_nested_array_locals_through_native_calls() {
        let program = parse_program(
            "(#fn nested-values () (#array (#array u64 2) 2) (#let value (#array (#array u64 2) 2) (#array (#array (#array u64 2) 2) (#array (#array u64 2) 10 20) (#array (#array u64 2) 30 40))) (#return value)) (#fn main () u64 (#return (#index (#index (#call nested-values (:)) 1) 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn mutates_nested_array_elements() {
        let program = parse_program(
            "(#fn main () u64 (#let-mut values (#array (#array u64 2) 2) (#array (#array (#array u64 2) 2) (#array (#array u64 2) 10 20) (#array (#array u64 2) 30 40))) (#set-index values 1 (#array (#array u64 2) 50 60)) (#return (#index (#index values 1) 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn mutates_nested_tuple_fields() {
        let program = parse_program(
            "(#fn main () u64 (#let-mut value (#tuple (#tuple u64 u64) u64) (#tuple (#tuple (#tuple u64 u64) u64) (#tuple (#tuple u64 u64) 10 20) 30)) (#set-field value 0 (#tuple (#tuple u64 u64) 50 60)) (#return (#get (#get value 0) 1)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn mutates_nested_struct_fields() {
        let program = parse_program(
            "(#struct Inner ((left u64) (right u64))) (#struct Outer ((inner Inner) (tail u64))) (#fn main () u64 (#let-mut value Outer (#struct-literal Outer ((inner (#struct-literal Inner ((left 10) (right 20)))) (tail 30)))) (#set-field value inner (#struct-literal Inner ((left 50) (right 60)))) (#return (#get (#get value inner) right)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn reads_nested_static_arrays() {
        let program = parse_program(
            "(#static Values (#array (#array u64 2) 2) (#array (#array (#array u64 2) 2) (#array (#array u64 2) 10 20) (#array (#array u64 2) 30 40))) (#fn main () u64 (#return (#unsafe (#index (#index Values 1) 0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn matches_nested_enum_payloads() {
        let program = parse_program(
            "(#enum Boxed ((Wrapped (#tuple u64 u64)) Empty)) (#fn sum ((value Boxed)) u64 (#return (#match value (#case (Wrapped (#tuple left right)) (#u64.+.wrap left right)) (#case Empty 0)))) (#fn main () u64 (#return (#call sum (: value (Wrapped (#tuple (#tuple u64 u64) 10 22))))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn reads_nested_enum_statics() {
        let program = parse_program(
            "(#enum Boxed ((Wrapped (#tuple u64 u64)) Empty)) (#static Value Boxed (Wrapped (#tuple (#tuple u64 u64) 10 22))) (#fn main () u64 (#return (#match (#unsafe Value) (#case (Wrapped (#tuple left right)) (#u64.+.wrap left right)) (#case Empty 0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn destructures_nested_aggregate_patterns() {
        let program = parse_program(
            "(#struct Inner ((left u64) (right u64))) (#struct Outer ((inner Inner) (tail u64))) (#fn main () u64 (#let (Outer (Inner left right) tail) Outer (#struct-literal Outer ((inner (#struct-literal Inner ((left 10) (right 20)))) (tail 30)))) (#return (#u64.+.wrap right tail)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn mutates_enum_payload_fields() {
        let program = parse_program(
            "(#enum Pair ((Pair u64 u64) Empty)) (#fn main () u64 (#let-mut value Pair (Pair 20 22)) (#set-payload value Pair 1 30) (#return (#match value (#case (Pair left right) (#u64.+.wrap left right)) (#case Empty 0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn checks_and_lowers_match_guards() {
        let program = parse_program(
            "(#enum Maybe ((Some u64) None)) (#fn main () u64 (#let value Maybe (Some 42)) (#return (#match value (#case (Some payload) (#when (#u64.>.wrap payload 40)) (#u64.+.wrap payload 8)) (#case (Some _) 0) (#case None 0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn checks_and_lowers_value_loops() {
        let program = parse_program("(#fn main () u64 (#return (#loop (#break 42))))").unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn lowers_value_loops_with_conditional_breaks() {
        let program = parse_program(
            "(#fn main () u64 (#let-mut i u64 0) (#return (#loop (#set i (#u64.+.wrap (#clone i) 1)) (#if (#u64.== (#clone i) 3) (#block (#break (#clone i))) (#u64.+.wrap (#clone i) 0)))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn checks_and_lowers_diverging_expressions() {
        let program = parse_program("(#fn main () u64 (#return (#if true 42 (#panic))))").unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn checks_and_lowers_never_returning_functions() {
        let program = parse_program(
            "(#fn abort () ! (#return (#unreachable))) (#fn choose ((condition bool)) u64 (#return (#if condition 42 (#call abort (:))))) (#fn main () u64 (#return (#call choose (: condition false))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("call abort"));
        assert!(assembly.contains("ud2"));
        let invalid = parse_program("(#fn bad () ! (#return 42))").unwrap();
        assert!(check_types(&invalid)
            .unwrap_err()
            .contains("expected Never"));

        let layout = parse_program(
            "(#fn main () u64 (#return (#u64.+.wrap (#as (#size-of ()) u64) (#as (#size-of !) u64))))",
        )
        .unwrap();
        assert!(check_types(&layout).is_ok());
        let assembly = generate_assembly(&layout).unwrap();
        assert!(assembly.contains("mov rax, 0"));
    }

    #[test]
    fn casts_fieldless_enum_discriminants() {
        let program = parse_program(
            "(#enum Color (Red Green)) (#fn discriminant ((value Color)) u64 (#return (#as value u64))) (#fn main () u64 (#let selected Color Green) (#return (#u64.+.wrap (#call discriminant (: value selected)) 41)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("call discriminant"));
        assert!(assembly.contains("mov rax, 1"));

        let payload = parse_program(
            "(#enum Maybe ((Some u64) None)) (#fn main () u64 (#return (#as (Some 1) u64)))",
        )
        .unwrap();
        assert!(check_types(&payload).is_err());
    }

    #[test]
    fn lowers_zero_word_unit_values() {
        let program = parse_program(
            "(#struct Tagged ((marker ()) (value u64))) (#fn consume ((marker ())) u64 (#return 41)) (#fn main () u64 (#let unit-value () ()) (#let pair (#tuple () u64) (#tuple (#tuple () u64) (#clone unit-value) 40)) (#let tagged Tagged (#struct-literal Tagged ((marker (#clone unit-value)) (value 1)))) (#return (#u64.+.wrap (#call consume (: marker unit-value)) (#u64.+.wrap (#get pair 1) (#get tagged value)))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn lowers_unit_like_structs() {
        let program = parse_program(
            "(#struct Marker ()) (#fn make () Marker (#return (#struct-literal Marker ()))) (#fn consume ((marker Marker)) u64 (#return 41)) (#fn main () u64 (#let marker Marker (#call make (:))) (#return (#call consume (: marker marker))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("call make"));
        assert!(assembly.contains("call consume"));
    }

    #[test]
    fn lowers_zero_sized_globals() {
        let program = parse_program(
            "(#let UNIT () ()) (#fn consume ((value ())) u64 (#return 41)) (#fn main () u64 (#return (#call consume (: value UNIT))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("call consume"));
        assert!(!assembly.contains("UNIT:"));
    }

    #[test]
    fn rejects_value_breaks_in_statement_loops() {
        let program =
            parse_program("(#fn main () u64 (#while true (#break 1)) (#return 0))").unwrap();
        let error = check_types(&program).unwrap_err();
        assert!(error.contains("only valid in a loop expression"));
    }

    #[test]
    fn checks_and_lowers_let_else() {
        let program = parse_program(
            "(#enum Maybe ((Some u64) None)) (#fn main () u64 (#let value Maybe (Some 42)) (#let-else (Some payload) Maybe value (#return 0)) (#return payload))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn accepts_diverging_let_else_expressions() {
        let program = parse_program(
            "(#enum Maybe ((Some u64) None)) (#fn main () u64 (#let value Maybe (Some 42)) (#let-else (Some payload) Maybe value (#unreachable)) (#return payload))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn let_else_accepts_blocks_and_branches_that_all_transfer_control() {
        for fallback in [
            "(#block (#return 0u64))",
            "(#if true (#block (#return 0u64)) (#block (#return 1u64)))",
            "(#match true (#case true (#block (#return 0u64))) (#case false (#block (#return 1u64))))",
        ] {
            let program = parse_program(&format!(
                "(#enum Maybe ((Some u64) None))
                 (#fn main () u64
                   (#let value Maybe (Some 42u64))
                   (#let-else (Some payload) Maybe value {fallback})
                   (#return payload))"
            )).unwrap();
            check_types(&program).unwrap();
            generate_assembly(&program).unwrap();
        }
        let program = parse_program(
            "(#enum Maybe ((Some u64) None))
             (#fn main () u64 (#let value Maybe (Some 42u64))
               (#let-else (Some payload) Maybe value
                 (#if true (#block (#return 0u64)) ()))
               (#return payload))",
        )
        .unwrap();
        assert!(check_types(&program).unwrap_err().contains("diverge"));
    }

    #[test]
    fn value_loop_control_transfers_diverge_without_losing_break_result_types() {
        for value in [
            "(#loop (#if true (#block (#break 42u64)) ()))",
            "(#label outer (#loop (#if true (#block (#break-to outer 42u64)) ())))",
            "(#loop (#loop (#break)) (#break 42u64))",
        ] {
            let program = parse_program(&format!("(#fn main () u64 (#return {value}))")).unwrap();
            check_types(&program).unwrap();
            generate_assembly(&program).unwrap();
        }
        let program = parse_program(
            "(#fn main () u64
               (#return (#loop (#if true (#block (#break 42u64)) (#block (#break false))))))",
        )
        .unwrap();
        assert!(check_types(&program).is_err());
        let program = parse_program(
            "(#fn main () u64
               (#return (#label outer (#loop (#break-to outer)))))",
        )
        .unwrap();
        assert!(check_types(&program).is_err());
    }

    #[test]
    fn statement_loop_headers_use_the_enclosing_value_loop_result_contract() {
        for statement in [
            "(#while (#block (#break 42u64) false) ())",
            "(#for (#let count u64 (#block (#break 42u64) 0u64)) false () ())",
            "(#for () (#block (#break 42u64) false) () ())",
            "(#for () true (#break 42u64) ())",
            "(#while true (#break-to outer 42u64))",
            "(#loop (#break-to outer 42u64))",
            "(#for () true () (#break-to outer 42u64))",
        ] {
            let source = format!(
                "(#fn main () u64
                   (#return (#label outer (#loop {statement} (#break 42u64)))))"
            );
            let program = parse_program(&source).unwrap();
            check_types(&program).unwrap_or_else(|error| panic!("{source}: {error}"));
            generate_assembly(&program).unwrap_or_else(|error| panic!("{source}: {error}"));
            let missing_value = source.replace("(#break 42u64)", "(#break)");
            if statement.contains("(#break 42u64)") {
                // Keep the final typed break, to expose an omitted Unit exit
                // rather than just rejecting an entirely Unit-valued loop.
                let missing_value = missing_value.replacen("(#break))", "(#break 42u64))", 1);
                assert!(
                    check_types(&parse_program(&missing_value).unwrap()).is_err(),
                    "{missing_value}"
                );
            }
        }
    }

    #[test]
    fn destructured_linear_cleanup_errors_retain_the_binding_span() {
        let source = "(#struct Token ((value u64))) (#linear Token)
          (#fn broken ((value Token)) ()
            (#let (#tuple retained) (#tuple Token) (#tuple (#tuple Token) value))
            (#return ()))";
        let program = parse_program(source).unwrap();
        let (message, code, span, _) =
            crate::typecheck::check_types_with_span(&program).unwrap_err();
        assert!(message.contains("retained") && message.contains("consum"));
        assert_eq!(code, DiagnosticCode::Linear);
        let span = span.expect("pattern declarations must retain their exact source spans");
        assert_eq!(&source[span.start..span.end], "retained");
    }

    #[test]
    fn matches_wide_enum_payload_literals() {
        let program = parse_program(
            "(#enum Maybe ((Some i128) None)) (#fn main () u64 (#let value Maybe (Some 42)) (#return (#match value (#case (Some 42) 42) (#case _ 0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn indexes_direct_aggregate_arrays_dynamically() {
        let program = parse_program(
            "(#fn main () u64 (#return (#get (#index (#array (#array (#tuple u64 u64) 2) (#tuple (#tuple u64 u64) 10 20) (#tuple (#tuple u64 u64) 30 12)) 1) 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn indexes_direct_aggregate_array_repeats_dynamically() {
        let program = parse_program(
            "(#fn main () u64 (#return (#get (#index (#array-repeat (#array (#tuple u64 u64) 2) (#tuple 30 12)) 1) 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn passes_aggregate_arrays_through_functions() {
        let program = parse_program(
            "(#fn consume ((values (#array (#tuple u64 u64) 2))) u64 (#return (#get (#index values 1) 0))) (#fn main () u64 (#let values (#array (#tuple u64 u64) 2) (#array (#array (#tuple u64 u64) 2) (#tuple (#tuple u64 u64) 10 20) (#tuple (#tuple u64 u64) 30 12))) (#return (#call consume (: values values))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn passes_repeated_aggregate_arrays_through_functions() {
        let program = parse_program(
            "(#fn consume ((values (#array (#tuple u64 u64) 2))) u64 (#return (#get (#index values 1) 0))) (#fn main () u64 (#return (#call consume (: values (#array-repeat (#tuple 30 12))))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn returns_repeated_aggregate_arrays() {
        let program = parse_program(
            "(#fn values () (#array (#tuple u64 u64) 2) (#return (#array-repeat (#tuple 30 12)))) (#fn main () u64 (#return (#get (#index (#call values (:)) 1) 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn returns_aggregate_if_values() {
        let program = parse_program(
            "(#fn choose ((condition bool)) (#tuple u64 u64) (#return (#if condition (#tuple (#tuple u64 u64) 10 20) (#tuple (#tuple u64 u64) 30 12)))) (#fn main () u64 (#return (#get (#call choose (: condition true)) 1)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn returns_aggregate_match_values() {
        let program = parse_program(
            "(#enum Maybe ((Some u64) None)) (#fn choose ((value Maybe)) (#tuple u64 u64) (#return (#match value (#case (Some payload) (#tuple (#tuple u64 u64) payload 20)) (#case None (#tuple (#tuple u64 u64) 30 12))))) (#fn main () u64 (#return (#get (#call choose (: value (Some 10))) 1)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn selects_fields_from_aggregate_if_values() {
        let program = parse_program(
            "(#fn main () u64 (#return (#get (#if true (#tuple (#tuple u64 u64) 10 20) (#tuple (#tuple u64 u64) 30 12)) 1)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn returns_aggregate_loop_values() {
        let program = parse_program(
            "(#fn values () (#tuple u64 u64) (#return (#loop (#break (#tuple (#tuple u64 u64) 30 12))))) (#fn main () u64 (#return (#get (#call values (:)) 1)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn lowers_aggregate_block_values() {
        let program = parse_program(
            "(#fn main () u64 (#return (#get (#block (#let value u64 10) (#tuple (#tuple u64 u64) value 20)) 1)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn lowers_conditional_aggregate_loop_breaks() {
        let program = parse_program(
            "(#fn values () (#tuple u64 u64) (#return (#loop (#if true (#block (#break (#tuple (#tuple u64 u64) 30 12))) (#unreachable))))) (#fn main () u64 (#return (#get (#call values (:)) 1)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn passes_aggregate_control_values_to_functions() {
        let program = parse_program(
            "(#fn consume ((value (#tuple u64 u64))) u64 (#return (#get value 1))) (#fn main () u64 (#return (#call consume (: value (#if true (#tuple (#tuple u64 u64) 10 20) (#tuple (#tuple u64 u64) 30 12))))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn evaluates_saturating_integer_constants() {
        let program = parse_program(
            "(#const Max u8 255) (#const Clamped u8 (#u8.+.saturate Max 1)) (#fn main () u64 (#return (#as Clamped u64)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn evaluates_saturating_minimum_division_constants() {
        let program = parse_program(
            "(#const Minimum i8 -128) (#const Quotient i8 (#i8./.saturate Minimum -1)) (#fn main () u64 (#return (#as Quotient u64)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn evaluates_u128_saturating_constants_in_the_unsigned_domain() {
        let program = parse_program(
            "(#const Maximum u128 0xffffffffffffffffffffffffffffffff) (#const Saturated u128 (#u128.+.saturate Maximum 1)) (#fn main () u64 (#return (#if (#u128.== Saturated Maximum) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn evaluates_i128_saturating_constants_at_signed_bounds() {
        let program = parse_program(
            "(#const Minimum i128 -170141183460469231731687303715884105728) (#const Saturated i128 (#i128.-.saturate Minimum 1)) (#fn main () u64 (#return (#if (#i128.== Saturated Minimum) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn evaluates_wrapping_i128_minimum_division_constants() {
        let program = parse_program(
            "(#const Minimum i128 -170141183460469231731687303715884105728) (#const Quotient i128 (#i128./.wrap Minimum -1)) (#const Remainder i128 (#i128.%.wrap Minimum -1)) (#fn main () u64 (#return (#if (#i128.== Quotient Minimum) (#if (#i128.== Remainder 0) 42 0) 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn preserves_boolean_constant_short_circuiting() {
        let program = parse_program(
            "(#const FalseAnd bool (#bool.&& false (#u64.== (#u64./.wrap 1 0) 0))) (#const TrueOr bool (#bool.|| true (#u64.== (#u64./.wrap 1 0) 0))) (#fn main () u64 (#return (#if (#bool.&& (#bool.! FalseAnd) TrueOr) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn evaluates_full_width_unsigned_machine_constants() {
        let program = parse_program(
            "(#const Maximum u64 18446744073709551615) (#const Wrapped u64 (#u64.*.wrap Maximum 2)) (#const Saturated u64 (#u64.*.saturate Maximum 2)) (#fn main () u64 (#return (#if (#u64.&& (#u64.== Wrapped 18446744073709551614) (#u64.== Saturated Maximum)) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn evaluates_wrapping_i128_constant_shifts() {
        let program = parse_program(
            "(#const Shifted i128 (#i128.<< 1 127)) (#const Minimum i128 -170141183460469231731687303715884105728) (#fn main () u64 (#return (#if (#i128.== Shifted Minimum) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn parses_and_checks_value_structs() {
        let program = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn point_x () u64 (#return (#get (#struct-literal Point ((x 7) (y 9))) x)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("mov rax, 7"));
        let local = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn point_y () u64 (#let p Point (#struct-literal Point ((x 7) (y 9)))) (#return (#get p y)))",
        )
        .unwrap();
        assert!(generate_assembly(&local).unwrap().contains("[rbp-16]"));
        let mutable = parse_program("(#struct Point ((x u64) (y u64))) (#fn main () u64 (#let-mut p Point (#struct-literal Point ((x 1) (y 2)))) (#set-field p y 40) (#return (#u64.+.wrap  (#get p x) (#get p y))))").unwrap();
        assert!(check_types(&mutable).is_ok());
        let returned = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn make_point () Point (#return (#struct-literal Point ((x 7) (y 9)))))",
        )
        .unwrap();
        assert!(check_types(&returned).is_ok());
        assert!(generate_assembly(&returned).unwrap().contains("pop rdx"));
        let consumed = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn make_point () Point (#return (#struct-literal Point ((x 7) (y 9))))) (#fn main () u64 (#let point Point (#call make_point (:))) (#return (#get point y)))",
        )
        .unwrap();
        assert!(check_types(&consumed).is_ok());
        assert!(generate_assembly(&consumed)
            .unwrap()
            .contains("call make_point"));
        let unsupported_parameter = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn identity ((point Point)) Point (#return point)) (#fn main () u64 (#let result Point (#call identity (: point (#struct-literal Point ((x 11) (y 37)))))) (#return (#get result y)))",
        )
        .unwrap();
        assert!(check_types(&unsupported_parameter).is_ok());
        assert!(generate_assembly(&unsupported_parameter)
            .unwrap()
            .contains("call identity"));
        let concrete = parse_program(
            "(#struct BoxU64 ((value u64))) (#fn main () u64 (#let boxed BoxU64 (#struct-literal BoxU64 ((value 42)))) (#return (#get boxed value)))",
        )
        .unwrap();
        assert!(check_types(&concrete).is_ok());
        assert!(generate_assembly(&concrete)
            .unwrap()
            .contains("mov rax, 42"));
        let concrete_enum = parse_program(
            "(#enum MaybeU64 ((SomeU64 u64) None)) (#fn main () u64 (#let value MaybeU64 (SomeU64 42)) (#return (#match value (#case (SomeU64 payload) payload) (#case None 0))))",
        )
        .unwrap();
        assert!(check_types(&concrete_enum).is_ok());
        assert!(generate_assembly(&concrete_enum).is_ok());
        let free_function = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn point-new ((x u64) (y u64)) Point (#return (#struct-literal Point ((x x) (y y))))) (#fn main () u64 (#return (#get (#call point-new (: x 7 : y 9)) y)))",
        )
        .unwrap();
        assert!(check_types(&free_function).is_ok());
        assert!(generate_assembly(&free_function).is_ok());
    }

    #[test]
    fn checks_boolean_and_unary_operators() {
        let program = parse_program(
            "(#fn main () bool (#return (#bool.&&  (#bool.!  false) (#bool.||  false true))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("and_false"));
        assert!(assembly.contains("xor eax, 1"));
        let bitwise =
            parse_program("(#fn main () bool (#return (#bool.^  (#bool.&  true true) false)))")
                .unwrap();
        assert!(check_types(&bitwise).is_ok());
        let bitwise_assembly = generate_assembly(&bitwise).unwrap();
        assert!(bitwise_assembly.contains("and rax, rcx"));
        assert!(bitwise_assembly.contains("xor rax, rcx"));
        let invalid_float = parse_program("(#fn main () f64 (#return (#f64.&  1.0 2.0)))").unwrap();
        assert!(check_types(&invalid_float)
            .unwrap_err()
            .contains("requires integer or boolean"));
        let invalid_aggregate = parse_program(
            "(#fn main () bool (#return (#u64.==  (#tuple (#tuple u64 u64) 1 2) (#tuple (#tuple u64 u64) 1 2))))",
        )
        .unwrap();
        assert!(check_types(&invalid_aggregate).is_err());
        let unit_if = parse_program("(#fn main () () (#return (#if true ())))").unwrap();
        assert!(check_types(&unit_if).is_ok());
        assert!(generate_assembly(&unit_if).is_ok());
        let missing_else = parse_program("(#fn main () u64 (#return (#if true 1)))").unwrap();
        assert!(check_types(&missing_else)
            .unwrap_err()
            .contains("if without else"));
    }

    #[test]
    fn checks_and_lowers_native_assertions() {
        let program =
            parse_program("(#fn main () u64 (#assert (#u64.==  40 40)) (#debug-assert (#u64.>=  42 0)) (#return 42))")
                .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("ud2"));
        let invalid = parse_program("(#fn main () () (#return (#assert 1)))").unwrap();
        assert!(check_types(&invalid).is_err());
    }

    #[test]
    fn checks_and_lowers_size_of() {
        let program = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn main () u64 (#return (#as (#usize.+.wrap (#size-of Point) (#size-of (#array u32 2))) u64)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("mov rax, 16"));
        let alignment =
            parse_program("(#fn main () u64 (#return (#as (#align-of u128) u64)))").unwrap();
        assert!(check_types(&alignment).is_ok());
        assert!(generate_assembly(&alignment)
            .unwrap()
            .contains("mov rax, 8"));
        let invalid = parse_program("(#fn main () usize (#return (#size-of Unknown)))").unwrap();
        let diagnostic = structured_type_error(&invalid);
        let span = diagnostic.span.expect("unknown size-of type has a span");
        assert_eq!(
            &"(#fn main () usize (#return (#size-of Unknown)))"[span.start..span.end],
            "Unknown"
        );
    }

    #[test]
    fn c_layout_is_explicit_and_reports_field_offsets() {
        let program = parse_program("(#struct Point #repr-c ((x u8) (y u32) (z u16))) (#fn main () usize (#return (#offset-of Point y)))").unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("mov rax, 4"));
        let size = parse_program("(#struct Point #repr-c ((x u8) (y u32) (z u16))) (#fn main () usize (#return (#size-of Point)))").unwrap();
        assert!(generate_assembly(&size).unwrap().contains("mov rax, 12"));
        let align = parse_program("(#struct Point #repr-c ((x u8) (y u32))) (#fn main () usize (#return (#align-of Point)))").unwrap();
        assert!(generate_assembly(&align).unwrap().contains("mov rax, 4"));
        let not_c = parse_program(
            "(#struct Point ((x u64))) (#fn main () usize (#return (#offset-of Point x)))",
        )
        .unwrap();
        assert!(generate_assembly(&not_c).is_err());
        let enum_layout = parse_program(
            "(#enum Code #repr-c (Small Large)) (#fn main () usize (#return (#size-of Code)))",
        )
        .unwrap();
        assert!(generate_assembly(&enum_layout)
            .unwrap()
            .contains("mov rax, 4"));
        let bad_enum = parse_program("(#enum Code #repr-c ((TooLarge 2147483648))) (#fn main () usize (#return (#size-of Code)))").unwrap();
        assert!(check_types(&bad_enum).is_err());
    }

    #[test]
    fn c_abi_rejects_by_value_aggregate_arguments_and_returns() {
        let argument = parse_program(
            "(#struct Point #repr-c ((x u64))) (#extern-fn #abi-c consume-point ((point Point)) u64)",
        )
        .unwrap();
        assert!(check_types(&argument).is_ok());
        assert!(generate_assembly(&argument)
            .unwrap_err()
            .contains("directly passed scalar values"));

        let result = parse_program(
            "(#struct Point #repr-c ((x u64))) (#extern-fn #abi-c make-point () Point)",
        )
        .unwrap();
        assert!(check_types(&result).is_ok());
        assert!(generate_assembly(&result)
            .unwrap_err()
            .contains("directly passed scalar values"));
    }

    #[test]
    fn checks_and_lowers_integer_bitwise_not() {
        let program = parse_program(
            "(#fn main () u32 (#let value u32 (#u32.!  0)) (#return (#u32.&  value 42)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("not rax"));
        let invalid = parse_program("(#fn main () u64 (#return (#u64.!  1.0)))").unwrap();
        assert!(check_types(&invalid)
            .unwrap_err()
            .contains("must be a boolean or integer"));
    }

    #[test]
    fn checks_and_lowers_payload_free_enums() {
        let program = parse_program(
            "(#enum Color (Red Green Blue)) (#fn main () u64 (#return (#match Green (#case Red 10) (#case Green 20) (#case _ 30))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("cmp QWORD PTR [rsp], 1"));
        assert!(parse_program("(#enum Bad (Same Same))")
            .unwrap_err()
            .contains("duplicate enum variant"));
    }

    #[test]
    fn checks_and_lowers_multi_payload_enums() {
        let program = parse_program(
            "(#enum Pair ((Pair u64 u64) Empty)) (#fn main () u64 (#let value Pair (Pair 20 22)) (#return (#match value (#case (Pair left right) (#u64.+.wrap  left right)) (#case Empty 0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("mov rax, 20"));
    }

    #[test]
    fn matches_enum_payload_literals() {
        let program = parse_program(
            "(#enum Maybe ((Some u64) None)) (#fn classify ((value Maybe)) u64 (#return (#match value (#case (Some 42) 1) (#case None 0)))) (#fn main () u64 (#return (#call classify (: value (Some 42)))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program)
            .unwrap()
            .contains("cmp QWORD PTR [rbp-16], 42"));
    }

    #[test]
    fn passes_multi_payload_enums_through_functions() {
        let program = parse_program(
            "(#enum Pair ((Pair u64 u64) Empty)) (#fn make () Pair (#let value Pair (Pair 20 22)) (#return value)) (#fn sum ((value Pair)) u64 (#return (#match value (#case (Pair left right) (#u64.+.wrap  left right)) (#case Empty 0)))) (#fn main () u64 (#return (#call sum (: value (#call make (:))))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("call sum"));
    }

    #[test]
    fn lowers_two_word_128_bit_integers() {
        let program = parse_program(
            "(#fn add ((left u128) (right u128)) u128 (#return (#u128.+.wrap  left right))) (#fn main () u64 (#return (#as (#call add (: left 20 : right 22)) u64)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("adc rdx, r8"));
        assert!(assembly.contains("call add"));
        let minimum =
            parse_program("(#fn main () i128 (#return -170141183460469231731687303715884105728))")
                .unwrap();
        assert!(check_types(&minimum).is_ok());
        assert!(generate_assembly(&minimum).is_ok());
    }

    #[test]
    fn lowers_128_bit_comparisons_and_shifts() {
        let program = parse_program(
            "(#fn main () u64 (#let left u128 1) (#let right u128 2) (#return (#if (#u128.&&  (#u128.<  (#clone left) (#clone right)) (#u128.==  (#u128.<<  left 5) 32)) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("shld rdx, rax, cl"));
        assert!(assembly.contains("cmp rdx, r8"));
    }

    #[test]
    fn lowers_128_bit_multiplication() {
        let program = parse_program(
            "(#fn multiply ((left u128) (right u128)) u128 (#return (#u128.*.wrap  left right))) (#fn main () u64 (#return (#as (#call multiply (: left 6 : right 7)) u64)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("mul rcx"));
    }

    #[test]
    fn lowers_unsigned_128_bit_division_and_remainder() {
        let program = parse_program(
            "(#fn main () u64 (#let value u128 100) (#let divisor u128 7) (#return (#if (#u128.&&  (#u128.==  (#u128./.wrap  (#clone value) (#clone divisor)) 14) (#u128.==  (#u128.%.wrap  value divisor) 2)) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program)
            .unwrap()
            .contains("wide_div_loop"));
    }

    #[test]
    fn lowers_signed_128_bit_division_and_remainder() {
        let program = parse_program(
            "(#fn main () u64 (#let value i128 100) (#let divisor i128 7) (#return (#if (#i128.&&  (#i128.==  (#i128./.wrap  (#i128.-.wrap  (#clone value)) (#clone divisor)) -14) (#i128.==  (#i128.%.wrap  (#i128.-.wrap  value) divisor) -2)) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("sar r9, 63"));
    }

    #[test]
    fn checks_and_lowers_scalar_enum_payloads() {
        let program = parse_program(
            "(#enum Maybe ((Some u64) None)) (#fn main () u64 (#let value Maybe (Some 42)) (#return (#match value (#case (Some _) 42) (#case None 7))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("mov QWORD PTR [rbp-8], 0"));
        assert!(assembly.contains("cmp QWORD PTR [rsp], 0"));
        let invalid = parse_program(
            "(#enum Maybe ((Some u64) None)) (#fn main () u64 (#return (#match None (#case (Some _) 1))))",
        )
        .unwrap();
        assert!(check_types(&invalid)
            .unwrap_err()
            .contains("not exhaustive"));
        let binding = parse_program(
            "(#enum Maybe ((Some u64) None)) (#fn main () u64 (#let value Maybe (Some 42)) (#return (#match value (#case (Some payload) payload) (#case None 0))))",
        )
        .unwrap();
        assert!(check_types(&binding).is_ok());
        assert!(generate_assembly(&binding)
            .unwrap()
            .contains("mov QWORD PTR [rbp-24], rax"));
        let returned = parse_program(
            "(#enum Maybe ((Some u64) None)) (#fn make () Maybe (#return (Some 42))) (#fn main () u64 (#let value Maybe (#call make (:))) (#return (#match value (#case (Some payload) payload) (#case None 0))))",
        )
        .unwrap();
        assert!(check_types(&returned).is_ok());
        assert!(generate_assembly(&returned).unwrap().contains("call make"));
        let passed = parse_program(
            "(#enum Maybe ((Some u64) None)) (#fn identity ((value Maybe)) Maybe (#return value)) (#fn main () u64 (#let result Maybe (#call identity (: value (Some 42)))) (#return (#match result (#case (Some payload) payload) (#case None 0))))",
        )
        .unwrap();
        assert!(check_types(&passed).is_ok());
        assert!(generate_assembly(&passed)
            .unwrap()
            .contains("call identity"));
        let repeated = parse_program(
            "(#fn main () u64 (#let values (#array u64 3) (#array-repeat 13)) (#return (#index values 1)))",
        )
        .unwrap();
        assert!(check_types(&repeated).is_ok());
        assert!(generate_assembly(&repeated)
            .unwrap()
            .contains("mov rax, 13"));
    }

    #[test]
    fn matches_computed_enum_values() {
        let program = parse_program(
            "(#enum Maybe ((Some u64) None)) (#fn main () u64 (#return (#match (Some 42) (#case (Some value) value) (#case None 0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("add rsp, 16"));
    }

    #[test]
    fn indexes_arrays_returned_by_functions() {
        let program = parse_program(
            "(#fn make () (#array u64 3) (#return (#array 10 20 30))) (#fn main () u64 (#return (#index (#call make (:)) 1)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("call make"));
    }

    #[test]
    fn selects_fields_from_structs_returned_by_functions() {
        let program = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn make () Point (#return (#struct-literal Point ((x 7) (y 9))))) (#fn main () u64 (#return (#get (#call make (:)) y)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("call make"));
    }

    #[test]
    fn passes_floating_struct_fields_through_functions() {
        let program = parse_program(
            "(#struct Point ((x f64) (y f32))) (#fn make () Point (#return (#struct-literal Point ((x 1.5) (y 2.5))))) (#fn main () u64 (#return (#if (#bool.&& (#f64.> (#get (#call make (:)) x) 1.0) (#f32.> (#get (#call make (:)) y) 2.0)) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("movq rax, xmm0"));
        assert!(assembly.contains("movd xmm0, eax"));
    }

    #[test]
    fn passes_floating_arrays_through_functions() {
        let program = parse_program(
            "(#fn sum ((values (#array f32 2))) f32 (#return (#index values 1))) (#fn make () (#array f32 2) (#return (#array 1.5 2.5))) (#fn main () u64 (#let value f32 (#call sum (: values (#call make (:))))) (#return (#if (#f32.>  value 2.0) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("movd eax, xmm0"));
        assert!(assembly.contains("movss xmm0, DWORD PTR"));
    }

    #[test]
    fn indexes_floating_arrays_returned_by_functions() {
        let program = parse_program(
            "(#fn make () (#array f32 2) (#return (#array 1.5 2.5))) (#fn main () u64 (#return (#if (#f32.>  (#index (#call make (:)) 1) 2.0) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("call make"));
        assert!(assembly.contains("movd xmm0, eax"));
    }

    #[test]
    fn passes_floating_enum_payloads_through_functions() {
        let program = parse_program(
            "(#enum MaybeF ((SomeF f32) None)) (#fn make () MaybeF (#return (SomeF 2.5))) (#fn read ((value MaybeF)) f32 (#return (#match value (#case (SomeF payload) payload) (#case None 0.0)))) (#fn main () u64 (#return (#if (#f32.>  (#call read (: value (#call make (:)))) 2.0) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("call make"));
        assert!(assembly.contains("movss xmm0, DWORD PTR"));
    }

    #[test]
    fn matches_scalar_values() {
        let program = parse_program(
            "(#fn classify ((value u64)) u64 (#return (#match value (#case 0 10) (#case 1 20) (#case _ 30)))) (#fn main () u64 (#return (#call classify (: value 1))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("cmp QWORD PTR [rsp], 1"));
        let bools = parse_program(
            "(#fn main () u64 (#return (#match true (#case true 42) (#case false 0))))",
        )
        .unwrap();
        assert!(check_types(&bools).is_ok());
        let incomplete =
            parse_program("(#fn main () u64 (#return (#match 1 (#case 1 42))))").unwrap();
        assert!(check_types(&incomplete)
            .unwrap_err()
            .contains("not exhaustive"));
        let duplicate_integer = parse_program(
            "(#fn main () u64 (#return (#match 1 (#case 1 10) (#case 1 20) (#case _ 30))))",
        )
        .unwrap();
        assert!(check_types(&duplicate_integer)
            .unwrap_err()
            .contains("duplicate integer match pattern"));
        let duplicate_enum = parse_program(
            "(#enum Color (Red Blue)) (#fn main () u64 (#return (#match Red (#case Red 1) (#case Red 2) (#case _ 0))))",
        )
        .unwrap();
        assert!(check_types(&duplicate_enum)
            .unwrap_err()
            .contains("duplicate enum match pattern 'Red'"));
        let wide = parse_program(
            "(#fn main () u64 (#let value u128 340282366920938463463374607431768211455) (#return (#match value (#case 340282366920938463463374607431768211455 42) (#case _ 0))))",
        )
        .unwrap();
        assert!(check_types(&wide).is_ok());
        assert!(generate_assembly(&wide).is_ok());
    }

    #[test]
    fn checks_and_lowers_fixed_arrays() {
        let program = parse_program("(#fn main () u64 (#let-mut values (#array u64 2) (#array 3 4)) (#set-index values 1 40) (#return (#u64.+.wrap  (#index values 0) (#index values 1))))").unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("lea r11"));
        assert!(assembly.contains("shl rcx, 3"));
        assert!(assembly.contains("jae"));
        assert!(assembly.contains("ud2"));
        let invalid = parse_program(
            "(#fn main () u64 (#let values (#array u64 2) (#array 1 2)) (#return (#index values 2)))",
        )
        .unwrap();
        assert!(check_types(&invalid).unwrap_err().contains("out of bounds"));
        let passed = parse_program(
            "(#fn identity ((values (#array u64 3))) (#array u64 3) (#return values)) (#fn main () u64 (#let values (#array u64 3) (#call identity (: values (#array 10 20 37)))) (#return (#index values 2)))",
        )
        .unwrap();
        assert!(check_types(&passed).is_ok());
        assert!(generate_assembly(&passed)
            .unwrap()
            .contains("call identity"));
    }

    #[test]
    fn lowers_fixed_string_arrays() {
        let program = parse_program(
            "(#fn main () u64 (#let chars (#array char 2) \"Hi\") (#return (#if (#char.== (#index \"Hi\" 1) #\\i) (#if (#char.== (#index chars 0) #\\H) 42 0) 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn checks_and_lowers_explicit_enum_discriminants() {
        let program = parse_program(
            "(#enum Result ((Ok 7 u64) (Err 99 u64))) (#fn main () u64 (#let value Result (Ok 42)) (#return (#match value (#case (Ok payload) payload) (#case (Err _) 0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn rejects_duplicate_enum_discriminants() {
        let program = parse_program("(#enum Code ((Ready 7) (AlsoReady 7)))");
        assert!(program.unwrap_err().contains("duplicate discriminant 7"));
    }

    #[test]
    fn accepts_maximum_final_enum_discriminant() {
        let program = parse_program(
            "(#enum Code ((Maximum 18446744073709551615))) (#fn main () u64 (#return (#match Maximum (#case Maximum 42) (#case _ 0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("0xffffffffffffffff"));
    }

    #[test]
    fn lowers_discarded_fixed_string_expressions() {
        let program =
            parse_program("(#fn main () u64 (#if true \"Hi\" \"No\") (#return 42))").unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn lowers_discarded_aggregate_expressions() {
        let program = parse_program(
            "(#struct Pair ((left u64) (right u64))) (#fn main () u64 (#tuple (#tuple u64 u64) 1 2) (#struct-literal Pair ((left 3) (right 4))) (#return 42))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn lowers_keyed_struct_literals() {
        let program = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn main () u64 (#let point Point (#struct-literal Point ((y 22u64) (x 20u64)))) (#return (#u64.+.wrap (#get point x) (#get point y))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());

        let missing = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn main () u64 (#return (#struct-literal Point ((x 20u64)))))",
        );
        assert!(missing.unwrap_err().contains("missing field 'y'"));

        let duplicate = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn main () u64 (#return (#struct-literal Point ((x 20u64) (x 21u64) (y 22u64)))))",
        );
        assert!(duplicate.unwrap_err().contains("duplicate field 'x'"));
    }

    #[test]
    fn struct_types_are_not_positional_constructors() {
        let direct = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn main () u64 (#return (#get (Point 20u64 22u64) x)))",
        );
        assert!(direct
            .unwrap_err()
            .contains("'Point' is a type, not a constructor function"));

        let named = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn make-point ((x u64) (y u64)) Point (#return (#struct-literal Point ((x x) (y y))))) (#fn main () u64 (#return (#get (#call make-point (: x 20u64 : y 22u64)) x)))",
        )
        .unwrap();
        assert!(check_types(&named).is_ok());
        assert!(generate_assembly(&named).is_ok());
    }

    #[test]
    fn calls_use_explicit_named_function_arguments() {
        let program = parse_program(
            "(#fn subtract ((minuend u64) (subtrahend u64)) u64 (#return (#u64.-.wrap minuend subtrahend))) (#fn main () u64 (#return (#call subtract (: subtrahend 2u64 : minuend 42u64))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());

        let duplicate = parse_program(
            "(#fn identity ((value u64)) u64 (#return value)) (#fn main () u64 (#return (#call identity (: value 1u64 : value 2u64))))",
        );
        assert!(duplicate.unwrap_err().contains("more than once"));
    }

    #[test]
    fn lowers_direct_array_constructor_indexing() {
        let program = parse_program(
            "(#fn main () u64 (#return (#index (#array (#array u64 3) 10 20 42) 2)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
        let inferred =
            parse_program("(#fn main () u64 (#return (#index (#array 10 20) 0)))").unwrap();
        assert!(check_types(&inferred)
            .unwrap_err()
            .contains("direct array constructors require"));
    }

    #[test]
    fn lowers_direct_array_repeat_indexing() {
        let program = parse_program(
            "(#fn main () u64 (#return (#index (#array-repeat (#array u64 3) 42) 2)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn passes_explicit_array_constructors_through_functions() {
        let program = parse_program(
            "(#fn make () (#array u64 3) (#return (#array (#array u64 3) 10 20 37))) (#fn consume ((values (#array u64 3))) u64 (#return (#index values 2))) (#fn main () u64 (#return (#call consume (: values (#call make (:))))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn lowers_explicit_direct_tuple_constructor() {
        let program =
            parse_program("(#fn main () u64 (#return (#get (#tuple (#tuple u64 u64) 40 2) 0)))")
                .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
        let inferred = parse_program("(#fn main () u64 (#return (#get (#tuple 40 2) 0)))").unwrap();
        assert!(check_types(&inferred).is_err());
    }

    #[test]
    fn passes_explicit_tuple_constructors_through_functions() {
        let program = parse_program(
            "(#fn make () (#tuple u64 u64) (#return (#tuple (#tuple u64 u64) 40 2))) (#fn consume ((value (#tuple u64 u64))) u64 (#return (#get value 0))) (#fn main () u64 (#return (#call consume (: value (#call make (:))))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn lowers_tuple_destructuring_match() {
        let program = parse_program(
            "(#fn classify ((value (#tuple u64 u64))) u64 (#return (#match value (#case (#tuple 40 second) second) (#case _ 0)))) (#fn main () u64 (#return (#call classify (: value (#tuple (#tuple u64 u64) 40 2)))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn lowers_struct_destructuring_match() {
        let program = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn classify ((value Point)) u64 (#return (#match value (#case (Point 40 second) second) (#case _ 0)))) (#fn main () u64 (#return (#call classify (: value (#struct-literal Point ((x 40) (y 2)))))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn wraps_signed_machine_width_division_overflow() {
        let program =
            parse_program("(#fn main () i64 (#return (#i64./.wrap -9223372036854775808 -1)))")
                .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program)
            .unwrap()
            .contains("wrapping_division_done"));
    }

    #[test]
    fn saturates_signed_machine_width_division_overflow() {
        let program =
            parse_program("(#fn main () i64 (#return (#i64./.saturate -9223372036854775808 -1)))")
                .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("0x7fffffffffffffff"));
    }

    #[test]
    fn lowers_saturating_wide_addition_and_subtraction() {
        let program = parse_program(
            "(#fn main () u128 (#return (#u128.+.saturate 340282366920938463463374607431768211455 1)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("wide_saturate_high"));
        let signed = parse_program(
            "(#fn main () i128 (#return (#i128.-.saturate -170141183460469231731687303715884105728 1)))",
        )
        .unwrap();
        assert!(check_types(&signed).is_ok());
        assert!(generate_assembly(&signed).is_ok());
        let multiplication = parse_program(
            "(#fn main () u128 (#return (#u128.*.saturate 340282366920938463463374607431768211455 2)))",
        )
        .unwrap();
        assert!(check_types(&multiplication).is_ok());
        assert!(generate_assembly(&multiplication).is_ok());
        let signed_multiplication = parse_program(
            "(#fn main () i128 (#return (#i128.*.saturate 170141183460469231731687303715884105727 2)))",
        )
        .unwrap();
        assert!(check_types(&signed_multiplication).is_ok());
        assert!(generate_assembly(&signed_multiplication).is_ok());
        let negative_multiplication = parse_program(
            "(#fn main () i128 (#return (#i128.*.saturate -170141183460469231731687303715884105728 2)))",
        )
        .unwrap();
        assert!(check_types(&negative_multiplication).is_ok());
        assert!(generate_assembly(&negative_multiplication).is_ok());
    }

    #[test]
    fn lowers_saturating_wide_division_and_remainder() {
        let program = parse_program(
            "(#fn main () i128 (#return (#i128./.saturate -170141183460469231731687303715884105728 -1)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("wide_saturating_division_done"));
        let remainder =
            parse_program("(#fn main () i128 (#return (#i128.%.saturate -10 3)))").unwrap();
        assert!(check_types(&remainder).is_ok());
        assert!(generate_assembly(&remainder).is_ok());
    }

    #[test]
    fn lowers_stack_arguments() {
        let program = parse_program("(#fn sum8 ((a u64) (b u64) (c u64) (d u64) (e u64) (f u64) (g u64) (h u64)) u64 (#return (#u64.+.wrap  (#u64.+.wrap  (#u64.+.wrap  (#u64.+.wrap  (#u64.+.wrap  (#u64.+.wrap  (#u64.+.wrap  a b) c) d) e) f) g) h))) (#fn main () u64 (#return (#call sum8 (: a 1 : b 2 : c 3 : d 4 : e 5 : f 6 : g 7 : h 8))))").unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("[rbp+16]"));
        assert!(assembly.contains("[rbp+24]"));
    }

    #[test]
    fn lowers_for_loop_with_continue_step() {
        let program = parse_program("(#fn main () u64 (#let-mut total u64 0) (#for (#let-mut i u64 0) (#u64.<  (#clone i) 3) (#set i (#u64.+.wrap  i 1)) (#continue)) (#return total))").unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("for_step"));
    }

    #[test]
    fn lowers_explicit_range_loops() {
        let program = parse_program(
            "(#fn main () u64 (#let-mut total u64 0) (#for-range (i u64) 0 10 (#set total (#u64.+.wrap  total i))) (#return total))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("for_step"));
    }

    #[test]
    fn lowers_statement_blocks_in_expressions() {
        let program =
            parse_program("(#fn main () u64 (#let-mut value u64 1) (#return (#if true (#block (#set value 40) value) (#block value))))")
                .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program)
            .unwrap()
            .contains("mov QWORD PTR"));
    }

    #[test]
    fn checks_and_lowers_loop_statements() {
        let program = parse_program(
            "(#fn main () u64 (#let-mut value u64 0) (#loop (#set value (#u64.+.wrap  value 1)) (#break)) (#return value))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("loop"));
        let invalid = parse_program("(#fn main () u64 (#break) (#return 0))").unwrap();
        assert!(check_types(&invalid)
            .unwrap_err()
            .contains("outside a loop"));
    }

    #[test]
    fn checks_and_lowers_labeled_value_loops() {
        let program = parse_program(
            "(#fn main () u64 (#let-mut count u64 0) (#let result u64 (#label outer (#loop (#set count (#u64.+.wrap count 1u64)) (#if (#u64.< count 3u64) (#block (#continue-to outer)) ()) (#break-to outer 42u64)))) (#return result))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("value_loop"));

        let invalid = parse_program("(#fn main () u64 (#return (#label nope 42u64)))").unwrap_err();
        assert!(invalid.contains("expression label"));
    }

    #[test]
    fn lowers_aggregate_labeled_value_breaks() {
        let program = parse_program(
            "(#fn main () (#tuple u64 u64) (#return (#label outer (#loop (#break-to outer (#tuple (#tuple u64 u64) 40u64 2u64))))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("value_loop"));
    }

    #[test]
    fn lowers_large_aggregate_labeled_value_breaks() {
        let program = parse_program(
            "(#fn main () (#array u64 7) (#return (#label outer (#loop (#break-to outer (#array (#array u64 7) 1u64 2u64 3u64 4u64 5u64 6u64 7u64))))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn keeps_loop_locals_in_lexical_scope() {
        for source in [
            "(#fn main () u64 (#while false (#let value u64 7) (#break)) (#return value))",
            "(#fn main () u64 (#loop (#let value u64 7) (#break)) (#return value))",
            "(#fn main () u64 (#for (#let-mut i u64 0) false (#set i 1) (#let value u64 7)) (#return value))",
        ] {
            let program = parse_program(source).unwrap();
            let error = check_types(&program).unwrap_err();
            assert!(error.contains("value"), "{source}: {error}");
        }
        let valid = parse_program(
            "(#fn main () u64 (#while false (#let value u64 7) (#break)) (#return 0))",
        )
        .unwrap();
        assert!(check_types(&valid).is_ok());
    }
    #[test]
    fn lowers_immutable_globals() {
        let program = parse_program(
            "(#let ANSWER u64 40) (#fn main () u64 (#return (#u64.+.wrap  ANSWER 2)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program)
            .unwrap()
            .contains("[rip+ANSWER]"));
        let invalid =
            parse_program("(#let-mut ANSWER u64 40) (#fn main () u64 (#return ANSWER))").unwrap();
        assert!(check_types(&invalid)
            .unwrap_err()
            .contains("cannot be mutable"));
    }

    #[test]
    fn lowers_float_and_char_globals() {
        let program = parse_program(
            "(#let scale f32 1.5) (#let pi f64 3.25) (#let letter char #\\a) (#fn main () u64 (#return (#if (#bool.&& (#f32.> scale 1.0) (#bool.&& (#f64.> pi 3.0) (#char.== letter #\\a))) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("movss xmm0, DWORD PTR [rip+scale]"));
        assert!(assembly.contains("movq xmm0, QWORD PTR [rip+pi]"));
    }

    #[test]
    fn lowers_saturating_unary_negation() {
        let program = parse_program(
            "(#fn saturate ((value i8)) i8 (#return (#i8.-.saturate value))) (#fn main () u64 (#return (#as (#call saturate (: value -128)) u64)))",
        )
        .unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("mov rax, 127"), "{assembly}");
        assert!(assembly.contains("cmp rax, -128"), "{assembly}");
    }

    #[test]
    fn lowers_static_float_arrays() {
        let program = parse_program(
            "(#static VALUES (#array f32 2) (#array (#array f32 2) 1.5f32 2.5f32)) (#fn main () u64 (#return (#unsafe (#if (#f32.== (#index VALUES 1) 2.5f32) 42 0))))",
        )
        .unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("VALUES:"), "{assembly}");
        assert!(assembly.contains(".quad 1075838976"), "{assembly}");
    }

    #[test]
    fn parses_and_lowers_typed_integer_literals() {
        let program = parse_program(
            "(#const BYTE u8 255u8) (#fn main () u64 (#return (#as (#u32.+.wrap 1u32 41u32) u64)))",
        )
        .unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("mov rax, 1"), "{assembly}");
        assert!(assembly.contains("mov rax, 41"), "{assembly}");

        let wide =
            parse_program("(#fn main () u128 (#return 0xffffffffffffffffffffffffffffffffu128))")
                .unwrap();
        assert!(generate_assembly(&wide).is_ok());
    }

    #[test]
    fn parses_and_evaluates_typed_float_literals() {
        let program = parse_program(
            "(#const SCALE f32 1.5f32) (#const OFFSET f64 0.25f64) (#fn main () u64 (#return (#if (#bool.&& (#f32.== SCALE 1.5f32) (#f64.== OFFSET 0.25f64)) 42 0)))",
        )
        .unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("SCALE:"), "{assembly}");
        assert!(assembly.contains("_lim_OFFSET:"), "{assembly}");
    }

    #[test]
    fn mangles_assembler_reserved_identifiers() {
        let program = parse_program(
            "(#fn offset () u64 (#return 41)) (#fn main () u64 (#return (#u64.+.wrap (#call offset (:)) 1u64)))",
        )
        .unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains(".globl _lim_offset"), "{assembly}");
        assert!(assembly.contains("call _lim_offset"), "{assembly}");
    }

    #[test]
    fn supports_large_tuple_locals_without_abi_flattening() {
        let program = parse_program(
            "(#fn main () u64 (#let value (#tuple u64 u64 u64 u64 u64 u64 u64) (#tuple (#tuple u64 u64 u64 u64 u64 u64 u64) 1u64 2u64 3u64 4u64 5u64 6u64 7u64)) (#let copy (#tuple u64 u64 u64 u64 u64 u64 u64) value) (#return (#u64.+.wrap (#get copy 0) (#get copy 6))))",
        )
        .unwrap();
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn supports_large_struct_locals_without_abi_flattening() {
        let program = parse_program(
            "(#struct Large ((a u64) (b u64) (c u64) (d u64) (e u64) (f u64) (g u64))) (#fn main () u64 (#let value Large (#struct-literal Large ((a 1u64) (b 2u64) (c 3u64) (d 4u64) (e 5u64) (f 6u64) (g 7u64)))) (#let copy Large value) (#return (#u64.+.wrap (#get copy a) (#get copy g))))",
        )
        .unwrap();
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn supports_large_array_locals_without_abi_flattening() {
        let program = parse_program(
            "(#fn main () u64 (#let values (#array u64 8) (#array (#array u64 8) 1u64 2u64 3u64 4u64 5u64 6u64 7u64 8u64)) (#let copy (#array u64 8) values) (#return (#u64.+.wrap (#index copy 0u64) (#index copy 7u64))))",
        )
        .unwrap();
        let assembly = generate_assembly(&program);
        assert!(assembly.is_ok(), "{assembly:?}");
    }

    #[test]
    fn copies_oversized_array_elements_by_local_binding_identity() {
        let program = parse_program(
            "(#struct Large ((a u64) (b u64) (c u64) (d u64) (e u64) (f u64) (g u64))) (#fn main () u64 (#let values (#array Large 1) (#array (#array Large 1) (#struct-literal Large ((a 1u64) (b 2u64) (c 3u64) (d 4u64) (e 5u64) (f 6u64) (g 42u64))))) (#let copied Large (#index values 0usize)) (#return (#get copied g)))",
        )
        .unwrap();
        let assembly = generate_assembly(&program);
        assert!(assembly.is_ok(), "{assembly:?}");
    }

    #[test]
    fn matches_large_scalar_array_locals_without_abi_flattening() {
        let program = parse_program(
            "(#fn main () u64 (#let values (#array u64 7) (#array (#array u64 7) 1u64 2u64 3u64 4u64 5u64 6u64 42u64)) (#return (#match values (#case (#array first second third fourth fifth sixth last) last) (#case _ 0u64))))",
        )
        .unwrap();
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn matches_direct_large_scalar_array_returns() {
        let program = parse_program(
            "(#fn make () (#array u64 7) (#return (#array (#array u64 7) 1u64 2u64 3u64 4u64 5u64 6u64 42u64))) (#fn main () u64 (#return (#match (#call make (:)) (#case (#array first second third fourth fifth sixth last) last) (#case _ 0u64))))",
        )
        .unwrap();
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn matches_direct_large_nested_aggregate_returns() {
        let program = parse_program(
            "(#fn make () (#array (#tuple u128 u64) 4) (#return (#array (#array (#tuple u128 u64) 4) (#tuple 10u128 1u64) (#tuple 20u128 2u64) (#tuple 30u128 3u64) (#tuple 40u128 42u64)))) (#fn main () u64 (#return (#match (#call make (:)) (#case (#array (#tuple _ _) (#tuple _ _) (#tuple _ _) (#tuple _ last)) last) (#case _ 0u64))))",
        )
        .unwrap();
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn matches_direct_large_tuple_and_struct_returns() {
        let program = parse_program(
            "(#struct Large ((a u64) (b u64) (c u64) (d u64) (e u64) (f u64) (g u64))) (#fn make-tuple () (#tuple u64 u64 u64 u64 u64 u64 u64) (#return (#tuple (#tuple u64 u64 u64 u64 u64 u64 u64) 1u64 2u64 3u64 4u64 5u64 6u64 20u64))) (#fn make-struct () Large (#return (#struct-literal Large ((a 1u64) (b 2u64) (c 3u64) (d 4u64) (e 5u64) (f 6u64) (g 22u64))))) (#fn main () u64 (#return (#u64.+.wrap (#match (#call make-tuple (:)) (#case (#tuple first second third fourth fifth sixth last) last) (#case _ 0u64)) (#match (#call make-struct (:)) (#case (Large first second third fourth fifth sixth last) last) (#case _ 0u64)))))",
        )
        .unwrap();
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn lowers_large_aggregate_let_else() {
        let program = parse_program(
            "(#fn main () u64 (#let values (#array u64 7) (#array (#array u64 7) 1u64 2u64 3u64 4u64 5u64 6u64 42u64)) (#let-else (#array first second third fourth fifth sixth last) (#array u64 7) values (#return 0u64)) (#return last))",
        )
        .unwrap();
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn supports_large_enum_payloads_in_locals() {
        let program = parse_program(
            "(#enum BigPayload ((Big u64 u64 u64 u64 u64 u64 u64) Empty)) (#fn main () u64 (#let-mut value BigPayload (Big 1u64 2u64 3u64 4u64 5u64 6u64 7u64)) (#set-payload value Big 6 42u64) (#return 42u64))",
        )
        .unwrap();
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn large_enum_payload_reference_checks_the_active_variant_before_copying() {
        let program =
            parse_program(include_str!("../examples/large_reference_projections.lim")).unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("inactive_large_enum_payload_projection"));
        assert!(assembly.contains("ud2"));
    }

    #[test]
    fn returns_large_arrays_with_nested_wide_elements() {
        let program = parse_program(
            "(#fn make () (#array (#tuple u128 u64) 4) (#return (#array (#array (#tuple u128 u64) 4) (#tuple 10u128 1u64) (#tuple 20u128 2u64) (#tuple 30u128 3u64) (#tuple 40u128 42u64)))) (#fn main () u64 (#let values (#array (#tuple u128 u64) 4) (#call make (:))) (#let item (#tuple u128 u64) (#index values 3u64)) (#let direct-item (#tuple u128 u64) (#index (#call make (:)) 3u64)) (#return (#u64.+.wrap (#get item 1) (#get direct-item 1))))",
        )
        .unwrap();
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn passes_large_arrays_with_nested_wide_elements() {
        let program = parse_program(
            "(#fn consume ((value (#array (#tuple u128 u64) 4))) u64 (#let item (#tuple u128 u64) (#index value 3u64)) (#return (#get item 1))) (#fn main () u64 (#return (#call consume (: value (#array (#array (#tuple u128 u64) 4) (#tuple 10u128 1u64) (#tuple 20u128 2u64) (#tuple 30u128 3u64) (#tuple 40u128 42u64))))))",
        )
        .unwrap();
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn passes_two_constructed_large_arguments_without_aliasing() {
        let program = parse_program(
            "(#fn add-last ((left (#array (#tuple u128 u64) 4)) (right (#array (#tuple u128 u64) 4))) u64 (#let left-item (#tuple u128 u64) (#index left 3u64)) (#let right-item (#tuple u128 u64) (#index right 3u64)) (#return (#u64.+.wrap (#get left-item 1) (#get right-item 1)))) (#fn main () u64 (#return (#call add-last (: left (#array (#array (#tuple u128 u64) 4) (#tuple 10u128 2u64) (#tuple 20u128 3u64) (#tuple 30u128 4u64) (#tuple 40u128 20u64)) : right (#array (#array (#tuple u128 u64) 4) (#tuple 50u128 5u64) (#tuple 60u128 6u64) (#tuple 70u128 7u64) (#tuple 80u128 22u64))))))",
        )
        .unwrap();
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn passes_constructed_large_enum_arguments() {
        let program = parse_program(
            "(#enum Wide ((Values u64 u64 u64 u64 u64 u64 u64) Empty)) (#fn last ((value Wide)) u64 (#return (#match value (#case (Values first second third fourth fifth sixth last) last) (#case _ 0u64)))) (#fn main () u64 (#return (#call last (: value (Values 1u64 2u64 3u64 4u64 5u64 6u64 42u64)))))",
        )
        .unwrap();
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn checks_and_lowers_type_aliases() {
        let program = parse_program(
            "(#type UserId u64) (#fn add_one ((id UserId)) UserId (#return (#u64.+.wrap  id 1))) (#fn main () UserId (#return (#call add_one (: id 41))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("add_one"));
        let invalid = parse_program(
            "(#type UserId u64) (#fn main () UserId (#let value u32 1) (#return value))",
        )
        .unwrap();
        assert!(check_types(&invalid).unwrap_err().contains("expected U64"));
        let nested = parse_program(
            "(#type UserId u64) (#fn main () UserId (#return (#block (#let inner UserId 41) inner)))",
        )
        .unwrap();
        assert!(check_types(&nested).is_ok());
        let tuple_alias = parse_program(
            "(#type UserId u64) (#fn main () (#tuple UserId u32) (#return (#tuple 40 2)))",
        )
        .unwrap();
        assert!(check_types(&tuple_alias).is_ok());
        assert!(generate_assembly(&tuple_alias).is_ok());
        let enum_payload = parse_program(
            "(#type Value u64) (#enum Box ((Some Value) None)) (#fn main () u64 (#return (#match (Some 42) (#case (Some value) value) (#case None 0))))",
        )
        .unwrap();
        assert!(check_types(&enum_payload).is_ok());
        assert!(generate_assembly(&enum_payload).is_ok());
        let concrete = parse_program(
            "(#type PairU64 (#tuple u64 u64)) (#fn main () u64 (#let pair PairU64 (#tuple 20 22)) (#return (#u64.+.wrap  (#get pair 0) (#get pair 1))))",
        )
        .unwrap();
        assert!(check_types(&concrete).is_ok());
        assert!(generate_assembly(&concrete).is_ok());
    }

    #[test]
    fn rejects_indirect_recursive_type_aliases() {
        let program = parse_program(
            "(#type First Second) (#type Second First) (#fn main () First (#return 0))",
        )
        .unwrap();
        let error = check_types(&program).unwrap_err();
        assert!(error.contains("recursive"), "{error}");
        assert!(generate_assembly(&program)
            .unwrap_err()
            .contains("recursive"));
    }

    #[test]
    fn rejects_ambiguous_unqualified_value_names() {
        let duplicate_field =
            parse_program("(#struct Point ((x u64) (x u64))) (#fn main () u64 (#return 0))")
                .unwrap();
        assert!(check_types(&duplicate_field)
            .unwrap_err()
            .contains("duplicate field 'x'"));
        let duplicate_variant = parse_program(
            "(#enum First (Ready)) (#enum Second (Ready)) (#fn main () u64 (#return 0))",
        )
        .unwrap();
        assert!(check_types(&duplicate_variant)
            .unwrap_err()
            .contains("already defined in enum 'First'"));
    }

    #[test]
    fn slices_borrow_arrays_and_bounds_check_indexing() {
        let program = parse_program(
            "(#fn main () u64 (#let values (#array u64 3) (#array (#array u64 3) 10u64 20u64 30u64)) (#let view (#slice u64) (#slice-of (#borrow values))) (#return (#deref (#slice-idx view 1usize))))",
        ).unwrap();
        check_types(&program).unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("slice_bounds_fail"));
        assert!(assembly.contains("cmp rax, rdx"));
    }

    #[test]
    fn slices_keep_their_array_borrow_active() {
        let program = parse_program(
            "(#fn bad () () (#let-mut values (#array u64 2) (#array (#array u64 2) 1u64 2u64)) (#let view (#slice u64) (#slice-of (#borrow values))) (#set values (#array (#array u64 2) 3u64 4u64)) (#return ()))",
        ).unwrap();
        let error = check_types(&program).unwrap_err();
        assert!(error.contains("while it is immutably borrowed"), "{error}");
    }

    #[test]
    fn slices_can_be_passed_to_functions() {
        let program = parse_program(
            "(#fn second ((view (#slice u64))) u64 (#return (#deref (#slice-idx view 1usize)))) (#fn main () u64 (#let values (#array u64 2) (#array (#array u64 2) 11u64 29u64)) (#let view (#slice u64) (#slice-of (#borrow values))) (#return (#call second (: view view))))",
        ).unwrap();
        check_types(&program).unwrap();
        generate_assembly(&program).unwrap();
    }

    #[test]
    fn ranged_slices_typecheck_and_emit_runtime_bounds_checks() {
        let source = "(#fn main () u64 (#let values (#array u64 3) (#array (#array u64 3) 4u64 8u64 15u64)) (#let all (#slice u64) (#slice-of (#borrow values))) (#let middle (#slice u64) (#slice-range all 1usize 2usize)) (#return (#deref (#slice-idx middle 0usize))))";
        let program = parse_program(source).unwrap();
        check_types(&program).unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("slice_range_bounds_fail"));
        assert!(assembly.contains("cmp rcx, r8"));
    }

    #[test]
    fn ranged_slice_cannot_outlive_its_array() {
        let source = "(#fn bad () (#slice u64) (#let values (#array u64 2) (#array (#array u64 2) 1u64 2u64)) (#let all (#slice u64) (#slice-of (#borrow values))) (#return (#slice-range all 0usize 1usize)))";
        let program = parse_program(source).unwrap();
        assert!(check_types(&program).is_err());
    }

    #[test]
    fn mutable_slice_split_produces_writable_disjoint_views() {
        let source = "(#fn main () u64 (#let-mut values (#array u64 4) (#array (#array u64 4) 1u64 2u64 3u64 4u64)) (#let view (#slice-mut u64) (#slice-mut-of (#borrow-mut values))) (#let (#tuple left right) (#tuple (#slice-mut u64) (#slice-mut u64)) (#slice-mut-split view 2usize)) (#deref-set (#slice-mut-idx left 0usize) 17u64) (#deref-set (#slice-mut-idx right 0usize) 25u64) (#let-mut result u64 (#u64.+.wrap (#deref (#slice-mut-idx left 0usize)) (#deref (#slice-mut-idx right 0usize)))) (#forget left) (#forget right) (#return result))";
        let program = parse_program(source).unwrap();
        check_types(&program).unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("slice_mut_split_bounds_fail"));
    }

    #[test]
    fn mutable_slice_split_rejects_parent_use_and_overlapping_mutable_borrow() {
        let parent_use = "(#fn main () () (#let-mut values (#array u64 4) (#array (#array u64 4) 1u64 2u64 3u64 4u64)) (#let view (#slice-mut u64) (#slice-mut-of (#borrow-mut values))) (#let (#tuple left right) (#tuple (#slice-mut u64) (#slice-mut u64)) (#slice-mut-split view 2usize)) (#let again (#slice-mut u64) (#slice-mut-of (#borrow-mut values))) (#return ()))";
        let program = parse_program(parent_use).unwrap();
        assert!(check_types(&program).is_err());

        let overlapping = "(#fn main () () (#let-mut values (#array u64 4) (#array (#array u64 4) 1u64 2u64 3u64 4u64)) (#let first (#slice-mut u64) (#slice-mut-of (#borrow-mut values))) (#let second (#slice-mut u64) (#slice-mut-of (#borrow-mut values))) (#return ()))";
        let program = parse_program(overlapping).unwrap();
        assert!(check_types(&program).is_err());
    }

    #[test]
    fn mutable_slice_supports_nested_splits_and_zero_sized_elements() {
        let nested = "(#fn main () usize (#let-mut values (#array u64 4) (#array (#array u64 4) 1u64 2u64 3u64 4u64)) (#let root (#slice-mut u64) (#slice-mut-of (#borrow-mut values))) (#let (#tuple left right) (#tuple (#slice-mut u64) (#slice-mut u64)) (#slice-mut-split root 3usize)) (#let (#tuple first second) (#tuple (#slice-mut u64) (#slice-mut u64)) (#slice-mut-split left 1usize)) (#let-mut result usize (#slice-mut-len second)) (#forget first) (#forget second) (#forget right) (#return result))";
        let program = parse_program(nested).unwrap();
        check_types(&program).unwrap();
        generate_assembly(&program).unwrap();

        let zero_sized = "(#fn split-zero-sized ((root (#slice-mut ()))) () (#let (#tuple left right) (#tuple (#slice-mut ()) (#slice-mut ())) (#slice-mut-split root 1usize)) (#forget left) (#forget right) (#return ())) (#fn main () () (#return ()))";
        let program = parse_program(zero_sized).unwrap();
        check_types(&program).unwrap();
        generate_assembly(&program).unwrap();
    }

    #[test]
    fn mutable_slice_return_preserves_source_provenance() {
        let valid = "(#fn identity-slice ((source (#slice-mut u64))) (#slice-mut u64) (#return source)) (#fn main () usize (#let-mut values (#array u64 4) (#array (#array u64 4) 1u64 2u64 3u64 4u64)) (#let view (#slice-mut u64) (#slice-mut-of (#borrow-mut values))) (#let returned (#slice-mut u64) (#call identity-slice (: source view))) (#let result usize (#slice-mut-len returned)) (#forget returned) (#return result))";
        let program = parse_program(valid).unwrap();
        check_types(&program).unwrap();

        let invalid = "(#fn bad () (#slice-mut u64) (#let-mut values (#array u64 2) (#array (#array u64 2) 1u64 2u64)) (#let root (#slice-mut u64) (#slice-mut-of (#borrow-mut values))) (#return root))";
        let program = parse_program(invalid).unwrap();
        assert!(check_types(&program).is_err());
    }

    #[test]
    fn atomics_typecheck_explicit_orders_and_reject_invalid_operations() {
        let valid = "(#fn main () u64 (#let-mut counter (#atomic u64) (#atomic-init u64 0u64)) (#atomic-fetch-add (#borrow counter) 1u64 #memory-acq-rel) (#let observed u64 (#atomic-load (#borrow counter) #memory-acquire)) (#atomic-store (#borrow counter) observed #memory-release) (#forget counter) (#return observed))";
        let program = parse_program(valid).unwrap();
        check_types(&program).unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("lock xadd QWORD PTR"));
        assert!(assembly.contains("mov rax, QWORD PTR [rax]"));

        for invalid in [
            "(#fn main () () (#let-mut counter (#atomic u64) (#atomic-init u64 0u64)) (#atomic-load (#borrow counter) #memory-release) (#forget counter) (#return ()))",
            "(#fn main () () (#let-mut counter (#atomic u64) (#atomic-init u64 0u64)) (#atomic-store (#borrow counter) 1u64 #memory-acquire) (#forget counter) (#return ()))",
            "(#fn main () () (#let-mut counter (#atomic u128) (#atomic-init u128 0u128)) (#forget counter) (#return ()))",
        ] {
            let program = parse_program(invalid).unwrap();
            assert!(check_types(&program).is_err());
        }

        let narrow = "(#fn main () u64 (#let-mut byte (#atomic i8) (#atomic-init i8 -1i8)) (#atomic-fetch-add (#borrow byte) 1i8 #memory-relaxed) (#let-mut half (#atomic u16) (#atomic-init u16 0u16)) (#atomic-store (#borrow half) 3u16 #memory-seq-cst) (#forget byte) (#forget half) (#return 42u64))";
        let program = parse_program(narrow).unwrap();
        check_types(&program).unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("lock xadd BYTE PTR"));
        assert!(assembly.contains("movsx rax, al"));
        assert!(assembly.contains("xchg WORD PTR"));
    }

    #[test]
    fn aggregate_layout_word_counts_reject_overflow() {
        let oversized = Type::Array(Box::new(Type::Array(Box::new(Type::U64), usize::MAX)), 2);
        let error =
            codegen::storage_word_count(&oversized, &HashMap::new(), &HashMap::new()).unwrap_err();
        assert!(error.contains("word count overflowed"), "{error}");
    }

    #[test]
    fn stack_usage_report_analyzes_generated_call_paths() {
        let program = parse_program(
            "(#fn leaf () u64 (#return 4u64)) (#fn main () u64 (#let value u64 (#call leaf (:))) (#return value))",
        )
        .unwrap();
        check_types(&program).unwrap();
        let assembly = generate_assembly(&program).unwrap();
        let report = stack_usage_report(&assembly).unwrap();
        assert!(report.contains("main: at most"), "{report}");
        assert!(report.contains("main -> leaf"), "{report}");
        assert!(!report.contains("total is unknown"), "{report}");
    }

    #[test]
    fn stack_usage_report_includes_bounded_kernel_thread_entries() {
        let program = parse_program(include_str!("../examples/thread_spawn.lim")).unwrap();
        check_types(&program).unwrap();
        let assembly = generate_assembly(&program).unwrap();
        let report = stack_usage_report(&assembly).unwrap();
        assert!(
            report.contains(".Llim_thread_entry_ReadValueTask: at most"),
            "{report}"
        );
        assert!(report.contains("main: at most"), "{report}");
        assert!(!report.contains("total is unknown"), "{report}");
        assert!(!report.contains("pthread_create"), "{report}");
    }
}
