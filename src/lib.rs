#![doc = include_str!("../docs/language.md")]

use std::{
    collections::{BTreeSet, HashMap, HashSet},
    env, fmt, fs,
    path::{Path, PathBuf},
};

mod borrowcheck;
mod codegen;
mod generator;
mod linearcheck;
mod typecheck;
mod unsafecheck;

pub use codegen::generate_assembly;
pub use typecheck::{check_types, type_has_auto_trait};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub line: usize,
    pub column: usize,
}

impl Span {
    const fn new(start: usize, end: usize, line: usize, column: usize) -> Self {
        Self {
            start,
            end,
            line,
            column,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TokenKind {
    LParen,
    RParen,
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
        } else {
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
                || matches!(byte, b'(' | b')' | b'\'' | b'`' | b',' | b'"' | b'@' | b';')
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
                None => return Err(self.error("unterminated string")),
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
    /// The generated-code sigil in source, e.g. `(@optional T T?)`.
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
    RawPointer {
        mutable: bool,
        target: Box<Type>,
    },
    /// Inline single-threaded interior-mutable scalar storage.
    Cell(Box<Type>),
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
    pub type_parameters: Vec<String>,
    pub parameters: Vec<Parameter>,
    pub return_type: Type,
    pub body: Vec<Statement>,
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
pub enum AutoTrait {
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
        type_parameters: Vec<String>,
        fields: Vec<Field>,
    },
    Enum {
        name: String,
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
    UnsafeAutoTraitImpl {
        trait_kind: AutoTrait,
        type_name: String,
    },
    ThreadTask {
        name: String,
        worker: String,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Program {
    pub items: Vec<Item>,
}

/// Compile-time key/value settings used by `#cfg-*` forms.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompileConfig {
    values: HashMap<String, String>,
}

impl Default for CompileConfig {
    fn default() -> Self {
        let platform = env::consts::OS;
        Self {
            values: HashMap::from([("platform".into(), platform.into())]),
        }
    }
}

impl CompileConfig {
    /// Set or override a configuration key, such as `feature=sorting` or
    /// `platform=linux`.
    pub fn set(&mut self, key: impl Into<String>, value: impl Into<String>) {
        self.values.insert(key.into(), value.into());
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
    parse_program_in_directory(source, &base, &CompileConfig::default(), None)
}

/// Parse a Lim program using explicit compile-time configuration values.
pub fn parse_program_with_config(source: &str, config: &CompileConfig) -> Result<Program, String> {
    let base =
        env::current_dir().map_err(|error| format!("cannot get current directory: {error}"))?;
    parse_program_in_directory(source, &base, config, None)
}

/// Parse a Lim program while resolving file imports relative to `source_path`.
pub fn parse_program_from_path(source: &str, source_path: &Path) -> Result<Program, String> {
    let base = source_path.parent().unwrap_or_else(|| Path::new("."));
    parse_program_in_directory(source, base, &CompileConfig::default(), None)
}

/// Parse a Lim program while resolving imports and evaluating cfg forms using `config`.
pub fn parse_program_from_path_with_config(
    source: &str,
    source_path: &Path,
    config: &CompileConfig,
) -> Result<Program, String> {
    let base = source_path.parent().unwrap_or_else(|| Path::new("."));
    parse_program_in_directory(source, base, config, None)
}

/// Parse a source file using cfg settings and a persistent generator cache.
pub fn parse_program_from_path_with_config_and_cache(
    source: &str,
    source_path: &Path,
    config: &CompileConfig,
    cache_directory: &Path,
) -> Result<Program, String> {
    let base = source_path.parent().unwrap_or_else(|| Path::new("."));
    parse_program_in_directory(source, base, config, Some(cache_directory))
}

fn parse_program_in_directory(
    source: &str,
    base: &Path,
    config: &CompileConfig,
    cache_directory: Option<&Path>,
) -> Result<Program, String> {
    let loaded = load_imports(source, base, config)?;
    let expressions = expand_cfg_forms(
        generator::expand_with_generated_cached(loaded, cache_directory)?.0,
        config,
    )?;
    let mut items = Vec::with_capacity(expressions.len());
    for expression in expressions {
        validate_prefixed_forms(&expression.expr)?;
        let expression = normalize_keywords(expression.expr);
        if let Expr::List(forms) = &expression {
            if matches!(forms.first(), Some(Expr::At)) {
                items.extend(parse_generated_items(forms)?);
                continue;
            }
        }
        items.push(parse_item(&expression)?);
    }
    rename_shadowed_locals(&mut items);
    let mut items = specialize_generic_types(items)?;
    normalize_struct_literals(&mut items)?;
    Ok(Program { items })
}

/// Turn keyed struct construction into the ordinary positional constructor
/// representation used by the type checker and backends.  Keeping this as a
/// source-level normalization means every later compiler phase gets exactly
/// the same semantics as `(Type value1 value2 ...)`.
fn normalize_struct_literals(items: &mut [Item]) -> Result<(), String> {
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
                for statement in &mut function.body {
                    normalize_struct_statement(statement, &structs)?;
                }
            }
            Item::Let { value, .. } | Item::Static { value, .. } => {
                normalize_struct_expr(value, &structs)?;
            }
            _ => {}
        }
    }
    Ok(())
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

fn rename_shadowed_locals(items: &mut [Item]) {
    let globals = items
        .iter()
        .filter_map(|item| match item {
            Item::Let { name, .. } | Item::Static { name, .. } => Some(name.clone()),
            _ => None,
        })
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
            rename_function_locals(function, &globals, &variants);
        }
    }
}

fn rename_function_locals(
    function: &mut Function,
    globals: &HashSet<String>,
    variants: &HashSet<String>,
) {
    let mut bindings = function
        .parameters
        .iter()
        .map(|parameter| (parameter.name.clone(), parameter.name.clone()))
        .collect::<HashMap<_, _>>();
    let mut used = bindings.values().cloned().collect::<HashSet<_>>();
    used.extend(globals.iter().cloned());
    let mut next_id = 0usize;
    rename_statements(
        &mut function.body,
        &mut bindings,
        &mut used,
        &mut next_id,
        globals,
        variants,
    );
}

fn fresh_binding(
    name: &str,
    bindings: &HashMap<String, String>,
    used: &mut HashSet<String>,
    next_id: &mut usize,
    globals: &HashSet<String>,
) -> String {
    if !bindings.contains_key(name) && !globals.contains(name) {
        used.insert(name.to_owned());
        return name.to_owned();
    }
    loop {
        let candidate = format!("__lim_shadow_{}_{}", *next_id, name);
        *next_id += 1;
        if used.insert(candidate.clone()) {
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
                "as" | "size-of" | "align-of" => {
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

fn is_builtin_form(name: &str) -> bool {
    matches!(
        name,
        "type"
            | "fn"
            | "extern-fn"
            | "struct"
            | "enum"
            | "let"
            | "let-else"
            | "const"
            | "static"
            | "unsafe-impl"
            | "if"
            | "if-let"
            | "while"
            | "while-let"
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
            | "when"
            | "range"
            | "or"
            | "as"
            | "array"
            | "array-repeat"
            | "tuple"
            | "index"
            | "get"
            | "size-of"
            | "align-of"
            | "assert"
            | "debug-assert"
            | "panic"
            | "unreachable"
            | "literal"
            | "borrow"
            | "borrow-mut"
            | "ref"
            | "ref-mut"
            | "deref"
            | "deref-set"
            | "mut"
            | "unsafe"
            | "addr-of"
            | "addr-of-mut"
            | "ptr-read"
            | "ptr-write"
            | "cell"
            | "cell-get"
            | "cell-set"
            | "clone"
            | "drop"
            | "ptr"
            | "ptr-mut"
            | "generator"
            | "import"
            | "import-external"
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

fn normalize_keywords(expression: Expr) -> Expr {
    match expression {
        Expr::Symbol(name) => {
            Expr::Symbol(name.strip_prefix('#').map_or(name.clone(), str::to_owned))
        }
        Expr::List(items) => Expr::List(items.into_iter().map(normalize_keywords).collect()),
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

fn load_imports(
    source: &str,
    base: &Path,
    config: &CompileConfig,
) -> Result<Vec<SpannedExpr>, String> {
    let mut active = Vec::new();
    let mut loaded = HashSet::new();
    load_imports_inner(source, base, &mut active, &mut loaded, config)
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

fn eval_cfg(expression: &Expr, config: &CompileConfig) -> Result<bool, String> {
    let Expr::List(items) = expression else {
        return Err("cfg condition must be a (#cfg-...) form".into());
    };
    let Some(Expr::Symbol(operator)) = items.first() else {
        return Err("cfg condition must start with a #cfg-* operator".into());
    };
    match operator.as_str() {
        "#cfg-is" if items.len() == 3 => {
            let Expr::Symbol(key) = &items[1] else {
                return Err("#cfg-is key must be a keyword such as #platform".into());
            };
            let key = key.strip_prefix('#').unwrap_or(key);
            let actual = config
                .values
                .get(key)
                .ok_or_else(|| format!("unknown cfg key '#{key}'"))?;
            Ok(actual == &cfg_value(&items[2])?)
        }
        "#cfg-and" if items.len() >= 2 => items[1..]
            .iter()
            .try_fold(true, |result, item| Ok(result && eval_cfg(item, config)?)),
        "#cfg-or" if items.len() >= 2 => items[1..]
            .iter()
            .try_fold(false, |result, item| Ok(result || eval_cfg(item, config)?)),
        "#cfg-not" if items.len() == 2 => Ok(!eval_cfg(&items[1], config)?),
        "#cfg-is" => Err("#cfg-is requires a key and a value".into()),
        "#cfg-and" | "#cfg-or" => Err(format!("{operator} requires at least one condition")),
        "#cfg-not" => Err("#cfg-not requires exactly one condition".into()),
        _ => Err(format!("unsupported cfg condition '{operator}'")),
    }
}

fn expand_cfg_forms(
    forms: Vec<SpannedExpr>,
    config: &CompileConfig,
) -> Result<Vec<SpannedExpr>, String> {
    let mut expanded = Vec::new();
    for form in forms {
        let Expr::List(items) = &form.expr else {
            expanded.push(form);
            continue;
        };
        if !matches!(items.first(), Some(Expr::Symbol(name)) if name == "#cfg-if") {
            if matches!(items.first(), Some(Expr::Symbol(name)) if name == "#cfg-else") {
                return Err("#cfg-else is only valid as the final branch of #cfg-if".into());
            }
            expanded.push(form);
            continue;
        }
        if items.len() < 3 {
            return Err("#cfg-if requires a condition and at least one form".into());
        }
        let condition = eval_cfg(&items[1], config)?;
        let mut else_forms = None;
        let mut then_forms = Vec::new();
        for branch in &items[2..] {
            if let Expr::List(branch_items) = branch {
                if matches!(branch_items.first(), Some(Expr::Symbol(name)) if name == "#cfg-else") {
                    if else_forms.is_some() || branch_items.len() < 2 {
                        return Err(
                            "#cfg-else must occur once and contain at least one form".into()
                        );
                    }
                    else_forms = Some(branch_items[1..].to_vec());
                    continue;
                }
            }
            if else_forms.is_some() {
                return Err("#cfg-else must be the final #cfg-if branch".into());
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
            })
            .collect();
        expanded.extend(expand_cfg_forms(selected, config)?);
    }
    Ok(expanded)
}

fn load_imports_inner(
    source: &str,
    base: &Path,
    active: &mut Vec<PathBuf>,
    loaded: &mut HashSet<String>,
    config: &CompileConfig,
) -> Result<Vec<SpannedExpr>, String> {
    let expressions = parse(source).map_err(|error| format!("{}: {error}", base.display()))?;
    let expressions = expand_cfg_forms(expressions, config)?;
    let mut result = Vec::new();
    for expression in expressions {
        let Some(specification) = import_form(&expression.expr)? else {
            result.push(expression);
            continue;
        };
        let unresolved_path = base.join(specification.path);
        let path = fs::canonicalize(&unresolved_path).map_err(|error| {
            format!(
                "{}:{}:{}: cannot resolve import '{}': {error}",
                base.display(),
                expression.span.line,
                expression.span.column,
                unresolved_path.display()
            )
        })?;
        if active.contains(&path) {
            let mut cycle = active
                .iter()
                .map(|entry| entry.display().to_string())
                .collect::<Vec<_>>();
            cycle.push(path.display().to_string());
            return Err(format!("import cycle: {}", cycle.join(" -> ")));
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
        let imported_source = fs::read_to_string(&path)
            .map_err(|error| format!("cannot read import '{}': {error}", path.display()))?;
        active.push(path.clone());
        let mut imported = load_imports_inner(
            &imported_source,
            path.parent().unwrap_or_else(|| Path::new(".")),
            active,
            loaded,
            config,
        )?;
        active.pop();
        if let Some(prefix) = specification.prefix {
            let generator_names = imported
                .iter()
                .filter_map(|form| match &form.expr {
                    Expr::List(items)
                        if matches!(items.first(), Some(Expr::Symbol(keyword)) if keyword == "#generator" || keyword == "#gn-fn") =>
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
        let path = fs::canonicalize(path)
            .map_err(|error| format!("cannot resolve source '{}': {error}", path.display()))?;
        if !visited.insert(path.clone()) {
            return Ok(());
        }
        let source = fs::read_to_string(&path)
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
    is_builtin_form(name)
        || is_operator_symbol(name)
        || matches!(
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
/// builds an inspectable cache of generated Lim source under .lim/.
pub fn write_generated_sources(source: &str, directory: &Path) -> Result<(), String> {
    let base =
        env::current_dir().map_err(|error| format!("cannot get current directory: {error}"))?;
    write_generated_sources_in_directory(source, &base, directory, &CompileConfig::default(), None)
}

/// Materialize generated source while resolving imports relative to `source_path`.
pub fn write_generated_sources_from_path(
    source: &str,
    source_path: &Path,
    directory: &Path,
) -> Result<(), String> {
    let base = source_path.parent().unwrap_or_else(|| Path::new("."));
    write_generated_sources_in_directory(source, base, directory, &CompileConfig::default(), None)
}

/// Materialize generated source using the same cfg values as compilation.
pub fn write_generated_sources_from_path_with_config(
    source: &str,
    source_path: &Path,
    directory: &Path,
    config: &CompileConfig,
) -> Result<(), String> {
    let base = source_path.parent().unwrap_or_else(|| Path::new("."));
    write_generated_sources_in_directory(source, base, directory, config, None)
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
    write_generated_sources_in_directory(source, base, directory, config, Some(cache_directory))
}

fn write_generated_sources_in_directory(
    source: &str,
    base: &Path,
    directory: &Path,
    config: &CompileConfig,
    cache_directory: Option<&Path>,
) -> Result<(), String> {
    let expressions = load_imports(source, base, config)?;
    let (expanded, user_generated) =
        generator::expand_with_generated_cached(expressions.clone(), cache_directory)?;
    let expanded = expand_cfg_forms(expanded, config)?;
    let mut generated = Vec::new();
    for expression in expanded {
        let Expr::List(forms) = expression.expr else {
            continue;
        };
        if !matches!(forms.first(), Some(Expr::At)) {
            continue;
        }
        let kind = expect_symbol(forms.get(1), "generated declaration name")?;
        if !matches!(kind, "optional" | "result") {
            continue;
        }
        let item = parse_generated_item(&forms)?;
        let Item::Enum { name, variants, .. } = item else {
            continue;
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
            generated.push(format!(
                "(#enum {name} (({first_name} {first_source}) {second_name}))\n(#fn {name}-construct ((value {first_source})) {name} (#return ({first_name} value)))\n(#fn {name}-is-some ((value {name})) bool (#return (#match value (({first_name} _) true) ({second_name} false))))\n(#fn {name}-unwrap-or ((value {name}) (fallback {first_source})) {first_source} (#return (#match value (({first_name} payload) payload) ({second_name} fallback))))\n",
            ));
        } else {
            let second = variants
                .get(1)
                .and_then(|variant| variant.fields.first())
                .ok_or_else(|| "result expansion has no error payload type".to_owned())?;
            let second_source = type_source(second);
            generated.push(format!(
                "(#enum {name} (({first_name} {first_source}) ({second_name} {second_source})))\n(#fn {name}-ok ((value {first_source})) {name} (#return ({first_name} value)))\n(#fn {name}-err ((error {second_source})) {name} (#return ({second_name} error)))\n(#fn {name}-is-ok ((value {name})) bool (#return (#match value (({first_name} _) true) (({second_name} _) false))))\n(#fn {name}-unwrap-or ((value {name}) (fallback {first_source})) {first_source} (#return (#match value (({first_name} payload) payload) (({second_name} _) fallback))))\n(#fn {name}-unwrap-err-or ((value {name}) (fallback {second_source})) {second_source} (#return (#match value (({first_name} _) fallback) (({second_name} error) error))))\n",
            ));
        }
    }
    if generated.is_empty() && user_generated.is_empty() {
        return Ok(());
    }
    fs::create_dir_all(directory)
        .map_err(|error| format!("cannot create generated-code directory: {error}"))?;
    for (index, source) in generated.iter().enumerate() {
        let prefix = if source.contains("-is-some") {
            "optional"
        } else {
            "result"
        };
        let path = directory.join(format!("{prefix}-{index}.lim"));
        write_if_changed(&path, source)
            .map_err(|error| format!("cannot write generated source: {error}"))?;
    }
    for (index, expression) in user_generated.iter().enumerate() {
        let source = expression_source(expression)?;
        let path = directory.join(format!("generator-{index}.lim"));
        write_if_changed(&path, &format!("{source}\n"))
            .map_err(|error| format!("cannot write generated source: {error}"))?;
    }
    Ok(())
}

fn write_if_changed(path: &Path, contents: &str) -> std::io::Result<()> {
    if fs::read_to_string(path).is_ok_and(|existing| existing == contents) {
        return Ok(());
    }
    fs::write(path, contents)
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
        Expr::Symbol(name) => Ok(name.clone()),
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
        Type::RawPointer { mutable, target } => format!(
            "(#{} {})",
            if *mutable { "ptr-mut" } else { "ptr" },
            type_source(target)
        ),
        Type::Cell(target) => format!("(#cell {})", type_source(target)),
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
                    name: _, fields, ..
                } => Item::Struct {
                    name: specialized.clone(),
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
                    name: _, variants, ..
                } => Item::Enum {
                    name: specialized.clone(),
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

fn specialize_generic_types(mut items: Vec<Item>) -> Result<Vec<Item>, String> {
    for item in &items {
        let Item::UnsafeAutoTraitImpl {
            trait_kind,
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
            return Err(format!(
                "unsafe {:?} implementation refers to undeclared type '{type_name}'",
                trait_kind
            ));
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
            return Err(format!(
                "unsafe {:?} implementations require a nominal struct or enum type, not alias '{type_name}'",
                trait_kind
            ));
        }
        if is_generic {
            return Err(format!(
                "unsafe {:?} implementation for generic type '{type_name}' is not supported",
                trait_kind
            ));
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
                    .map(|statement| {
                        specialize_statement(
                            statement,
                            &HashMap::new(),
                            &templates,
                            &mut names,
                            &mut generated,
                        )
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
                *ty = specialize_type(ty, &HashMap::new(), &templates, &mut names, &mut generated)?;
                *value = specialize_expr(
                    value,
                    &HashMap::new(),
                    &templates,
                    &mut names,
                    &mut generated,
                )?;
            }
            Item::Static { ty, value, .. } => {
                *ty = specialize_type(ty, &HashMap::new(), &templates, &mut names, &mut generated)?;
                *value = specialize_expr(
                    value,
                    &HashMap::new(),
                    &templates,
                    &mut names,
                    &mut generated,
                )?;
            }
            Item::UnsafeAutoTraitImpl { .. } => {}
            Item::ThreadTask { .. } => {}
        }
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
        "fn" => Ok(Item::Function(parse_function(items, false)?)),
        "extern-fn" => Ok(Item::Function(parse_function(items, true)?)),
        "struct" => {
            let (type_parameters, field_index) = parse_type_parameters(items, 2)?;
            Ok(Item::Struct {
                name: expect_symbol(items.get(1), "struct name")?.to_owned(),
                type_parameters: type_parameters.clone(),
                fields: parse_struct_fields_at(items, field_index, &type_parameters)?,
            })
        }
        "enum" => {
            let (type_parameters, variant_index) = parse_type_parameters(items, 2)?;
            Ok(Item::Enum {
                name: expect_symbol(items.get(1), "enum name")?.to_owned(),
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
        "unsafe-impl" => {
            if items.len() != 3 {
                return Err("unsafe-impl requires (#unsafe-impl #send-or-sync Type)".into());
            }
            let trait_kind = match expect_symbol(items.get(1), "auto-trait name")? {
                "send" => AutoTrait::Send,
                "sync" => AutoTrait::Sync,
                other => return Err(format!("unsupported unsafe auto-trait '{other}'")),
            };
            let type_name = expect_symbol(items.get(2), "auto-trait type")?.to_owned();
            Ok(Item::UnsafeAutoTraitImpl {
                trait_kind,
                type_name,
            })
        }
        other => Err(format!("unknown top-level form '{other}'")),
    }
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
                    "generated declaration must have the form (@optional Type OptionalType)".into(),
                );
            }
            let payload = parse_type(items.get(2))?;
            let name = expect_symbol(items.get(3), "generated optional type name")?.to_owned();
            Ok(Item::Enum {
                name: name.clone(),
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
                    "generated declaration must have the form (@result OkType ErrType ResultType)"
                        .into(),
                );
            }
            let ok = parse_type(items.get(2))?;
            let error = parse_type(items.get(3))?;
            let name = expect_symbol(items.get(4), "generated result type name")?.to_owned();
            Ok(Item::Enum {
                name: name.clone(),
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
                    "generated declaration must have the form (@thread-spawn TaskType worker-function)".into(),
                );
            }
            Ok(Item::ThreadTask {
                name: expect_symbol(items.get(2), "thread task type name")?.to_owned(),
                worker: expect_symbol(items.get(3), "thread worker function")?.to_owned(),
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
        return Ok(vec![parse_generated_item(items)?]);
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
    Ok((result, index + 1))
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

fn parse_function(items: &[Expr], external: bool) -> Result<Function, String> {
    if items.len() < 4 {
        return Err("fn requires a name, parameter list, return type, and body".into());
    }
    let name = expect_symbol(items.get(1), "function name")?.to_owned();
    let (type_parameters, parameter_index, return_index, body_index) =
        if let Some(Expr::List(generic_items)) = items.get(2) {
            if !generic_items.is_empty()
                && generic_items
                    .iter()
                    .all(|item| matches!(item, Expr::Symbol(_)))
            {
                let mut names = Vec::with_capacity(generic_items.len());
                for item in generic_items {
                    let name = expect_symbol(Some(item), "generic type parameter")?.to_owned();
                    if names.iter().any(|existing| existing == &name) {
                        return Err(format!("duplicate generic type parameter '{name}'"));
                    }
                    names.push(name);
                }
                (names, 3, 4, 5)
            } else {
                (Vec::new(), 2, 3, 4)
            }
        } else {
            (Vec::new(), 2, 3, 4)
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
    } else {
        for expression in &items[body_index..] {
            body.push(replace_generic_statement(
                &parse_statement(expression)?,
                &type_parameters,
            ));
        }
    }
    if !external && !matches!(body.last(), Some(Statement::Return(Some(_)))) {
        return Err(
            "functions require an explicit (#return value) as their final statement".into(),
        );
    }
    Ok(Function {
        name,
        external,
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
        let statement = parse_statement(&items[2])?;
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
        if items.len() == 2 && matches!(&items[0], Expr::Symbol(name) if name == "cell") {
            return Ok(Type::Cell(Box::new(parse_type(items.get(1))?)));
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
    Ok(Type::from_name(expect_symbol(expression, "type")?))
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
}

impl<'a> Parser<'a> {
    fn new(tokens: &'a [Token]) -> Self {
        Self { tokens, index: 0 }
    }

    fn run(mut self) -> Result<Vec<SpannedExpr>, ParseError> {
        let mut expressions = Vec::new();
        while self.index < self.tokens.len() {
            expressions.push(self.expression()?);
        }
        Ok(expressions)
    }

    fn expression(&mut self) -> Result<SpannedExpr, ParseError> {
        let token = self
            .tokens
            .get(self.index)
            .ok_or_else(|| self.error("expected expression", self.eof_span()))?;
        match &token.kind {
            TokenKind::LParen => self.list(),
            TokenKind::RParen => {
                Err(self.error("unexpected ')'; expected an expression", token.span))
            }
            TokenKind::Quote => {
                self.index += 1;
                let quoted = self
                    .expression()
                    .map_err(|_| self.error("expected expression after quote", token.span))?;
                Ok(SpannedExpr {
                    expr: Expr::Quote(Box::new(quoted.expr)),
                    span: Span::new(
                        token.span.start,
                        quoted.span.end,
                        token.span.line,
                        token.span.column,
                    ),
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
                let expr = match token.kind {
                    TokenKind::QuasiQuote => Expr::QuasiQuote(Box::new(nested.expr)),
                    TokenKind::Unquote => Expr::Unquote(Box::new(nested.expr)),
                    TokenKind::UnquoteSplicing => Expr::UnquoteSplicing(Box::new(nested.expr)),
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
                })
            }
            TokenKind::At => {
                self.index += 1;
                Ok(SpannedExpr {
                    expr: Expr::At,
                    span: token.span,
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
                    });
                }
                Ok(SpannedExpr {
                    expr: Expr::Symbol(value.clone()),
                    span: token.span,
                })
            }
            TokenKind::Integer(value) => {
                self.index += 1;
                Ok(SpannedExpr {
                    expr: Expr::Integer(*value),
                    span: token.span,
                })
            }
            TokenKind::UnsignedInteger(value) => {
                self.index += 1;
                Ok(SpannedExpr {
                    expr: Expr::UnsignedInteger(*value),
                    span: token.span,
                })
            }
            TokenKind::Float(value) => {
                self.index += 1;
                Ok(SpannedExpr {
                    expr: Expr::Float(value.clone()),
                    span: token.span,
                })
            }
            TokenKind::Char(value) => {
                self.index += 1;
                Ok(SpannedExpr {
                    expr: Expr::Char(*value),
                    span: token.span,
                })
            }
            TokenKind::String(value) => {
                self.index += 1;
                Ok(SpannedExpr {
                    expr: Expr::String(value.clone()),
                    span: token.span,
                })
            }
        }
    }

    fn list(&mut self) -> Result<SpannedExpr, ParseError> {
        let start = self.tokens[self.index].span;
        self.index += 1;
        let mut items = Vec::new();
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
                    });
                }
                Some(_) => items.push(self.expression()?.expr),
                None => return Err(self.error("unterminated list; expected ')'", self.eof_span())),
            }
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
    fn lexes_function_and_generated_forms() {
        let tokens =
            lex("(#fn add ((left i32) (right i32)) i32 (#return (#u64.+.wrap  left right)))")
                .unwrap();
        assert_eq!(tokens[0].kind, TokenKind::LParen);
        assert_eq!(tokens[1].kind, TokenKind::Symbol("#fn".into()));
        assert_eq!(tokens[6].kind, TokenKind::Symbol("i32".into()));

        let generated = lex("(@optional MyType MyType?)").unwrap();
        assert_eq!(generated[1].kind, TokenKind::At);
        assert_eq!(generated[4].kind, TokenKind::Symbol("MyType?".into()));
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
            "(#generator aliases (pairs) (#gn-for-each pair pairs (#gn-list (#gn-symbol \"#type\") (#gn-first pair) (#gn-first (#gn-rest pair))))) (@aliases ((Byte u8) (Word u16))) (@aliases ((Byte u8) (Word u16))) (#fn main () u64 (#return 42))",
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
        let source = "(#gn-fn make-type-form (name target) (#gn-list (#gn-symbol \"#type\") name target)) (#gn-fn make-alias (name target) (#gn-call make-type-form name target)) (#generator aliases (pairs) (#gn-for-each pair pairs (#gn-call make-alias (#gn-first pair) (#gn-first (#gn-rest pair))))) (@aliases ((Byte u8) (Word u16))) (#fn main () u64 (#return 42))";
        let program = parse_program(source).unwrap();
        assert_eq!(program.items.len(), 3);

        let recursive = parse_program(
            "(#gn-fn first (x) (#gn-call second x)) (#gn-fn second (x) (#gn-call first x)) (#generator make (x) (#gn-call first x)) (@make value)",
        )
        .unwrap_err();
        assert!(recursive.contains("recursive generator function calls are not allowed"));
    }

    #[test]
    fn generator_functions_return_syntax_not_predicate_values() {
        let error = parse_program(
            "(#gn-fn invalid (value) (#gn-symbol? value)) (#generator make () (#gn-call invalid name)) (@make)",
        )
        .unwrap_err();
        assert!(error.contains("must return a syntax value"));
    }

    #[test]
    fn generator_quasiquote_unquotes_and_splices_syntax() {
        let source = "(#gn-fn emit-alias (name) `(#type ,name u64)) (#generator aliases (names) `(,@(#gn-for-each name names (#gn-call emit-alias name)))) (@aliases (First Second)) (#fn main () u64 (#return 42))";
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
            parse_program("(#generator bad () `((#type X u64) ,@not-a-list)) (@bad)").unwrap_err();
        assert!(non_list.contains("unquote-splicing requires list syntax"));
        let outside_template = parse_program("(#generator bad (x) ,x) (@bad value)").unwrap_err();
        assert!(outside_template.contains("only valid inside a backtick syntax template"));
    }

    #[test]
    fn generator_errors_and_recursion_are_reported() {
        let error = parse_program("(#generator fail () (#gn-error \"unsupported input\")) (@fail)")
            .unwrap_err();
        assert!(error.contains("generator error: unsupported input"));

        let recursive =
            parse_program("(#generator repeat () (#gn-list (@repeat))) (@repeat)").unwrap_err();
        assert!(recursive.contains("recursive generator expansion is not allowed"));

        let unknown = parse_program("(#generator typo () (#gn-unknown 1))\n(@typo)").unwrap_err();
        assert!(unknown.contains("unknown generator builtin '#gn-unknown'"));
        assert!(unknown.contains("defined at 1:1"));
        assert!(unknown.contains("2:1: generator expansion"));
    }

    #[test]
    fn loads_internal_and_prefixes_external_imports() {
        let directory = std::env::temp_dir().join(format!("lim-imports-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        let module_path = directory.join("definitions.lim");
        std::fs::write(
            &module_path,
            "(#struct Thing ((value u64))) (#fn read-value ((thing Thing)) u64 (#return (#get thing value))) (#generator make-alias (alias target) (#gn-list (#gn-list (#gn-symbol \"#type\") alias target))) (@make-alias GeneratedAlias u64)",
        )
        .unwrap();
        let root_path = directory.join("root.lim");
        let program_source = "(#import \"definitions.lim\") (#import-external \"definitions.lim\" ext-) (#import-external \"definitions.lim\" ext-) (#fn main () u64 (#return (#u64.+.wrap (read-value (Thing 20)) (ext-read-value (ext-Thing 22)))))";
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

        let shared_write = parse_program(
            "(#fn main () u64 (#let-mut value u64 40) (#return (#borrow value (#block (#set value 42) value))))",
        )
        .unwrap();
        assert!(check_types(&shared_write)
            .unwrap_err()
            .contains("immutably borrowed"));
    }

    #[test]
    fn supports_single_threaded_interior_mutable_cells() {
        let program = parse_program(
            "(#fn main () u64 (#let counter (#cell u64) (#cell 40)) (#cell-set counter (#u64.+.wrap (#cell-get counter) 2)) (#return (#cell-get counter)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok(), "{:?}", check_types(&program));
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("lea rax, [rbp-"));
        assert!(assembly.contains("mov QWORD PTR [r11], rax"));
        assert!(assembly.contains("mov rax, QWORD PTR [rax]"));

        let invalid = parse_program(
            "(#fn main () u64 (#let counter (#cell u64) (#cell 40)) (#cell-set counter true) (#return 0))",
        )
        .unwrap();
        assert!(check_types(&invalid)
            .unwrap_err()
            .contains("cell-set value"));
    }

    #[test]
    fn supports_shared_references_to_aggregate_allocator_state() {
        let program = parse_program(
            "(#struct ArenaState ((cursor (#cell u64)))) (#fn ArenaState-advance ((arena (#ref ArenaState))) u64 (#cell-set (#get arena cursor) (#u64.+.wrap (#cell-get (#get arena cursor)) 1)) (#return (#cell-get (#get arena cursor)))) (#fn main () u64 (#return 0))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok(), "{:?}", check_types(&program));
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("mov rax, QWORD PTR [rbp-"));
        assert!(assembly.contains("mov QWORD PTR [r11], rax"));

        let runnable = parse_program(
            "(#struct ArenaState ((cursor (#cell u64)))) (#fn main () u64 (#let-mut arena ArenaState (ArenaState (#cell 40))) (#let allocator (#ref ArenaState) (#borrow arena)) (#cell-set (#get allocator cursor) (#u64.+.wrap (#cell-get (#get allocator cursor)) 2)) (#return (#cell-get (#get allocator cursor))))",
        )
        .unwrap();
        assert!(
            check_types(&runnable).is_ok(),
            "{:?}",
            check_types(&runnable)
        );
        assert!(generate_assembly(&runnable).is_ok());

        let reference_to_global = parse_program(
            "(#struct Point ((x u64) (y u64))) (#static Origin Point (Point 20 22)) (#fn origin () (#ref Point) (#return (#unsafe (#borrow Origin)))) (#fn main () u64 (#return (#get (#origin) x)))",
        )
        .unwrap();
        assert!(check_types(&reference_to_global).is_ok());
        assert!(generate_assembly(&reference_to_global).is_ok());

        let aggregate_deref = parse_program(
            "(#struct Point ((x u64))) (#fn main () u64 (#let-mut point Point (Point 42)) (#return (#get (#deref (#borrow point)) x)))",
        )
        .unwrap();
        assert!(check_types(&aggregate_deref)
            .unwrap_err()
            .contains("use get to project aggregate fields"));

        let stored = parse_program(
            "(#struct Allocator ((cursor u64))) (#struct VecWithAllocator ((allocator (#ref Allocator)) (length u64))) (#fn main () u64 (#let-mut allocator Allocator (Allocator 0)) (#let-mut vector VecWithAllocator (VecWithAllocator (#borrow allocator) 0)) (#set-field allocator cursor 1) (#return 0))",
        )
        .unwrap();
        assert!(check_types(&stored)
            .unwrap_err()
            .contains("immutably borrowed"));

        let escaping = parse_program(
            "(#struct Allocator ((cursor u64))) (#struct VecWithAllocator ((allocator (#ref Allocator)) (length u64))) (#fn make () VecWithAllocator (#let-mut allocator Allocator (Allocator 0)) (#let vector VecWithAllocator (VecWithAllocator (#borrow allocator) 0)) (#return vector))",
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
        let program = parse_program(
            "(#struct Plain ((value u64))) (#struct HasCell ((value (#cell u64)))) (#struct HasPointer ((value (#ptr u64)))) (#struct HasSharedReference ((value (#ref Plain)))) (#struct PromisedSend ((value (#ptr u64)))) (#struct PromisedSync ((value (#cell u64)))) (#unsafe-impl #send PromisedSend) (#unsafe-impl #sync PromisedSync)",
        )
        .unwrap();
        check_types(&program).unwrap();
        let has = |name: &str, trait_kind: AutoTrait| {
            type_has_auto_trait(&program, &Type::Named(name.to_owned()), trait_kind).unwrap()
        };

        assert!(has("Plain", AutoTrait::Send));
        assert!(has("Plain", AutoTrait::Sync));
        assert!(has("HasCell", AutoTrait::Send));
        assert!(!has("HasCell", AutoTrait::Sync));
        assert!(!has("HasPointer", AutoTrait::Send));
        assert!(!has("HasPointer", AutoTrait::Sync));
        assert!(has("HasSharedReference", AutoTrait::Send));
        assert!(has("HasSharedReference", AutoTrait::Sync));
        assert!(has("PromisedSend", AutoTrait::Send));
        assert!(!has("PromisedSend", AutoTrait::Sync));
        assert!(has("PromisedSync", AutoTrait::Sync));

        assert!(type_has_auto_trait(
            &program,
            &Type::Reference {
                mutable: false,
                target: Box::new(Type::Named("Plain".to_owned())),
            },
            AutoTrait::Send,
        )
        .unwrap());
        assert!(!type_has_auto_trait(
            &program,
            &Type::Reference {
                mutable: false,
                target: Box::new(Type::Named("HasCell".to_owned())),
            },
            AutoTrait::Send,
        )
        .unwrap());
        assert!(type_has_auto_trait(
            &program,
            &Type::Reference {
                mutable: true,
                target: Box::new(Type::Named("Plain".to_owned())),
            },
            AutoTrait::Send,
        )
        .unwrap());
        assert!(!type_has_auto_trait(
            &program,
            &Type::Reference {
                mutable: true,
                target: Box::new(Type::Named("HasCell".to_owned())),
            },
            AutoTrait::Sync,
        )
        .unwrap());

        let duplicate = parse_program(
            "(#struct Value ((value u64))) (#unsafe-impl #send Value) (#unsafe-impl #send Value)",
        )
        .unwrap();
        assert!(check_types(&duplicate)
            .unwrap_err()
            .contains("duplicate unsafe Send implementation"));

        assert!(parse_program("(#unsafe-impl #send Unknown)")
            .unwrap_err()
            .contains("undeclared type 'Unknown'"));

        let generic_override =
            parse_program("(#struct Box (T) ((value T))) (#unsafe-impl #sync Box)").unwrap_err();
        assert!(generic_override.contains("for generic type 'Box' is not supported"));

        let alias_override =
            parse_program("(#type Resource (#ptr u8)) (#unsafe-impl #send Resource)").unwrap_err();
        assert!(alias_override.contains("require a nominal struct or enum type"));
    }

    #[test]
    fn thread_spawn_generator_requires_send_worker_inputs_and_output() {
        let valid = parse_program(
            "(#fn increment ((value u64)) u64 (#return (#u64.+.wrap value 1))) (@thread-spawn IncrementTask increment)",
        )
        .unwrap();
        assert!(check_types(&valid).is_ok(), "{:?}", check_types(&valid));
        assert!(valid.items.iter().any(|item| matches!(
            item,
            Item::ThreadTask { name, worker }
                if name == "IncrementTask" && worker == "increment"
        )));
        let api = parse_program(
            "(#fn increment ((value u64)) u64 (#return (#u64.+.wrap value 1))) (@thread-spawn IncrementTask increment) (#fn main () u64 (#let task IncrementTask (IncrementTask-spawn 41)) (#let result u64 (IncrementTask-join task)) (#return result))",
        )
        .unwrap();
        assert!(check_types(&api).is_ok(), "{:?}", check_types(&api));
        let assembly = generate_assembly(&api).unwrap();
        assert!(assembly.contains("call pthread_create"));
        assert!(assembly.contains("call pthread_join"));
        assert!(assembly.contains(".Llim_thread_entry_IncrementTask"));

        let non_send_input = parse_program(
            "(#fn inspect ((pointer (#ptr u64))) u64 (#return (#unsafe (#ptr-read pointer)))) (@thread-spawn PointerTask inspect)",
        )
        .unwrap();
        assert!(check_types(&non_send_input)
            .unwrap_err()
            .contains("parameter 'pointer' does not implement Send"));

        let unsafe_send_input = parse_program(
            "(#struct NativeToken ((pointer (#ptr u64)))) (#unsafe-impl #send NativeToken) (#fn inspect ((token NativeToken)) u64 (#return 0)) (@thread-spawn TokenTask inspect)",
        )
        .unwrap();
        assert!(check_types(&unsafe_send_input).is_ok());

        let unsafe_sync_reference = parse_program(
            "(#struct NativeShared ((pointer (#ptr u64)))) (#unsafe-impl #sync NativeShared) (#fn inspect ((value (#ref NativeShared))) u64 (#return 0)) (@thread-spawn InspectTask inspect)",
        )
        .unwrap();
        assert!(check_types(&unsafe_sync_reference).is_ok());

        let missing_sync_reference = parse_program(
            "(#struct NativeShared ((pointer (#ptr u64)))) (#fn inspect ((value (#ref NativeShared))) u64 (#return 0)) (@thread-spawn InspectTask inspect)",
        )
        .unwrap();
        assert!(check_types(&missing_sync_reference)
            .unwrap_err()
            .contains("parameter 'value' does not implement Send"));

        let reference_return = parse_program(
            "(#fn identity ((value (#ref u64))) (#ref u64) (#return value)) (@thread-spawn IdentityTask identity)",
        )
        .unwrap();
        assert!(check_types(&reference_return)
            .unwrap_err()
            .contains("cannot return reference-containing values"));

        let duplicate_join = parse_program(
            "(#fn work ((value u64)) u64 (#return value)) (@thread-spawn WorkTask work) (#fn main () u64 (#let task WorkTask (WorkTask-spawn 1)) (#let first u64 (WorkTask-join task)) (#let second u64 (WorkTask-join task)) (#return second))",
        )
        .unwrap();
        assert!(check_types(&duplicate_join)
            .unwrap_err()
            .contains("was joined more than once"));

        let unjoined = parse_program(
            "(#fn work ((value u64)) u64 (#return value)) (@thread-spawn WorkTask work) (#fn main () u64 (#let task WorkTask (WorkTask-spawn 1)) (#return 0))",
        )
        .unwrap();
        assert!(check_types(&unjoined)
            .unwrap_err()
            .contains("may return while thread task 'task' is still running"));

        let borrowed_then_mutated = parse_program(
            "(#struct Shared ((value u64))) (#fn read ((value (#ref Shared))) u64 (#return (#get value value))) (@thread-spawn ReadTask read) (#fn main () u64 (#let-mut shared Shared (Shared 1)) (#let task ReadTask (ReadTask-spawn (#borrow shared))) (#set-field shared value 2) (#let result u64 (ReadTask-join task)) (#return result))",
        )
        .unwrap();
        let borrow_error = check_types(&borrowed_then_mutated).unwrap_err();
        assert!(
            borrow_error.contains("cannot mutate 'shared' while it is immutably borrowed"),
            "{borrow_error}"
        );

        let joined_then_mutated = parse_program(
            "(#struct Shared ((value u64))) (#fn read ((value (#ref Shared))) u64 (#return (#get value value))) (@thread-spawn ReadTask read) (#fn main () u64 (#let-mut shared Shared (Shared 1)) (#let task ReadTask (ReadTask-spawn (#borrow shared))) (#let result u64 (ReadTask-join task)) (#set-field shared value 2) (#return result))",
        )
        .unwrap();
        assert!(check_types(&joined_then_mutated).is_ok());

        let mutable_borrow_while_running = parse_program(
            "(#struct Shared ((value u64))) (#fn inspect ((value (#ref-mut Shared))) u64 (#return (#get value value))) (@thread-spawn InspectTask inspect) (#fn main () u64 (#let-mut shared Shared (Shared 1)) (#let task InspectTask (InspectTask-spawn (#borrow-mut shared))) (#set-field shared value 2) (#let result u64 (InspectTask-join task)) (#return result))",
        )
        .unwrap();
        let mutable_borrow_error = check_types(&mutable_borrow_while_running).unwrap_err();
        assert!(
            mutable_borrow_error.contains("mutably borrowed by a running thread"),
            "{mutable_borrow_error}"
        );

        let mutable_borrow_read_while_running = parse_program(
            "(#struct Shared ((value u64))) (#fn inspect ((value (#ref-mut Shared))) u64 (#return (#get value value))) (@thread-spawn InspectTask inspect) (#fn main () u64 (#let-mut shared Shared (Shared 1)) (#let task InspectTask (InspectTask-spawn (#borrow-mut shared))) (#let copy Shared shared) (#let result u64 (InspectTask-join task)) (#return result))",
        )
        .unwrap();
        let mutable_read_error = check_types(&mutable_borrow_read_while_running).unwrap_err();
        assert!(
            mutable_read_error.contains("cannot access 'shared' while it is mutably borrowed"),
            "{mutable_read_error}"
        );

        let mutable_borrow_then_join = parse_program(
            "(#struct Shared ((value u64))) (#fn inspect ((value (#ref-mut Shared))) u64 (#return (#get value value))) (@thread-spawn InspectTask inspect) (#fn main () u64 (#let-mut shared Shared (Shared 1)) (#let task InspectTask (InspectTask-spawn (#borrow-mut shared))) (#let result u64 (InspectTask-join task)) (#set-field shared value 2) (#return result))",
        )
        .unwrap();
        assert!(check_types(&mutable_borrow_then_join).is_ok());

        let unknown_worker = parse_program("(@thread-spawn MissingTask missing-worker)").unwrap();
        assert!(check_types(&unknown_worker)
            .unwrap_err()
            .contains("unknown worker function 'missing-worker'"));
    }

    #[test]
    fn returns_and_dereferences_references() {
        let program = parse_program(
            "(#let answer u64 42) (#fn identity ((value (#ref u64))) (#ref u64) (#return value)) (#fn get-answer () (#ref u64) (#return (#borrow answer))) (#fn main () u64 (#return (#deref (identity (get-answer)))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program);
        assert!(assembly.is_ok(), "{assembly:?}");

        let local_escape =
            parse_program("(#fn bad () (#ref u64) (#let value u64 42) (#return (#borrow value)))")
                .unwrap();
        assert!(check_types(&local_escape)
            .unwrap_err()
            .contains("reference to local variable 'value'"));

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
            "(#struct Point ((x u64) (y u64))) (#fn main () u64 (#let-mut point Point (Point 1 2)) (#let point-ref (#ref-mut Point) (#borrow-mut point)) (#let x-ref (#ref-mut u64) (#borrow-mut (#get point-ref x))) (#deref-set x-ref 42) (#return (#deref x-ref)))",
        )
        .unwrap();
        assert!(
            check_types(&derived_field).is_ok(),
            "{:?}",
            check_types(&derived_field)
        );
        assert!(generate_assembly(&derived_field).is_ok());

        let suspended_parent = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn main () u64 (#let-mut point Point (Point 1 2)) (#let point-ref (#ref-mut Point) (#borrow-mut point)) (#let x-ref (#ref-mut u64) (#borrow-mut (#get point-ref x))) (#return (#get point-ref y)))",
        )
        .unwrap();
        assert!(
            check_types(&suspended_parent).is_ok(),
            "{:?}",
            check_types(&suspended_parent)
        );

        let overlapping_field = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn main () u64 (#let-mut point Point (Point 1 2)) (#let point-ref (#ref-mut Point) (#borrow-mut point)) (#let x-ref (#ref-mut u64) (#borrow-mut (#get point-ref x))) (#return (#get point-ref x)))",
        )
        .unwrap();
        assert!(check_types(&overlapping_field)
            .unwrap_err()
            .contains("cannot access 'point.x' while it is mutably borrowed"));

        let dropped_field_reference = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn main () u64 (#let-mut point Point (Point 1 2)) (#let point-ref (#ref-mut Point) (#borrow-mut point)) (#let x-ref (#ref-mut u64) (#borrow-mut (#get point-ref x))) (#drop x-ref) (#let y-ref (#ref-mut u64) (#borrow-mut (#get point-ref y))) (#return (#deref y-ref)))",
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

        let original_owner_suspended = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn main () u64 (#let-mut point Point (Point 1 2)) (#let point-ref (#ref-mut Point) (#borrow-mut point)) (#return (#get point y)))",
        )
        .unwrap();
        assert!(check_types(&original_owner_suspended)
            .unwrap_err()
            .contains("while it is mutably borrowed"));

        let immutable_derived_field = parse_program(
            "(#struct Point ((x u64))) (#fn main () () (#let point Point (Point 1)) (#let point-ref (#ref Point) (#borrow point)) (#let x-ref (#ref-mut u64) (#borrow-mut (#get point-ref x))) (#return ()))",
        )
        .unwrap();
        assert!(check_types(&immutable_derived_field)
            .unwrap_err()
            .contains("cannot mutably borrow through an immutable reference"));

        let returned_field_reference = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn point-x ((point (#ref Point))) (#ref u64) (#return (#borrow (#get point x)))) (#fn main () u64 (#let-mut point Point (Point 40 2)) (#return (#deref (point-x (#borrow point)))))",
        )
        .unwrap();
        assert!(check_types(&returned_field_reference).is_ok());
        assert!(generate_assembly(&returned_field_reference).is_ok());

        let escaping_field_reference = parse_program(
            "(#struct Point ((x u64))) (#fn bad () (#ref u64) (#let-mut point Point (Point 42)) (#let point-ref (#ref Point) (#borrow point)) (#return (#borrow (#get point-ref x))))",
        )
        .unwrap();
        assert!(check_types(&escaping_field_reference)
            .unwrap_err()
            .contains("cannot return a reference to local variable 'point'"));

        let cloned_local_reference = parse_program(
            "(#fn bad () (#ref u64) (#let value u64 42) (#let reference (#ref u64) (#borrow value)) (#return (#clone reference)))",
        )
        .unwrap();
        assert!(check_types(&cloned_local_reference)
            .unwrap_err()
            .contains("cannot return a value retaining a reference to local 'value'"));

        let matched_local_reference = parse_program(
            "(#fn bad () (#ref u64) (#let value u64 42) (#let reference (#ref u64) (#borrow value)) (#return (#match true (true (#clone reference)) (_ (#clone reference)))))",
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
            "(#struct MutView ((data (#ref-mut u64)))) (#fn make ((data (#ref-mut u64))) MutView (#return (MutView data))) (#fn main () u64 (#let-mut value u64 40) (#let view MutView (make (#borrow-mut value))) (#deref-set (#get view data) 42) (#return (#deref (#get view data))))",
        )
        .unwrap();
        assert!(
            check_types(&mutable_reference_struct).is_ok(),
            "{:?}",
            check_types(&mutable_reference_struct)
        );
        assert!(generate_assembly(&mutable_reference_struct).is_ok());

        let mutable_reference_struct_escape = parse_program(
            "(#struct MutView ((data (#ref-mut u64)))) (#fn make ((data (#ref-mut u64))) MutView (#return (MutView data))) (#fn bad () MutView (#let-mut value u64 40) (#return (make (#borrow-mut value))))",
        )
        .unwrap();
        assert!(check_types(&mutable_reference_struct_escape)
            .unwrap_err()
            .contains("cannot return a value retaining a reference to local 'value'"));

        let mutable_reference_struct_clone = parse_program(
            "(#struct MutView ((data (#ref-mut u64)))) (#fn main () () (#let-mut value u64 40) (#let view MutView (MutView (#borrow-mut value))) (#let duplicate MutView (#clone view)) (#return ()))",
        )
        .unwrap();
        assert!(check_types(&mutable_reference_struct_clone)
            .unwrap_err()
            .contains("a mutable reference cannot be cloned"));
    }

    #[test]
    fn checks_raw_pointers_and_unsafe_blocks() {
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
        let valid = parse_program("(#fn main () u64 (#return (#u64.+.wrap 40 2)))");
        assert!(valid.is_ok());
        let external = parse_program(
            "(#extern-fn abs ((value i32)) i32) (#fn main () u64 (#return (#as (abs -42) u64)))",
        )
        .unwrap();
        assert!(check_types(&external).is_ok());
        let external_assembly = generate_assembly(&external).unwrap();
        assert!(external_assembly.contains(".extern abs"));
        assert!(external_assembly.contains("call abs"));
    }

    #[test]
    fn treats_dotted_names_as_ordinary_identifiers() {
        let tokens = lex("a.b.c - . #u64.+.wrap").unwrap();
        assert_eq!(tokens[0].kind, TokenKind::Symbol("a.b.c".into()));
        assert_eq!(tokens[1].kind, TokenKind::Symbol("-".into()));
        assert_eq!(tokens[2].kind, TokenKind::Symbol(".".into()));
        assert_eq!(tokens[3].kind, TokenKind::Symbol("#u64.+.wrap".into()));
        let program = parse_program(
            "(#fn util.add-one () u64 (#return 42)) (#fn main () u64 (#return (util.add-one)))",
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
        let generic = parse_program("(#fn identity (T) ((value T)) T (#return value))").unwrap();
        let Item::Function(identity) = &generic.items[0] else {
            panic!()
        };
        assert_eq!(identity.type_parameters, vec!["T"]);
        assert_eq!(identity.parameters[0].ty, Type::Generic("T".into()));
        assert_eq!(identity.return_type, Type::Generic("T".into()));
        let instantiated = parse_program(
            "(#fn identity (T) ((value T)) T (#return value)) (#fn main () u64 (#return (identity<u64> 42)))",
        )
        .unwrap();
        assert!(check_types(&instantiated).is_ok());
        let assembly = generate_assembly(&instantiated).unwrap();
        assert!(assembly.contains("identity_x24_u64"));
        let generic_local = parse_program(
            "(#fn copy (T) ((value T)) T (#let result T value) (#return result)) (#fn main () u64 (#return (copy<u64> 42)))",
        )
        .unwrap();
        assert!(generate_assembly(&generic_local).is_ok());
        let missing_arguments =
            parse_program("(#fn identity (T) ((value T)) T (#return value)) (#fn main () u64 (#return (identity 42)))")
                .unwrap();
        assert!(check_types(&missing_arguments)
            .unwrap_err()
            .contains("expects 1 type arguments"));
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
            "(#struct Point ((x u64) (y u64))) (#static Values (#array u64 3) (#array (#array u64 3) 10 20 30)) (#static Origin Point (Point 7 9)) (#static Pair (#tuple u64 f64) (#tuple (#tuple u64 f64) 4 2.5)) (#enum Maybe ((Some u64) None)) (#static Choice Maybe (Some 12)) (#fn take ((values (#array u64 3)) (point Point)) u64 (#return (#u64.+.wrap (#index values 1) (#get point y)))) (#fn return-values () (#array u64 3) (#return (#unsafe Values))) (#fn read-choice ((choice Maybe)) u64 (#return (#match choice ((Some value) value) (None 0)))) (#fn return-choice () Maybe (#return (#unsafe Choice))) (#fn main () u64 (#let copied (#array u64 3) (#unsafe Values)) (#let copied-choice Maybe (#unsafe Choice)) (#return (#u64.+.wrap (#index copied 0) (#u64.+.wrap (#index (#return-values) 2) (#u64.+.wrap (take (#unsafe Values) (#unsafe Origin)) (#u64.+.wrap (read-choice copied-choice) (read-choice (#return-choice))))))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn evaluates_floating_remainder_constants() {
        let program = parse_program(
            "(#const Remainder f64 (#f64.% 7.5 2.5)) (#fn main () u64 (#return (#if (#f64.== Remainder 0.0) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
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
            parse_program("(#fn inc ((value u32)) u32 (#return (#u32.+.wrap  value 1))) (#fn main () u32 (#return (inc 41)))")
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
    fn supports_shadowed_local_bindings() {
        let program = parse_program(
            "(#fn main () u64 (#let value u64 40) (#let value u64 (#u64.+.wrap value 1)) (#return (#u64.+.wrap value (#block (#let value u64 1) (#u64.+.wrap value 1)))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn allows_parameters_to_shadow_globals() {
        let program = parse_program(
            "(#let value u64 10) (#fn read ((value u64)) u64 (#return value)) (#fn main () u64 (#return (read 42)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn allows_match_bindings_to_shadow_outer_locals() {
        let program = parse_program(
            "(#enum Maybe ((Some u64) None)) (#fn main () u64 (#let value u64 40) (#return (#match (Some 1) ((Some value) (#u64.+.wrap value 1)) (None value))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
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
            "(#struct Point ((x f64) (y f32))) (#fn main () u64 (#let point Point (Point 1.5 2.5)) (#let x f64 (#get point x)) (#let values (#array f32 2) (#array 1.5 2.5)) (#let y f32 (#index values 1)) (#return (#if (#bool.&& (#f64.> x 1.0) (#f32.> y 2.0)) 42 0)))",
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
            "(#fn widen () u128 (#return (#as 42 u128))) (#fn main () u64 (#let value u128 (widen)) (#return (#as value u64)))",
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
            "(#struct Pair ((scale f32) (value u64))) (#fn consume ((pair Pair) (factor f32)) u64 (#return (#if (#f32.>  (#get pair scale) 1.0) (#u64.+.wrap (#get pair value) 1) 0))) (#fn main () u64 (#return (consume (Pair 1.5 41) 2.0)))",
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
            "(#struct Values ((a u64) (b u64) (c u64) (d u64) (e u64) (f u64))) (#fn make () Values (#return (Values 1 2 3 4 5 6))) (#fn sum ((value Values)) u64 (#return (#u64.+.wrap  (#u64.+.wrap  (#u64.+.wrap  (#u64.+.wrap  (#u64.+.wrap  (#get value a) (#get value b)) (#get value c)) (#get value d)) (#get value e)) (#get value f)))) (#fn main () u64 (#return (sum (make))))",
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
            "(#fn blend ((small f32) (large f64)) f64 (#return (#f64.+ (#as small f64) large))) (#fn main () u64 (#return (#if (#f64.> (blend 1.5 2.5) 4.0) 42 0)))",
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
            "(#fn make () (#tuple u64 f32) (#return (#tuple 40 2.5))) (#fn consume ((value (#tuple u64 f32))) u64 (#return (#u64.+.wrap (#get value 0) (#as (#get value 1) u64)))) (#fn main () u64 (#let value (#tuple u64 f32) (make)) (#return (consume value)))",
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
            "(#fn recurse () u64 (#return (recurse))) (#fn main () u64 (#return (recurse)))",
        )
        .unwrap();
        let error = check_types(&direct).unwrap_err();
        assert!(error.contains("recursive calls"), "{error}");

        let indirect = parse_program(
            "(#fn first () u64 (#return (second))) (#fn second () u64 (#return (first))) (#fn main () u64 (#return (first)))",
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
            "(#fn choose ((flag bool)) f32 (#return (#if flag 1.5 2.5))) (#fn main () u64 (#return (#if (#f32.>  (choose true) 1.0) 42 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("movd xmm0, eax"));
        let matched = parse_program(
            "(#enum MaybeF ((SomeF f32) None)) (#fn read ((value MaybeF)) f32 (#return (#match value ((SomeF payload) payload) (None 2.5)))) (#fn main () u64 (#return (#if (#f32.>  (read None) 2.0) 42 0)))",
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
            "(#fn make () u128 (#return 0x8000000000000000000000000000002a)) (#fn main () u64 (#return (#as (make) u64)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("mov rdx, 0x8000000000000000"));
    }

    #[test]
    fn lowers_unit_functions_and_calls() {
        let program =
            parse_program("(#fn noop () () (#return ())) (#fn main () u64 (noop) (#return 42))")
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
            "(#fn add ((left f64) (right f64)) f64 (#return (#f64.+  left right))) (#fn main () f64 (#return (add 1.5 2.5)))",
        )
        .unwrap();
        assert!(generate_assembly(&called).unwrap().contains("call add"));
        let mixed = parse_program(
            "(#fn choose ((value u64) (scale f64)) u64 (#return (#if (#f64.>  scale 1.0) value 0))) (#fn main () u64 (#return (choose 42 2.0)))",
        )
        .unwrap();
        assert!(check_types(&mixed).is_ok());
        assert!(generate_assembly(&mixed).unwrap().contains("movq xmm0"));
    }

    #[test]
    fn checks_and_lowers_f32_arithmetic_and_calls() {
        let program = parse_program(
            "(#fn add ((left f32) (right f32)) f32 (#return (#f32.+  left right))) (#fn main () u64 (#return (#if (#f32.>  (add 1.5 2.5) 3.0) 42 0)))",
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
    fn expands_optional_generated_declarations() {
        let program = parse_program(
            "(@optional u64 Maybe?) (#fn main () u64 (#let value Maybe? (Maybe?-construct 42)) (#return (#if (Maybe?-is-some (#clone value)) (Maybe?-unwrap-or value 0) 0)))",
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
    fn materializes_strict_optional_source_with_explicit_returns() {
        let directory =
            std::env::temp_dir().join(format!("lim-generated-optional-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        write_generated_sources("(@optional u64 Maybe?)", &directory).unwrap();
        let generated = std::fs::read_to_string(directory.join("optional-0.lim")).unwrap();
        assert!(generated.contains("#enum"));
        assert!(generated.contains("#return"));
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
        write_generated_sources("(@result u64 u32 Result)", &directory).unwrap();
        let generated = std::fs::read_to_string(directory.join("result-0.lim")).unwrap();
        assert!(generated.contains("Result-ok-value"));
        assert!(generated.contains("Result-unwrap-or"));
        assert!(generated.contains("Result-unwrap-err-or"));
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn lowers_if_let_to_native_match() {
        let program = parse_program(
            "(@optional u64 Maybe?) (#fn main () u64 (#let value Maybe? (Maybe?-construct 42)) (#return (#if-let (Maybe?-some payload) value payload 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn expands_result_generated_declarations() {
        let program = parse_program(
            "(@result u64 u32 Result) (#fn classify ((value Result)) u64 (#return (#match value ((Result-ok-value 42) 1) ((Result-err-value _) 0)))) (#fn main () u64 (#let value Result (Result-ok 42)) (#return (classify value)))",
        )
        .unwrap();
        let type_result = check_types(&program);
        assert!(type_result.is_ok(), "{type_result:?}");
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn lowers_while_let_with_match_guard() {
        let program = parse_program(
            "(@optional u64 Maybe?) (#fn main () u64 (#let-mut value Maybe? (Maybe?-construct 42)) (#let-mut total u64 0) (#while-let (Maybe?-some payload) value (#set total (#u64.+.wrap  total payload)) (#set value Maybe?-none)) (#return total))",
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
            "(#struct Point ((x u64) (y u64))) (#fn point_value () u64 (#let point Point (Point 40 2)) (#return (#if-let (Point 40 y) point y 0))) (#fn main () u64 (#let-mut value (#tuple u64 u64) (#tuple (#tuple u64 u64) 1 2)) (#let-mut total u64 0) (#while-let (#tuple 1 _) value (#set total (#u64.+.wrap total (#get value 1))) (#set-field value 0 0)) (#return (#u64.+.wrap total (point_value))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn lowers_typed_tuple_and_struct_let_destructuring() {
        let program = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn sum_tuple ((value (#tuple u64 u64))) u64 (#let (#tuple first second) (#tuple u64 u64) value) (#return (#u64.+.wrap first second))) (#fn sum_point ((value Point)) u64 (#let (Point x y) Point value) (#return (#u64.+.wrap x y))) (#fn main () u64 (#return (#u64.+.wrap (sum_tuple (#tuple (#tuple u64 u64) 20 10)) (sum_point (Point 7 5)))))",
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
            "(#fn classify ((value (#array u64 3))) u64 (#return (#match value ((#array 10 middle _) middle) (_ 0)))) (#fn main () u64 (#return (classify (#array (#array u64 3) 10 32 12))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn matches_empty_arrays() {
        let program = parse_program(
            "(#fn main () u64 (#return (#match (#array (#array u64 0)) ((#array) 42) (_ 0))))",
        )
        .unwrap();
        let type_result = check_types(&program);
        assert!(type_result.is_ok(), "{type_result:?}");
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn matches_direct_array_values() {
        let program = parse_program(
            "(#fn main () u64 (#return (#match (#array (#array u64 3) 10 32 12) ((#array 10 middle _) middle) (_ 0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn matches_direct_struct_values() {
        let program = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn main () u64 (#return (#match (Point 10 32) ((Point 10 middle) middle) (_ 0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn matches_direct_tuple_values() {
        let program = parse_program(
            "(#fn main () u64 (#return (#match (#tuple (#tuple u64 u64) 10 32) ((#tuple 10 middle) middle) (_ 0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn returns_nested_direct_tuple_values() {
        let program = parse_program(
            "(#fn make () (#tuple (#tuple u64 u64) u64) (#return (#tuple (#tuple (#tuple u64 u64) 10 20) 32))) (#fn main () u64 (#return (#get (make) 1)))",
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
            "(#struct Inner ((left u64) (right u64))) (#struct Outer ((inner Inner) (tail u64))) (#fn main () u64 (#let value Outer (Outer (Inner 10 20) 32)) (#return (#get value tail)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn destructures_nested_struct_locals() {
        let program = parse_program(
            "(#struct Inner ((left u64) (right u64))) (#struct Outer ((inner Inner) (tail u64))) (#fn main () u64 (#let (Outer inner tail) Outer (Outer (Inner 10 20) 32)) (#return tail))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn matches_nested_direct_tuple_values() {
        let program = parse_program(
            "(#fn main () u64 (#return (#match (#tuple (#tuple (#tuple u64 u64) u64) (#tuple (#tuple u64 u64) 10 20) 32) (_ 32))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn matches_nested_tuple_patterns_and_binds_flattened_values() {
        let program = parse_program(
            "(#fn main () u64 (#return (#match (#tuple (#tuple (#tuple u64 u64) u64) (#tuple (#tuple u64 u64) 10 20) 32) ((#tuple (#tuple _ inner) tail) (#u64.+.wrap inner tail)) (_ 0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn passes_nested_tuple_parameters_through_native_calls() {
        let program = parse_program(
            "(#fn add-inner-and-tail ((value (#tuple (#tuple u64 u64) u64))) u64 (#return (#u64.+.wrap (#u64.+.wrap (#get (#get value 0) 1) (#get value 1)) (#get (#get value 0) 0)))) (#fn main () u64 (#return (add-inner-and-tail (#tuple (#tuple (#tuple u64 u64) u64) (#tuple (#tuple u64 u64) 10 20) 32))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn returns_nested_array_locals_through_native_calls() {
        let program = parse_program(
            "(#fn nested-values () (#array (#array u64 2) 2) (#let value (#array (#array u64 2) 2) (#array (#array (#array u64 2) 2) (#array (#array u64 2) 10 20) (#array (#array u64 2) 30 40))) (#return value)) (#fn main () u64 (#return (#index (#index (nested-values) 1) 0)))",
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
            "(#struct Inner ((left u64) (right u64))) (#struct Outer ((inner Inner) (tail u64))) (#fn main () u64 (#let-mut value Outer (Outer (Inner 10 20) 30)) (#set-field value inner (Inner 50 60)) (#return (#get (#get value inner) right)))",
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
            "(#enum Boxed ((Wrapped (#tuple u64 u64)) Empty)) (#fn sum ((value Boxed)) u64 (#return (#match value ((Wrapped (#tuple left right)) (#u64.+.wrap left right)) (Empty 0)))) (#fn main () u64 (#return (sum (Wrapped (#tuple (#tuple u64 u64) 10 22)))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn reads_nested_enum_statics() {
        let program = parse_program(
            "(#enum Boxed ((Wrapped (#tuple u64 u64)) Empty)) (#static Value Boxed (Wrapped (#tuple (#tuple u64 u64) 10 22))) (#fn main () u64 (#return (#match (#unsafe Value) ((Wrapped (#tuple left right)) (#u64.+.wrap left right)) (Empty 0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn destructures_nested_aggregate_patterns() {
        let program = parse_program(
            "(#struct Inner ((left u64) (right u64))) (#struct Outer ((inner Inner) (tail u64))) (#fn main () u64 (#let (Outer (Inner left right) tail) Outer (Outer (Inner 10 20) 30)) (#return (#u64.+.wrap right tail)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn mutates_enum_payload_fields() {
        let program = parse_program(
            "(#enum Pair ((Pair u64 u64) Empty)) (#fn main () u64 (#let-mut value Pair (Pair 20 22)) (#set-payload value Pair 1 30) (#return (#match value ((Pair left right) (#u64.+.wrap left right)) (Empty 0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn checks_and_lowers_match_guards() {
        let program = parse_program(
            "(#enum Maybe ((Some u64) None)) (#fn main () u64 (#let value Maybe (Some 42)) (#return (#match value ((Some payload) (#when (#u64.>.wrap payload 40)) (#u64.+.wrap payload 8)) ((Some _) 0) (None 0))))",
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
            "(#fn abort () ! (#return (#unreachable))) (#fn choose ((condition bool)) u64 (#return (#if condition 42 (abort)))) (#fn main () u64 (#return (choose false)))",
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
            "(#enum Color (Red Green)) (#fn discriminant ((value Color)) u64 (#return (#as value u64))) (#fn main () u64 (#let selected Color Green) (#return (#u64.+.wrap (discriminant selected) 41)))",
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
            "(#struct Tagged ((marker ()) (value u64))) (#fn consume ((marker ())) u64 (#return 41)) (#fn main () u64 (#let unit-value () ()) (#let pair (#tuple () u64) (#tuple (#tuple () u64) (#clone unit-value) 40)) (#let tagged Tagged (Tagged (#clone unit-value) 1)) (#return (#u64.+.wrap (consume unit-value) (#u64.+.wrap (#get pair 1) (#get tagged value)))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn lowers_unit_like_structs() {
        let program = parse_program(
            "(#struct Marker ()) (#fn make () Marker (#return (Marker))) (#fn consume ((marker Marker)) u64 (#return 41)) (#fn main () u64 (#let marker Marker (make)) (#return (consume marker)))",
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
            "(#let UNIT () ()) (#fn consume ((value ())) u64 (#return 41)) (#fn main () u64 (#return (consume UNIT)))",
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
    fn matches_wide_enum_payload_literals() {
        let program = parse_program(
            "(#enum Maybe ((Some i128) None)) (#fn main () u64 (#let value Maybe (Some 42)) (#return (#match value ((Some 42) 42) (_ 0))))",
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
            "(#fn consume ((values (#array (#tuple u64 u64) 2))) u64 (#return (#get (#index values 1) 0))) (#fn main () u64 (#let values (#array (#tuple u64 u64) 2) (#array (#array (#tuple u64 u64) 2) (#tuple (#tuple u64 u64) 10 20) (#tuple (#tuple u64 u64) 30 12))) (#return (consume values)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn passes_repeated_aggregate_arrays_through_functions() {
        let program = parse_program(
            "(#fn consume ((values (#array (#tuple u64 u64) 2))) u64 (#return (#get (#index values 1) 0))) (#fn main () u64 (#return (consume (#array-repeat (#tuple 30 12)))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn returns_repeated_aggregate_arrays() {
        let program = parse_program(
            "(#fn values () (#array (#tuple u64 u64) 2) (#return (#array-repeat (#tuple 30 12)))) (#fn main () u64 (#return (#get (#index (values) 1) 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn returns_aggregate_if_values() {
        let program = parse_program(
            "(#fn choose ((condition bool)) (#tuple u64 u64) (#return (#if condition (#tuple (#tuple u64 u64) 10 20) (#tuple (#tuple u64 u64) 30 12)))) (#fn main () u64 (#return (#get (choose true) 1)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn returns_aggregate_match_values() {
        let program = parse_program(
            "(#enum Maybe ((Some u64) None)) (#fn choose ((value Maybe)) (#tuple u64 u64) (#return (#match value ((Some payload) (#tuple (#tuple u64 u64) payload 20)) (None (#tuple (#tuple u64 u64) 30 12))))) (#fn main () u64 (#return (#get (choose (Some 10)) 1)))",
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
            "(#fn values () (#tuple u64 u64) (#return (#loop (#break (#tuple (#tuple u64 u64) 30 12))))) (#fn main () u64 (#return (#get (values) 1)))",
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
            "(#fn values () (#tuple u64 u64) (#return (#loop (#if true (#block (#break (#tuple (#tuple u64 u64) 30 12))) (#unreachable))))) (#fn main () u64 (#return (#get (values) 1)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn passes_aggregate_control_values_to_functions() {
        let program = parse_program(
            "(#fn consume ((value (#tuple u64 u64))) u64 (#return (#get value 1))) (#fn main () u64 (#return (consume (#if true (#tuple (#tuple u64 u64) 10 20) (#tuple (#tuple u64 u64) 30 12)))))",
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
            "(#struct Point ((x u64) (y u64))) (#fn point_x () u64 (#return (#get (Point 7 9) x)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("mov rax, 7"));
        let local = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn point_y () u64 (#let p Point (Point 7 9)) (#return (#get p y)))",
        )
        .unwrap();
        assert!(generate_assembly(&local).unwrap().contains("[rbp-16]"));
        let mutable = parse_program("(#struct Point ((x u64) (y u64))) (#fn main () u64 (#let-mut p Point (Point 1 2)) (#set-field p y 40) (#return (#u64.+.wrap  (#get p x) (#get p y))))").unwrap();
        assert!(check_types(&mutable).is_ok());
        let returned = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn make_point () Point (#return (Point 7 9)))",
        )
        .unwrap();
        assert!(check_types(&returned).is_ok());
        assert!(generate_assembly(&returned).unwrap().contains("pop rdx"));
        let consumed = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn make_point () Point (#return (Point 7 9))) (#fn main () u64 (#let point Point (make_point)) (#return (#get point y)))",
        )
        .unwrap();
        assert!(check_types(&consumed).is_ok());
        assert!(generate_assembly(&consumed)
            .unwrap()
            .contains("call make_point"));
        let unsupported_parameter = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn identity ((point Point)) Point (#return point)) (#fn main () u64 (#let result Point (identity (Point 11 37))) (#return (#get result y)))",
        )
        .unwrap();
        assert!(check_types(&unsupported_parameter).is_ok());
        assert!(generate_assembly(&unsupported_parameter)
            .unwrap()
            .contains("call identity"));
        let generic = parse_program(
            "(#struct Box (T) ((value T))) (#fn main () u64 (#let boxed Box<u64> (Box<u64> 42)) (#return (#get boxed value)))",
        )
        .unwrap();
        assert!(check_types(&generic).is_ok());
        assert!(generic.items.iter().any(|item| {
            matches!(item, Item::Struct { name, fields, .. } if name == "Box$u64" && fields[0].ty == Type::U64)
        }));
        assert!(generate_assembly(&generic).unwrap().contains("mov rax, 42"));
        let generic_enum = parse_program(
            "(#enum Maybe (T) ((Some T) None)) (#fn main () u64 (#let value Maybe<u64> (Some 42)) (#return (#match value ((Some payload) payload) (None 0))))",
        )
        .unwrap();
        assert!(check_types(&generic_enum).is_ok());
        assert!(generate_assembly(&generic_enum).is_ok());
        let free_function = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn point-new ((x u64) (y u64)) Point (#return (Point x y))) (#fn main () u64 (#return (#get (point-new 7 9) y)))",
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
        assert!(check_types(&invalid).is_err());
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
            "(#enum Color (Red Green Blue)) (#fn main () u64 (#return (#match Green (Red 10) (Green 20) (_ 30))))",
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
            "(#enum Pair ((Pair u64 u64) Empty)) (#fn main () u64 (#let value Pair (Pair 20 22)) (#return (#match value ((Pair left right) (#u64.+.wrap  left right)) (Empty 0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("mov rax, 20"));
    }

    #[test]
    fn matches_enum_payload_literals() {
        let program = parse_program(
            "(#enum Maybe ((Some u64) None)) (#fn classify ((value Maybe)) u64 (#return (#match value ((Some 42) 1) (None 0)))) (#fn main () u64 (#return (classify (Some 42))))",
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
            "(#enum Pair ((Pair u64 u64) Empty)) (#fn make () Pair (#let value Pair (Pair 20 22)) (#return value)) (#fn sum ((value Pair)) u64 (#return (#match value ((Pair left right) (#u64.+.wrap  left right)) (Empty 0)))) (#fn main () u64 (#return (sum (make))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("call sum"));
    }

    #[test]
    fn lowers_two_word_128_bit_integers() {
        let program = parse_program(
            "(#fn add ((left u128) (right u128)) u128 (#return (#u128.+.wrap  left right))) (#fn main () u64 (#return (#as (add 20 22) u64)))",
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
            "(#fn multiply ((left u128) (right u128)) u128 (#return (#u128.*.wrap  left right))) (#fn main () u64 (#return (#as (multiply 6 7) u64)))",
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
            "(#enum Maybe ((Some u64) None)) (#fn main () u64 (#let value Maybe (Some 42)) (#return (#match value ((Some _) 42) (None 7))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("mov QWORD PTR [rbp-8], 0"));
        assert!(assembly.contains("cmp QWORD PTR [rsp], 0"));
        let invalid = parse_program(
            "(#enum Maybe ((Some u64) None)) (#fn main () u64 (#return (#match None ((Some _) 1))))",
        )
        .unwrap();
        assert!(check_types(&invalid)
            .unwrap_err()
            .contains("not exhaustive"));
        let binding = parse_program(
            "(#enum Maybe ((Some u64) None)) (#fn main () u64 (#let value Maybe (Some 42)) (#return (#match value ((Some payload) payload) (None 0))))",
        )
        .unwrap();
        assert!(check_types(&binding).is_ok());
        assert!(generate_assembly(&binding)
            .unwrap()
            .contains("mov QWORD PTR [rbp-24], rax"));
        let returned = parse_program(
            "(#enum Maybe ((Some u64) None)) (#fn make () Maybe (#return (Some 42))) (#fn main () u64 (#let value Maybe (make)) (#return (#match value ((Some payload) payload) (None 0))))",
        )
        .unwrap();
        assert!(check_types(&returned).is_ok());
        assert!(generate_assembly(&returned).unwrap().contains("call make"));
        let passed = parse_program(
            "(#enum Maybe ((Some u64) None)) (#fn identity ((value Maybe)) Maybe (#return value)) (#fn main () u64 (#let result Maybe (identity (Some 42))) (#return (#match result ((Some payload) payload) (None 0))))",
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
            "(#enum Maybe ((Some u64) None)) (#fn main () u64 (#return (#match (Some 42) ((Some value) value) (None 0))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("add rsp, 16"));
    }

    #[test]
    fn indexes_arrays_returned_by_functions() {
        let program = parse_program(
            "(#fn make () (#array u64 3) (#return (#array 10 20 30))) (#fn main () u64 (#return (#index (make) 1)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("call make"));
    }

    #[test]
    fn selects_fields_from_structs_returned_by_functions() {
        let program = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn make () Point (#return (Point 7 9))) (#fn main () u64 (#return (#get (make) y)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("call make"));
    }

    #[test]
    fn passes_floating_struct_fields_through_functions() {
        let program = parse_program(
            "(#struct Point ((x f64) (y f32))) (#fn make () Point (#return (Point 1.5 2.5))) (#fn main () u64 (#return (#if (#bool.&& (#f64.> (#get (make) x) 1.0) (#f32.> (#get (make) y) 2.0)) 42 0)))",
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
            "(#fn sum ((values (#array f32 2))) f32 (#return (#index values 1))) (#fn make () (#array f32 2) (#return (#array 1.5 2.5))) (#fn main () u64 (#let value f32 (sum (make))) (#return (#if (#f32.>  value 2.0) 42 0)))",
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
            "(#fn make () (#array f32 2) (#return (#array 1.5 2.5))) (#fn main () u64 (#return (#if (#f32.>  (#index (make) 1) 2.0) 42 0)))",
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
            "(#enum MaybeF ((SomeF f32) None)) (#fn make () MaybeF (#return (SomeF 2.5))) (#fn read ((value MaybeF)) f32 (#return (#match value ((SomeF payload) payload) (None 0.0)))) (#fn main () u64 (#return (#if (#f32.>  (read (make)) 2.0) 42 0)))",
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
            "(#fn classify ((value u64)) u64 (#return (#match value (0 10) (1 20) (_ 30)))) (#fn main () u64 (#return (classify 1)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("cmp QWORD PTR [rsp], 1"));
        let bools =
            parse_program("(#fn main () u64 (#return (#match true (true 42) (false 0))))").unwrap();
        assert!(check_types(&bools).is_ok());
        let incomplete = parse_program("(#fn main () u64 (#return (#match 1 (1 42))))").unwrap();
        assert!(check_types(&incomplete)
            .unwrap_err()
            .contains("not exhaustive"));
        let duplicate_integer =
            parse_program("(#fn main () u64 (#return (#match 1 (1 10) (1 20) (_ 30))))").unwrap();
        assert!(check_types(&duplicate_integer)
            .unwrap_err()
            .contains("duplicate integer match pattern"));
        let duplicate_enum = parse_program(
            "(#enum Color (Red Blue)) (#fn main () u64 (#return (#match Red (Red 1) (Red 2) (_ 0))))",
        )
        .unwrap();
        assert!(check_types(&duplicate_enum)
            .unwrap_err()
            .contains("duplicate enum match pattern 'Red'"));
        let wide = parse_program(
            "(#fn main () u64 (#let value u128 340282366920938463463374607431768211455) (#return (#match value (340282366920938463463374607431768211455 42) (_ 0))))",
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
            "(#fn identity ((values (#array u64 3))) (#array u64 3) (#return values)) (#fn main () u64 (#let values (#array u64 3) (identity (#array 10 20 37))) (#return (#index values 2)))",
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
            "(#enum Result ((Ok 7 u64) (Err 99 u64))) (#fn main () u64 (#let value Result (Ok 42)) (#return (#match value ((Ok payload) payload) ((Err _) 0))))",
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
            "(#enum Code ((Maximum 18446744073709551615))) (#fn main () u64 (#return (#match Maximum (Maximum 42) (_ 0))))",
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
            "(#struct Pair ((left u64) (right u64))) (#fn main () u64 (#tuple (#tuple u64 u64) 1 2) (Pair 3 4) (#return 42))",
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
            "(#fn make () (#array u64 3) (#return (#array (#array u64 3) 10 20 37))) (#fn consume ((values (#array u64 3))) u64 (#return (#index values 2))) (#fn main () u64 (#return (consume (make))))",
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
            "(#fn make () (#tuple u64 u64) (#return (#tuple (#tuple u64 u64) 40 2))) (#fn consume ((value (#tuple u64 u64))) u64 (#return (#get value 0))) (#fn main () u64 (#return (consume (make))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn lowers_tuple_destructuring_match() {
        let program = parse_program(
            "(#fn classify ((value (#tuple u64 u64))) u64 (#return (#match value ((#tuple 40 second) second) (_ 0)))) (#fn main () u64 (#return (classify (#tuple (#tuple u64 u64) 40 2))))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn lowers_struct_destructuring_match() {
        let program = parse_program(
            "(#struct Point ((x u64) (y u64))) (#fn classify ((value Point)) u64 (#return (#match value ((Point 40 second) second) (_ 0)))) (#fn main () u64 (#return (classify (Point 40 2))))",
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
        let program = parse_program("(#fn sum8 ((a u64) (b u64) (c u64) (d u64) (e u64) (f u64) (g u64) (h u64)) u64 (#return (#u64.+.wrap  (#u64.+.wrap  (#u64.+.wrap  (#u64.+.wrap  (#u64.+.wrap  (#u64.+.wrap  (#u64.+.wrap  a b) c) d) e) f) g) h))) (#fn main () u64 (#return (sum8 1 2 3 4 5 6 7 8)))").unwrap();
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
            "(#fn saturate ((value i8)) i8 (#return (#i8.-.saturate value))) (#fn main () u64 (#return (#as (saturate -128) u64)))",
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
            "(#fn offset () u64 (#return 41)) (#fn main () u64 (#return (#u64.+.wrap (offset) 1u64)))",
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
            "(#struct Large ((a u64) (b u64) (c u64) (d u64) (e u64) (f u64) (g u64))) (#fn main () u64 (#let value Large (Large 1u64 2u64 3u64 4u64 5u64 6u64 7u64)) (#let copy Large value) (#return (#u64.+.wrap (#get copy a) (#get copy g))))",
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
    fn matches_large_scalar_array_locals_without_abi_flattening() {
        let program = parse_program(
            "(#fn main () u64 (#let values (#array u64 7) (#array (#array u64 7) 1u64 2u64 3u64 4u64 5u64 6u64 42u64)) (#return (#match values ((#array first second third fourth fifth sixth last) last) (_ 0u64))))",
        )
        .unwrap();
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn matches_direct_large_scalar_array_returns() {
        let program = parse_program(
            "(#fn make () (#array u64 7) (#return (#array (#array u64 7) 1u64 2u64 3u64 4u64 5u64 6u64 42u64))) (#fn main () u64 (#return (#match (make) ((#array first second third fourth fifth sixth last) last) (_ 0u64))))",
        )
        .unwrap();
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn matches_direct_large_nested_aggregate_returns() {
        let program = parse_program(
            "(#fn make () (#array (#tuple u128 u64) 4) (#return (#array (#array (#tuple u128 u64) 4) (#tuple 10u128 1u64) (#tuple 20u128 2u64) (#tuple 30u128 3u64) (#tuple 40u128 42u64)))) (#fn main () u64 (#return (#match (make) ((#array (#tuple _ _) (#tuple _ _) (#tuple _ _) (#tuple _ last)) last) (_ 0u64))))",
        )
        .unwrap();
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn matches_direct_large_tuple_and_struct_returns() {
        let program = parse_program(
            "(#struct Large ((a u64) (b u64) (c u64) (d u64) (e u64) (f u64) (g u64))) (#fn make-tuple () (#tuple u64 u64 u64 u64 u64 u64 u64) (#return (#tuple (#tuple u64 u64 u64 u64 u64 u64 u64) 1u64 2u64 3u64 4u64 5u64 6u64 20u64))) (#fn make-struct () Large (#return (Large 1u64 2u64 3u64 4u64 5u64 6u64 22u64))) (#fn main () u64 (#return (#u64.+.wrap (#match (make-tuple) ((#tuple first second third fourth fifth sixth last) last) (_ 0u64)) (#match (make-struct) ((Large first second third fourth fifth sixth last) last) (_ 0u64)))))",
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
    fn returns_large_arrays_with_nested_wide_elements() {
        let program = parse_program(
            "(#fn make () (#array (#tuple u128 u64) 4) (#return (#array (#array (#tuple u128 u64) 4) (#tuple 10u128 1u64) (#tuple 20u128 2u64) (#tuple 30u128 3u64) (#tuple 40u128 42u64)))) (#fn main () u64 (#let values (#array (#tuple u128 u64) 4) (make)) (#let item (#tuple u128 u64) (#index values 3u64)) (#let direct-item (#tuple u128 u64) (#index (make) 3u64)) (#return (#u64.+.wrap (#get item 1) (#get direct-item 1))))",
        )
        .unwrap();
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn passes_large_arrays_with_nested_wide_elements() {
        let program = parse_program(
            "(#fn consume ((value (#array (#tuple u128 u64) 4))) u64 (#let item (#tuple u128 u64) (#index value 3u64)) (#return (#get item 1))) (#fn main () u64 (#return (consume (#array (#array (#tuple u128 u64) 4) (#tuple 10u128 1u64) (#tuple 20u128 2u64) (#tuple 30u128 3u64) (#tuple 40u128 42u64)))))",
        )
        .unwrap();
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn passes_two_constructed_large_arguments_without_aliasing() {
        let program = parse_program(
            "(#fn add-last ((left (#array (#tuple u128 u64) 4)) (right (#array (#tuple u128 u64) 4))) u64 (#let left-item (#tuple u128 u64) (#index left 3u64)) (#let right-item (#tuple u128 u64) (#index right 3u64)) (#return (#u64.+.wrap (#get left-item 1) (#get right-item 1)))) (#fn main () u64 (#return (add-last (#array (#array (#tuple u128 u64) 4) (#tuple 10u128 2u64) (#tuple 20u128 3u64) (#tuple 30u128 4u64) (#tuple 40u128 20u64)) (#array (#array (#tuple u128 u64) 4) (#tuple 50u128 5u64) (#tuple 60u128 6u64) (#tuple 70u128 7u64) (#tuple 80u128 22u64)))))",
        )
        .unwrap();
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn passes_constructed_large_enum_arguments() {
        let program = parse_program(
            "(#enum Wide ((Values u64 u64 u64 u64 u64 u64 u64) Empty)) (#fn last ((value Wide)) u64 (#return (#match value ((Values first second third fourth fifth sixth last) last) (_ 0u64)))) (#fn main () u64 (#return (last (Values 1u64 2u64 3u64 4u64 5u64 6u64 42u64))))",
        )
        .unwrap();
        assert!(generate_assembly(&program).is_ok());
    }

    #[test]
    fn checks_and_lowers_type_aliases() {
        let program = parse_program(
            "(#type UserId u64) (#fn add_one ((id UserId)) UserId (#return (#u64.+.wrap  id 1))) (#fn main () UserId (#return (add_one 41)))",
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
            "(#type Value u64) (#enum Box ((Some Value) None)) (#fn main () u64 (#return (#match (Some 42) ((Some value) value) (None 0))))",
        )
        .unwrap();
        assert!(check_types(&enum_payload).is_ok());
        assert!(generate_assembly(&enum_payload).is_ok());
        let generic = parse_program(
            "(#type Pair (T) (#tuple T T)) (#fn main () u64 (#let pair Pair<u64> (#tuple 20 22)) (#return (#u64.+.wrap  (#get pair 0) (#get pair 1))))",
        )
        .unwrap();
        assert!(check_types(&generic).is_ok());
        assert!(generate_assembly(&generic).is_ok());
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
}
