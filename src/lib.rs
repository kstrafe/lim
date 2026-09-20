//! Lexer and parser for Lim's Lisp syntax.
//!
//! This crate deliberately has no dependencies.  The syntax tree keeps the
//! `@` sigil as a first-class expression so macro/generated-code expansion can
//! be implemented later without changing the parser's public representation.

use std::fmt;

mod codegen;
mod typecheck;

pub use codegen::generate_assembly;
pub use typecheck::check_types;

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
                b'#' if self.source.get(self.offset + 1) != Some(&b'\\') => {
                    self.skip_comment();
                }
                b'(' => tokens.push(self.one(TokenKind::LParen)),
                b')' => tokens.push(self.one(TokenKind::RParen)),
                b'\'' => tokens.push(self.one(TokenKind::Quote)),
                b'@' => tokens.push(self.one(TokenKind::At)),
                b'"' => tokens.push(self.string_token()?),
                b'#' if self.source.get(self.offset + 1) == Some(&b'\\') => {
                    tokens.push(self.char_token()?)
                }
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
                || matches!(byte, b'(' | b')' | b'\'' | b'"' | b'@' | b'#' | b';')
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
                let mut chars = text.chars();
                let Some(character) = chars.next() else {
                    return Err(self.error("character literal is empty"));
                };
                if chars.next().is_some() {
                    return Err(self.error("character literal must contain one character"));
                }
                character
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
    /// The generated-code sigil in source, e.g. `(@optional T T?)`.
    At,
    Quote(Box<Expr>),
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
    Tuple(Vec<Type>),
    Array(Box<Type>, usize),
    Named(String),
}

impl Type {
    pub fn from_name(name: &str) -> Self {
        match name {
            "()" => Self::Unit,
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
    Break,
    Continue,
    Return(Option<Expr>),
    Expr(Expr),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Function {
    pub name: String,
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
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Item {
    TypeAlias {
        name: String,
        target: Type,
    },
    Function(Function),
    Struct {
        name: String,
        fields: Vec<Field>,
    },
    Enum {
        name: String,
        variants: Vec<EnumVariant>,
    },
    Let {
        name: String,
        ty: Type,
        value: Expr,
        mutable: bool,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Program {
    pub items: Vec<Item>,
}

/// Parse top-level `fn` and `let` forms into the typed declaration AST.
///
/// The lower-level [`parse`] function remains available for syntax that has
/// not acquired a language-level meaning yet, such as future macros.
pub fn parse_program(source: &str) -> Result<Program, String> {
    let expressions = parse(source)?;
    let mut items = Vec::with_capacity(expressions.len());
    for expression in expressions {
        if let Expr::List(forms) = &expression.expr {
            if matches!(forms.first(), Some(Expr::At)) {
                items.extend(parse_generated_items(forms)?);
                continue;
            }
        }
        items.push(parse_item(&expression.expr)?);
    }
    Ok(Program { items })
}

fn parse_item(expression: &Expr) -> Result<Item, String> {
    let items = expect_list(expression, "top-level declaration")?;
    if matches!(items.first(), Some(Expr::At)) {
        return parse_generated_item(items);
    }
    let keyword = expect_symbol(items.first(), "declaration keyword")?;
    match keyword {
        "type" => {
            if items.len() != 3 {
                return Err("type requires a name and target type".into());
            }
            Ok(Item::TypeAlias {
                name: expect_symbol(items.get(1), "type alias name")?.to_owned(),
                target: parse_type(items.get(2))?,
            })
        }
        "fn" => Ok(Item::Function(parse_function(items)?)),
        "struct" => Ok(Item::Struct {
            name: parse_struct_name(items)?,
            fields: parse_struct_fields(items)?,
        }),
        "enum" => Ok(Item::Enum {
            name: parse_enum_name(items)?,
            variants: parse_enum_variants(items)?,
        }),
        "let" => {
            let binding = parse_let(items)?;
            Ok(Item::Let {
                name: binding.name,
                ty: binding.ty,
                value: binding.value,
                mutable: binding.mutable,
            })
        }
        other => Err(format!("unknown top-level form '{other}'")),
    }
}

fn parse_generated_item(items: &[Expr]) -> Result<Item, String> {
    if items.len() != 4
        || !matches!(items.first(), Some(Expr::At))
        || !matches!(items.get(1), Some(Expr::Symbol(name)) if name == "optional")
    {
        return Err(
            "generated declaration must have the form (@optional Type OptionalType)".into(),
        );
    }
    let payload = parse_type(items.get(2))?;
    let name = expect_symbol(items.get(3), "generated optional type name")?.to_owned();
    Ok(Item::Enum {
        name: name.clone(),
        variants: vec![
            EnumVariant {
                name: format!("{name}-some"),
                fields: vec![payload],
            },
            EnumVariant {
                name: format!("{name}-none"),
                fields: Vec::new(),
            },
        ],
    })
}

fn parse_generated_items(items: &[Expr]) -> Result<Vec<Item>, String> {
    let generated = parse_generated_item(items)?;
    let Item::Enum { name, variants } = &generated else {
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
    Ok(vec![
        generated,
        Item::Function(Function {
            name: format!("{name}-construct"),
            parameters: vec![Parameter {
                name: "value".into(),
                ty: payload,
                mutable: false,
            }],
            return_type: Type::Named(name),
            body: vec![Statement::Expr(Expr::List(vec![
                Expr::Symbol(some),
                Expr::Symbol("value".into()),
            ]))],
        }),
    ])
}

fn parse_struct_name(items: &[Expr]) -> Result<String, String> {
    if items.len() != 3 {
        return Err("struct requires a name and field list".into());
    }
    Ok(expect_symbol(items.get(1), "struct name")?.to_owned())
}

fn parse_struct_fields(items: &[Expr]) -> Result<Vec<Field>, String> {
    let fields = expect_list(items.get(2).unwrap(), "struct fields")?;
    let mut result = Vec::with_capacity(fields.len());
    for field in fields {
        let fields = expect_list(field, "struct field")?;
        if fields.len() != 2 {
            return Err("struct fields must have the form (name Type)".into());
        }
        result.push(Field {
            name: expect_symbol(fields.first(), "field name")?.to_owned(),
            ty: parse_type(fields.get(1))?,
        });
    }
    Ok(result)
}

fn parse_enum_name(items: &[Expr]) -> Result<String, String> {
    if items.len() != 3 {
        return Err("enum requires a name and variant list".into());
    }
    Ok(expect_symbol(items.get(1), "enum name")?.to_owned())
}

fn parse_enum_variants(items: &[Expr]) -> Result<Vec<EnumVariant>, String> {
    let variants = expect_list(items.get(2).unwrap(), "enum variants")?;
    if variants.is_empty() {
        return Err("enum requires at least one variant".into());
    }
    let mut result = Vec::with_capacity(variants.len());
    for variant in variants {
        let (name, fields) = match variant {
            Expr::Symbol(name) => (name.clone(), Vec::new()),
            Expr::List(items) => {
                if items.is_empty() {
                    return Err("enum variant cannot be empty".into());
                }
                let name = expect_symbol(items.first(), "enum variant name")?.to_owned();
                let fields = items[1..]
                    .iter()
                    .map(|field| parse_type(Some(field)))
                    .collect::<Result<Vec<_>, _>>()?;
                (name, fields)
            }
            _ => return Err("enum variant must be a symbol or (name Type ...)".into()),
        };
        if result
            .iter()
            .any(|existing: &EnumVariant| existing.name == name)
        {
            return Err(format!("duplicate enum variant '{name}'"));
        }
        result.push(EnumVariant { name, fields });
    }
    Ok(result)
}

fn parse_function(items: &[Expr]) -> Result<Function, String> {
    if items.len() < 4 {
        return Err("fn requires a name, parameter list, return type, and body".into());
    }
    let name = expect_symbol(items.get(1), "function name")?.to_owned();
    let parameter_items = expect_list(items.get(2).unwrap(), "function parameters")?;
    let mut parameters = Vec::with_capacity(parameter_items.len());
    for parameter in parameter_items {
        let fields = expect_list(parameter, "function parameter")?;
        let mutable = matches!(fields.first(), Some(Expr::Symbol(name)) if name == "mut");
        let expected_len = if mutable { 3 } else { 2 };
        if fields.len() != expected_len {
            return Err(
                "function parameters must have the form (name Type) or (mut name Type)".into(),
            );
        }
        let name_index = if mutable { 1 } else { 0 };
        let type_index = if mutable { 2 } else { 1 };
        parameters.push(Parameter {
            name: expect_symbol(fields.get(name_index), "parameter name")?.to_owned(),
            ty: parse_type(fields.get(type_index))?,
            mutable,
        });
    }

    let return_type = parse_type(items.get(3))?;
    let mut body = Vec::with_capacity(items.len() - 4);
    for expression in &items[4..] {
        body.push(parse_statement(expression)?);
    }
    Ok(Function {
        name,
        parameters,
        return_type,
        body,
    })
}

fn lower_expr(expression: &Expr) -> Result<Expr, String> {
    match expression {
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
    if !matches!(items.first(), Some(Expr::Symbol(keyword)) if keyword == "let")
        || !(items.len() == 4 || items.len() == 5)
    {
        return Err("let requires the form (let name Type value)".into());
    }
    let mutable = matches!(items.get(1), Some(Expr::Symbol(keyword)) if keyword == "mut");
    let name_index = if mutable { 2 } else { 1 };
    let type_index = name_index + 1;
    let value_index = type_index + 1;
    if mutable && items.len() != 5 {
        return Err("mutable let requires the form (let mut name Type value)".into());
    }
    Ok(LetBinding {
        name: expect_symbol(items.get(name_index), "binding name")?.to_owned(),
        ty: parse_type(items.get(type_index))?,
        value: lower_expr(&items[value_index])?,
        mutable,
    })
}

fn parse_statement(expression: &Expr) -> Result<Statement, String> {
    let lowered = lower_expr(expression)?;
    let expression = &lowered;
    if is_form(expression, "let") {
        let binding = parse_let(expect_list(expression, "let statement")?)?;
        return Ok(Statement::Let {
            name: binding.name,
            ty: binding.ty,
            value: binding.value,
            mutable: binding.mutable,
        });
    }
    if is_form(expression, "set") {
        let items = expect_list(expression, "assignment")?;
        if items.len() != 3 {
            return Err("set requires the form (set name value)".into());
        }
        return Ok(Statement::Assign {
            name: expect_symbol(items.get(1), "assignment name")?.to_owned(),
            value: items[2].clone(),
        });
    }
    if is_form(expression, "set-index") {
        let items = expect_list(expression, "array assignment")?;
        if items.len() != 4 {
            return Err("set-index requires the form (set-index array index value)".into());
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
            return Err("set-field requires the form (set-field struct field value)".into());
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
    if is_form(expression, "loop") {
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
        if expect_list(expression, "break statement")?.len() != 1 {
            return Err("break takes no arguments".into());
        }
        return Ok(Statement::Break);
    }
    if is_form(expression, "continue") {
        if expect_list(expression, "continue statement")?.len() != 1 {
            return Err("continue takes no arguments".into());
        }
        return Ok(Statement::Continue);
    }
    if is_form(expression, "return") {
        let items = expect_list(expression, "return statement")?;
        if items.len() > 2 {
            return Err("return takes zero or one expression".into());
        }
        return Ok(Statement::Return(items.get(1).cloned()));
    }
    Ok(Statement::Expr(expression.clone()))
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
            if length == 0 {
                return Err("arrays must have a non-zero length".into());
            }
            return Ok(Type::Array(Box::new(element), length));
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
            TokenKind::At => {
                self.index += 1;
                Ok(SpannedExpr {
                    expr: Expr::At,
                    span: token.span,
                })
            }
            TokenKind::Symbol(value) => {
                self.index += 1;
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
        let tokens = lex("(fn add ((left i32) (right i32)) i32 (+ left right))").unwrap();
        assert_eq!(tokens[0].kind, TokenKind::LParen);
        assert_eq!(tokens[1].kind, TokenKind::Symbol("fn".into()));
        assert_eq!(tokens[6].kind, TokenKind::Symbol("i32".into()));

        let generated = lex("(@optional MyType MyType?)").unwrap();
        assert_eq!(generated[1].kind, TokenKind::At);
        assert_eq!(generated[4].kind, TokenKind::Symbol("MyType?".into()));
    }

    #[test]
    fn parses_nested_lists_quotes_and_comments() {
        let expressions = parse("# header\n'(fn main () i32 42) ; tail\n").unwrap();
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
    }

    #[test]
    fn reports_unterminated_list() {
        let error = parse("(fn missing").unwrap_err();
        assert!(error.contains("unterminated list"));
    }

    #[test]
    fn parses_typed_lets_and_functions() {
        let program = parse_program(
            "(fn add ((left u32) (right u64)) u64 (let total u64 (+ left right)) total)",
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
        assert!(
            matches!(function.body[1], Statement::Expr(Expr::Symbol(ref name)) if name == "total")
        );
    }

    #[test]
    fn parses_all_builtin_scalar_types_and_named_types() {
        let program = parse_program(
            "(fn types ((a u8) (b u16) (c u32) (d u64) (e u128) (f usize) (g i8) (h i16) (i i32) (j i64) (k i128) (l isize) (m f32) (n f64) (o bool) (p char) (q UserId)) () ())",
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
    fn rejects_malformed_let_and_functions() {
        assert!(parse_program("(let value u32)")
            .unwrap_err()
            .contains("let requires"));
        let broken = parse_program("(fn broken ((value u32)) u32)").unwrap();
        assert!(check_types(&broken)
            .unwrap_err()
            .contains("return of function"));
        assert!(parse_program("(unknown form)")
            .unwrap_err()
            .contains("unknown top-level"));
        let empty = parse_program("(fn empty () ())").unwrap();
        assert!(check_types(&empty).is_ok());
        assert!(generate_assembly(&empty).is_ok());
        let missing_value = parse_program("(fn missing () u64)").unwrap();
        assert!(check_types(&missing_value)
            .unwrap_err()
            .contains("return of function"));
    }

    #[test]
    fn generates_native_integer_assembly() {
        let program = parse_program("(fn main () i64 (+ 20 22))").unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains(".globl main"));
        assert!(assembly.contains("add rax, rcx"));
        assert!(assembly.contains("ret"));
        assert!(assembly.contains(".note.GNU-stack"));
    }

    #[test]
    fn type_checks_variables_calls_and_returns() {
        let program =
            parse_program("(fn inc ((value u32)) u32 (+ value 1)) (fn main () u32 (inc 41))")
                .unwrap();
        assert!(check_types(&program).is_ok());
        let mismatch = parse_program("(fn main () u32 true)").unwrap();
        assert!(check_types(&mismatch).unwrap_err().contains("expected U32"));
        let unknown = parse_program("(fn main () u32 missing)").unwrap();
        assert!(check_types(&unknown)
            .unwrap_err()
            .contains("unknown variable"));
    }

    #[test]
    fn parses_mutable_while_statements() {
        let program =
            parse_program("(fn count () u64 (let mut n u64 0) (while (< n 3) (set n (+ n 1))) n)")
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
        let program = parse_program("(fn main () u64 18446744073709551615)").unwrap();
        assert!(check_types(&program).is_ok());
        let too_large = parse_program("(fn main () u32 4294967296)").unwrap();
        assert!(check_types(&too_large)
            .unwrap_err()
            .contains("does not fit"));
    }

    #[test]
    fn checks_break_and_continue_scope() {
        let valid = parse_program(
            "(fn main () u64 (let mut n u64 0) (while (< n 3) (set n (+ n 1)) (continue)) n)",
        )
        .unwrap();
        assert!(check_types(&valid).is_ok());
        let invalid = parse_program("(fn main () () (break))").unwrap();
        assert!(check_types(&invalid)
            .unwrap_err()
            .contains("outside a loop"));
    }

    #[test]
    fn checks_and_lowers_early_return() {
        let program = parse_program("(fn main () u64 (return 42) 0)").unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("mov rax, 42"));
        assert!(assembly.contains("jmp .Lreturn_main"));
    }

    #[test]
    fn generates_integer_operator_family() {
        let program = parse_program("(fn main () i64 (% (/ (^ 20 1) 2) 3))").unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("idiv rcx"));
        assert!(assembly.contains("xor rax, rcx"));
    }

    #[test]
    fn lowers_unsigned_division_and_remainder() {
        let program = parse_program(
            "(fn main () u64 (let left u64 20) (let right u64 3) (+ (/ left right) (% left right)))",
        )
        .unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("div rcx"));
        assert!(!assembly.contains("idiv rcx"));
    }

    #[test]
    fn lowers_float_values_inside_aggregates() {
        let program = parse_program(
            "(struct Point ((x f64) (y f32))) (fn main () u64 (let point Point (Point 1.5 2.5)) (let x f64 (get point x)) (let values (array f32 2) (array 1.5 2.5)) (let y f32 (index values 1)) (if (&& (> x 1.0) (> y 2.0)) 42 0))",
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
            parse_program("(fn main () u64 (let value u64 1) (if (< value 2) (>> value 1) 0))")
                .unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("setb al"));
        assert!(assembly.contains("shr rax, cl"));
    }

    #[test]
    fn checks_and_lowers_explicit_integer_casts() {
        let program = parse_program("(fn main () u64 (as (as 42 u32) u64))").unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("mov rax, 42"));
        let invalid = parse_program("(fn main () u64 (as 42 ()))").unwrap();
        assert!(check_types(&invalid).unwrap_err().contains("numeric"));
    }

    #[test]
    fn checks_and_lowers_numeric_casts() {
        let program = parse_program(
            "(fn main () u64 (let value f64 41.75) (let whole u64 (as value u64)) (let small f32 (as whole f32)) (as small u64))",
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
            "(fn widen () u128 (as 42 u128)) (fn main () u64 (let value u128 (widen)) (as value u64))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("xor edx, edx"));
        let signed = parse_program("(fn main () i64 (as (as (- 1) i128) i64))").unwrap();
        assert!(check_types(&signed).is_ok());
        assert!(generate_assembly(&signed).unwrap().contains("sar rdx, 63"));
    }

    #[test]
    fn passes_aggregate_values_with_mixed_float_parameters() {
        let program = parse_program(
            "(struct Pair ((scale f32) (value u64))) (fn consume ((pair Pair) (factor f32)) u64 (if (> (get pair scale) 1.0) (+ (get pair value) 1) 0)) (fn main () u64 (consume (Pair 1.5 41) 2.0))",
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
            "(struct Values ((a u64) (b u64) (c u64) (d u64) (e u64) (f u64))) (fn make () Values (Values 1 2 3 4 5 6)) (fn sum ((value Values)) u64 (+ (+ (+ (+ (+ (get value a) (get value b)) (get value c)) (get value d)) (get value e)) (get value f))) (fn main () u64 (sum (make)))",
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
            "(fn blend ((small f32) (large f64)) f64 (+ (as small f64) large)) (fn main () u64 (if (> (blend 1.5 2.5) 4.0) 42 0))",
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
            "(fn make () (tuple u64 f32) (tuple 40 2.5)) (fn consume ((value (tuple u64 f32))) u64 (+ (get value 0) (as (get value 1) u64))) (fn main () u64 (let value (tuple u64 f32) (make)) (consume value))",
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
            "(fn main () u64 (let mut value (tuple u64 f32) (tuple 1 2.5)) (set-field value 0 40) (+ (get value 0) 2))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program)
            .unwrap()
            .contains("QWORD PTR [rbp-8]"));
        let invalid = parse_program(
            "(fn main () u64 (let value (tuple u64 f32) (tuple 1 2.5)) (set-field value 0 40) 0)",
        )
        .unwrap();
        assert!(check_types(&invalid)
            .unwrap_err()
            .contains("immutable variable"));
    }

    #[test]
    fn normalizes_integer_width_after_arithmetic() {
        let program = parse_program(
            "(fn main () u64 (let value u8 (+ (as 255 u8) 1)) (if (== value 0) 42 0))",
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
            parse_program("(let WRAPPED u8 (+ 255 1)) (fn main () u64 (if (== WRAPPED 0) 42 0))")
                .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("WRAPPED:\n    .quad 0"));
    }

    #[test]
    fn preserves_float_width_across_control_flow() {
        let program = parse_program(
            "(fn choose ((flag bool)) f32 (if flag 1.5 2.5)) (fn main () u64 (if (> (choose true) 1.0) 42 0))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("movd xmm0, eax"));
        let matched = parse_program(
            "(enum MaybeF ((SomeF f32) None)) (fn read ((value MaybeF)) f32 (match value ((SomeF payload) payload) (None 2.5))) (fn main () u64 (if (> (read None) 2.0) 42 0))",
        )
        .unwrap();
        assert!(check_types(&matched).is_ok());
        assert!(generate_assembly(&matched)
            .unwrap()
            .contains("movd xmm0, eax"));
    }

    #[test]
    fn handles_nan_float_comparisons() {
        let program = parse_program("(fn main () u64 (if (!= (/ 0.0 0.0) 0.0) 42 0))").unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("jp .Lfloat_unordered"));
    }

    #[test]
    fn checks_shift_counts_against_integer_width() {
        let program = parse_program("(fn main () u64 (<< 21 1))").unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("shift_failure"));
        let invalid = parse_program("(fn main () u8 (<< (as 1 u8) 8))").unwrap();
        assert!(check_types(&invalid)
            .unwrap_err()
            .contains("shift count 8 is out of range"));
        let wide = parse_program("(fn main ((count u128)) u128 (<< (as 1 u128) count))").unwrap();
        assert!(generate_assembly(&wide)
            .unwrap()
            .contains("wide_shift_failure"));
    }

    #[test]
    fn accepts_high_bit_u128_literals() {
        let program = parse_program(
            "(fn make () u128 0x8000000000000000000000000000002a) (fn main () u64 (as (make) u64))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("mov rdx, 0x8000000000000000"));
    }

    #[test]
    fn lowers_unit_functions_and_calls() {
        let program = parse_program("(fn noop () () ()) (fn main () u64 (noop) 42)").unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains(".globl noop"));
        assert!(assembly.contains("call noop"));
    }

    #[test]
    fn checks_and_lowers_mutable_parameters() {
        let program =
            parse_program("(fn increment ((mut value u64)) u64 (set value (+ value 1)) value)")
                .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program)
            .unwrap()
            .contains("add rax, rcx"));
        let invalid =
            parse_program("(fn increment ((value u64)) u64 (set value 1) value)").unwrap();
        assert!(check_types(&invalid).unwrap_err().contains("immutable"));
    }

    #[test]
    fn checks_and_lowers_f64_arithmetic() {
        let program = parse_program(
            "(fn calculate () f64 (let left f64 1.5) (let right f64 2.25) (+ left right))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("addsd xmm1, xmm0"));
        assert!(assembly.contains("movq xmm0"));
        let parameter = parse_program("(fn calculate ((value f64)) f64 value)").unwrap();
        assert!(generate_assembly(&parameter)
            .unwrap()
            .contains("movq QWORD PTR [rbp-8], xmm0"));
        let called = parse_program(
            "(fn add ((left f64) (right f64)) f64 (+ left right)) (fn main () f64 (add 1.5 2.5))",
        )
        .unwrap();
        assert!(generate_assembly(&called).unwrap().contains("call add"));
        let mixed = parse_program(
            "(fn choose ((value u64) (scale f64)) u64 (if (> scale 1.0) value 0)) (fn main () u64 (choose 42 2.0))",
        )
        .unwrap();
        assert!(check_types(&mixed).is_ok());
        assert!(generate_assembly(&mixed).unwrap().contains("movq xmm0"));
    }

    #[test]
    fn checks_and_lowers_f32_arithmetic_and_calls() {
        let program = parse_program(
            "(fn add ((left f32) (right f32)) f32 (+ left right)) (fn main () u64 (if (> (add 1.5 2.5) 3.0) 42 0))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("addss xmm1, xmm0"));
        assert!(assembly.contains("ucomiss xmm1, xmm0"));
        assert!(assembly.contains("movd xmm0"));
        let overflow_f32 = parse_program("(fn main () f32 1e100)").unwrap();
        assert!(check_types(&overflow_f32)
            .unwrap_err()
            .contains("not finite for F32"));
        let overflow_f64 = parse_program("(fn main () f64 1e400)").unwrap();
        assert!(check_types(&overflow_f64)
            .unwrap_err()
            .contains("not finite for F64"));
    }

    #[test]
    fn checks_and_lowers_char_values() {
        let program = parse_program("(fn main () u64 (if (== #\\a #\\a) 42 0))").unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("mov rax, 97"));
    }

    #[test]
    fn expands_optional_generated_declarations() {
        let program = parse_program(
            "(@optional u64 Maybe?) (fn main () u64 (let value Maybe? (Maybe?-construct 42)) (match value ((Maybe?-some payload) payload) (Maybe?-none 0)))",
        )
        .unwrap();
        assert!(program.items.iter().any(|item| {
            matches!(item, Item::Function(function) if function.name == "Maybe?-construct")
        }));
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program)
            .unwrap()
            .contains(".globl Maybe_x3f__x2d_construct"));
    }

    #[test]
    fn parses_and_checks_value_structs() {
        let program = parse_program(
            "(struct Point ((x u64) (y u64))) (fn point_x () u64 (get (Point 7 9) x))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("mov rax, 7"));
        let local = parse_program(
            "(struct Point ((x u64) (y u64))) (fn point_y () u64 (let p Point (Point 7 9)) (get p y))",
        )
        .unwrap();
        assert!(generate_assembly(&local).unwrap().contains("[rbp-16]"));
        let mutable = parse_program("(struct Point ((x u64) (y u64))) (fn main () u64 (let mut p Point (Point 1 2)) (set-field p y 40) (+ (get p x) (get p y)))").unwrap();
        assert!(check_types(&mutable).is_ok());
        let returned =
            parse_program("(struct Point ((x u64) (y u64))) (fn make_point () Point (Point 7 9))")
                .unwrap();
        assert!(check_types(&returned).is_ok());
        assert!(generate_assembly(&returned).unwrap().contains("pop rdx"));
        let consumed = parse_program(
            "(struct Point ((x u64) (y u64))) (fn make_point () Point (Point 7 9)) (fn main () u64 (let point Point (make_point)) (get point y))",
        )
        .unwrap();
        assert!(check_types(&consumed).is_ok());
        assert!(generate_assembly(&consumed)
            .unwrap()
            .contains("call make_point"));
        let unsupported_parameter = parse_program(
            "(struct Point ((x u64) (y u64))) (fn identity ((point Point)) Point point) (fn main () u64 (let result Point (identity (Point 11 37))) (get result y))",
        )
        .unwrap();
        assert!(check_types(&unsupported_parameter).is_ok());
        assert!(generate_assembly(&unsupported_parameter)
            .unwrap()
            .contains("call identity"));
    }

    #[test]
    fn checks_boolean_and_unary_operators() {
        let program = parse_program("(fn main () bool (&& (! false) (|| false true)))").unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("and_false"));
        assert!(assembly.contains("xor eax, 1"));
        let bitwise = parse_program("(fn main () bool (^ (& true true) false))").unwrap();
        assert!(check_types(&bitwise).is_ok());
        let bitwise_assembly = generate_assembly(&bitwise).unwrap();
        assert!(bitwise_assembly.contains("and rax, rcx"));
        assert!(bitwise_assembly.contains("xor rax, rcx"));
        let invalid_float = parse_program("(fn main () f64 (& 1.0 2.0))").unwrap();
        assert!(check_types(&invalid_float)
            .unwrap_err()
            .contains("requires integer or boolean"));
        let unit_if = parse_program("(fn main () () (if true ()))").unwrap();
        assert!(check_types(&unit_if).is_ok());
        assert!(generate_assembly(&unit_if)
            .unwrap()
            .contains("xor eax, eax"));
        let missing_else = parse_program("(fn main () u64 (if true 1))").unwrap();
        assert!(check_types(&missing_else)
            .unwrap_err()
            .contains("if without else"));
    }

    #[test]
    fn checks_and_lowers_integer_bitwise_not() {
        let program = parse_program("(fn main () u32 (let value u32 (! 0)) (& value 42))").unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("not rax"));
        let invalid = parse_program("(fn main () u64 (! 1.0))").unwrap();
        assert!(check_types(&invalid)
            .unwrap_err()
            .contains("must be a boolean or integer"));
    }

    #[test]
    fn checks_and_lowers_payload_free_enums() {
        let program = parse_program(
            "(enum Color (Red Green Blue)) (fn main () u64 (match Green (Red 10) (Green 20) (_ 30)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("cmp QWORD PTR [rsp], 1"));
        assert!(parse_program("(enum Bad (Same Same))")
            .unwrap_err()
            .contains("duplicate enum variant"));
    }

    #[test]
    fn checks_and_lowers_multi_payload_enums() {
        let program = parse_program(
            "(enum Pair ((Pair u64 u64) Empty)) (fn main () u64 (let value Pair (Pair 20 22)) (match value ((Pair left right) (+ left right)) (Empty 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("mov rax, 20"));
    }

    #[test]
    fn passes_multi_payload_enums_through_functions() {
        let program = parse_program(
            "(enum Pair ((Pair u64 u64) Empty)) (fn make () Pair (let value Pair (Pair 20 22)) value) (fn sum ((value Pair)) u64 (match value ((Pair left right) (+ left right)) (Empty 0))) (fn main () u64 (sum (make)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("call sum"));
    }

    #[test]
    fn lowers_two_word_128_bit_integers() {
        let program = parse_program(
            "(fn add ((left u128) (right u128)) u128 (+ left right)) (fn main () u64 (as (add 20 22) u64))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("adc rdx, r8"));
        assert!(assembly.contains("call add"));
        let minimum =
            parse_program("(fn main () i128 -170141183460469231731687303715884105728)").unwrap();
        assert!(check_types(&minimum).is_ok());
        assert!(generate_assembly(&minimum).is_ok());
    }

    #[test]
    fn lowers_128_bit_comparisons_and_shifts() {
        let program = parse_program(
            "(fn main () u64 (let left u128 1) (let right u128 2) (if (&& (< left right) (== (<< left 5) 32)) 42 0))",
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
            "(fn multiply ((left u128) (right u128)) u128 (* left right)) (fn main () u64 (as (multiply 6 7) u64))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("mul rcx"));
    }

    #[test]
    fn lowers_unsigned_128_bit_division_and_remainder() {
        let program = parse_program(
            "(fn main () u64 (let value u128 100) (let divisor u128 7) (if (&& (== (/ value divisor) 14) (== (% value divisor) 2)) 42 0))",
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
            "(fn main () u64 (let value i128 100) (let divisor i128 7) (if (&& (== (/ (- value) divisor) -14) (== (% (- value) divisor) -2)) 42 0))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("sar r9, 63"));
    }

    #[test]
    fn checks_and_lowers_scalar_enum_payloads() {
        let program = parse_program(
            "(enum Maybe ((Some u64) None)) (fn main () u64 (let value Maybe (Some 42)) (match value ((Some _) 42) (None 7)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("mov QWORD PTR [rbp-8], 0"));
        assert!(assembly.contains("cmp QWORD PTR [rsp], 0"));
        let invalid = parse_program(
            "(enum Maybe ((Some u64) None)) (fn main () u64 (match None ((Some _) 1)))",
        )
        .unwrap();
        assert!(check_types(&invalid)
            .unwrap_err()
            .contains("not exhaustive"));
        let binding = parse_program(
            "(enum Maybe ((Some u64) None)) (fn main () u64 (let value Maybe (Some 42)) (match value ((Some payload) payload) (None 0)))",
        )
        .unwrap();
        assert!(check_types(&binding).is_ok());
        assert!(generate_assembly(&binding)
            .unwrap()
            .contains("mov QWORD PTR [rbp-24], rax"));
        let returned = parse_program(
            "(enum Maybe ((Some u64) None)) (fn make () Maybe (Some 42)) (fn main () u64 (let value Maybe (make)) (match value ((Some payload) payload) (None 0)))",
        )
        .unwrap();
        assert!(check_types(&returned).is_ok());
        assert!(generate_assembly(&returned).unwrap().contains("call make"));
        let passed = parse_program(
            "(enum Maybe ((Some u64) None)) (fn identity ((value Maybe)) Maybe value) (fn main () u64 (let result Maybe (identity (Some 42))) (match result ((Some payload) payload) (None 0)))",
        )
        .unwrap();
        assert!(check_types(&passed).is_ok());
        assert!(generate_assembly(&passed)
            .unwrap()
            .contains("call identity"));
        let repeated = parse_program(
            "(fn main () u64 (let values (array u64 3) (array-repeat 13)) (index values 1))",
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
            "(enum Maybe ((Some u64) None)) (fn main () u64 (match (Some 42) ((Some value) value) (None 0)))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("add rsp, 16"));
    }

    #[test]
    fn indexes_arrays_returned_by_functions() {
        let program = parse_program(
            "(fn make () (array u64 3) (array 10 20 30)) (fn main () u64 (index (make) 1))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("call make"));
    }

    #[test]
    fn selects_fields_from_structs_returned_by_functions() {
        let program = parse_program(
            "(struct Point ((x u64) (y u64))) (fn make () Point (Point 7 9)) (fn main () u64 (get (make) y))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("call make"));
    }

    #[test]
    fn passes_floating_struct_fields_through_functions() {
        let program = parse_program(
            "(struct Point ((x f64) (y f32))) (fn make () Point (Point 1.5 2.5)) (fn main () u64 (if (&& (> (get (make) x) 1.0) (> (get (make) y) 2.0)) 42 0))",
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
            "(fn sum ((values (array f32 2))) f32 (index values 1)) (fn make () (array f32 2) (array 1.5 2.5)) (fn main () u64 (let value f32 (sum (make))) (if (> value 2.0) 42 0))",
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
            "(fn make () (array f32 2) (array 1.5 2.5)) (fn main () u64 (if (> (index (make) 1) 2.0) 42 0))",
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
            "(enum MaybeF ((SomeF f32) None)) (fn make () MaybeF (SomeF 2.5)) (fn read ((value MaybeF)) f32 (match value ((SomeF payload) payload) (None 0.0))) (fn main () u64 (if (> (read (make)) 2.0) 42 0))",
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
            "(fn classify ((value u64)) u64 (match value (0 10) (1 20) (_ 30))) (fn main () u64 (classify 1))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("cmp QWORD PTR [rsp], 1"));
        let bools = parse_program("(fn main () u64 (match true (true 42) (false 0)))").unwrap();
        assert!(check_types(&bools).is_ok());
        let incomplete = parse_program("(fn main () u64 (match 1 (1 42)))").unwrap();
        assert!(check_types(&incomplete)
            .unwrap_err()
            .contains("not exhaustive"));
    }

    #[test]
    fn checks_and_lowers_fixed_arrays() {
        let program = parse_program("(fn main () u64 (let mut values (array u64 2) (array 3 4)) (set-index values 1 40) (+ (index values 0) (index values 1)))").unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("lea rdx"));
        assert!(assembly.contains("shl rcx, 3"));
        assert!(assembly.contains("jae"));
        assert!(assembly.contains("ud2"));
        let invalid = parse_program(
            "(fn main () u64 (let values (array u64 2) (array 1 2)) (index values 2))",
        )
        .unwrap();
        assert!(check_types(&invalid).unwrap_err().contains("out of bounds"));
        let passed = parse_program(
            "(fn identity ((values (array u64 3))) (array u64 3) values) (fn main () u64 (let values (array u64 3) (identity (array 10 20 37))) (index values 2))",
        )
        .unwrap();
        assert!(check_types(&passed).is_ok());
        assert!(generate_assembly(&passed)
            .unwrap()
            .contains("call identity"));
    }

    #[test]
    fn lowers_stack_arguments() {
        let program = parse_program("(fn sum8 ((a u64) (b u64) (c u64) (d u64) (e u64) (f u64) (g u64) (h u64)) u64 (+ (+ (+ (+ (+ (+ (+ a b) c) d) e) f) g) h)) (fn main () u64 (sum8 1 2 3 4 5 6 7 8))").unwrap();
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("[rbp+16]"));
        assert!(assembly.contains("[rbp+24]"));
    }

    #[test]
    fn lowers_for_loop_with_continue_step() {
        let program = parse_program("(fn main () u64 (let mut total u64 0) (for (let mut i u64 0) (< i 3) (set i (+ i 1)) (continue)) total)").unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("for_step"));
    }

    #[test]
    fn lowers_statement_blocks_in_expressions() {
        let program =
            parse_program("(fn main () u64 (let mut value u64 1) (if true (block (set value 40) value) (block value)))")
                .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program)
            .unwrap()
            .contains("mov QWORD PTR"));
    }

    #[test]
    fn checks_and_lowers_loop_statements() {
        let program = parse_program(
            "(fn main () u64 (let mut value u64 0) (loop (set value (+ value 1)) (break)) value)",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("loop"));
        let invalid = parse_program("(fn main () u64 (break))").unwrap();
        assert!(check_types(&invalid)
            .unwrap_err()
            .contains("outside a loop"));
    }

    #[test]
    fn keeps_loop_locals_in_lexical_scope() {
        for source in [
            "(fn main () u64 (while false (let value u64 7) (break)) value)",
            "(fn main () u64 (loop (let value u64 7) (break)) value)",
            "(fn main () u64 (for (let mut i u64 0) false (set i 1) (let value u64 7)) value)",
        ] {
            let program = parse_program(source).unwrap();
            let error = check_types(&program).unwrap_err();
            assert!(error.contains("value"), "{source}: {error}");
        }
        let valid =
            parse_program("(fn main () u64 (while false (let value u64 7) (break)) 0)").unwrap();
        assert!(check_types(&valid).is_ok());
    }
    #[test]
    fn lowers_immutable_globals() {
        let program = parse_program("(let ANSWER u64 40) (fn main () u64 (+ ANSWER 2))").unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program)
            .unwrap()
            .contains("[rip+ANSWER]"));
        let invalid = parse_program("(let mut ANSWER u64 40) (fn main () u64 ANSWER)").unwrap();
        assert!(check_types(&invalid)
            .unwrap_err()
            .contains("cannot be mutable"));
    }

    #[test]
    fn lowers_float_and_char_globals() {
        let program = parse_program(
            "(let scale f32 1.5) (let pi f64 3.25) (let letter char #\\a) (fn main () u64 (if (&& (> scale 1.0) (&& (> pi 3.0) (== letter #\\a))) 42 0))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("movss xmm0, DWORD PTR [rip+scale]"));
        assert!(assembly.contains("movq xmm0, QWORD PTR [rip+pi]"));
    }

    #[test]
    fn checks_and_lowers_type_aliases() {
        let program = parse_program(
            "(type UserId u64) (fn add_one ((id UserId)) UserId (+ id 1)) (fn main () UserId (add_one 41))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(generate_assembly(&program).unwrap().contains("add_one"));
        let invalid =
            parse_program("(type UserId u64) (fn main () UserId (let value u32 1) value)").unwrap();
        assert!(check_types(&invalid)
            .unwrap_err()
            .contains("return of function"));
        let nested = parse_program(
            "(type UserId u64) (fn main () UserId (block (let inner UserId 41) inner))",
        )
        .unwrap();
        assert!(check_types(&nested).is_ok());
        let enum_payload = parse_program(
            "(type Value u64) (enum Box ((Some Value) None)) (fn main () u64 (match (Some 42) ((Some value) value) (None 0)))",
        )
        .unwrap();
        assert!(check_types(&enum_payload).is_ok());
        assert!(generate_assembly(&enum_payload).is_ok());
    }
}
