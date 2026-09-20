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
                b'#' | b';' => {
                    self.skip_comment();
                }
                b'(' => tokens.push(self.one(TokenKind::LParen)),
                b')' => tokens.push(self.one(TokenKind::RParen)),
                b'\'' => tokens.push(self.one(TokenKind::Quote)),
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
                || matches!(byte, b'(' | b')' | b'\'' | b'"' | b'@' | b'#' | b';')
            {
                break;
            }
            self.advance();
        }
        let text = std::str::from_utf8(&self.source[start..self.offset]).unwrap();
        let kind = match text.parse::<i128>() {
            Ok(value) => TokenKind::Integer(value),
            Err(_) => TokenKind::Symbol(text.to_owned()),
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

    fn error(&self, message: &str) -> LexError {
        LexError {
            message: message.to_owned(),
            span: Span::new(self.offset, self.offset, self.line, self.column),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Expr {
    List(Vec<Expr>),
    Block(Vec<Statement>),
    Symbol(String),
    Integer(i128),
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
        items.push(parse_item(&expression.expr)?);
    }
    Ok(Program { items })
}

fn parse_item(expression: &Expr) -> Result<Item, String> {
    let items = expect_list(expression, "top-level declaration")?;
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
        let name = expect_symbol(Some(variant), "enum variant")?.to_owned();
        if result
            .iter()
            .any(|existing: &EnumVariant| existing.name == name)
        {
            return Err(format!("duplicate enum variant '{name}'"));
        }
        result.push(EnumVariant { name });
    }
    Ok(result)
}

fn parse_function(items: &[Expr]) -> Result<Function, String> {
    if items.len() < 5 {
        return Err("fn requires a name, parameter list, return type, and body".into());
    }
    let name = expect_symbol(items.get(1), "function name")?.to_owned();
    let parameter_items = expect_list(items.get(2).unwrap(), "function parameters")?;
    let mut parameters = Vec::with_capacity(parameter_items.len());
    for parameter in parameter_items {
        let fields = expect_list(parameter, "function parameter")?;
        if fields.len() != 2 {
            return Err("function parameters must have the form (name Type)".into());
        }
        parameters.push(Parameter {
            name: expect_symbol(fields.first(), "parameter name")?.to_owned(),
            ty: parse_type(fields.get(1))?,
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
        return Ok(Statement::FieldAssign {
            name: expect_symbol(items.get(1), "struct name")?.to_owned(),
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

fn parse_type(expression: Option<&Expr>) -> Result<Type, String> {
    if matches!(expression, Some(Expr::List(items)) if items.is_empty()) {
        return Ok(Type::Unit);
    }
    if let Some(Expr::List(items)) = expression {
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
        assert!(parse_program("(fn broken ((value u32)) u32)")
            .unwrap_err()
            .contains("fn requires"));
        assert!(parse_program("(unknown form)")
            .unwrap_err()
            .contains("unknown top-level"));
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
    }

    #[test]
    fn checks_boolean_and_unary_operators() {
        let program = parse_program("(fn main () bool (&& (! false) (|| false true)))").unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("and_false"));
        assert!(assembly.contains("xor eax, 1"));
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
    fn checks_and_lowers_fixed_arrays() {
        let program = parse_program("(fn main () u64 (let mut values (array u64 2) (array 3 4)) (set-index values 1 40) (+ (index values 0) (index values 1)))").unwrap();
        assert!(check_types(&program).is_ok());
        let assembly = generate_assembly(&program).unwrap();
        assert!(assembly.contains("lea rdx"));
        assert!(assembly.contains("rcx*8"));
        let invalid = parse_program(
            "(fn main () u64 (let values (array u64 2) (array 1 2)) (index values 2))",
        )
        .unwrap();
        assert!(check_types(&invalid).unwrap_err().contains("out of bounds"));
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
    }
}
