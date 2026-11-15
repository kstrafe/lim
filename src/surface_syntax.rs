//! Local surface notation lowering. The checked representation stays unchanged.
use crate::{Expr, ParseError, Parser, Span, SpannedExpr as Node, TokenKind as T};

#[derive(Clone)]
pub(super) struct Math {
    scalar: String,
    mode: Option<String>,
}

fn symbol(value: &str, span: Span) -> Node {
    Node {
        expr: Expr::Symbol(value.into()),
        span,
        children: Vec::new().into(),
    }
}

fn list(children: Vec<Node>, span: Span) -> Node {
    Node {
        expr: Expr::List(children.iter().map(|node| node.expr.clone()).collect()),
        span,
        children: children.into(),
    }
}

fn through(start: Span, end: usize) -> Span {
    Span { end, ..start }
}
fn synthetic(span: Span) -> Span {
    through(span, span.start)
}
fn name(node: &Node) -> &str {
    match &node.expr {
        Expr::Symbol(name) => name,
        _ => "",
    }
}
fn callable(node: &Node) -> bool {
    callable_name(name(node))
}

pub(super) fn callable_name(value: &str) -> bool {
    (!value.is_empty() && !value.starts_with('#') && crate::names::value_name(value))
        || crate::names::numeric_operation(value).is_some()
}

fn syntax_operand(terms: &[Node]) -> bool {
    terms.is_empty()
        || (terms.len() == 1
            && (matches!(
                name(&terms[0]),
                "#fn"
                    | "#unsafe-fn"
                    | "#extern-fn"
                    | "#static"
                    | "#const"
                    | "#call"
                    | "#unsafe-call"
                    | "#gn"
                    | "#gn-fn"
                    | "#gn-call"
                    | "#struct-literal"
                    | "#enum-literal"
                    | "#thread-task-spawn"
                    | "#thread-task-join"
                    | "#type"
                    | "#syntax"
                    | "#struct"
                    | "#enum"
                    | "#distributed-enum"
            ) || matches!(terms[0].expr, Expr::Generate)))
        || (terms.len() == 2 && name(&terms[0]) == "#extern-fn")
}

// A trailing single colon is punctuation in a record key or layout header.
// Keep the lexer unchanged so ordinary symbols and qualified names retain
// their spelling. Unquoted keys use the same rule inside generator templates.
fn split_layout_suffix(key: &Node) -> Option<(Node, Span)> {
    let (expr, children, colon) = match &key.expr {
        Expr::Symbol(value) => {
            let value = value.strip_suffix(':')?;
            if value.is_empty() || value.ends_with(':') {
                return None;
            }
            let colon = Span::new(
                key.span.end - 1,
                key.span.end,
                key.span.line,
                key.span.column + value.chars().count(),
            );
            // Decode the operand again without the colon: `11:` is an
            // integer followed by punctuation, rather than a symbol `11`.
            let mut tokens = crate::lex(value).ok()?;
            if tokens.len() != 1 {
                return None;
            }
            tokens[0].span = through(key.span, colon.start);
            let node = Parser::new(&tokens).expression_application(false).ok()?;
            (node.expr, node.children.to_vec(), colon)
        }
        Expr::Unquote(_) => {
            let (child, colon) = split_layout_suffix(key.children.first()?)?;
            (
                Expr::Unquote(Box::new(child.expr.clone())),
                vec![child],
                colon,
            )
        }
        _ => return None,
    };
    Some((
        Node {
            expr,
            span: through(key.span, colon.start),
            children: children.into(),
        },
        colon,
    ))
}

pub(super) fn record_declaration(name: &str) -> bool {
    matches!(
        name,
        "#fn" | "#unsafe-fn" | "#extern-fn" | "#static" | "#const"
    )
}

pub(super) fn has_surface_notation(node: &Node, source: &str) -> bool {
    fn implicit_call(node: &Node) -> bool {
        (name(node) == "#call" && node.span.start == node.span.end)
            || node.children.iter().any(implicit_call)
    }
    if implicit_call(node) {
        return true;
    }
    let text = &source[node.span.start..node.span.end];
    let mut lexer = crate::Lexer::new(text);
    while let Ok(Some(token)) = lexer.next_token() {
        if matches!(
            token.kind,
            T::LBrace | T::LBracket | T::Semicolon | T::Colon
        ) || matches!(token.kind, T::Symbol(ref value) if value.ends_with(':') && !value.ends_with("::"))
        {
            return true;
        }
    }
    false
}

pub(super) fn format_surface(node: &Node, source: &str) -> String {
    // Layout is semantic after a record-key colon, so retain line boundaries
    // and leading spaces. Never pretty-print the lowered tree as source sugar.
    let line = source[..node.span.start].rfind('\n').map_or(0, |i| i + 1);
    let prefix = &source[line..node.span.start];
    let start = if prefix.bytes().all(|b| b == b' ' || b == b'\t') {
        line
    } else {
        node.span.start
    };
    let text = &source[start..node.span.end];
    let mut literals = Vec::new();
    let mut lexer = crate::Lexer::new(text);
    while let Ok(Some(token)) = lexer.next_token() {
        if matches!(token.kind, T::String(_) | T::Char(_)) {
            literals.push(token.span);
        }
    }
    let mut output = String::with_capacity(text.len());
    let mut offset = 0;
    for line in text.split_inclusive('\n') {
        let newline = line.ends_with('\n');
        let mut end = line.len() - usize::from(newline);
        while end > 0 && matches!(line.as_bytes()[end - 1], b' ' | b'\t' | b'\r') {
            let byte = offset + end - 1;
            let index = literals.partition_point(|span| span.end <= byte);
            if literals
                .get(index)
                .is_some_and(|span| span.start <= byte && byte < span.end)
            {
                break;
            }
            end -= 1;
        }
        output.push_str(&line[..end]);
        if newline {
            output.push('\n');
        }
        offset += line.len();
    }
    output
}

impl<'a> Parser<'a> {
    pub(super) fn with_source(mut self, source: &'a str) -> Self {
        self.source = Some(source);
        self
    }

    fn kind(&self) -> Option<&T> {
        self.tokens.get(self.index).map(|token| &token.kind)
    }
    fn current_span(&self) -> Span {
        self.tokens
            .get(self.index)
            .map_or_else(|| self.eof_span(), |token| token.span)
    }
    fn take(&mut self, kind: T, message: &str) -> Result<Span, ParseError> {
        if self.kind() != Some(&kind) {
            return Err(self.error(message, self.current_span()));
        }
        let span = self.current_span();
        self.index += 1;
        Ok(span)
    }

    /// Read the contents of one implicit source root without creating a second
    /// list when an indented colon operand completes the declaration.
    pub(super) fn implicit_root(&mut self) -> Result<Node, ParseError> {
        let start = self.current_span();
        let mut terms: Vec<Node> = Vec::new();
        while self.kind().is_some() {
            if self.kind() == Some(&T::Colon) {
                let colon = self.take(T::Colon, "expected ':'")?;
                let header = terms.first().map_or(start, |node| node.span);
                terms.push(self.colon_value(header, colon)?);
            } else {
                let term = self.expression_application(!syntax_operand(&terms))?;
                if let Some((term, colon)) = split_layout_suffix(&term) {
                    terms.push(term);
                    terms.push(self.colon_value(start, colon)?);
                } else {
                    terms.push(term);
                }
            }
        }
        let end = terms.last().map_or(start.end, |node| node.span.end);
        self.finish_list(terms, through(start, end))
    }

    pub(super) fn top_expression(&mut self) -> Result<Node, ParseError> {
        if (matches!(self.kind(), Some(T::Symbol(value)) if record_declaration(value))
            || self.kind() == Some(&T::Generate))
            && self
                .tokens
                .get(self.index + 2)
                .is_some_and(|token| token.kind == T::LBrace)
        {
            let head = self.expression_application(false)?;
            let declared = self.expression_application(false)?;
            if self.kind() != Some(&T::LBrace) {
                return Err(self.error(
                    "an unparenthesized declaration requires a named record",
                    self.current_span(),
                ));
            }
            let fields = self.expression()?;
            let span = through(head.span, fields.span.end);
            return self.normalize_declaration(list(vec![head, declared, fields], span));
        }
        if self.top_colon_header() {
            let line = self.current_span().line;
            let mut terms = Vec::new();
            while self.kind().is_some()
                && self.current_span().line == line
                && self.kind() != Some(&T::Semicolon)
            {
                let term = self.expression_application(!syntax_operand(&terms))?;
                if let Some((term, colon)) = split_layout_suffix(&term) {
                    terms.push(term);
                    let inline = self.current_span().line == colon.line;
                    let header = terms[0].span;
                    terms.push(self.colon_value(header, colon)?);
                    if !inline {
                        break;
                    }
                } else {
                    terms.push(term);
                }
            }
            let end = if self.kind() == Some(&T::Semicolon) {
                let end = self.current_span().end;
                self.index += 1;
                Some(end)
            } else {
                None
            };
            let mut form = self.form_group(terms)?;
            if let Some(end) = end {
                form.span.end = end;
            }
            return Ok(form);
        }
        self.expression()
    }

    fn top_colon_header(&self) -> bool {
        if matches!(
            self.kind(),
            Some(
                T::Quote
                    | T::QuasiQuote
                    | T::Unquote
                    | T::UnquoteSplicing
                    | T::LParen
                    | T::LBrace
                    | T::LBracket
            )
        ) {
            return false;
        }
        let line = self.current_span().line;
        let mut depth = 0;
        for token in &self.tokens[self.index..] {
            if depth == 0 && (token.span.line != line || token.kind == T::Semicolon) {
                break;
            }
            if depth == 0
                && (token.kind == T::Colon
                    || matches!(&token.kind, T::Symbol(value) if value.ends_with(':') && !value.ends_with("::")))
            {
                return true;
            }
            match token.kind {
                T::LParen | T::LBrace | T::LBracket => depth += 1,
                T::RParen | T::RBrace | T::RBracket => {
                    if depth == 0 {
                        break;
                    }
                    depth -= 1;
                }
                _ => {}
            }
        }
        false
    }

    pub(super) fn postfix_call(&mut self, callee: Node) -> Result<Node, ParseError> {
        let named_arguments = self.kind() == Some(&T::LBrace);
        if named_arguments && callable(&callee) {
            let arguments = self.expression()?;
            Ok(self.application(callee, arguments))
        } else {
            Ok(callee)
        }
    }

    fn named_arguments(&self, node: &Node) -> bool {
        self.records.contains(&node.span.start)
    }

    fn application(&self, callee: Node, arguments: Node) -> Node {
        let span = through(callee.span, arguments.span.end);
        list(
            vec![symbol("#call", synthetic(callee.span)), callee, arguments],
            span,
        )
    }

    pub(super) fn record(&mut self) -> Result<Node, ParseError> {
        let start = self.take(T::LBrace, "expected '{'")?;
        self.records.insert(start.start);
        let mut pairs = Vec::new();
        while self.kind() != Some(&T::RBrace) {
            if self.kind().is_none() {
                return Err(self.error("unterminated named record; expected '}'", self.eof_span()));
            }
            let mut key = self.expression_application(false)?;
            if !matches!(key.expr, Expr::Symbol(_) | Expr::Unquote(_)) {
                return Err(self.error("record keys must be identifiers", key.span));
            }
            let attached_colon = if let Some((plain_key, colon)) = split_layout_suffix(&key) {
                key = plain_key;
                Some(colon)
            } else if self.kind() == Some(&T::Equal) {
                self.index += 1;
                None
            } else if self.kind() == Some(&T::Colon) {
                None
            } else {
                return Err(self.error(
                    "record entries require 'key = value;' or 'key:' with an indented value",
                    self.current_span(),
                ));
            };
            if !matches!(key.expr, Expr::Symbol(_) | Expr::Unquote(_)) {
                return Err(self.error("record keys must be identifiers", key.span));
            }
            let colon = if attached_colon.is_some() {
                attached_colon
            } else if self.kind() == Some(&T::Colon) {
                Some(self.take(T::Colon, "expected ':'")?)
            } else {
                None
            };
            let inline = colon.is_some_and(|colon| self.current_span().line == colon.line);
            let value = if let Some(colon) = colon {
                self.colon_value(key.span, colon)?
            } else {
                self.expression()?
            };
            let end = if colon.is_some() && !inline {
                value.span.end
            } else {
                self.take(T::Semicolon, "record entries require a terminating ';'")?
                    .end
            };
            let span = through(key.span, end);
            pairs.push(list(vec![key, value], span));
        }
        let end = self.take(T::RBrace, "expected '}'")?.end;
        Ok(list(pairs, through(start, end)))
    }

    pub(super) fn surface_list(&mut self) -> Result<Node, ParseError> {
        let start = self.take(T::LParen, "expected '('")?;
        let mut segment: Vec<Node> = Vec::new();
        let mut groups = Vec::new();
        let mut terminated = false;
        loop {
            match self.kind() {
                Some(T::RParen) => {
                    let end = self.take(T::RParen, "expected ')'")?.end;
                    if terminated && !segment.is_empty() {
                        return Err(self.error(
                            "every form in a semicolon list requires a terminating ';'",
                            segment[0].span,
                        ));
                    }
                    return self.finish_list(
                        if terminated { groups } else { segment },
                        through(start, end),
                    );
                }
                Some(T::Semicolon) => {
                    self.index += 1;
                    if segment.is_empty() {
                        return Err(
                            self.error("empty semicolon group", self.tokens[self.index - 1].span)
                        );
                    }
                    groups.push(self.form_group(std::mem::take(&mut segment))?);
                    terminated = true;
                }
                Some(T::Colon) => {
                    let colon = self.take(T::Colon, "expected ':'")?;
                    let inline = self.current_span().line == colon.line;
                    let header = segment.first().map_or(colon, |term| term.span);
                    segment.push(self.colon_value(header, colon)?);
                    if !inline && segment.len() > 1 {
                        groups.push(self.form_group(std::mem::take(&mut segment))?);
                        terminated = true;
                    }
                }
                None => return Err(self.error("unterminated list; expected ')'", self.eof_span())),
                _ => {
                    // Declaration names and explicit call targets are syntax,
                    // so their following argument record is a separate child.
                    let term = self.expression_application(!syntax_operand(&segment))?;
                    if let Some((term, colon)) = split_layout_suffix(&term) {
                        segment.push(term);
                        let inline = self.current_span().line == colon.line;
                        let header = segment[0].span;
                        segment.push(self.colon_value(header, colon)?);
                        if !inline {
                            groups.push(self.form_group(std::mem::take(&mut segment))?);
                            terminated = true;
                        }
                    } else {
                        segment.push(term);
                    }
                }
            }
        }
    }

    // Keep normalization and its temporaries off the recursive reader stack.
    #[inline(never)]
    fn finish_list(&self, mut children: Vec<Node>, span: Span) -> Result<Node, ParseError> {
        if children.first().is_some_and(|node| name(node) == "$") {
            let mut items = children
                .iter()
                .map(|node| node.expr.clone())
                .collect::<Vec<_>>();
            self.expand_dollar_shorthand(&mut items, &mut children)?;
            return Ok(Node {
                expr: Expr::List(items.into()),
                span,
                children: children.into(),
            });
        }
        if children.len() == 2 && callable(&children[0]) && self.named_arguments(&children[1]) {
            return Ok(self.application(children[0].clone(), children[1].clone()));
        }
        self.normalize_declaration(self.body_lists(list(children, span)))
    }

    fn form_group(&self, mut terms: Vec<Node>) -> Result<Node, ParseError> {
        if terms.len() == 2 && callable(&terms[0]) && self.named_arguments(&terms[1]) {
            return Ok(self.application(terms[0].clone(), terms[1].clone()));
        }
        if terms.len() == 1 {
            let term = terms.pop().unwrap();
            if !matches!(
                name(&term),
                "#panic" | "#unreachable" | "#break" | "#continue" | "#result" | "#call-graph"
            ) {
                return Ok(term);
            }
            return Ok(list(vec![term.clone()], term.span));
        }
        let span = through(terms[0].span, terms.last().unwrap().span.end);
        self.normalize_declaration(self.body_lists(list(terms, span)))
    }

    fn indentation(&self, span: Span) -> Result<usize, ParseError> {
        if let Some(source) = self.source {
            let start = source[..span.start].rfind('\n').map_or(0, |i| i + 1);
            let prefix = &source[start..span.start];
            if prefix
                .bytes()
                .take_while(|b| b.is_ascii_whitespace())
                .any(|b| b == b'\t')
            {
                return Err(self.error("indentation blocks require spaces, not tabs", span));
            }
            return Ok(prefix.bytes().take_while(|b| *b == b' ').count());
        }
        Ok(self
            .tokens
            .iter()
            .find(|token| token.span.line == span.line)
            .map_or(span.column - 1, |token| token.span.column - 1))
    }

    // Body collections are accepted identically whether written with explicit
    // parentheses or introduced by a colon. Colon reading knows no form names.
    fn body_lists(&self, node: Node) -> Node {
        let offset = match node.children.first().map(name) {
            Some("#loop" | "#block") => 1,
            Some(
                "#while" | "#match" | "#case" | "#case-ref" | "#case-ref-mut" | "#case-pin"
                | "#case-pin-mut" | "#if" | "#if-valid" | "#label",
            ) => 2,
            Some("#for" | "#for-range") => 4,
            Some("#while-let") => 3,
            _ => return node,
        };
        if node.children.len() != offset + 1 {
            return node;
        }
        let body = &node.children[offset];
        if !matches!(body.expr, Expr::List(_))
            || !body
                .children
                .first()
                .is_some_and(|child| matches!(child.expr, Expr::List(_)))
        {
            return node;
        }
        let mut children = node.children[..offset].to_vec();
        children.extend(body.children.iter().cloned());
        list(children, node.span)
    }

    pub(super) fn colon_expression(&mut self) -> Result<Node, ParseError> {
        let colon = self.take(T::Colon, "expected ':'")?;
        // expression_application has already counted this grouping level.
        if self.kind().is_some() && self.current_span().line == colon.line {
            self.inline_colon(colon)
        } else {
            self.layout_inner(colon, colon)
        }
    }

    fn colon_value(&mut self, header: Span, colon: Span) -> Result<Node, ParseError> {
        if self.kind().is_none() || self.current_span().line != colon.line {
            return self.layout(header, colon);
        }
        if self.depth >= crate::MAX_PARSE_NESTING {
            return Err(self.error("expression nesting exceeds maximum", colon));
        }
        self.depth += 1;
        let result = self.inline_colon(colon);
        self.depth -= 1;
        result
    }

    fn inline_colon(&mut self, colon: Span) -> Result<Node, ParseError> {
        let mut children = Vec::new();
        while self.kind().is_some()
            && self.current_span().line == colon.line
            && !matches!(
                self.kind(),
                Some(T::RParen | T::RBrace | T::RBracket | T::Semicolon)
            )
        {
            let term = self.expression_application(!syntax_operand(&children))?;
            if let Some((term, nested)) = split_layout_suffix(&term) {
                children.push(term);
                children.push(self.colon_value(colon, nested)?);
            } else {
                children.push(term);
            }
        }
        if children.is_empty() {
            return Err(self.error("':' requires following syntax or an indented group", colon));
        }
        let end = children.last().unwrap().span.end;
        self.finish_list(children, through(colon, end))
    }

    fn layout(&mut self, key: Span, start: Span) -> Result<Node, ParseError> {
        if self.depth >= crate::MAX_PARSE_NESTING {
            return Err(self.error("expression nesting exceeds maximum", start));
        }
        self.depth += 1;
        let result = self.layout_inner(key, start);
        self.depth -= 1;
        result
    }

    fn layout_inner(&mut self, key: Span, start: Span) -> Result<Node, ParseError> {
        let header = self.indentation(key)?;
        let first = self.current_span();
        let indent = self.indentation(first)?;
        if self.kind().is_none() || first.line <= start.line || indent <= header {
            return Err(self.error(
                "':' requires a nonempty indented group on the following line",
                if first.line <= start.line {
                    start
                } else {
                    first
                },
            ));
        }
        let mut groups = Vec::new();
        let mut terms: Vec<Node> = Vec::new();
        let mut end = start.end;
        let mut terminated = false;
        loop {
            let next = self.current_span();
            let at_end = self.kind().is_none()
                || matches!(self.kind(), Some(T::RBrace | T::RParen | T::RBracket));
            let continued_terminator = !terms.is_empty()
                && self.kind() == Some(&T::Semicolon)
                && self.index > 0
                && self.source.map_or_else(
                    || self.tokens[self.index - 1].span.line == next.line,
                    |source| {
                        !source[self.tokens[self.index - 1].span.end..next.start].contains('\n')
                    },
                );
            let next_indent = if at_end {
                header
            } else if continued_terminator {
                // An explicit operand may close on an outdented line. Its
                // following semicolon still ends the enclosing statement.
                indent
            } else {
                self.indentation(next)?
            };
            if at_end || next_indent < indent {
                if terminated && !terms.is_empty() {
                    return Err(self.error("every indented form requires a terminating ';'", next));
                }
                if !at_end && next_indent > header {
                    return Err(
                        self.error("dedent must return to an enclosing indentation level", next)
                    );
                }
                break;
            }
            if terms.is_empty() && next_indent != indent {
                return Err(self.error(
                    "unexpected indentation; use ':' after a header to open another group",
                    next,
                ));
            }
            if self.kind() == Some(&T::Colon) && !terms.is_empty() {
                let colon = self.take(T::Colon, "expected ':'")?;
                let inline = self.current_span().line == colon.line;
                let header = terms[0].span;
                terms.push(self.colon_value(header, colon)?);
                if !inline {
                    let form = self.form_group(std::mem::take(&mut terms))?;
                    end = form.span.end;
                    groups.push(form);
                    terminated = true;
                }
            } else if self.kind() == Some(&T::Semicolon) {
                end = self.current_span().end;
                self.index += 1;
                if terms.is_empty() {
                    return Err(self.error("empty semicolon group", next));
                }
                groups.push(self.form_group(std::mem::take(&mut terms))?);
                terminated = true;
            } else {
                let term = self.expression_application(!syntax_operand(&terms))?;
                if let Some((term, colon)) = split_layout_suffix(&term) {
                    terms.push(term);
                    let inline = self.current_span().line == colon.line;
                    let header = terms[0].span;
                    terms.push(self.colon_value(header, colon)?);
                    if !inline {
                        let form = self.form_group(std::mem::take(&mut terms))?;
                        end = form.span.end;
                        groups.push(form);
                        terminated = true;
                    }
                } else {
                    terms.push(term);
                }
            }
        }
        if !terminated {
            end = terms.last().map_or(start.end, |term| term.span.end);
            return self.finish_list(terms, through(start, end));
        }
        Ok(list(groups, through(start, end)))
    }

    fn normalize_declaration(&self, node: Node) -> Result<Node, ParseError> {
        let children = &node.children;
        let Some(head) = children.first().map(name) else {
            return Ok(node);
        };
        if matches!(head, "#fn" | "#unsafe-fn")
            && children.get(2).is_some_and(|section| {
                matches!(
                    section.children.first().map(name),
                    Some(
                        "#params" | "#returns" | "#effects" | "#requires" | "#ensures"
                            | "#preserves" | "#body"
                    )
                )
            })
        {
            let mut pairs = Vec::new();
            for section in &children[2..] {
                let Some(key) = section.children.first() else {
                    return Err(self.error(
                        "function sections must start with a reserved keyword",
                        section.span,
                    ));
                };
                let args = section.children.iter().skip(1).cloned().collect::<Vec<_>>();
                let value = if matches!(name(key), "#params" | "#returns" | "#effects") {
                    if args.len() != 1 {
                        return Err(self.error(
                            "#params, #returns and #effects sections require exactly one value",
                            section.span,
                        ));
                    }
                    args[0].clone()
                } else {
                    list(args, section.span)
                };
                pairs.push(list(vec![key.clone(), value], section.span));
            }
            let fields = list(pairs, children[2].span);
            return self.normalize_declaration(list(
                vec![children[0].clone(), children[1].clone(), fields],
                node.span,
            ));
        }
        if !record_declaration(head) || children.len() != 3 {
            return Ok(node);
        }
        let fields = &children[2];
        if !self.records.contains(&fields.span.start)
            && !fields.children.first().is_some_and(|pair| {
                pair.children
                    .first()
                    .is_some_and(|key| name(key).starts_with('#'))
            })
        {
            return Ok(node);
        }
        let external = head == "#extern-fn";
        let function = matches!(head, "#fn" | "#unsafe-fn" | "#extern-fn");
        let allowed = if external {
            &["#abi", "#params", "#returns", "#effects"][..]
        } else if function {
            &[
                "#params",
                "#returns",
                "#effects",
                "#requires",
                "#ensures",
                "#preserves",
                "#body",
            ][..]
        } else {
            &["#type", "#value"][..]
        };
        let mut values = std::collections::HashMap::new();
        for pair in &fields.children {
            if pair.children.len() != 2 {
                return Err(self.error("declaration records require key/value pairs", pair.span));
            }
            let key = &pair.children[0];
            if !allowed.contains(&name(key)) {
                return Err(
                    self.error(&format!("unknown {head} section '{}'", name(key)), key.span)
                );
            }
            if values.insert(name(key), (key, &pair.children[1])).is_some() {
                return Err(self.error(
                    &format!("duplicate {head} section '{}'", name(key)),
                    key.span,
                ));
            }
        }
        let require = |field: &str| -> Result<Node, ParseError> {
            values
                .get(field)
                .map(|(_, value)| (*value).clone())
                .ok_or_else(|| {
                    self.error(&format!("{head} record requires '{field}'"), fields.span)
                })
        };
        let mut output = vec![children[0].clone()];
        if external {
            let abi = require("#abi")?;
            if name(&abi) != "#abi-c" {
                return Err(self.error("#extern-fn record requires '#abi = #abi-c;'", abi.span));
            }
            output.push(abi);
        }
        output.push(children[1].clone());
        if !function {
            output.push(require("#type")?);
            output.push(require("#value")?);
        } else {
            let params = require("#params")?;
            output.push(
                if params
                    .children
                    .first()
                    .is_some_and(|node| matches!(node.expr, Expr::Symbol(_)))
                {
                    list(vec![params.clone()], params.span)
                } else {
                    params
                },
            );
            output.push(require("#returns")?);
            if let Some((key, effects)) = values.get("#effects") {
                output.push(list(
                    vec![(*key).clone(), (*effects).clone()],
                    through(key.span, effects.span.end),
                ));
            }
            if external {
                return Ok(list(output, node.span));
            }
            for section in ["#requires", "#ensures", "#preserves"] {
                if let Some((key, predicates)) = values.get(section) {
                    if !matches!(&predicates.expr, Expr::List(items) if items.len() == predicates.children.len())
                    {
                        return Err(self.error(
                            "contract sections require a list of predicates",
                            predicates.span,
                        ));
                    }
                    let clauses = if predicates
                        .children
                        .first()
                        .is_some_and(|node| matches!(node.expr, Expr::Symbol(_)))
                    {
                        vec![(*predicates).clone()]
                    } else {
                        predicates.children.to_vec()
                    };
                    for predicate in &clauses {
                        output.push(list(
                            vec![(*key).clone(), predicate.clone()],
                            through(key.span, predicate.span.end),
                        ));
                    }
                }
            }
            let body = require("#body")?;
            if !matches!(&body.expr, Expr::List(items) if items.len() == body.children.len()) {
                return Err(self.error("#body requires a list of forms", body.span));
            }
            if body
                .children
                .first()
                .is_some_and(|node| matches!(node.expr, Expr::Symbol(_)))
            {
                output.push(body);
            } else {
                output.extend(body.children.iter().cloned());
            }
        }
        Ok(list(output, node.span))
    }

    pub(super) fn infix(&mut self, inherited: Option<&Math>) -> Result<Node, ParseError> {
        if self.depth >= crate::MAX_PARSE_NESTING {
            return Err(self.error("expression nesting exceeds maximum", self.current_span()));
        }
        self.depth += 1;
        let result = self.infix_inner(inherited);
        self.depth -= 1;
        result
    }

    fn infix_inner(&mut self, inherited: Option<&Math>) -> Result<Node, ParseError> {
        let start = self.take(T::LBracket, "expected '['")?;
        let context = if matches!(self.kind(), Some(T::Symbol(value)) if value.strip_prefix('#').is_some_and(crate::is_primitive_type_name))
        {
            let T::Symbol(scalar) = self.tokens[self.index].kind.clone() else {
                unreachable!()
            };
            self.index += 1;
            let mode = if matches!(self.kind(), Some(T::Symbol(value)) if matches!(value.as_str(), "#wrap" | "#saturate"))
            {
                let T::Symbol(mode) = self.tokens[self.index].kind.clone() else {
                    unreachable!()
                };
                self.index += 1;
                Some(mode.trim_start_matches('#').to_owned())
            } else {
                None
            };
            self.take(T::Semicolon, "infix headers end with ';'")?;
            if mode.is_some() && matches!(scalar.as_str(), "#bool" | "#char" | "#f32" | "#f64") {
                return Err(self.error("overflow modes apply only to integer arithmetic", start));
            }
            Math { scalar, mode }
        } else {
            inherited.cloned().ok_or_else(|| {
                self.error(
                    "an independent infix expression requires a scalar header",
                    start,
                )
            })?
        };
        let mut result = self.math_expression(&context, 0)?;
        let end = self
            .take(
                T::RBracket,
                "expected an infix operator or ']'; operators require whitespace",
            )?
            .end;
        result.span = through(start, end);
        Ok(result)
    }

    fn math_expression(&mut self, context: &Math, minimum: u8) -> Result<Node, ParseError> {
        if self.depth >= crate::MAX_PARSE_NESTING {
            return Err(self.error("expression nesting exceeds maximum", self.current_span()));
        }
        self.depth += 1;
        let result = self.math_expression_inner(context, minimum);
        self.depth -= 1;
        result
    }

    fn math_expression_inner(&mut self, context: &Math, minimum: u8) -> Result<Node, ParseError> {
        let mut left = match self.kind() {
            Some(T::LBracket) => self.infix(Some(context))?,
            Some(T::Symbol(value)) if matches!(value.as_str(), "-" | "!") => {
                let op = self.tokens[self.index].clone();
                self.index += 1;
                let right = self.math_expression(context, 12)?;
                self.math_operation(context, &op, vec![right])?
            }
            _ => {
                let node = self.expression()?;
                if matches!(
                    node.expr,
                    Expr::Integer(_) | Expr::UnsignedInteger(_) | Expr::Float(_)
                ) {
                    list(
                        vec![
                            symbol("#literal", synthetic(node.span)),
                            symbol(&context.scalar, synthetic(node.span)),
                            node.clone(),
                        ],
                        node.span,
                    )
                } else {
                    node
                }
            }
        };
        let mut compared = false;
        loop {
            let Some(T::Symbol(operation)) = self.kind() else {
                break;
            };
            let binding = match operation.as_str() {
                "||" => 1,
                "&&" => 2,
                "==" | "!=" | "<" | "<=" | ">" | ">=" => 3,
                "|" => 4,
                "^" => 5,
                "&" => 6,
                "<<" | ">>" => 7,
                "+" | "-" => 8,
                "*" | "/" | "%" => 9,
                _ => break,
            };
            if binding < minimum {
                break;
            }
            let comparison = binding == 3;
            if comparison && compared {
                return Err(self.error(
                    "chained comparisons require separate explicit comparisons",
                    self.current_span(),
                ));
            }
            let op = self.tokens[self.index].clone();
            self.index += 1;
            let right = self.math_expression(context, binding + 1)?;
            left = self.math_operation(context, &op, vec![left, right])?;
            compared = comparison;
        }
        Ok(left)
    }

    fn math_operation(
        &self,
        context: &Math,
        operation: &crate::Token,
        operands: Vec<Node>,
    ) -> Result<Node, ParseError> {
        // Precedence parsing can create deep trees from a flat token stream.
        // Bound the lowered tree as well as explicit source nesting.
        let mut pending = operands
            .iter()
            .map(|node| (node, self.depth + 1))
            .collect::<Vec<_>>();
        while let Some((node, depth)) = pending.pop() {
            if depth >= crate::MAX_PARSE_NESTING {
                return Err(self.error("lowered infix nesting exceeds maximum", operation.span));
            }
            pending.extend(node.children.iter().map(|child| (child, depth + 1)));
        }
        let T::Symbol(op) = &operation.kind else {
            unreachable!()
        };
        let Some((_, word)) = crate::names::OPERATIONS
            .iter()
            .find(|(symbol, _)| *symbol == op)
        else {
            return Err(self.error("unsupported infix operator", operation.span));
        };
        let arithmetic = matches!(op.as_str(), "+" | "-" | "*" | "/" | "%");
        let scalar = if matches!(op.as_str(), "&&" | "||") {
            "#bool"
        } else {
            &context.scalar
        };
        let suffix = if arithmetic && !matches!(scalar, "#f32" | "#f64") {
            format!(
                "-{}",
                context.mode.as_deref().ok_or_else(|| self.error(
                    &format!(
                        "integer infix arithmetic requires #wrap or #saturate; write '[{scalar} #wrap; ...]' or '[{scalar} #saturate; ...]'"
                    ),
                    operation.span
                ))?
            )
        } else {
            String::new()
        };
        let function = format!("{scalar}::{word}{suffix}");
        if !matches!(op.as_str(), "&&" | "||") {
            crate::intrinsics::declaration(&function)
                .map_err(|error| self.error(&error, operation.span))?;
        }
        let span = through(operands[0].span, operands.last().unwrap().span.end);
        let mut children = vec![symbol(&function, operation.span)];
        children.extend(operands);
        Ok(list(children, span))
    }
}
