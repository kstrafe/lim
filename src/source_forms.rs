use crate::{Lexer, Parser, SpannedExpr, Token, TokenKind};

/// Preserve the ordinary lex-before-parse error order without retaining tokens.
pub(crate) fn validate_lexically(source: &str) -> Result<(), String> {
    let mut lexer = Lexer::new(source);
    while lexer
        .next_token()
        .map_err(|error| error.to_string())?
        .is_some()
    {}
    Ok(())
}

/// Streaming source-unit reader. Every root has exactly one implicit list.
/// Compilation and source formatting share this boundary implementation.
pub(crate) struct SourceForms<'a> {
    lexer: Lexer<'a>,
    pending: Option<Token>,
    source: &'a str,
}

impl<'a> SourceForms<'a> {
    pub(crate) fn new(source: &'a str) -> Self {
        Self {
            lexer: Lexer::new(source),
            pending: None,
            source,
        }
    }

    pub(crate) fn next_start(&mut self) -> Result<Option<usize>, crate::ParseError> {
        if self.pending.is_none() {
            self.pending = self.lexer.next_token().map_err(|e| crate::ParseError {
                message: e.message,
                span: e.span,
            })?;
        }
        Ok(self.pending.as_ref().map(|t| t.span.start))
    }

    pub(crate) fn next(&mut self) -> Result<Option<SpannedExpr>, crate::ParseError> {
        let first = match self.pending.take() {
            Some(token) => token,
            None => match self.lexer.next_token().map_err(|e| crate::ParseError {
                message: e.message,
                span: e.span,
            })? {
                Some(token) => token,
                None => return Ok(None),
            },
        };
        if let TokenKind::Symbol(name) = &first.kind {
            if !name.starts_with('#') {
                return Err(crate::ParseError {
                    message: format!("top-level declaration head '{name}' must use its '#' prefix"),
                    span: first.span,
                });
            }
        }
        if !matches!(&first.kind, TokenKind::Symbol(name) if name.starts_with('#'))
            && first.kind != TokenKind::Generate
        {
            return Err(crate::ParseError {
                message:
                    "source declarations require a bare root head; remove the outer parentheses"
                        .into(),
                span: first.span,
            });
        }
        let header = first.span;
        let indentation = |start: usize| {
            let line = self.source[..start].rfind('\n').map_or(0, |i| i + 1);
            self.source[line..start]
                .bytes()
                .take_while(|b| matches!(b, b' ' | b'\t'))
                .count()
        };
        let baseline = indentation(header.start);
        let trailing_colon = |kind: &TokenKind| {
            matches!(kind, TokenKind::Symbol(name)
                if name.ends_with(':') && !name.ends_with("::"))
        };
        let mut colon_operand = trailing_colon(&first.kind);
        let mut tokens = vec![first];
        let mut delimiters = Vec::new();
        let mut previous_end = header.end;
        loop {
            let Some(token) = self.lexer.next_token().map_err(|e| crate::ParseError {
                message: e.message,
                span: e.span,
            })?
            else {
                break;
            };
            if delimiters.is_empty() {
                let nested_line =
                    token.span.line > header.line && indentation(token.span.start) > baseline;
                if token.kind == TokenKind::Semicolon && !nested_line {
                    break;
                }
                // Newlines inside a multiline token do not separate roots.
                // Only whitespace/comments between complete tokens can do so.
                if self.source[previous_end..token.span.start].contains('\n')
                    && indentation(token.span.start) <= baseline
                {
                    self.pending = Some(token);
                    break;
                }
            }
            // A colon introduces a nested operand even without explicit
            // delimiters. Declaration heads inside it are data/children of
            // this root, not unseparated sibling roots. Colons inside records
            // and other explicit operands must not change root boundaries.
            let layout_suffix = trailing_colon(&token.kind)
                && !tokens
                    .iter()
                    .rev()
                    .take_while(|previous| {
                        matches!(
                            previous.kind,
                            TokenKind::Quote
                                | TokenKind::QuasiQuote
                                | TokenKind::Unquote
                                | TokenKind::UnquoteSplicing
                        )
                    })
                    .any(|previous| previous.kind != TokenKind::Unquote);
            // Only Unquote wrappers participate in split_layout_suffix.
            // Quoted trailing-colon symbols remain literal data. An explicit
            // Colon token still groups syntax even underneath a quote.
            if delimiters.is_empty() && (token.kind == TokenKind::Colon || layout_suffix) {
                colon_operand = true;
            }
            if delimiters.is_empty()
                && !colon_operand
                && (token.kind == TokenKind::Generate
                    || matches!(&token.kind, TokenKind::Symbol(head) if declaration_head(head)))
                && !matches!(
                    tokens.last().map(|t| &t.kind),
                    Some(
                        TokenKind::Quote
                            | TokenKind::QuasiQuote
                            | TokenKind::Unquote
                            | TokenKind::UnquoteSplicing
                    )
                )
            {
                return Err(crate::ParseError {
                    message: "root declarations require a newline or semicolon separator".into(),
                    span: token.span,
                });
            }
            match token.kind {
                TokenKind::LParen => delimiters.push(TokenKind::RParen),
                TokenKind::LBrace => delimiters.push(TokenKind::RBrace),
                TokenKind::LBracket => delimiters.push(TokenKind::RBracket),
                TokenKind::RParen | TokenKind::RBrace | TokenKind::RBracket => {
                    if delimiters.last() != Some(&token.kind) {
                        return Err(crate::ParseError {
                            message: "unexpected or mismatched source delimiter".into(),
                            span: token.span,
                        });
                    }
                    delimiters.pop();
                }
                _ => {}
            }
            previous_end = token.span.end;
            tokens.push(token);
        }
        // Read the root's contents directly. Adding synthetic explicit
        // parentheses would double-wrap roots completed by a layout operand.
        let end = tokens.last().unwrap().span;
        let mut parser = Parser::new(&tokens).with_source(self.source);
        let mut node = parser.implicit_root()?;
        // Parsing knows where a colon operand actually ends. A declaration
        // head left as an immediate symbol is an ungrouped sibling, even if
        // the lexical scan previously entered a colon operand. Nested and
        // quoted declaration trees remain ordinary children of this root.
        if colon_operand {
            if let Some(child) = node
                .children
                .iter()
                .skip(1)
                .find(|child| match &child.expr {
                    crate::Expr::Symbol(head) => declaration_head(head),
                    crate::Expr::Generate => true,
                    _ => false,
                })
            {
                return Err(crate::ParseError {
                    message: "root declarations require a newline or semicolon separator".into(),
                    span: child.span,
                });
            }
        }
        validate_function_declarations(&node, &tokens)?;
        node.span = crate::Span {
            end: end.end,
            ..header
        };
        Ok(Some(node))
    }
}

// Only compilation-unit declarations are source syntax. A generator's quoted
// template, function-shaped data and ordinary grouping retain the raw grammar.
fn validate_function_declarations(
    node: &SpannedExpr,
    tokens: &[Token],
) -> Result<(), crate::ParseError> {
    let Some(head) = node.children.first() else {
        return Ok(());
    };
    let crate::Expr::Symbol(keyword) = &head.expr else {
        return Ok(());
    };
    if matches!(keyword.as_str(), "#fn" | "#unsafe-fn" | "#extern-fn") {
        let start = tokens.partition_point(|token| token.span.start < head.span.end);
        let end = tokens.partition_point(|token| token.span.start < node.span.end);
        let operands = &tokens[start..end];
        if !matches!(
            operands.first().map(|token| &token.kind),
            Some(TokenKind::Symbol(_))
        )
            || operands.get(1).map(|token| &token.kind) != Some(&TokenKind::LBrace)
        {
            return Err(crate::ParseError {
                message: format!(
                    "{keyword} source declarations require a named record; use {keyword} name {{ #params = {{}}; #returns = (); {} }}",
                    if keyword == "#extern-fn" { "#abi = #abi-c;" } else { "#body: #return ();" }
                ),
                span: head.span,
            });
        }
        // Normalization has already replaced valid records with their
        // canonical positional tree. Check the original token boundary so a
        // record followed by positional operands cannot bypass that lowering.
        let mut depth = 0;
        for (index, token) in operands.iter().enumerate().skip(1) {
            match token.kind {
                TokenKind::LBrace => depth += 1,
                TokenKind::RBrace => depth -= 1,
                _ => continue,
            }
            if depth == 0 {
                let remaining = &operands[index + 1..];
                // A cfg branch may have one explicit pair of parentheses
                // around the declaration; that closing delimiter is its own.
                let closes_declaration = remaining.len() == 1
                    && remaining[0].kind == TokenKind::RParen
                    && node.span.start < head.span.start
                    && remaining[0].span.end == node.span.end;
                if !remaining.is_empty() && !closes_declaration {
                    return Err(crate::ParseError {
                        message: format!(
                            "{keyword} source declaration must end after its record; put all fields inside '{{ ... }}'"
                        ),
                        span: remaining[0].span,
                    });
                }
                break;
            }
        }
    } else if keyword == "#cfg-if" {
        for branch in node.children.iter().skip(2) {
            validate_function_declarations(branch, tokens)?;
        }
    } else if keyword == "#cfg-else" {
        for branch in node.children.iter().skip(1) {
            validate_function_declarations(branch, tokens)?;
        }
    }
    Ok(())
}

fn declaration_head(name: &str) -> bool {
    matches!(
        name,
        "#fn"
            | "#unsafe-fn"
            | "#extern-fn"
            | "#struct"
            | "#enum"
            | "#type"
            | "#alias"
            | "#export"
            | "#std"
            | "#cfg-if"
            | "#gn"
            | "#gn-fn"
            | "#const"
            | "#static"
            | "#opaque"
            | "#unsafe-impl"
            | "#capability"
            | "#syntax"
            | "#distributed-enum"
            | "#enum-contribute"
            | "#thread-task"
            | "#require-generated"
    )
}

/// Serialize canonical declaration trees as source, without changing their AST
/// representation or reinterpreting quoted generator templates as declarations.
pub(crate) fn modern_declaration_source(
    expression: &crate::Expr,
) -> Result<Option<String>, String> {
    use crate::{expression_source, Expr};
    let Expr::List(items) = expression else {
        return Ok(None);
    };
    let Some(Expr::Symbol(head)) = items.first() else {
        return Ok(None);
    };
    if matches!(head.as_str(), "#cfg-if" | "#cfg-else") {
        let prefix = if head == "#cfg-if" { 2 } else { 1 };
        if items.len() < prefix {
            return Ok(None);
        }
        let mut output = items[..prefix]
            .iter()
            .map(expression_source)
            .collect::<Result<Vec<_>, _>>()?
            .join(" ");
        for branch in &items[prefix..] {
            output.push('\n');
            if matches!(branch, Expr::List(parts) if matches!(parts.first(), Some(Expr::Symbol(name)) if name.starts_with('#')) || matches!(parts.first(), Some(Expr::Generate)))
            {
                let source = crate::declaration_source(branch)?;
                output.push_str("  (");
                output.push_str(&source.replace('\n', "\n  "));
                output.push(')');
            } else {
                output.push_str("  ");
                output.push_str(&expression_source(branch)?);
            }
        }
        return Ok(Some(output));
    }
    if !matches!(head.as_str(), "#fn" | "#unsafe-fn" | "#extern-fn") {
        return Ok(None);
    }
    let external = head == "#extern-fn";
    let name_index = if external { 2 } else { 1 };
    let params_index = name_index + 1;
    let returns_index = name_index + 2;
    let body_index = name_index + 3;
    if items.len() < body_index {
        return Err(format!(
            "{head} requires a name, parameters and return type"
        ));
    }
    if external && items.len() != body_index {
        return Err("extern-fn requires a non-generic signature without a body".into());
    }
    let mut output = format!("{head} {} {{\n", expression_source(&items[name_index])?);
    if external {
        output.push_str(&format!("  #abi = {};\n", expression_source(&items[1])?));
    }
    let parameters = match &items[params_index] {
        Expr::List(parameters) if parameters.iter().all(|parameter| matches!(parameter,
            Expr::List(parts) if parts.len() == 2 && matches!(parts.first(), Some(Expr::Symbol(name)) if !name.starts_with('#')))) => {
            let mut record = String::from("{");
            for parameter in parameters {
                let Expr::List(parts) = parameter else { unreachable!() };
                record.push_str(&format!(" {} = {};", expression_source(&parts[0])?, expression_source(&parts[1])?));
            }
            if !parameters.is_empty() { record.push(' '); }
            record.push('}');
            record
        }
        // Mutable binders retain their explicit (#mut name Type) structure.
        // Only the enclosing declaration changes syntax in this cutover.
        parameters => expression_source(parameters)?,
    };
    output.push_str(&format!(
        "  #params = {parameters};\n  #returns = {};\n",
        expression_source(&items[returns_index])?
    ));
    if !external {
        let mut body_start = body_index;
        let mut contracts = [Vec::new(), Vec::new(), Vec::new()];
        while let Some(Expr::List(clause)) = items.get(body_start) {
            if !matches!(clause.first(), Some(Expr::Symbol(name)) if matches!(name.as_str(), "#requires" | "#ensures" | "#preserves"))
            {
                break;
            }
            if clause.len() != 2 {
                break;
            }
            let index = match &clause[0] {
                Expr::Symbol(name) if name == "#requires" => 0,
                Expr::Symbol(name) if name == "#ensures" => 1,
                _ => 2,
            };
            contracts[index].push(&clause[1]);
            body_start += 1;
        }
        for (name, predicates) in ["#requires", "#ensures", "#preserves"]
            .into_iter()
            .zip(contracts)
        {
            if !predicates.is_empty() {
                output.push_str(&format!(
                    "  {name} = ({});\n",
                    predicates
                        .into_iter()
                        .map(expression_source)
                        .collect::<Result<Vec<_>, _>>()?
                        .join(" ")
                ));
            }
        }
        if body_start == items.len() {
            output.push_str("  #body = ();\n");
        } else {
            output.push_str("  #body:\n");
            for statement in &items[body_start..] {
                output.push_str(&format!("    {};\n", expression_source(statement)?));
            }
        }
    }
    output.push('}');
    Ok(Some(output))
}
