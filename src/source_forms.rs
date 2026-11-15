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
        let mut tokens = vec![first];
        let mut delimiters = Vec::new();
        let mut last_line = header.line;
        loop {
            let Some(token) = self.lexer.next_token().map_err(|e| crate::ParseError {
                message: e.message,
                span: e.span,
            })?
            else {
                break;
            };
            if delimiters.is_empty() {
                if token.kind == TokenKind::Semicolon {
                    break;
                }
                if token.span.line > last_line && indentation(token.span.start) <= baseline {
                    self.pending = Some(token);
                    break;
                }
            }
            if delimiters.is_empty()
                && (token.kind == TokenKind::Generate
                    || matches!(&token.kind, TokenKind::Symbol(head) if matches!(head.as_str(),
                    "#fn" | "#unsafe-fn" | "#extern-fn" | "#struct" | "#enum" | "#type"
                    | "#alias" | "#export" | "#std" | "#cfg-if" | "#gn" | "#gn-fn"
                    | "#const" | "#static" | "#opaque" | "#unsafe-impl" | "#capability"
                    | "#syntax" | "#distributed-enum" | "#enum-contribute" | "#thread-task" | "#require-generated")))
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
            last_line = token.span.line;
            tokens.push(token);
        }
        // Synthetic delimiters never enter the source map: every child keeps
        // its authored span and the root covers exactly its actual tokens.
        let end = tokens.last().unwrap().span;
        tokens.insert(
            0,
            Token {
                kind: TokenKind::LParen,
                span: crate::Span {
                    end: header.start,
                    ..header
                },
            },
        );
        tokens.push(Token {
            kind: TokenKind::RParen,
            span: crate::Span {
                start: end.end,
                end: end.end,
                ..end
            },
        });
        let mut parser = Parser::new(&tokens).with_source(self.source);
        let mut node = parser.expression()?;
        if parser.index != tokens.len() {
            return Err(crate::ParseError {
                message: "expected exactly one source declaration".into(),
                span: header,
            });
        }
        node.span = crate::Span {
            end: end.end,
            ..header
        };
        Ok(Some(node))
    }
}
