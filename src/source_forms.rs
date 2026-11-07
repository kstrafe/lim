use crate::{Lexer, Parser, Span, SpannedExpr, Token, TokenKind};

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

/// Reads one top-level expression at a time while retaining only its tokens.
pub(crate) struct SourceForms<'a> {
    lexer: Lexer<'a>,
    pending: Option<Token>,
}

impl<'a> SourceForms<'a> {
    pub(crate) fn new(source: &'a str) -> Self {
        Self {
            lexer: Lexer::new(source),
            pending: None,
        }
    }

    /// One-token lookahead, used to keep inter-form comments in place.
    pub(crate) fn next_start(&mut self) -> Result<Option<usize>, String> {
        if self.pending.is_none() {
            self.pending = self.lexer.next_token().map_err(|error| error.to_string())?;
        }
        Ok(self.pending.as_ref().map(|token| token.span.start))
    }

    pub(crate) fn next(&mut self) -> Result<Option<SpannedExpr>, String> {
        let mut tokens = Vec::new();
        let mut depth = 0usize;
        let mut started = false;
        loop {
            let token = match self.pending.take() {
                Some(token) => Some(token),
                None => self.lexer.next_token().map_err(|error| error.to_string())?,
            };
            let Some(token) = token else {
                if tokens.is_empty() {
                    return Ok(None);
                }
                return Parser::new(&tokens)
                    .run()
                    .map(|mut forms| forms.pop())
                    .map_err(|e| e.to_string());
            };
            tokens.push(token);
            let kind = &tokens.last().unwrap().kind;
            if !started {
                match kind {
                    TokenKind::Quote
                    | TokenKind::QuasiQuote
                    | TokenKind::Unquote
                    | TokenKind::UnquoteSplicing => {}
                    TokenKind::LParen => {
                        started = true;
                        depth = 1;
                    }
                    _ => return parse_one(&tokens).map(Some),
                }
            } else {
                match kind {
                    TokenKind::LParen => depth += 1,
                    TokenKind::RParen => {
                        depth -= 1;
                        if depth == 0 {
                            return parse_one(&tokens).map(Some);
                        }
                    }
                    _ => {}
                }
            }
        }
    }
}

fn parse_one(tokens: &[Token]) -> Result<SpannedExpr, String> {
    let mut forms = Parser::new(tokens)
        .run()
        .map_err(|error| error.to_string())?;
    if forms.len() != 1 {
        return Err("expected exactly one expression".into());
    }
    Ok(forms.remove(0))
}

pub(crate) fn parse_at(source: &str, span: Span) -> Result<SpannedExpr, String> {
    if span.start > span.end
        || span.end > source.len()
        || !source.is_char_boundary(span.start)
        || !source.is_char_boundary(span.end)
    {
        return Err("expression span is outside the source or not on UTF-8 boundaries".into());
    }
    let mut lexer = Lexer::new(source);
    lexer.source = &source.as_bytes()[..span.end];
    lexer.offset = span.start;
    lexer.line = span.line;
    lexer.column = span.column;
    let mut tokens = Vec::new();
    while lexer.offset < span.end {
        let Some(token) = lexer.next_token().map_err(|error| error.to_string())? else {
            break;
        };
        if token.span.end > span.end {
            return Err("expression token exceeds requested span".into());
        }
        tokens.push(token);
    }
    let expression = parse_one(&tokens)?;
    if expression.span.start != span.start || expression.span.end != span.end {
        return Err("requested span does not contain exactly one expression".into());
    }
    Ok(expression)
}

/// Parse a complete saved form with its original global coordinates.
pub(crate) fn parse_fragment(source: &str, span: Span) -> Result<SpannedExpr, String> {
    if span.start.checked_add(source.len()) != Some(span.end) {
        return Err("proof fragment length differs from its source span".into());
    }
    let mut lexer = Lexer::new(source);
    lexer.line = span.line;
    lexer.column = span.column;
    let mut tokens = Vec::new();
    while let Some(mut token) = lexer.next_token().map_err(|error| error.to_string())? {
        token.span.start += span.start;
        token.span.end += span.start;
        tokens.push(token);
    }
    let expression = parse_one(&tokens)?;
    if expression.span != span {
        return Err("proof fragment does not contain exactly its saved form".into());
    }
    Ok(expression)
}

#[cfg(all(test, not(feature = "proof-kernel-tests")))]
mod tests {
    use super::*;

    #[test]
    fn streams_the_same_spanned_trees_as_parse() {
        let source =
            "; λ comment\n(foo :bar '(:x \"a\\\"(b)\" #\\u{28} #\\u{1f642})) `,(,@items)\n'hello";
        let expected = crate::parse(source).unwrap();
        let mut forms = SourceForms::new(source);
        let actual: Vec<_> = std::iter::from_fn(|| forms.next().transpose())
            .collect::<Result<_, _>>()
            .unwrap();
        assert_eq!(actual, expected);
    }

    #[test]
    fn parse_at_preserves_global_offsets_and_rejects_wrong_bounds() {
        let source = "; λ\n  '(a :b) trailing";
        let expected = crate::parse(source).unwrap()[0].clone();
        assert_eq!(parse_at(source, expected.span).unwrap(), expected);
        assert!(parse_at(
            source,
            Span {
                end: expected.span.end + 1,
                ..expected.span
            }
        )
        .is_err());
    }

    #[test]
    fn errors_are_local_to_the_form_and_trailing_lex_errors_are_observed() {
        let mut forms = SourceForms::new("ok (bad");
        assert_eq!(forms.next().unwrap().unwrap().span.start, 0);
        assert!(forms.next().unwrap_err().contains("expected"));
        let mut forms = SourceForms::new("ok \"unterminated");
        assert!(forms.next().unwrap().is_some());
        assert!(forms.next().unwrap_err().contains("unterminated string"));
        assert!(SourceForms::new("'")
            .next()
            .unwrap_err()
            .contains("expected expression"));
        assert!(SourceForms::new(")").next().is_err());
        assert!(SourceForms::new("(a").next().is_err());
        let too_deep = format!(
            "{}x{}",
            "(".repeat(crate::MAX_PARSE_NESTING + 1),
            ")".repeat(crate::MAX_PARSE_NESTING + 1)
        );
        assert!(SourceForms::new(&too_deep)
            .next()
            .unwrap_err()
            .contains("nesting exceeds"));
    }

    #[test]
    fn large_multiform_input_can_be_drained_incrementally() {
        let source = (0..4096)
            .map(|index| format!("(item {index})\n"))
            .collect::<String>();
        let mut forms = SourceForms::new(&source);
        for index in 0..4096 {
            let form = forms.next().unwrap().unwrap();
            assert_eq!(
                form.span.start,
                source.find(&format!("(item {index})")).unwrap()
            );
        }
        assert!(forms.next().unwrap().is_none());
    }
}
