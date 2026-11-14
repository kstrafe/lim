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

/// Reads one top-level expression at a time while retaining only its tokens.
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
                    .with_source(self.source)
                    .run()
                    .map(|mut forms| forms.pop())
                    .map_err(|e| e.to_string());
            };
            tokens.push(token);
            let kind = &tokens.last().unwrap().kind;
            if !started && *kind == TokenKind::Colon && tokens.len() > 1 {
                return self.read_colon_form(tokens).map(Some);
            }
            if tokens.len() == 1
                && (matches!(kind, TokenKind::Symbol(name) if crate::surface_syntax::record_declaration(name))
                    || *kind == TokenKind::Generate)
            {
                let mut lookahead = self.lexer.clone();
                if let (Ok(Some(name)), Ok(Some(record))) =
                    (lookahead.next_token(), lookahead.next_token())
                {
                    if record.kind == TokenKind::LBrace {
                        tokens.push(name);
                        tokens.push(record);
                        self.lexer = lookahead;
                        started = true;
                        depth = 1;
                        continue;
                    }
                }
            }
            if tokens.len() == 1
                && !matches!(
                    kind,
                    TokenKind::LParen
                        | TokenKind::LBrace
                        | TokenKind::LBracket
                        | TokenKind::Quote
                        | TokenKind::QuasiQuote
                        | TokenKind::Unquote
                        | TokenKind::UnquoteSplicing
                )
                && self.colon_header(tokens.first().unwrap())?
            {
                return self.read_colon_form(tokens).map(Some);
            }
            if !started {
                match kind {
                    TokenKind::Quote
                    | TokenKind::QuasiQuote
                    | TokenKind::Unquote
                    | TokenKind::UnquoteSplicing => {}
                    TokenKind::LParen | TokenKind::LBrace | TokenKind::LBracket => {
                        started = true;
                        depth = 1;
                    }
                    _ => {
                        if tokens.len() == 1
                            && matches!(kind, TokenKind::Symbol(name) if crate::surface_syntax::callable_name(name))
                        {
                            let mut lookahead = self.lexer.clone();
                            if let Ok(next) = lookahead.next_token() {
                                self.pending = next;
                                self.lexer = lookahead;
                            }
                            if matches!(
                                self.pending.as_ref().map(|token| &token.kind),
                                Some(TokenKind::LBrace)
                            ) {
                                continue;
                            }
                        }
                        return parse_one(&tokens, self.source).map(Some);
                    }
                }
            } else {
                match kind {
                    TokenKind::LParen | TokenKind::LBrace | TokenKind::LBracket => depth += 1,
                    TokenKind::RParen | TokenKind::RBrace | TokenKind::RBracket => {
                        depth -= 1;
                        if depth == 0 {
                            return parse_one(&tokens, self.source).map(Some);
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    fn colon_header(&self, first: &Token) -> Result<bool, String> {
        let colon = |token: &Token| {
            token.kind == TokenKind::Colon
                || matches!(&token.kind, TokenKind::Symbol(value) if value.ends_with(':') && !value.ends_with("::"))
        };
        if colon(first) {
            return Ok(true);
        }
        let mut lexer = self.lexer.clone();
        let mut depth = 0;
        while let Ok(Some(token)) = lexer.next_token() {
            if depth == 0
                && (token.span.line != first.span.line || token.kind == TokenKind::Semicolon)
            {
                break;
            }
            if depth == 0 && colon(&token) {
                return Ok(true);
            }
            match token.kind {
                TokenKind::LParen | TokenKind::LBrace | TokenKind::LBracket => depth += 1,
                TokenKind::RParen | TokenKind::RBrace | TokenKind::RBracket => {
                    if depth == 0 {
                        break;
                    }
                    depth -= 1;
                }
                _ => {}
            }
        }
        Ok(false)
    }

    fn read_colon_form(&mut self, mut tokens: Vec<Token>) -> Result<SpannedExpr, String> {
        let first = tokens[0].span;
        let indentation = |start: usize| {
            let line = self.source[..start]
                .rfind('\n')
                .map_or(0, |index| index + 1);
            self.source[line..start]
                .bytes()
                .take_while(|byte| *byte == b' ' || *byte == b'\t')
                .count()
        };
        let header = indentation(first.start);
        let mut depth = 0;
        let mut indented = matches!(&tokens.last().unwrap().kind, TokenKind::Colon)
            || matches!(&tokens.last().unwrap().kind, TokenKind::Symbol(value) if value.ends_with(':') && !value.ends_with("::"));
        while let Some(token) = self.lexer.next_token().map_err(|error| error.to_string())? {
            if depth == 0
                && token.span.line > first.line
                && (!indented || indentation(token.span.start) <= header)
            {
                self.pending = Some(token);
                break;
            }
            if token.span.line == first.line && depth == 0 {
                indented = token.kind == TokenKind::Colon
                    || matches!(&token.kind, TokenKind::Symbol(value) if value.ends_with(':') && !value.ends_with("::"));
            }
            let semicolon =
                depth == 0 && token.kind == TokenKind::Semicolon && token.span.line == first.line;
            match token.kind {
                TokenKind::LParen | TokenKind::LBrace | TokenKind::LBracket => depth += 1,
                TokenKind::RParen | TokenKind::RBrace | TokenKind::RBracket => {
                    if depth > 0 {
                        depth -= 1;
                    }
                }
                _ => {}
            }
            tokens.push(token);
            if semicolon {
                break;
            }
        }
        parse_one(&tokens, self.source)
    }
}

fn parse_one(tokens: &[Token], source: &str) -> Result<SpannedExpr, String> {
    let mut forms = Parser::new(tokens)
        .with_source(source)
        .run()
        .map_err(|error| error.to_string())?;
    if forms.len() != 1 {
        return Err("expected exactly one expression".into());
    }
    Ok(forms.remove(0))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn streams_inline_and_indented_colon_groups_locally() {
        for source in [
            "read (: value 42)\n",
            "#generate make : (type #u64) (name Example)\n",
            "#fn f { #params = {}; #returns = (); #body: #return (); } other : value\n",
            "a : b : c\n: d e\n",
            "a : b; c : d;\n",
            "a:\n  b c;\n  d e;\nf : g\n",
            "': a b\n`:\n  c d;\n: e\n",
            "#fn main { #params = {}; #returns = #u64; #body: #return : #u64::add-wrap 20 22; }\n",
        ] {
            let expected = crate::parse(source).unwrap();
            let mut reader = SourceForms::new(source);
            let actual = std::iter::from_fn(|| reader.next().transpose())
                .collect::<Result<Vec<_>, _>>()
                .unwrap();
            assert_eq!(actual, expected, "{source}");
            let formatted = crate::format_source(source).unwrap();
            assert_eq!(crate::format_source(&formatted).unwrap(), formatted);
            assert_eq!(
                crate::parse(&formatted)
                    .unwrap()
                    .into_iter()
                    .map(|node| node.expr)
                    .collect::<Vec<_>>(),
                expected
                    .into_iter()
                    .map(|node| node.expr)
                    .collect::<Vec<_>>()
            );
        }
    }

    #[test]
    fn streams_marker_free_named_calls_with_the_same_spans_as_parse() {
        let source = "read ((value 42))\n#usize::lt ((left 1usize) (right 4usize))\n(read ((value 1)))\nread {}";
        let expected = crate::parse(source).unwrap();
        let mut reader = SourceForms::new(source);
        let actual = std::iter::from_fn(|| reader.next().transpose())
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        assert_eq!(actual, expected);
        let formatted = crate::format_source(source).unwrap();
        assert!(!formatted.contains("#call"));
        assert_eq!(crate::format_source(&formatted).unwrap(), formatted);
    }

    #[test]
    fn streams_the_same_spanned_trees_as_parse() {
        let source =
            "// λ comment\n(foo :bar '(:x \"a\\\"(b)\" #\\u{28} #\\u{1f642})) `,(,@items)\n'hello";
        let expected = crate::parse(source).unwrap();
        let mut forms = SourceForms::new(source);
        let actual: Vec<_> = std::iter::from_fn(|| forms.next().transpose())
            .collect::<Result<_, _>>()
            .unwrap();
        assert_eq!(actual, expected);
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
