use std::io::Read;

use crate::{Lexer, Span, Token, TokenKind, MAX_PARSE_NESTING};

const REFILL_BYTES: usize = 64 * 1024;

#[derive(Debug)]
pub(crate) struct ReadForm {
    pub text: String,
    pub span: Span,
}

/// Frames lexical top-level lists; the caller still parses each returned form.
/// Offsets in the buffer are local, while line and column remain global.
pub(crate) struct ReaderForms<R: Read> {
    reader: R,
    buffer: Vec<u8>,
    base: usize,
    offset: usize,
    line: usize,
    column: usize,
    valid_end: usize,
    invalid_utf8: bool,
    eof: bool,
    max_form_bytes: usize,
    error: Option<String>,
}

impl<R: Read> ReaderForms<R> {
    pub(crate) fn new(reader: R, max_form_bytes: usize) -> Self {
        Self {
            reader,
            buffer: Vec::new(),
            base: 0,
            offset: 0,
            line: 1,
            column: 1,
            valid_end: 0,
            invalid_utf8: false,
            eof: false,
            max_form_bytes,
            error: None,
        }
    }

    pub(crate) fn next(&mut self) -> Result<Option<ReadForm>, String> {
        if let Some(error) = &self.error {
            return Err(error.clone());
        }
        let result = self.next_form();
        if let Err(error) = &result {
            // A caller must never mistake a failed read for subsequent EOF.
            self.error = Some(error.clone());
        }
        result
    }

    fn next_form(&mut self) -> Result<Option<ReadForm>, String> {
        self.retention_limit()?;
        let mut root = None;
        let mut depth = 0usize;
        loop {
            if root.is_some() && self.offset >= self.max_form_bytes {
                return Err(self.size_error());
            }
            let Some(token) = self.next_token(root.is_some())? else {
                return if root.is_some() {
                    Err(format!(
                        "{}:{}: unterminated list; expected ')'",
                        self.line, self.column
                    ))
                } else {
                    // Do not retain trailing trivia after EOF.
                    self.discard_prefix(self.offset)?;
                    Ok(None)
                };
            };
            if root.is_none() {
                if !matches!(token.kind, TokenKind::LParen) {
                    return Err(format!(
                        "{}:{}: reader requires a top-level list",
                        token.span.line, token.span.column
                    ));
                }
                let start = self
                    .base
                    .checked_add(token.span.start)
                    .ok_or_else(|| "source byte offset overflow".to_owned())?;
                root = Some(Span::new(start, start, token.span.line, token.span.column));
                // Leading comments and whitespace are not part of the form.
                self.discard_prefix(token.span.start)?;
            }
            if self.offset > self.max_form_bytes {
                return Err(self.size_error());
            }
            match token.kind {
                TokenKind::LParen => {
                    depth += 1;
                    if depth > MAX_PARSE_NESTING {
                        return Err(format!(
                            "{}:{}: expression nesting exceeds maximum of {MAX_PARSE_NESTING}",
                            token.span.line, token.span.column
                        ));
                    }
                }
                TokenKind::RParen => {
                    depth -= 1;
                    if depth == 0 {
                        let mut span = root.expect("a root list has started");
                        span.end = self
                            .base
                            .checked_add(self.offset)
                            .ok_or_else(|| "source byte offset overflow".to_owned())?;
                        let text = std::str::from_utf8(&self.buffer[..self.offset])
                            .expect("only validated UTF-8 is lexed")
                            .to_owned();
                        self.discard_prefix(self.offset)?;
                        return Ok(Some(ReadForm { text, span }));
                    }
                }
                _ => {}
            }
        }
    }

    fn next_token(&mut self, in_form: bool) -> Result<Option<Token>, String> {
        loop {
            // A partial UTF-8 scalar is kept outside the lexer's input. The
            // validated prefix is cached so many small tokens remain linear.
            let mut lexer = Lexer {
                source: &self.buffer[..self.valid_end],
                offset: self.offset,
                line: self.line,
                column: self.column,
            };
            let result = lexer.next_token();
            let needs_more = match &result {
                Ok(Some(token)) => {
                    if token.span.end == token.span.start {
                        return Err(format!(
                            "{}:{}: lexer made no progress",
                            lexer.line, lexer.column
                        ));
                    }
                    lexer.offset == self.valid_end
                        && !matches!(
                            token.kind,
                            TokenKind::LParen
                                | TokenKind::RParen
                                | TokenKind::Quote
                                | TokenKind::QuasiQuote
                                | TokenKind::UnquoteSplicing
                                | TokenKind::String(_)
                        )
                }
                Ok(None) => true,
                Err(_) => lexer.offset == self.valid_end,
            };
            let position = (lexer.offset, lexer.line, lexer.column);
            if needs_more {
                if self.invalid_utf8 || (self.eof && self.valid_end < self.buffer.len()) {
                    return Err(format!(
                        "{}:{}: invalid or incomplete UTF-8 at byte {}",
                        position.1,
                        position.2,
                        self.base
                            .checked_add(self.valid_end)
                            .ok_or_else(|| "source byte offset overflow".to_owned())?
                    ));
                }
                if !self.eof {
                    if in_form && self.valid_end >= self.max_form_bytes {
                        return Err(self.size_error());
                    }
                    // Outside a form, complete lines and plain whitespace can
                    // be dropped. An unfinished comment must be retried intact.
                    let trivia = &self.buffer[self.offset..self.valid_end];
                    if !in_form && matches!(result, Ok(None)) {
                        if let Some(newline) = trivia.iter().rposition(|byte| *byte == b'\n') {
                            // Retain only the unfinished final line. The lexer
                            // consumed trivia through valid_end, so its line is
                            // also the line immediately after this last LF.
                            self.offset += newline + 1;
                            self.line = position.1;
                            self.column = 1;
                            self.discard_prefix(self.offset)?;
                        } else if trivia
                            .iter()
                            .all(|byte| matches!(byte, b' ' | b'\t' | b'\r'))
                        {
                            self.offset = position.0;
                            self.line = position.1;
                            self.column = position.2;
                            self.discard_prefix(self.offset)?;
                        }
                    }
                    // Otherwise keep the pre-token position, including its
                    // line and Unicode column, and lex it again after refill.
                    self.refill()?;
                    continue;
                }
            }
            self.offset = position.0;
            self.line = position.1;
            self.column = position.2;
            return result.map_err(|error| error.to_string());
        }
    }

    fn retention_limit(&self) -> Result<usize, String> {
        self.max_form_bytes
            .checked_add(REFILL_BYTES)
            .ok_or_else(|| "form byte limit exceeds the source reader's range".to_owned())
    }

    fn size_error(&self) -> String {
        format!(
            "source form or inter-form comment exceeds byte limit {}",
            self.max_form_bytes
        )
    }

    fn refill(&mut self) -> Result<(), String> {
        let remaining = self
            .retention_limit()?
            .checked_sub(self.buffer.len())
            .ok_or_else(|| self.size_error())?;
        let count = remaining.min(REFILL_BYTES);
        if count == 0 {
            return Err(self.size_error());
        }
        let mut chunk = [0u8; REFILL_BYTES];
        let read = loop {
            match self.reader.read(&mut chunk[..count]) {
                Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
                result => break result.map_err(|error| format!("source read failed: {error}"))?,
            }
        };
        if read == 0 {
            self.eof = true;
            return Ok(());
        }
        // The finite retention limit is checked before any buffer allocation.
        self.buffer
            .try_reserve_exact(read)
            .map_err(|error| format!("cannot retain source form: {error}"))?;
        self.buffer.extend_from_slice(&chunk[..read]);
        match std::str::from_utf8(&self.buffer[self.valid_end..]) {
            Ok(_) => self.valid_end = self.buffer.len(),
            Err(error) => {
                self.valid_end += error.valid_up_to();
                // With no error length the suffix is at most three bytes of
                // an incomplete scalar, which the next refill may complete.
                self.invalid_utf8 = error.error_len().is_some();
            }
        }
        Ok(())
    }

    fn discard_prefix(&mut self, count: usize) -> Result<(), String> {
        let base = self
            .base
            .checked_add(count)
            .ok_or_else(|| "source byte offset overflow".to_owned())?;
        self.buffer.copy_within(count.., 0);
        self.buffer.truncate(self.buffer.len() - count);
        self.base = base;
        self.offset -= count;
        self.valid_end -= count;
        Ok(())
    }
}

#[cfg(all(test, not(feature = "proof-kernel-tests")))]
mod tests {
    use super::*;

    struct ShortRead<'a> {
        bytes: &'a [u8],
        step: usize,
    }

    impl Read for ShortRead<'_> {
        fn read(&mut self, output: &mut [u8]) -> std::io::Result<usize> {
            let count = self.bytes.len().min(self.step).min(output.len());
            output[..count].copy_from_slice(&self.bytes[..count]);
            self.bytes = &self.bytes[count..];
            Ok(count)
        }
    }

    fn compare_with_parse(source: &str, step: usize, limit: usize) {
        let expected = crate::parse(source).unwrap();
        let mut reader = ReaderForms::new(
            ShortRead {
                bytes: source.as_bytes(),
                step,
            },
            limit,
        );
        let mut rebased = Vec::new();
        for expression in &expected {
            let form = reader.next().unwrap().unwrap();
            assert_eq!(form.span, expression.span);
            assert_eq!(
                form.text,
                source[expression.span.start..expression.span.end]
            );
            assert_eq!(crate::parse(&form.text).unwrap()[0].expr, expression.expr);
            let mut tokens = crate::lex(&form.text).unwrap();
            for token in &mut tokens {
                token.span.start += form.span.start;
                token.span.end += form.span.start;
                if token.span.line == 1 {
                    token.span.column += form.span.column - 1;
                }
                token.span.line += form.span.line - 1;
            }
            rebased.extend(crate::Parser::new(&tokens).run().unwrap());
            assert!(reader.buffer.len() <= limit + REFILL_BYTES);
            assert!(reader.buffer.capacity() <= limit + REFILL_BYTES);
            assert_eq!(reader.base, form.span.end);
            assert_eq!(reader.offset, 0);
        }
        assert_eq!(rebased, expected);
        assert!(reader.next().unwrap().is_none());
        assert!(reader.next().unwrap().is_none());
    }

    #[test]
    fn short_reads_match_ordinary_parser_and_exact_global_spans() {
        let source = concat!(
            "; λ🙂 leading ) (\r\n  ",
            "(foo :bar '(: x : y) `,(,@items) #generate ",
            "\"é🙂\\\"(b)\\\\\\n\\u{1f642}\" #\\u{28} #\\u{29} #\\u{3b} ",
            "#\\λ #\\🙂 #\\space #\\newline #\\{ #\\} ",
            "; ignored ) (\r\n # ignored ) (\r\n (nested))",
            "(同じ)  (last #u64 #!name) # trailing ( )\r\n"
        );
        for step in [1, 2, 3, 5, 17, REFILL_BYTES] {
            compare_with_parse(source, step, 4096);
        }
    }

    #[test]
    fn utf8_and_tokens_cross_real_refill_boundaries() {
        for padding in 0..4 {
            let source = format!(
                "(\"{}🙂\\u{{28}}\\\"\" #\\u{{29}})\r\n(λ)",
                "x".repeat(REFILL_BYTES - 3 + padding)
            );
            compare_with_parse(&source, REFILL_BYTES, 2 * REFILL_BYTES);
        }
        let source = format!(
            "({} #\\u{{28}} ; )\r\n # )\r\n done)",
            "a".repeat(REFILL_BYTES)
        );
        compare_with_parse(&source, REFILL_BYTES, source.len());
        for marker in ["; ", "# "] {
            let source = format!(
                "({marker}{})( ignored\r\n done) (next)",
                "x".repeat(REFILL_BYTES - 3)
            );
            compare_with_parse(&source, REFILL_BYTES, source.len());
        }
    }

    #[test]
    fn exact_size_limits_exclude_trivia_and_the_next_form() {
        let source = " ; prefix\r\n(λ)(x) ; suffix\n";
        compare_with_parse(source, 1, "(λ)".len());
        compare_with_parse(source, REFILL_BYTES, "(λ)".len());
        for step in [1, 3, REFILL_BYTES] {
            let mut reader = ReaderForms::new(
                ShortRead {
                    bytes: b"(abc)",
                    step,
                },
                5,
            );
            assert_eq!(reader.next().unwrap().unwrap().text, "(abc)");
            assert!(reader.next().unwrap().is_none());
            let mut reader = ReaderForms::new(
                ShortRead {
                    bytes: b"(abc)",
                    step,
                },
                4,
            );
            assert!(reader.next().unwrap_err().contains("byte limit"));
        }
        assert!(ReaderForms::new(&b""[..], 0).next().unwrap().is_none());
        assert!(ReaderForms::new(&b"()"[..], 0).next().is_err());
        assert!(ReaderForms::new(&b"()"[..], 1).next().is_err());
        compare_with_parse("()", 1, 2);
        for size in [REFILL_BYTES - 1, REFILL_BYTES, REFILL_BYTES + 1] {
            let source = format!("({})", "x".repeat(size - 2));
            compare_with_parse(&source, REFILL_BYTES, size);
            assert!(ReaderForms::new(source.as_bytes(), size - 1)
                .next()
                .unwrap_err()
                .contains("byte limit"));
        }
    }

    #[test]
    fn late_lexical_and_utf8_errors_are_never_eof() {
        let tails: &[&[u8]] = &[
            b")",
            b"'()",
            b"atom",
            b"(",
            b"(x",
            b"(\"unfinished)",
            b"(\"bad\\q\")",
            b"(#\\)",
            b"(#\\u{d800})",
            b"(#\\u{110000})",
            b"(#\\u{28}",
            b"(\"\\u{",
            b"(\"\\uX\")",
            b"\xff",
            b"\xf0\x9f\x99",
            b"(\"\xff\")",
            b"(\"\xc3\")",
        ];
        for tail in tails {
            let source = [b"(ok) ".as_slice(), *tail].concat();
            for step in [1, 2, REFILL_BYTES] {
                let mut reader = ReaderForms::new(
                    ShortRead {
                        bytes: &source,
                        step,
                    },
                    1024,
                );
                assert_eq!(reader.next().unwrap().unwrap().text, "(ok)");
                let error = reader.next().unwrap_err();
                assert_eq!(reader.next().unwrap_err(), error);
            }
        }
    }

    #[test]
    fn comments_at_eof_and_hash_lookahead_are_lexed_normally() {
        for source in ["#", ";", "# )", "; (", "# λ🙂", "\r\n ; trailing"] {
            let mut reader = ReaderForms::new(
                ShortRead {
                    bytes: source.as_bytes(),
                    step: 1,
                },
                100,
            );
            assert!(reader.next().unwrap().is_none());
        }
        compare_with_parse("(#fn #_ #! #+ #- #* #/ #% #& #| #^ #< #> #=)", 1, 100);
        // Vertical tab is a valid symbol in the ordinary lexer, unlike the
        // ASCII whitespace it recognizes. Framing must preserve that grammar.
        compare_with_parse("(\u{b})", 1, 100);
        for source in ["'()", "`()", ",()", ",@()", "x", ":", "#generate", ")"] {
            assert!(ReaderForms::new(source.as_bytes(), 100).next().is_err());
        }
    }

    #[test]
    fn nesting_and_offset_ranges_are_checked() {
        let allowed = format!(
            "{}{}",
            "(".repeat(MAX_PARSE_NESTING),
            ")".repeat(MAX_PARSE_NESTING)
        );
        compare_with_parse(&allowed, 1, allowed.len());
        let too_deep = format!("({allowed})");
        assert!(ReaderForms::new(too_deep.as_bytes(), too_deep.len())
            .next()
            .unwrap_err()
            .contains("nesting exceeds"));
        assert!(ReaderForms::new(&b"()"[..], usize::MAX)
            .next()
            .unwrap_err()
            .contains("range"));
        let mut reader = ReaderForms::new(&b"()"[..], 10);
        reader.base = usize::MAX;
        assert!(reader.next().unwrap_err().contains("offset overflow"));
    }

    struct FailsAfterBytes {
        bytes: &'static [u8],
    }

    impl Read for FailsAfterBytes {
        fn read(&mut self, output: &mut [u8]) -> std::io::Result<usize> {
            if self.bytes.is_empty() {
                return Err(std::io::Error::other("injected read failure"));
            }
            let count = self.bytes.len().min(output.len());
            output[..count].copy_from_slice(&self.bytes[..count]);
            self.bytes = &self.bytes[count..];
            Ok(count)
        }
    }

    #[test]
    fn read_failures_propagate_even_after_a_complete_form() {
        let mut reader = ReaderForms::new(FailsAfterBytes { bytes: b"()" }, 2);
        assert_eq!(reader.next().unwrap().unwrap().text, "()");
        let error = reader.next().unwrap_err();
        assert!(error.contains("injected read failure"));
        assert_eq!(reader.next().unwrap_err(), error);
        assert!(ReaderForms::new(FailsAfterBytes { bytes: b"" }, 2)
            .next()
            .unwrap_err()
            .contains("injected read failure"));
        for bytes in [
            b"(".as_slice(),
            b"(atom",
            b"(#",
            b"(#\\u{28}",
            b"(\"\\u{",
            b"(\xf0\x9f",
            b"; unfinished comment",
        ] {
            let mut reader = ReaderForms::new(FailsAfterBytes { bytes }, 100);
            assert!(reader.next().unwrap_err().contains("injected read failure"));
        }
    }

    #[test]
    fn interrupted_reads_retry_without_poisoning_the_stream() {
        struct InterruptedReader<'a> {
            bytes: &'a [u8],
            interrupted: bool,
        }
        impl Read for InterruptedReader<'_> {
            fn read(&mut self, output: &mut [u8]) -> std::io::Result<usize> {
                self.interrupted = !self.interrupted;
                if self.interrupted {
                    return Err(std::io::ErrorKind::Interrupted.into());
                }
                let count = output.len().min(self.bytes.len()).min(1);
                output[..count].copy_from_slice(&self.bytes[..count]);
                self.bytes = &self.bytes[count..];
                Ok(count)
            }
        }
        let mut reader = ReaderForms::new(
            InterruptedReader {
                bytes: "(λ)(x)".as_bytes(),
                interrupted: false,
            },
            100,
        );
        assert_eq!(reader.next().unwrap().unwrap().text, "(λ)");
        assert_eq!(reader.next().unwrap().unwrap().text, "(x)");
        assert!(reader.next().unwrap().is_none());
    }

    struct EndlessAtom {
        read: usize,
    }

    impl Read for EndlessAtom {
        fn read(&mut self, output: &mut [u8]) -> std::io::Result<usize> {
            assert!(output.len() <= REFILL_BYTES);
            output.fill(b'a');
            if self.read == 0 {
                output[0] = b'(';
            }
            self.read += output.len();
            Ok(output.len())
        }
    }

    #[test]
    fn malicious_atoms_and_comments_have_finite_retention() {
        let mut reader = ReaderForms::new(EndlessAtom { read: 0 }, 100);
        assert!(reader.next().unwrap_err().contains("byte limit"));
        assert!(reader.reader.read <= 100 + REFILL_BYTES);
        assert!(reader.buffer.capacity() <= 100 + REFILL_BYTES);
        let source = format!(";{}", "x".repeat(3 * REFILL_BYTES));
        let mut reader = ReaderForms::new(source.as_bytes(), 100);
        assert!(reader.next().unwrap_err().contains("byte limit"));
        assert!(reader.buffer.len() <= 100 + REFILL_BYTES);
        assert!(reader.buffer.capacity() <= 100 + REFILL_BYTES);
    }

    #[test]
    fn many_forms_keep_only_the_current_form_and_read_ahead() {
        let source = "(λ) ; comment\r\n".repeat(10000);
        let mut reader = ReaderForms::new(source.as_bytes(), 4);
        for _ in 0..10000 {
            assert_eq!(reader.next().unwrap().unwrap().text, "(λ)");
            assert!(reader.buffer.capacity() <= 4 + REFILL_BYTES);
            assert!(reader.buffer.len() <= REFILL_BYTES);
        }
        assert!(reader.next().unwrap().is_none());
    }

    #[test]
    fn complete_comment_lines_are_released_before_the_next_form() {
        let comment = format!("; λ{}\r\n", "x".repeat(995));
        let source = format!("(first)\n{}(last)", comment.repeat(200));
        let expected = source.rfind("(last)").unwrap();
        let mut reader = ReaderForms::new(source.as_bytes(), 2048);
        assert_eq!(reader.next().unwrap().unwrap().text, "(first)");
        let last = reader.next().unwrap().unwrap();
        assert_eq!(last.text, "(last)");
        assert_eq!(last.span, Span::new(expected, source.len(), 202, 1));
        assert!(reader.buffer.capacity() <= 2048 + REFILL_BYTES);
        assert!(reader.next().unwrap().is_none());
    }
}
