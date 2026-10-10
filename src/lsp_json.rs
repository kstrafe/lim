//! Small bounded JSON parser and stdio framing for the language server.
use std::{
    collections::BTreeMap,
    io::{self, BufRead, Read, Write},
};

pub const MAX_BODY: usize = 8 * 1024 * 1024;
const MAX_HEADER: usize = 8192;
const MAX_DEPTH: usize = 64;

#[derive(Clone, Debug, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    Number(String),
    String(String),
    Array(Vec<Json>),
    Object(BTreeMap<String, Json>),
}
impl Json {
    pub fn get(&self, key: &str) -> Option<&Self> {
        if let Self::Object(v) = self {
            v.get(key)
        } else {
            None
        }
    }
    pub fn string(&self) -> Option<&str> {
        if let Self::String(v) = self {
            Some(v)
        } else {
            None
        }
    }
    pub fn integer(&self) -> Option<i64> {
        if let Self::Number(v) = self {
            v.parse().ok()
        } else {
            None
        }
    }
    pub fn array(&self) -> Option<&[Self]> {
        if let Self::Array(v) = self {
            Some(v)
        } else {
            None
        }
    }
    pub fn render(&self) -> String {
        match self {
            Self::Null => "null".into(),
            Self::Bool(v) => v.to_string(),
            Self::Number(v) => v.clone(),
            Self::String(v) => crate::diagnostic_json::quoted(v),
            Self::Array(v) => format!(
                "[{}]",
                v.iter().map(Self::render).collect::<Vec<_>>().join(",")
            ),
            Self::Object(v) => format!(
                "{{{}}}",
                v.iter()
                    .map(|(k, v)| format!("{}:{}", crate::diagnostic_json::quoted(k), v.render()))
                    .collect::<Vec<_>>()
                    .join(",")
            ),
        }
    }
}

pub fn parse(text: &str) -> Result<Json, &'static str> {
    struct Parser<'a> {
        bytes: &'a [u8],
        at: usize,
    }
    impl Parser<'_> {
        fn ws(&mut self) {
            while self
                .bytes
                .get(self.at)
                .is_some_and(|b| matches!(b, b' ' | b'\t' | b'\r' | b'\n'))
            {
                self.at += 1;
            }
        }
        fn take(&mut self, b: u8) -> bool {
            if self.bytes.get(self.at) == Some(&b) {
                self.at += 1;
                true
            } else {
                false
            }
        }
        fn hex(&mut self) -> Result<u16, &'static str> {
            let mut n = 0;
            for _ in 0..4 {
                let b = *self.bytes.get(self.at).ok_or("short unicode escape")?;
                self.at += 1;
                n = n * 16
                    + match b {
                        b'0'..=b'9' => (b - b'0') as u16,
                        b'a'..=b'f' => (b - b'a' + 10) as u16,
                        b'A'..=b'F' => (b - b'A' + 10) as u16,
                        _ => return Err("invalid unicode escape"),
                    };
            }
            Ok(n)
        }
        fn string(&mut self) -> Result<String, &'static str> {
            if !self.take(b'"') {
                return Err("expected string");
            }
            let mut out = String::new();
            loop {
                let start = self.at;
                while self
                    .bytes
                    .get(self.at)
                    .is_some_and(|b| *b >= 32 && !matches!(b, b'"' | b'\\'))
                {
                    self.at += 1;
                }
                out.push_str(
                    std::str::from_utf8(&self.bytes[start..self.at]).map_err(|_| "invalid utf8")?,
                );
                if self.take(b'"') {
                    return Ok(out);
                }
                if !self.take(b'\\') {
                    return Err("invalid string");
                }
                let b = *self.bytes.get(self.at).ok_or("short escape")?;
                self.at += 1;
                match b {
                    b'"' => out.push('"'),
                    b'\\' => out.push('\\'),
                    b'/' => out.push('/'),
                    b'b' => out.push('\u{8}'),
                    b'f' => out.push('\u{c}'),
                    b'n' => out.push('\n'),
                    b'r' => out.push('\r'),
                    b't' => out.push('\t'),
                    b'u' => {
                        let hi = self.hex()?;
                        let code = if (0xd800..=0xdbff).contains(&hi) {
                            if !self.take(b'\\') || !self.take(b'u') {
                                return Err("missing low surrogate");
                            }
                            let lo = self.hex()?;
                            if !(0xdc00..=0xdfff).contains(&lo) {
                                return Err("invalid low surrogate");
                            }
                            0x10000 + ((hi as u32 - 0xd800) << 10) + lo as u32 - 0xdc00
                        } else {
                            hi as u32
                        };
                        out.push(char::from_u32(code).ok_or("invalid unicode scalar")?);
                    }
                    _ => return Err("invalid escape"),
                }
            }
        }
        fn value(&mut self, depth: usize) -> Result<Json, &'static str> {
            if depth > MAX_DEPTH {
                return Err("JSON nesting limit");
            }
            self.ws();
            match self.bytes.get(self.at).copied() {
                Some(b'"') => Ok(Json::String(self.string()?)),
                Some(b'{') => {
                    self.at += 1;
                    self.ws();
                    let mut v = BTreeMap::new();
                    if self.take(b'}') {
                        return Ok(Json::Object(v));
                    }
                    loop {
                        self.ws();
                        let k = self.string()?;
                        self.ws();
                        if !self.take(b':') {
                            return Err("expected colon");
                        }
                        let value = self.value(depth + 1)?;
                        if v.insert(k, value).is_some() {
                            return Err("duplicate object key");
                        }
                        self.ws();
                        if self.take(b'}') {
                            break;
                        }
                        if !self.take(b',') {
                            return Err("expected comma");
                        }
                    }
                    Ok(Json::Object(v))
                }
                Some(b'[') => {
                    self.at += 1;
                    self.ws();
                    let mut v = Vec::new();
                    if self.take(b']') {
                        return Ok(Json::Array(v));
                    }
                    loop {
                        v.push(self.value(depth + 1)?);
                        self.ws();
                        if self.take(b']') {
                            break;
                        }
                        if !self.take(b',') {
                            return Err("expected comma");
                        }
                    }
                    Ok(Json::Array(v))
                }
                Some(b'n' | b't' | b'f') => {
                    for (literal, value) in [
                        ("null", Json::Null),
                        ("true", Json::Bool(true)),
                        ("false", Json::Bool(false)),
                    ] {
                        if self.bytes[self.at..].starts_with(literal.as_bytes()) {
                            self.at += literal.len();
                            return Ok(value);
                        }
                    }
                    Err("invalid literal")
                }
                Some(b'-' | b'0'..=b'9') => {
                    let start = self.at;
                    self.take(b'-');
                    if !self.take(b'0') {
                        if !self
                            .bytes
                            .get(self.at)
                            .is_some_and(|b| matches!(b, b'1'..=b'9'))
                        {
                            return Err("invalid number");
                        }
                        while self.bytes.get(self.at).is_some_and(u8::is_ascii_digit) {
                            self.at += 1;
                        }
                    }
                    for marker in [b'.', b'e'] {
                        let found = if marker == b'e' {
                            self.take(b'e') || self.take(b'E')
                        } else {
                            self.take(marker)
                        };
                        if found {
                            if marker == b'e' && !self.take(b'+') {
                                self.take(b'-');
                            }
                            let digits = self.at;
                            while self.bytes.get(self.at).is_some_and(u8::is_ascii_digit) {
                                self.at += 1;
                            }
                            if digits == self.at {
                                return Err("invalid number");
                            }
                        }
                    }
                    let s = std::str::from_utf8(&self.bytes[start..self.at])
                        .map_err(|_| "invalid number")?;
                    if !s.parse::<f64>().is_ok_and(f64::is_finite) {
                        return Err("number out of range");
                    }
                    Ok(Json::Number(s.into()))
                }
                _ => Err("expected value"),
            }
        }
    }
    if text.len() > MAX_BODY {
        return Err("JSON size limit");
    }
    let mut p = Parser {
        bytes: text.as_bytes(),
        at: 0,
    };
    let result = p.value(0)?;
    p.ws();
    if p.at != p.bytes.len() {
        return Err("trailing JSON");
    }
    Ok(result)
}

/// Invalid framing is fatal: guessing where the next body starts is unsafe.
pub fn read_frame(input: &mut impl BufRead) -> io::Result<Option<String>> {
    let invalid = || io::Error::new(io::ErrorKind::InvalidData, "invalid LSP framing");
    let mut total = 0;
    let mut length = None;
    loop {
        let mut line = Vec::new();
        let n = input
            .take((MAX_HEADER - total + 1) as u64)
            .read_until(b'\n', &mut line)?;
        if n == 0 {
            return if total == 0 { Ok(None) } else { Err(invalid()) };
        }
        total += n;
        if total > MAX_HEADER || !line.ends_with(b"\r\n") {
            return Err(invalid());
        }
        if line == b"\r\n" {
            break;
        }
        let line = std::str::from_utf8(&line[..line.len() - 2]).map_err(|_| invalid())?;
        let (key, value) = line.split_once(':').ok_or_else(invalid)?;
        if key.eq_ignore_ascii_case("Content-Length") {
            if length.is_some()
                || value.trim().is_empty()
                || !value.trim().bytes().all(|b| b.is_ascii_digit())
            {
                return Err(invalid());
            }
            length = Some(value.trim().parse::<usize>().map_err(|_| invalid())?);
        }
    }
    let length = length.filter(|n| *n <= MAX_BODY).ok_or_else(invalid)?;
    let mut body = vec![0; length];
    input.read_exact(&mut body)?;
    String::from_utf8(body).map(Some).map_err(|_| invalid())
}
pub fn write_frame(output: &mut impl Write, body: &str) -> io::Result<()> {
    write!(output, "Content-Length: {}\r\n\r\n{}", body.len(), body)?;
    output.flush()
}
