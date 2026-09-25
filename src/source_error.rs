use crate::{Diagnostic, DiagnosticCode, SourceFile, Span};

/// Error identity and location travel separately from explanatory prose.
#[derive(Clone, Debug)]
pub(crate) struct SourceError {
    pub(crate) message: String,
    pub(crate) code: DiagnosticCode,
    pub(crate) span: Option<Span>,
    pub(crate) source_name: Option<String>,
    pub(crate) source_text: Option<String>,
}

impl SourceError {
    pub(crate) fn new(message: impl Into<String>, code: DiagnosticCode) -> Self {
        Self {
            message: message.into(),
            code,
            span: None,
            source_name: None,
            source_text: None,
        }
    }
    pub(crate) fn at(mut self, span: Span) -> Self {
        if self.span.is_none() {
            self.span = Some(span);
        }
        self
    }
    pub(crate) fn attach(mut self, files: &[SourceFile]) -> Self {
        if self.source_name.is_none() {
            if let Some(file) = self
                .span
                .and_then(|span| files.get(span.source_id as usize))
            {
                self.source_name = Some(file.path.display().to_string());
                self.source_text = Some(file.source.clone());
            }
        }
        self
    }
    pub(crate) fn diagnostic(self) -> Diagnostic {
        let mut diagnostic = Diagnostic::new(self.code, self.message);
        diagnostic.span = self.span;
        diagnostic.source_name = self.source_name;
        diagnostic.source_text = self.source_text;
        diagnostic
    }
}
impl From<String> for SourceError {
    fn from(message: String) -> Self {
        Self::new(message, DiagnosticCode::Type)
    }
}
impl From<&str> for SourceError {
    fn from(message: &str) -> Self {
        Self::from(message.to_owned())
    }
}
impl From<SourceError> for String {
    fn from(error: SourceError) -> Self {
        error.to_string()
    }
}
impl std::fmt::Display for SourceError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(span) = self.span {
            if let Some(path) = &self.source_name {
                write!(formatter, "{path}: ")?;
            }
            write!(formatter, "{}:{}: ", span.line, span.column)?;
        }
        formatter.write_str(&self.message)
    }
}
impl std::ops::Deref for SourceError {
    type Target = str;
    fn deref(&self) -> &str {
        &self.message
    }
}
