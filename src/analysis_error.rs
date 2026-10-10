//! Diagnostic-only node identities scoped to an immutable analysis pass.
//!
//! RAII restores the current site on normal returns and unwinding; thread-local
//! storage isolates concurrent compiler calls. Addresses are never dereferenced
//! and are resolved to owned spans before returning a public diagnostic.
use crate::{Expr, Program, Span, Statement};
use std::cell::Cell;

#[derive(Clone, Copy, Debug)]
pub(crate) struct Site {
    pub node: usize,
    pub statement: bool,
    pub child: Option<usize>,
}
thread_local! { static CURRENT: Cell<Option<Site>> = const { Cell::new(None) }; }
#[cfg(test)]
thread_local! { static REWORD: Cell<bool> = const { Cell::new(false) }; }
pub(crate) struct Enter(Option<Site>);
impl Drop for Enter {
    fn drop(&mut self) {
        CURRENT.with(|current| current.set(self.0));
    }
}
impl Site {
    pub fn expression(value: &Expr) -> Self {
        let child = match value {
            Expr::List(items) => match items.first() {
                Some(Expr::Symbol(head)) if matches!(head.as_str(), "borrow" | "borrow-mut") => {
                    Some(0)
                }
                Some(Expr::Symbol(head))
                    if matches!(head.as_str(), "forget" | "drop" | "clone") =>
                {
                    Some(1)
                }
                _ => None,
            },
            _ => None,
        };
        Self {
            node: std::ptr::from_ref(value) as usize,
            statement: false,
            child,
        }
    }
    pub fn statement(value: &Statement) -> Self {
        let child = if matches!(
            value,
            Statement::Assign { .. }
                | Statement::ArrayAssign { .. }
                | Statement::FieldAssign { .. }
                | Statement::TupleAssign { .. }
                | Statement::EnumPayloadAssign { .. }
        ) {
            0
        } else {
            1
        };
        Self {
            node: std::ptr::from_ref(value) as usize,
            statement: true,
            child: Some(child),
        }
    }
    pub fn enter(self) -> Enter {
        Enter(CURRENT.with(|current| current.replace(Some(self))))
    }
    pub fn current() -> Option<Self> {
        CURRENT.with(Cell::get)
    }
    pub fn span(self, program: &Program) -> Option<Span> {
        let source = crate::typecheck::analysis_node_source(program, self.node, self.statement)?;
        let child = self.child.and_then(|index| {
            // Lowered call heads correspond to the source callee, not #call.
            let index = if index == 0 && matches!(&source.expr, Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#call")) { 1 } else { index };
            source.children.get(index)
        });
        Some(child.unwrap_or(source).span)
    }
}

#[derive(Debug)]
pub(crate) struct Error {
    pub message: String,
    pub site: Option<Site>,
    pub related: Vec<Site>,
}
impl Error {
    pub fn related(mut self, site: Option<Site>) -> Self {
        self.related.extend(site);
        self
    }
    pub fn at(mut self, site: Site) -> Self {
        self.site = Some(site);
        self
    }
    pub fn child(mut self, index: usize) -> Self {
        if let Some(site) = &mut self.site {
            site.child = Some(index);
        }
        self
    }
}
impl From<String> for Error {
    fn from(message: String) -> Self {
        #[cfg(test)]
        let message = if REWORD.with(Cell::get) {
            "diagnostic wording replaced".to_owned()
        } else {
            message
        };
        Self {
            message,
            site: Site::current(),
            related: Vec::new(),
        }
    }
}
impl From<&str> for Error {
    fn from(message: &str) -> Self {
        message.to_owned().into()
    }
}
impl std::fmt::Display for Error {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.message.fmt(out)
    }
}
impl From<Error> for String {
    fn from(error: Error) -> Self {
        error.message
    }
}
macro_rules! failure { ($($arg:tt)*) => { $crate::analysis_error::Error::from(format!($($arg)*)) }; }
pub(crate) use failure;

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn ownership_and_unsafe_spans_do_not_depend_on_error_wording() {
        let sources = [
            include_str!("../tests/ui/borrow-conflict-callee-name.lim"),
            include_str!("../tests/ui/borrow-conflict-field-name.lim"),
            include_str!("../tests/ui/borrow.lim"),
            include_str!("../tests/ui/linear.lim"),
            include_str!("../tests/ui/unsafe-pointer-op.lim"),
            include_str!("../tests/ui/unsafe-external-call.lim"),
            "(#struct Resource ((value #u64))) (#linear Resource) (#fn use ((a Resource) (b Resource)) () (#forget a) (#forget b) (#return ())) (#fn main () () (#let a.b Resource (#struct-literal Resource ((value 1u64)))) (#call use (: b a.b : a a.b)) (#return ()))",
            "(#struct Resource ((value #u64))) (#linear Resource) (#fn main () #u64 (#let a Resource (#struct-literal Resource ((value 1u64)))) (#forget a) (#let a-again Resource (#struct-literal Resource ((value 2u64)))) (#forget a-again) (#forget a-again) (#return 0u64))",
            "(#fn read ((p (#ptr #u64))) #u64 (#let first #u64 (#unsafe (#ptr-read p))) (#return (#ptr-read p)))",
            "(#fn read ((p (#ptr #u64))) #u64 (#return (#match true (#case true (#ptr-read p)) (#case false 0u64))))",
        ];
        for source in sources {
            let program = crate::parse_program(source).unwrap();
            let original = crate::typecheck::check_types_with_span(&program).unwrap_err();
            REWORD.with(|flag| flag.set(true));
            let changed = crate::typecheck::check_types_with_span(&program).unwrap_err();
            REWORD.with(|flag| flag.set(false));
            assert_ne!(original.0, changed.0, "{source}");
            assert_eq!(
                (original.1, original.2, &original.3),
                (changed.1, changed.2, &changed.3),
                "{source}"
            );
            assert!(original.2.is_some());
            if source.contains("(#let first") {
                assert_eq!(
                    original.2.unwrap().start,
                    source.rfind("#ptr-read").unwrap()
                );
            }
            if source.contains("(b a.b)") {
                assert_eq!(
                    original.2.unwrap().start,
                    source.find("(b a.b)").unwrap() + 3
                );
                assert!(!changed.3.is_empty(), "prior move must be labeled");
            }
            if source.contains("(#match true") {
                assert_eq!(original.2.unwrap().start, source.find("#ptr-read").unwrap());
            }
        }
    }
}
