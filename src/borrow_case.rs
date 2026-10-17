//! Explicit borrowed match patterns, after surface arm normalization.

use crate::{Expr, Type};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Mode {
    pub pinned: bool,
    pub mutable: bool,
}

impl Mode {
    pub fn from_keyword(keyword: &str) -> Option<Self> {
        let (pinned, mutable) = match keyword {
            "#case-ref" => (false, false),
            "#case-ref-mut" => (false, true),
            "#case-pin" => (true, false),
            "#case-pin-mut" => (true, true),
            _ => return None,
        };
        Some(Self { pinned, mutable })
    }

    pub fn keyword(self) -> &'static str {
        match (self.pinned, self.mutable) {
            (false, false) => "#case-ref",
            (false, true) => "#case-ref-mut",
            (true, false) => "#case-pin",
            (true, true) => "#case-pin-mut",
        }
    }

    pub fn reference(self, target: Type) -> Type {
        let target = Box::new(target);
        if self.pinned {
            Type::PinnedReference {
                mutable: self.mutable,
                target,
            }
        } else {
            Type::Reference {
                mutable: self.mutable,
                target,
            }
        }
    }
}

pub(crate) fn parts(pattern: &Expr) -> Option<(Mode, &Expr)> {
    let Expr::List(items) = pattern else {
        return None;
    };
    if items.len() != 2 {
        return None;
    }
    let Expr::Symbol(head) = &items[0] else {
        return None;
    };
    Some((Mode::from_keyword(head)?, &items[1]))
}
