//! Compiler-owned, reproducible syntax symbols. Source cannot enter this domain.

use std::collections::{HashMap, HashSet};

use crate::Expr;

pub(crate) const PREFIX: &str = "lim.gensym.";

pub(crate) fn reserved(name: &str) -> bool {
    name.starts_with(PREFIX)
}

pub(crate) fn contains_reserved(expression: &Expr) -> bool {
    let mut names = Vec::new();
    collect(expression, &mut names);
    !names.is_empty()
}

fn valid_hint(hint: &str) -> bool {
    !hint.starts_with('#')
        && !reserved(hint)
        && crate::parse(hint)
            .is_ok_and(|forms| forms.len() == 1 && forms[0].expr == Expr::Symbol(hint.to_owned()))
}

pub(crate) struct Scope {
    prefix: String,
    next: u64,
}

impl Scope {
    pub(crate) fn new(domain: char, identity: &str) -> Self {
        Self {
            prefix: format!(
                "{PREFIX}{domain}{:032x}.",
                crate::generator::stable_hash(identity.as_bytes())
            ),
            next: 0,
        }
    }

    pub(crate) fn fresh(&mut self, hint: &str) -> Result<String, String> {
        if !valid_hint(hint) {
            return Err("#gn-gensym hint must be one non-keyword ordinary identifier".into());
        }
        let ordinal = self.next;
        self.next = self.next.checked_add(1).ok_or("gensym counter exhausted")?;
        Ok(format!("{}{ordinal}.{hint}", self.prefix))
    }

    fn owns(&self, name: &str) -> bool {
        let Some(suffix) = name.strip_prefix(&self.prefix) else {
            return false;
        };
        let Some((ordinal, hint)) = suffix.split_once('.') else {
            return false;
        };
        ordinal
            .parse::<u64>()
            .is_ok_and(|value| ordinal == value.to_string())
            && valid_hint(hint)
    }
}

#[derive(Default)]
pub(crate) struct Registry {
    identities: HashMap<String, String>,
    issued: HashSet<String>,
}

impl Registry {
    pub(crate) fn open(&mut self, identity: &str) -> Result<Scope, String> {
        let scope = Scope::new('g', identity);
        self.claim(&scope.prefix, identity)?;
        Ok(scope)
    }

    fn claim(&mut self, namespace: &str, identity: &str) -> Result<(), String> {
        match self.identities.get(namespace) {
            Some(previous) if previous != identity => {
                Err("gensym namespace hash collision between distinct generator invocations".into())
            }
            Some(_) => Ok(()),
            None => {
                self.identities.insert(namespace.into(), identity.into());
                Ok(())
            }
        }
    }

    pub(crate) fn issue(&mut self, name: &str) {
        self.issued.insert(name.into());
    }

    // Cached output can reuse inherited symbols, or restore symbols belonging
    // to precisely this invocation. A foreign namespace never gains authority.
    #[cfg(all(test, not(feature = "proof-kernel-tests")))]
    pub(crate) fn restore(&mut self, forms: &[Expr], scope: &Scope) -> bool {
        self.restore_refs(forms.iter(), scope)
    }

    pub(crate) fn restore_refs<'a>(
        &mut self,
        forms: impl IntoIterator<Item = &'a Expr>,
        scope: &Scope,
    ) -> bool {
        let mut names = Vec::new();
        for form in forms {
            collect(form, &mut names);
        }
        if names
            .iter()
            .any(|name| !self.issued.contains(*name) && !scope.owns(name))
        {
            return false;
        }
        self.issued.extend(names.into_iter().cloned());
        true
    }
}

fn collect<'a>(expression: &'a Expr, names: &mut Vec<&'a String>) {
    match expression {
        Expr::Symbol(name) if reserved(name) => names.push(name),
        Expr::List(items) => {
            for item in items {
                collect(item, names);
            }
        }
        Expr::Quote(inner)
        | Expr::QuasiQuote(inner)
        | Expr::Unquote(inner)
        | Expr::UnquoteSplicing(inner)
        | Expr::Labeled {
            expression: inner, ..
        } => collect(inner, names),
        // This module operates on reader syntax, before Block/Loop lowering.
        _ => {}
    }
}

#[cfg(all(test, not(feature = "proof-kernel-tests")))]
mod tests {
    use super::*;

    #[test]
    fn deterministic_scopes_are_fresh_and_distinct() {
        let mut a = Scope::new('g', "one");
        let mut b = Scope::new('g', "one");
        let first = a.fresh("task").unwrap();
        assert_eq!(first, b.fresh("task").unwrap());
        assert_ne!(first, a.fresh("task").unwrap());
        assert_ne!(first, Scope::new('g', "two").fresh("task").unwrap());
        assert_ne!(first, Scope::new('a', "one").fresh("task").unwrap());
        for hint in ["", "#let", "a b", "()", "42", "lim.gensym.fake"] {
            assert!(a.fresh(hint).is_err(), "{hint}");
        }
    }

    #[test]
    fn cache_restores_only_owned_or_previously_issued_names() {
        let mut registry = Registry::default();
        let mut parent = registry.open("parent").unwrap();
        let parent_name = parent.fresh("task").unwrap();
        let mut child = registry.open("child").unwrap();
        assert!(!registry.restore(&[Expr::Symbol(parent_name.clone())], &child));
        assert!(registry.restore(&[Expr::Symbol(parent_name.clone())], &parent));
        assert!(registry.restore(&[Expr::Symbol(parent_name)], &child));
        assert!(registry.restore(&[Expr::Symbol(child.fresh("local.name").unwrap())], &child));
        assert!(!registry.restore(&[Expr::Symbol("lim.gensym.fake".into())], &child));
    }

    #[test]
    fn namespace_collisions_fail_instead_of_aliasing() {
        let mut registry = Registry::default();
        registry.claim("forced-collision", "first").unwrap();
        assert!(registry
            .claim("forced-collision", "second")
            .unwrap_err()
            .contains("collision"));
    }
}
