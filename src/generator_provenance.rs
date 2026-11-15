//! Compiler-owned generation records. Syntax can require provenance, never assert it.
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::{source_error::SourceError, DiagnosticCode, Expr, Span, SpannedExpr};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct Origin {
    pub producer: Arc<str>,
    pub invocation: Arc<str>,
}

#[derive(Clone, Default)]
pub(crate) struct Registry {
    declarations: HashMap<String, HashSet<Origin>>,
    source_declarations: HashMap<(u32, String), HashSet<Origin>>,
    builtin_parents: HashMap<String, HashSet<Origin>>,
}

pub(crate) struct Requirement {
    producer: String,
    names: Vec<(String, Span)>,
}

fn identifier(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Symbol(name) if !name.starts_with('#') && !name.starts_with('@') && name != "$" => {
            Some(name)
        }
        _ => None,
    }
}

pub(crate) fn declared_names(expr: &Expr) -> Vec<&str> {
    let Expr::List(items) = expr else {
        return Vec::new();
    };
    let Some(Expr::Symbol(head)) = items.first() else {
        return Vec::new();
    };
    let mut names = Vec::new();
    if matches!(
        head.as_str(),
        "#fn"
            | "#unsafe-fn"
            | "#extern-fn"
            | "#struct"
            | "#enum"
            | "#type"
            | "#static"
            | "#let"
            | "#let-mut"
            | "#const"
            | "#thread-task"
            | "#syntax"
            | "#dispatch-fn"
            | "#distributed-enum"
    ) {
        names.extend(
            items
                .get(if head == "#extern-fn" { 2 } else { 1 })
                .and_then(identifier),
        );
    }
    if head == "#enum" {
        if let Some(Expr::List(variants)) = items.get(3) {
            for variant in variants {
                names.extend(match variant {
                    Expr::List(parts) => parts.first().and_then(identifier),
                    other => identifier(other),
                });
            }
        }
    }
    if head == "#enum-contribute" {
        if let Some(Expr::List(parts)) = items.get(2) {
            names.extend(parts.first().and_then(identifier));
        }
    }
    if head == "#thread-task" {
        for declaration in items.iter().skip(3) {
            if let Expr::List(parts) = declaration {
                if matches!(parts.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#thread-task-spawn" | "#thread-task-join"))
                {
                    names.extend(parts.get(1).and_then(identifier));
                }
            }
        }
    }
    names
}

impl Registry {
    pub(crate) fn inherit_invocation(&mut self, invocation: &str, origins: &[Origin]) {
        for records in self
            .declarations
            .values_mut()
            .chain(self.source_declarations.values_mut())
            .chain(self.builtin_parents.values_mut())
        {
            if records
                .iter()
                .any(|record| record.invocation.as_ref() == invocation)
            {
                records.extend(origins.iter().cloned());
            }
        }
    }

    pub(crate) fn record(&mut self, expr: &Expr, origins: &[Origin]) {
        if origins.is_empty() {
            return;
        }
        for name in declared_names(expr) {
            self.declarations
                .entry(name.into())
                .or_default()
                .extend(origins.iter().cloned());
        }
    }

    pub(crate) fn record_in_source(&mut self, expr: &Expr, origins: &[Origin], source: u32) {
        self.record(expr, origins);
        if origins.is_empty() {
            return;
        }
        for name in declared_names(expr) {
            self.source_declarations
                .entry((source, name.into()))
                .or_default()
                .extend(origins.iter().cloned());
        }
    }

    pub(crate) fn resolve_declarations(
        &mut self,
        names: impl IntoIterator<Item = (u32, String, String)>,
    ) {
        let mut declarations: HashMap<String, HashSet<Origin>> = HashMap::new();
        // Raw names can coincide across files. Only transfer the claims from
        // the actual declaration's invocation file, never their global union.
        for (source, previous, resolved) in names {
            if let Some(origins) = self.source_declarations.get(&(source, previous)) {
                declarations
                    .entry(resolved)
                    .or_default()
                    .extend(origins.iter().cloned());
            }
        }
        self.declarations = declarations;
    }

    pub(crate) fn record_builtin_parents(
        &mut self,
        invocation: &Expr,
        origins: &[Origin],
    ) -> Result<(), String> {
        if origins.is_empty() {
            return Ok(());
        }
        self.builtin_parents
            .entry(crate::expression_source(invocation)?)
            .or_default()
            .extend(origins.iter().cloned());
        Ok(())
    }

    pub(crate) fn rewrite_builtin(&mut self, previous: &str, rewritten: &str) {
        if previous == rewritten {
            return;
        }
        if let Some(parents) = self.builtin_parents.remove(previous) {
            self.builtin_parents
                .entry(rewritten.into())
                .or_default()
                .extend(parents);
        }
    }

    pub(crate) fn record_builtin_output(
        &mut self,
        invocation: &Expr,
        forms: &[SpannedExpr],
    ) -> Result<(), String> {
        let Expr::List(items) = invocation else {
            return Err("generated invocation must be a list".into());
        };
        let Some(Expr::Symbol(producer)) = items.get(1) else {
            return Err("generated invocation requires a generator name".into());
        };
        let key = crate::expression_source(invocation)?;
        let mut origins = self
            .builtin_parents
            .get(&key)
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .collect::<Vec<_>>();
        origins.push(Origin {
            producer: producer.as_str().into(),
            invocation: key.into(),
        });
        for form in forms {
            self.record(&form.expr, &origins);
        }
        Ok(())
    }

    pub(crate) fn validate(&self, requirements: &[Requirement]) -> Result<(), SourceError> {
        for requirement in requirements {
            let mut candidates: Option<HashSet<&str>> = None;
            for (name, span) in &requirement.names {
                let invocations = self
                    .declarations
                    .get(name)
                    .into_iter()
                    .flatten()
                    .filter(|origin| origin.producer.as_ref() == requirement.producer)
                    .map(|origin| origin.invocation.as_ref())
                    .collect::<HashSet<_>>();
                if invocations.is_empty() {
                    return Err(SourceError::new(
                        format!(
                            "'{name}' was not generated by '#generate {}'",
                            requirement.producer
                        ),
                        DiagnosticCode::Generator,
                    )
                    .at(*span));
                }
                match &mut candidates {
                    Some(candidates) => candidates.retain(|key| invocations.contains(key)),
                    None => candidates = Some(invocations),
                }
                if candidates.as_ref().is_some_and(HashSet::is_empty) {
                    return Err(SourceError::new(
                        format!(
                            "'{name}' and '{}' must come from the same '#generate {}' invocation",
                            requirement.names[0].0, requirement.producer
                        ),
                        DiagnosticCode::Generator,
                    )
                    .at(*span));
                }
            }
        }
        Ok(())
    }
}

/// Requirements are collected before ordinary parsing and checked only after
/// every generator has emitted its declarations. They never schedule expansion.
pub(crate) fn extract(
    forms: Vec<SpannedExpr>,
) -> Result<(Vec<SpannedExpr>, Vec<Requirement>), SourceError> {
    let mut remaining = Vec::with_capacity(forms.len());
    let mut requirements = Vec::new();
    for form in forms {
        let Expr::List(items) = &form.expr else {
            remaining.push(form);
            continue;
        };
        if !matches!(items.first(), Some(Expr::Symbol(head)) if head == "#require-generated") {
            remaining.push(form);
            continue;
        }
        let fail = || {
            SourceError::new("#require-generated expects an identifier, generator name, and optional companion list", DiagnosticCode::Generator).at(form.span)
        };
        if !matches!(items.len(), 3 | 4) {
            return Err(fail());
        }
        let name = identifier(&items[1]).ok_or_else(fail)?;
        let Expr::Symbol(producer) = &items[2] else {
            return Err(fail());
        };
        if producer.starts_with('@') || producer == "$" {
            return Err(fail());
        }
        let span = |index: usize| {
            form.children
                .get(index)
                .map_or(form.span, |child| child.span)
        };
        let mut names = vec![(name.into(), span(1))];
        if let Some(companions) = items.get(3) {
            let Expr::List(companions) = companions else {
                return Err(fail());
            };
            for (index, companion) in companions.iter().enumerate() {
                let name = identifier(companion).ok_or_else(fail)?;
                let companion_span = form
                    .children
                    .get(3)
                    .and_then(|list| list.children.get(index))
                    .map_or(span(3), |child| child.span);
                names.push((name.into(), companion_span));
            }
        }
        requirements.push(Requirement {
            producer: producer.clone(),
            names,
        });
    }
    Ok((remaining, requirements))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn origin(producer: &str, invocation: &str) -> Origin {
        Origin {
            producer: producer.into(),
            invocation: invocation.into(),
        }
    }

    fn requirements(source: &str) -> Vec<Requirement> {
        extract(crate::parse(source).unwrap()).unwrap().1
    }

    #[test]
    fn file_resolution_does_not_merge_same_spelled_generation_claims() {
        let form = crate::parse("(#struct Thing () ())").unwrap().remove(0);
        let mut registry = Registry::default();
        registry.record_in_source(&form.expr, &[origin("first", "one")], 1);
        registry.record_in_source(&form.expr, &[origin("second", "two")], 2);
        registry.resolve_declarations([
            (1, "Thing".into(), "./a.lim::Thing".into()),
            (2, "Thing".into(), "./b.lim::Thing".into()),
        ]);
        registry
            .validate(&requirements("(#require-generated ./a.lim::Thing first)"))
            .unwrap();
        registry
            .validate(&requirements("(#require-generated ./b.lim::Thing second)"))
            .unwrap();
        assert!(registry
            .validate(&requirements("(#require-generated ./b.lim::Thing first)"))
            .is_err());
        assert!(registry
            .validate(&requirements("(#require-generated ./a.lim::Thing second)"))
            .is_err());
        assert!(registry
            .validate(&requirements("(#require-generated Thing first)"))
            .is_err());
    }

    #[test]
    fn companions_must_share_the_expected_invocation() {
        let forms = crate::parse(
            "(#struct Work::Frame () ()) (#enum Work::Poll () (Work::Poll.Pending Work::Poll.Ready))",
        )
        .unwrap();
        let mut registry = Registry::default();
        for form in &forms {
            registry.record(&form.expr, &[origin("producer", "one")]);
        }
        let requirements = requirements(
            "(#require-generated Work::Frame producer (Work::Poll Work::Poll.Pending Work::Poll.Ready))",
        );
        registry.validate(&requirements).unwrap();
        assert!(registry
            .validate(&self::requirements(
                "(#require-generated Work::Frame other)"
            ))
            .is_err());

        let mut mixed = Registry::default();
        mixed.record(&forms[0].expr, &[origin("producer", "one")]);
        mixed.record(&forms[1].expr, &[origin("producer", "two")]);
        let error = mixed.validate(&requirements).unwrap_err();
        assert!(error
            .message
            .contains("same '#generate producer' invocation"));
        assert!(error.span.is_some());
    }

    #[test]
    fn plain_syntax_cannot_claim_generation() {
        let (forms, requirements) = extract(
            crate::parse("(#struct Fake () ()) (#require-generated Fake producer)").unwrap(),
        )
        .unwrap();
        assert_eq!(forms.len(), 1);
        let error = Registry::default().validate(&requirements).unwrap_err();
        assert!(error.message.contains("was not generated"));
    }

    #[test]
    fn duplicate_nested_expansions_retain_new_wrapper_ancestry() {
        let mut registry = Registry::default();
        let form = crate::parse("(#struct Value () ())").unwrap().remove(0);
        registry.record(
            &form.expr,
            &[
                origin("inner", "inner:Value"),
                origin("first", "first:Value"),
            ],
        );
        registry.inherit_invocation("inner:Value", &[origin("second", "second:Value")]);
        registry.validate(&requirements("(#require-generated Value inner) (#require-generated Value first) (#require-generated Value second)")).unwrap();
    }

    #[test]
    fn builtin_output_inherits_wrapper_but_not_unrelated_invocations() {
        let mut registry = Registry::default();
        let invocation = crate::parse("(#generate #optional ((type #u64) (name Maybe)))")
            .unwrap()
            .remove(0)
            .expr;
        registry
            .record_builtin_parents(&invocation, &[origin("wrapper", "wrapper:Maybe")])
            .unwrap();
        let output = crate::parse("(#enum Maybe () ((Maybe.Some #u64) Maybe.None))").unwrap();
        registry
            .record_builtin_output(&invocation, &output)
            .unwrap();
        registry.validate(&requirements("(#require-generated Maybe #optional (Maybe.Some Maybe.None)) (#require-generated Maybe wrapper)")).unwrap();
        assert!(registry
            .validate(&requirements("(#require-generated Maybe unrelated)"))
            .is_err());
    }

    #[test]
    fn external_functions_and_native_task_signatures_are_exports() {
        let mut registry = Registry::default();
        let forms = crate::parse(
            "(#extern-fn #abi-c foreign () #u64 (#effects (#io #global-access)))
          (#thread-task Task worker
            (#thread-task-spawn spawn () SpawnResult)
            (#thread-task-join join ((task Task)) JoinResult))",
        )
        .unwrap();
        for form in forms {
            registry.record(&form.expr, &[origin("producer", "one")]);
        }
        registry
            .validate(&requirements(
                "(#require-generated foreign producer (Task spawn join))",
            ))
            .unwrap();
    }
}
