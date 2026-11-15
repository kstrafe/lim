//! Merge distributed enum declarations after generator and cfg expansion.

use crate::source_error::SourceError;
use crate::{DiagnosticCode, Expr, SpannedExpr};
use std::collections::{BTreeMap, HashMap};

fn items(form: &SpannedExpr) -> Option<&[Expr]> {
    match &form.expr {
        Expr::List(items) => Some(items),
        _ => None,
    }
}

fn child(form: &SpannedExpr, index: usize) -> &SpannedExpr {
    form.children.get(index).unwrap_or(form)
}

fn identifier(expr: Option<&Expr>) -> Option<&str> {
    match expr {
        Some(Expr::Symbol(name)) if !name.starts_with('#') && !name.starts_with('@') => Some(name),
        _ => None,
    }
}

fn error(message: impl Into<String>, span: crate::Span) -> SourceError {
    SourceError::new(message, DiagnosticCode::Parse).at(span)
}

fn recognized(form: &SpannedExpr, head: &str) -> bool {
    matches!(items(form).and_then(|xs| xs.first()), Some(Expr::Symbol(s)) if s == head)
}

fn variant_name(variant: &Expr) -> Option<&str> {
    match variant {
        Expr::Symbol(name) if !name.starts_with('#') && !name.starts_with('@') => Some(name),
        Expr::List(parts) => identifier(parts.first()),
        _ => None,
    }
}

fn add_variant(
    variants: &mut HashMap<String, BTreeMap<String, (Expr, SpannedExpr)>>,
    enum_name: &str,
    variant: &Expr,
    source: &SpannedExpr,
) -> Result<(), SourceError> {
    let Some(name) = variant_name(variant) else {
        return Err(error(
            "enum variant must begin with a user-defined identifier",
            source.span,
        ));
    };
    let entries = variants.entry(enum_name.to_owned()).or_default();
    if let Some((previous_expr, previous_source)) = entries.get(name) {
        if previous_expr != variant {
            return Err(error(
                format!("conflicting definitions of enum variant '{name}' in '{enum_name}'"),
                source.span,
            )
            .with_label(previous_source.span, "previous variant definition"));
        }
    } else {
        entries.insert(name.to_owned(), (variant.clone(), source.clone()));
    }
    Ok(())
}

/// Combines `#distributed-enum` declarations and single-variant
/// `#enum-contribute` forms into ordinary `#enum` declarations.
pub(crate) fn merge(forms: Vec<SpannedExpr>) -> Result<Vec<SpannedExpr>, SourceError> {
    let mut declarations: HashMap<String, usize> = HashMap::new();
    for (index, form) in forms.iter().enumerate() {
        if !recognized(form, "#distributed-enum") {
            continue;
        }
        let xs = items(form).unwrap();
        if xs.len() != 3 {
            return Err(error(
                "#distributed-enum requires a name and properties",
                child(form, 0).span,
            ));
        }
        let Some(name) = identifier(xs.get(1)) else {
            return Err(error(
                "distributed enum name must be a user-defined identifier",
                child(form, 1).span,
            ));
        };
        if let Some(previous) = declarations.insert(name.to_owned(), index) {
            return Err(error(
                format!("duplicate distributed enum declaration '{name}'"),
                child(form, 1).span,
            )
            .with_label(
                child(&forms[previous], 1).span,
                "previous distributed enum declaration",
            ));
        }
        if !matches!(xs.get(2), Some(Expr::List(_))) {
            return Err(error(
                "distributed enum properties must be a list",
                child(form, 2).span,
            ));
        }
    }

    let mut variants: HashMap<String, BTreeMap<String, (Expr, SpannedExpr)>> = HashMap::new();
    for form in &forms {
        if recognized(form, "#enum-contribute") {
            let xs = items(form).unwrap();
            if xs.len() != 3 {
                return Err(error(
                    "#enum-contribute requires an enum name and one variant",
                    child(form, 0).span,
                ));
            }
            let Some(name) = identifier(xs.get(1)) else {
                return Err(error(
                    "enum contribution target must be a user-defined identifier",
                    child(form, 1).span,
                ));
            };
            let Some(Expr::List(_)) = xs.get(2) else {
                return Err(error(
                    "enum contribution variant must be a list",
                    child(form, 2).span,
                ));
            };
            if !declarations.contains_key(name) {
                return Err(error(
                    format!("enum contribution refers to missing distributed enum '{name}'"),
                    child(form, 1).span,
                ));
            }
            add_variant(&mut variants, name, &xs[2], child(form, 2))?;
        }
    }

    let mut output = Vec::with_capacity(forms.len());
    for (index, mut form) in forms.into_iter().enumerate() {
        if recognized(&form, "#enum-contribute") {
            continue;
        }
        if !recognized(&form, "#distributed-enum") {
            output.push(form);
            continue;
        }
        let xs = items(&form).unwrap();
        let name = identifier(xs.get(1)).unwrap();
        debug_assert_eq!(declarations.get(name), Some(&index));
        let merged = variants.remove(name).unwrap_or_default();
        let mut result = vec![Expr::Symbol("#enum".into()), xs[1].clone(), xs[2].clone()];
        let mut result_children = vec![
            child(&form, 0).clone(),
            child(&form, 1).clone(),
            child(&form, 2).clone(),
        ];
        result_children[0].expr = Expr::Symbol("#enum".into());
        let mut variant_exprs = Vec::with_capacity(merged.len());
        let mut variant_children = Vec::with_capacity(merged.len());
        for (_, (expr, source)) in merged {
            variant_exprs.push(expr);
            variant_children.push(source);
        }
        let variant_list = Expr::List(variant_exprs.into());
        result.push(variant_list.clone());
        result_children.push(SpannedExpr {
            expr: variant_list,
            span: form.span,
            children: variant_children.into(),
        });
        form.expr = Expr::List(result.into());
        form.children = result_children.into();
        output.push(form);
    }
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(source: &str) -> Vec<SpannedExpr> {
        crate::parse(source).expect("test source should parse")
    }

    fn merged(source: &str) -> Vec<SpannedExpr> {
        merge(parse(source)).expect("merge should succeed")
    }

    fn enum_form(forms: &[SpannedExpr]) -> (&[Expr], &SpannedExpr) {
        let form = forms
            .iter()
            .find(|form| recognized(form, "#enum"))
            .expect("merged enum should exist");
        (items(form).unwrap(), form)
    }

    #[test]
    fn properties_are_not_variants_and_contributions_sort_after_declaration() {
        let forms = merged(
            "(#enum-contribute E (E.Zulu #u64))\n(#distributed-enum E (#linear #repr-c))\n(#enum-contribute E (E.Alpha))",
        );
        let (xs, _) = enum_form(&forms);
        assert_eq!(
            xs[2],
            Expr::List(
                vec![
                    Expr::Symbol("#linear".into()),
                    Expr::Symbol("#repr-c".into())
                ]
                .into()
            )
        );
        assert_eq!(
            xs[3],
            Expr::List(
                vec![
                    Expr::List(vec![Expr::Symbol("E.Alpha".into())].into()),
                    Expr::List(
                        vec![Expr::Symbol("E.Zulu".into()), Expr::Symbol("#u64".into())].into()
                    ),
                ]
                .into()
            )
        );
    }

    #[test]
    fn identical_variants_deduplicate_and_keep_variant_source() {
        let forms = merged(
            "(#enum-contribute E (E.A #u64))\n(#distributed-enum E ())\n(#enum-contribute E (E.A #u64))",
        );
        let (xs, form) = enum_form(&forms);
        let Expr::List(variants) = &xs[3] else {
            panic!("variants should be a list")
        };
        assert_eq!(variants.len(), 1);
        assert_eq!(
            variants[0],
            Expr::List(vec![Expr::Symbol("E.A".into()), Expr::Symbol("#u64".into())].into())
        );
        assert_eq!(form.children[3].children[0].expr, variants[0]);
    }

    #[test]
    fn conflicting_variant_reports_later_span_and_previous_label() {
        let parsed = parse(
            "(#distributed-enum E ())\n(#enum-contribute E (E.A #u64))\n(#enum-contribute E (E.A #i64))",
        );
        let later_span = parsed[2].children[2].span;
        let error = merge(parsed).expect_err("different payloads conflict");
        assert_eq!(error.span, Some(later_span));
        assert!(error
            .message
            .contains("conflicting definitions of enum variant 'E.A'"));
    }

    #[test]
    fn contribution_can_precede_declaration_but_missing_enum_fails() {
        let forms = merged("(#enum-contribute E (E.Empty))\n(#distributed-enum E ())");
        assert_eq!(
            enum_form(&forms).0[3],
            Expr::List(vec![Expr::List(vec![Expr::Symbol("E.Empty".into())].into())].into())
        );
        let error =
            merge(parse("(#enum-contribute missing (Missing.Empty))")).expect_err("missing target");
        assert!(error.message.contains("missing distributed enum 'missing'"));
    }
}
