//! Shared declaration shapes and pattern bindings for generator analysis.
//! No body rewriting, storage layout, or legacy lowering lives here.

#[cfg(all(test, not(feature = "proof-kernel-tests")))]
use crate::{normalize_keywords, parse_type, Expr, Type};
use std::collections::HashMap;
#[cfg(all(test, not(feature = "proof-kernel-tests")))]
use std::collections::HashSet;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct AsyncTypeEnvironment {
    pub enums: HashMap<String, HashMap<String, Vec<String>>>,
    pub aliases: HashMap<String, String>,
    pub functions: HashMap<String, HashMap<String, String>>,
    /// Named call operands execute in parameter declaration order.
    pub function_parameter_order: HashMap<String, Vec<String>>,
    pub function_results: HashMap<String, String>,
    pub struct_fields: HashMap<String, HashMap<String, String>>,
    /// Positional struct patterns follow declaration order, never hash order.
    pub struct_field_order: HashMap<String, Vec<String>>,
}

#[cfg(all(test, not(feature = "proof-kernel-tests")))]
fn resolve_async_enum_name<'a>(
    type_name: &'a str,
    environment: &'a AsyncTypeEnvironment,
) -> Option<&'a str> {
    let mut current = type_name;
    for _ in 0..=environment.aliases.len() {
        if environment.enums.contains_key(current) {
            return Some(current);
        }
        current = environment.aliases.get(current)?;
    }
    None
}

#[cfg(all(test, not(feature = "proof-kernel-tests")))]
pub(crate) fn collect_enum_pattern_bindings(
    pattern: &Expr,
    type_name: &str,
    environment: &AsyncTypeEnvironment,
    bindings: &mut Vec<(String, String)>,
) -> Result<(), String> {
    match pattern {
        Expr::Symbol(name) if name == "_" || matches!(name.as_str(), "true" | "false") => {}
        Expr::Symbol(name) => {
            let is_unit_variant = resolve_async_enum_name(type_name, environment)
                .and_then(|enum_name| environment.enums.get(enum_name))
                .is_some_and(|variants| variants.contains_key(name));
            if !is_unit_variant {
                bindings.push((name.clone(), type_name.to_owned()));
            }
        }
        Expr::List(items) if !items.is_empty() => {
            let Expr::Symbol(variant_name) = &items[0] else {
                return Err(
                    "#generate #async-fn #for initializer requires named enum patterns".into(),
                );
            };
            // Tuple/array payloads have explicit structural declarations too.
            // Resolve aliases only to select their layout; keep the declared
            // field type spelling when introducing each captured binding.
            let mut declared = type_name;
            let mut visited = HashSet::new();
            while let Some(target) = environment.aliases.get(declared) {
                if !visited.insert(declared) {
                    return Err(format!(
                        "#generate #async-fn cyclic pattern type alias '{type_name}'"
                    ));
                }
                declared = target;
            }
            let parsed = crate::parse(declared)?;
            let ty = parse_type(Some(&normalize_keywords(
                parsed
                    .first()
                    .ok_or_else(|| {
                        format!("#generate #async-fn missing pattern type '{type_name}'")
                    })?
                    .expr
                    .clone(),
            )))?;
            let structural_fields = match ty {
                Type::Tuple(fields) if matches!(variant_name.as_str(), "#tuple" | "tuple") => {
                    Some(fields.iter().map(crate::type_source).collect::<Vec<_>>())
                }
                Type::Array(element, length)
                    if matches!(variant_name.as_str(), "#array" | "array") =>
                {
                    if length != items.len() - 1 {
                        return Err(format!(
                            "#generate #async-fn array pattern expects {length} elements"
                        ));
                    }
                    Some(vec![crate::type_source(&element); length])
                }
                Type::Named(name)
                    if variant_name == &name && environment.struct_fields.contains_key(&name) =>
                {
                    let order = environment.struct_field_order.get(&name).ok_or_else(|| {
                        format!("#generate #async-fn missing declared field order for '{name}'")
                    })?;
                    let fields = &environment.struct_fields[&name];
                    Some(
                        order
                            .iter()
                            .map(|field| {
                                fields.get(field).cloned().ok_or_else(|| {
                                    format!("#generate #async-fn missing declared field '{name}.{field}'")
                                })
                            })
                            .collect::<Result<Vec<_>, _>>()?,
                    )
                }
                _ => None,
            };
            if let Some(fields) = structural_fields {
                if fields.len() != items.len() - 1 {
                    return Err(format!(
                        "#generate #async-fn aggregate pattern '{variant_name}' expects {} fields",
                        fields.len()
                    ));
                }
                for (pattern, field_type) in items[1..].iter().zip(&fields) {
                    collect_enum_pattern_bindings(pattern, field_type, environment, bindings)?;
                }
                return Ok(());
            }
            let enum_name = resolve_async_enum_name(type_name, environment).ok_or_else(|| {
                format!("#generate #async-fn cannot resolve enum payload types for '{type_name}'")
            })?;
            let fields = environment
                .enums
                .get(enum_name)
                .and_then(|variants| variants.get(variant_name))
                .ok_or_else(|| {
                    format!(
                        "#generate #async-fn cannot resolve pattern variant '{variant_name}' for '{type_name}'"
                    )
                })?;
            if fields.len() != items.len() - 1 {
                return Err(format!(
                    "#generate #async-fn enum pattern '{variant_name}' has {} fields, but the declaration has {}",
                    items.len() - 1,
                    fields.len()
                ));
            }
            for (field_pattern, field_type) in items[1..].iter().zip(fields) {
                collect_enum_pattern_bindings(field_pattern, field_type, environment, bindings)?;
            }
        }
        Expr::Integer(_) | Expr::UnsignedInteger(_) | Expr::Char(_) | Expr::String(_) => {}
        _ => return Err("#generate #async-fn #for initializer has an unsupported pattern".into()),
    }
    Ok(())
}

#[cfg(all(test, not(feature = "proof-kernel-tests")))]
mod tests {
    use super::*;

    fn environment() -> AsyncTypeEnvironment {
        let mut environment = AsyncTypeEnvironment::default();
        environment.enums.insert(
            "Choice".into(),
            HashMap::from([
                ("Empty".into(), vec![]),
                (
                    "Data".into(),
                    vec!["(#tuple PairAlias (#array #u8 2))".into()],
                ),
            ]),
        );
        environment.aliases.extend([
            ("ChoiceAlias".into(), "Choice".into()),
            ("PairAlias".into(), "Pair".into()),
        ]);
        environment.struct_fields.insert(
            "Pair".into(),
            HashMap::from([
                ("right".into(), "#u64".into()),
                ("left".into(), "#u32".into()),
            ]),
        );
        environment
            .struct_field_order
            .insert("Pair".into(), vec!["left".into(), "right".into()]);
        environment
    }

    fn bindings(
        pattern: &str,
        ty: &str,
        environment: &AsyncTypeEnvironment,
    ) -> Result<Vec<(String, String)>, String> {
        let pattern = crate::parse(pattern).unwrap().remove(0).expr;
        let mut bindings = Vec::new();
        collect_enum_pattern_bindings(&pattern, ty, environment, &mut bindings)?;
        Ok(bindings)
    }

    #[test]
    fn nested_patterns_follow_declared_order_and_preserve_alias_spelling() {
        let environment = environment();
        assert_eq!(
            bindings(
                "(Data (#tuple (Pair first second) (#array a b)))",
                "ChoiceAlias",
                &environment
            )
            .unwrap(),
            vec![
                ("first".into(), "#u32".into()),
                ("second".into(), "#u64".into()),
                ("a".into(), "#u8".into()),
                ("b".into(), "#u8".into())
            ]
        );
        assert_eq!(
            bindings(
                "(Data (#tuple pair (#array _ b)))",
                "ChoiceAlias",
                &environment
            )
            .unwrap(),
            vec![
                ("pair".into(), "PairAlias".into()),
                ("b".into(), "#u8".into())
            ]
        );
        assert!(bindings("Empty", "ChoiceAlias", &environment)
            .unwrap()
            .is_empty());
        assert_eq!(
            bindings(
                "(#tuple a (#array b c))",
                "(#tuple #u64 (#array #u8 2))",
                &environment
            )
            .unwrap(),
            vec![
                ("a".into(), "#u64".into()),
                ("b".into(), "#u8".into()),
                ("c".into(), "#u8".into())
            ]
        );
    }

    #[test]
    fn malformed_shape_metadata_fails_without_choosing_a_guessed_layout() {
        let mut environment = environment();
        assert!(
            bindings("(Data (#tuple pair (#array a)))", "Choice", &environment)
                .unwrap_err()
                .contains("expects 2 elements")
        );
        assert!(bindings("(missing value)", "Choice", &environment)
            .unwrap_err()
            .contains("cannot resolve pattern variant"));
        environment.struct_field_order.remove("Pair");
        assert!(bindings("(Pair a b)", "PairAlias", &environment)
            .unwrap_err()
            .contains("missing declared field order"));
        environment
            .aliases
            .extend([("A".into(), "B".into()), ("B".into(), "A".into())]);
        assert!(bindings("(Data value)", "A", &environment)
            .unwrap_err()
            .contains("cyclic pattern type alias"));
    }
}
