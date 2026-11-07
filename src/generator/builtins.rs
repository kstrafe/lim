//! Built-in generator registration and argument validation.
use crate::*;

pub(crate) fn capitalized_type_name(name: &str) -> String {
    if let Some((path, name)) = crate::file_access::split(name) {
        return format!("{path}::{}", capitalized_type_name(name));
    }
    if let Some((prefix, local)) = name.rsplit_once('@') {
        return format!("{prefix}@{}", capitalized_type_name(local));
    }
    let mut characters = name.chars();
    let Some(first) = characters.next() else {
        return String::new();
    };
    first.to_uppercase().chain(characters).collect()
}

pub(crate) fn named_builtin_keys(kind: &str) -> Option<&'static [&'static str]> {
    Some(match kind {
        "#optional" => &["type", "name"],
        "#result" => &["ok", "error", "name"],
        "#thread-spawn" => &["task", "worker"],
        "#vec" => &["element", "allocator", "name"],
        "#vec-alloc" => &["element", "allocator", "vector", "destroy"],
        "#vec-sort" => &["element", "vector", "comparator"],
        "#async-fn" | "#async-fn-pinned" => &["protocol", "waker", "function", "cancel", "access"],
        _ => return None,
    })
}

pub(crate) fn normalize_builtin_generator_invocation(expression: &Expr) -> Result<Expr, String> {
    let Expr::List(items) = expression else {
        return Ok(expression.clone());
    };
    if !matches!(items.first(), Some(Expr::Generate)) {
        return Ok(expression.clone());
    }
    let Some(Expr::Symbol(kind)) = items.get(1) else {
        return Ok(expression.clone());
    };
    let Some(keys) = named_builtin_keys(kind) else {
        return Ok(expression.clone());
    };
    let Some(Expr::List(arguments)) = items.get(2) else {
        return Err(format!(
            "#generate {kind} requires a named argument list (: key value : ...)"
        ));
    };
    if items.len() != 3 {
        return Err(format!(
            "#generate {kind} requires exactly one named argument list"
        ));
    }
    let mut values = HashMap::new();
    for argument in arguments {
        let Expr::List(pair) = argument else {
            return Err(format!(
                "#generate {kind} arguments must be (: key value : ...)"
            ));
        };
        let [Expr::Symbol(key), value] = pair.as_slice() else {
            return Err(format!(
                "#generate {kind} arguments must be (: key value : ...)"
            ));
        };
        if !keys.contains(&key.as_str()) {
            return Err(format!("#generate {kind} has no argument '{key}'"));
        }
        if matches!(
            key.as_str(),
            "name" | "task" | "vector" | "alloc-result" | "alloc-error"
        ) {
            if let Expr::Symbol(name) = value {
                if name.starts_with('#') {
                    return Err(format!(
                        "identifier '{name}' is reserved for the language and standard library"
                    ));
                }
                crate::names::require(name, "type")?;
            }
        }
        if values.insert(key.as_str(), value.clone()).is_some() {
            return Err(format!("#generate {kind} repeats argument '{key}'"));
        }
    }
    let mut normalized = vec![Expr::Generate, Expr::Symbol(kind.clone())];
    if matches!(kind.as_str(), "#async-fn" | "#async-fn-pinned") {
        let protocol = values
            .remove("protocol")
            .ok_or_else(|| format!("#generate {kind} is missing argument 'protocol'"))?;
        let name = expect_symbol(Some(&protocol), "async protocol name")?;
        if name.starts_with('#') || name.starts_with('@') || name == "$" {
            return Err("async protocol names must be user-defined identifiers".into());
        }
        let function = values
            .remove("function")
            .ok_or_else(|| format!("#generate {kind} is missing argument 'function'"))?;
        let declaration = expect_list(&function, "async function")?;
        let start = expect_symbol(declaration.get(1), "async function name")?;
        let frame_suffix = if kind == "#async-fn-pinned" {
            "frame"
        } else {
            "task"
        };
        let root = capitalized_type_name(start);
        let storage_name = if frame_suffix == "task" {
            "Task"
        } else {
            "Frame"
        };
        let mut names = [
            format!("{root}::{storage_name}"),
            format!("{root}::Poll"),
            format!("{root}::Poll.Pending"),
            format!("{root}::Poll.Ready"),
            format!("{root}::poll"),
        ]
        .into_iter()
        .map(Expr::Symbol)
        .collect::<Vec<_>>();
        names.push(protocol);
        if let Some(access) = values.remove("access") {
            if kind != "#async-fn-pinned" {
                return Err("async parameter access requires #generate #async-fn-pinned".into());
            }
            let entries = expect_list(&access, "async access parameters")?;
            let mut seen = HashSet::new();
            for entry in entries {
                let pair = expect_list(entry, "async access (parameter accessor-name)")?;
                if pair.len() != 2 {
                    return Err("async access requires (parameter accessor-name) pairs".into());
                }
                let name = expect_symbol(pair.first(), "async access parameter")?;
                let accessor = expect_symbol(pair.get(1), "async access name")?;
                if accessor.starts_with('#') || accessor.starts_with('@') || accessor == "$" {
                    return Err("async access names must be user-defined identifiers".into());
                }
                if !seen.insert(name) {
                    return Err(format!("async access repeats parameter '{name}'"));
                }
            }
            names.push(access);
        }
        normalized.push(Expr::List(names.into()));
        normalized.push(
            values
                .remove("waker")
                .ok_or_else(|| format!("#generate {kind} is missing argument 'waker'"))?,
        );
        normalized.push(function);
        if let Some(cancel) = values.remove("cancel") {
            normalized.push(cancel);
        }
        return Ok(Expr::List(normalized.into()));
    }
    for key in keys {
        normalized.push(
            values
                .remove(key)
                .ok_or_else(|| format!("#generate {kind} is missing argument '{key}'"))?,
        );
    }
    Ok(Expr::List(normalized.into()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn async_type_names_are_capitalized_without_renaming_functions_or_variants() {
        for (generator, storage) in [
            ("#async-fn", "Work::Task"),
            ("#async-fn-pinned", "Work::Frame"),
        ] {
            let source = format!("(#generate {generator} (: protocol WorkAwait : waker #u64 : function (#fn work () #u64 (#return 0u64))))");
            let expression = crate::parse(&source).unwrap().remove(0).expr;
            let normalized = normalize_builtin_generator_invocation(&expression).unwrap();
            let Expr::List(items) = normalized else {
                panic!("expected invocation");
            };
            let Expr::List(names) = &items[2] else {
                panic!("expected generated names");
            };
            let expected = [
                storage,
                "Work::Poll",
                "Work::Poll.Pending",
                "Work::Poll.Ready",
                "Work::poll",
                "WorkAwait",
            ];
            assert_eq!(
                names.as_slice(),
                &expected.map(|name| Expr::Symbol(name.into()))
            );
        }
    }
}
