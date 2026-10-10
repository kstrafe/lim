//! Built-in generator registration and argument validation.
use crate::*;

pub(crate) fn named_builtin_keys(kind: &str) -> Option<&'static [&'static str]> {
    Some(match kind {
        "optional" => &["type", "name"],
        "result" => &["ok", "error", "name"],
        "thread-spawn" => &["task", "worker"],
        "vec" => &["element", "allocator", "name"],
        "vec-alloc" => &[
            "element",
            "allocator",
            "vector",
            "alloc-result",
            "alloc-error",
            "alloc",
            "grow",
            "dealloc",
            "destroy",
        ],
        "vec-sort" => &["element", "vector", "comparator"],
        "async-fn" | "async-fn-pinned" => &["protocol", "waker", "function", "cancel"],
        _ => return None,
    })
}

pub(crate) fn normalize_builtin_generator_invocation(expression: &Expr) -> Result<Expr, String> {
    let Expr::List(items) = expression else {
        return Ok(expression.clone());
    };
    if !matches!(items.first(), Some(Expr::At)) {
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
            "@{kind} requires a named argument list (: key value : ...)"
        ));
    };
    if items.len() != 3 {
        return Err(format!("@{kind} requires exactly one named argument list"));
    }
    let mut values = HashMap::new();
    for argument in arguments {
        let Expr::List(pair) = argument else {
            return Err(format!("@{kind} arguments must be (: key value : ...)"));
        };
        let [Expr::Symbol(key), value] = pair.as_slice() else {
            return Err(format!("@{kind} arguments must be (: key value : ...)"));
        };
        if !keys.contains(&key.as_str()) {
            return Err(format!("@{kind} has no argument '{key}'"));
        }
        if values.insert(key.as_str(), value.clone()).is_some() {
            return Err(format!("@{kind} repeats argument '{key}'"));
        }
    }
    let mut normalized = vec![Expr::At, Expr::Symbol(kind.clone())];
    if matches!(kind.as_str(), "async-fn" | "async-fn-pinned") {
        let protocol = values
            .remove("protocol")
            .ok_or_else(|| format!("@{kind} is missing argument 'protocol'"))?;
        let name = expect_symbol(Some(&protocol), "async protocol name")?;
        if name.starts_with('#') || name.starts_with('@') || name == "$" {
            return Err("async protocol names must be user-defined identifiers".into());
        }
        let function = values
            .remove("function")
            .ok_or_else(|| format!("@{kind} is missing argument 'function'"))?;
        let declaration = expect_list(&function, "async function")?;
        let start = expect_symbol(declaration.get(1), "async function name")?;
        let frame_suffix = if kind == "async-fn-pinned" {
            "frame"
        } else {
            "task"
        };
        let mut names = [frame_suffix, "poll-result", "pending", "ready", "poll"]
            .iter()
            .map(|suffix| Expr::Symbol(format!("{start}-{suffix}")))
            .collect::<Vec<_>>();
        names.push(protocol);
        normalized.push(Expr::List(names));
        normalized.push(
            values
                .remove("waker")
                .ok_or_else(|| format!("@{kind} is missing argument 'waker'"))?,
        );
        normalized.push(function);
        if let Some(cancel) = values.remove("cancel") {
            normalized.push(cancel);
        }
        return Ok(Expr::List(normalized));
    }
    for key in keys {
        normalized.push(
            values
                .remove(key)
                .ok_or_else(|| format!("@{kind} is missing argument '{key}'"))?,
        );
    }
    Ok(Expr::List(normalized))
}
