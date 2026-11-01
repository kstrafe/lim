//! Explicit theorem declarations lower to the kernel's closed Pi/lambda terms.
//! This is a source transformation; the kernel independently checks its output.
use crate::{Expr, Item};

fn list(expr: &Expr) -> Result<&[Expr], String> {
    if let Expr::List(parts) = expr {
        Ok(parts)
    } else {
        Err("theorem clauses must be lists".into())
    }
}
fn symbol(expr: &Expr) -> Result<&str, String> {
    if let Expr::Symbol(name) = expr {
        Ok(name)
    } else {
        Err("theorem names and parameter names must be identifiers".into())
    }
}
fn clause<'a>(expr: &'a Expr, keyword: &str) -> Result<&'a [Expr], String> {
    let parts = list(expr)?;
    if parts.first().and_then(|p| symbol(p).ok()) != Some(keyword) {
        return Err(format!("expected ({keyword} ...) clause"));
    }
    Ok(&parts[1..])
}
fn form(head: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::List(
        std::iter::once(Expr::Symbol(head.into()))
            .chain(args)
            .collect(),
    )
}

pub(crate) fn parse(items: &[Expr]) -> Result<Item, String> {
    let head = symbol(items.first().ok_or("missing theorem declaration")?)?;
    let name = symbol(items.get(1).ok_or("missing theorem name")?)?;
    crate::names::require(name, "value")?;
    let proposition = match head {
        "theorem" if items.len() == 3 => {
            if matches!(&items[2], Expr::List(parts) if matches!(parts.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(),"#proof-theorem"|"#proof-definition"|"proof-definition"|"#proof-opaque"|"proof-opaque"|"#proof-inductive"|"proof-inductive")))
            {
                return Err("invalid theorem proposition".into());
            }
            items[2].clone()
        }
        "theorem" => {
            if items.len() != 6 {
                return Err(
                    "#theorem requires a name, #universes, #parameters, #statement, and #proof"
                        .into(),
                );
            }
            let universes = clause(&items[2], "#universes")?;
            let parameters = clause(&items[3], "#parameters")?;
            let statement = clause(&items[4], "#statement")?;
            let evidence = clause(&items[5], "#proof")?;
            if statement.len() != 1 || evidence.len() != 1 {
                return Err("#statement and #proof each require exactly one term".into());
            }
            let mut bindings = Vec::new();
            for parameter in parameters {
                let parts = clause(parameter, "#parameter")?;
                if parts.len() != 2 {
                    return Err("#parameter requires an identifier and an explicit type".into());
                }
                symbol(&parts[0])?;
                bindings.push(Expr::List(parts.to_vec()));
            }
            let (ty, value) = if bindings.is_empty() {
                (statement[0].clone(), evidence[0].clone())
            } else {
                let parameters = Expr::List(bindings);
                (
                    form("#pt-pi", [parameters.clone(), statement[0].clone()]),
                    form("#pt-lambda", [parameters, evidence[0].clone()]),
                )
            };
            form(
                "#proof-theorem",
                [Expr::List(universes.to_vec()), ty, value],
            )
        }
        "math-definition" | "math-opaque" => {
            if items.len() != 5 {
                return Err(format!(
                    "#{head} requires a name, universe list, type, and value"
                ));
            }
            let internal = if head == "math-opaque" {
                "#proof-opaque"
            } else {
                "#proof-definition"
            };
            form(internal, items[2..].iter().cloned())
        }
        "math-inductive" => {
            let mut at = 4;
            for keyword in ["#mutual", "#indices"] {
                if matches!(items.get(at), Some(Expr::List(parts)) if matches!(parts.first(), Some(Expr::Symbol(head)) if head == keyword))
                {
                    at += 1;
                }
            }
            if items.len() != at + 2 {
                return Err("#math-inductive requires a name, universe list, parameters, optional #mutual then #indices clauses, sort, and constructors".into());
            }
            form("#proof-inductive", items[2..].iter().cloned())
        }
        _ => return Err("unknown theorem declaration".into()),
    };
    Ok(Item::Proof {
        name: name.into(),
        proposition,
    })
}
