//! Pinned literal expansion through ordinary, independently checked terms.
//! No primitive string typing rule or unchecked helper declaration is added.
use super::*;

pub(super) const MAX_STRING_BYTES: usize = 4096;
const CHUNK: usize = 8;
const NAT: &str = "$lean:s3:Nat";
const CHAR: &str = "$lean:s4:Char";
const STRING: &str = "$lean:s6:String";
const LIST: &str = "$lean:s4:List";
const NIL: &str = "$lean:s4:Lists3:nil";
const CONS: &str = "$lean:s4:Lists4:cons";
const OF_NAT: &str = "$lean:s4:Chars5:ofNat";
const OF_LIST: &str = "$lean:s6:Strings6:ofList";

fn global(name: &str) -> T {
    term(Term::Global(name.into(), vec![]))
}
fn list_global(name: &str) -> Result<T> {
    Ok(term(Term::Global(name.into(), vec![Level::number(0)?])))
}

/// Source accounting includes the ordinary expansion, even for unused syntax.
/// The conservative node allowance also covers temporary scalar/builder data.
pub(super) fn dimensions(value: &str) -> Result<(usize, usize)> {
    if value.len() > MAX_STRING_BYTES {
        return Err("string literal byte limit exceeded (maximum 4096)".into());
    }
    let count = value.chars().count();
    fn builder_depth(count: usize) -> usize {
        if count <= CHUNK {
            count + 4
        } else {
            let middle = count / 2;
            2 + builder_depth(middle).max(1 + builder_depth(count - middle))
        }
    }
    let depth = if count == 0 {
        3
    } else if count <= CHUNK {
        count + 4
    } else {
        builder_depth(count) + 2
    };
    let node_bytes = std::mem::size_of::<TermNode>() + 2 * std::mem::size_of::<usize>();
    let payload = (count * 6 + 32) * node_bytes + count * 24 + value.len() + 1024;
    Ok((depth, payload))
}

/// Match Lean's String.ofList (List.cons (Char.ofNat scalar) ...) expansion.
/// Larger lists use closed, balanced difference-list lambdas; ordinary beta
/// reduction recovers precisely that constructor sequence without deep syntax.
pub(super) fn expand(value: &str) -> Result<T> {
    dimensions(value)?;
    let chars = value.chars().collect::<Vec<_>>();
    let char_type = global(CHAR);
    let list_type = apps(list_global(LIST)?, &[char_type.clone()]);
    let nil = apps(list_global(NIL)?, &[char_type.clone()]);
    let cons = apps(list_global(CONS)?, &[char_type]);
    let of_nat = global(OF_NAT);
    fn sequence(chars: &[char], mut tail: T, cons: &T, of_nat: &T) -> Result<T> {
        for ch in chars.iter().rev() {
            let value = Natural::parse(&(*ch as u32).to_string())?;
            let scalar = term(Term::NatLiteral {
                family: NAT.into(),
                value,
            });
            let head = apps(of_nat.clone(), &[scalar]);
            tail = apps(cons.clone(), &[head, tail]);
        }
        Ok(tail)
    }
    fn builder(chars: &[char], ty: &T, cons: &T, of_nat: &T) -> Result<T> {
        let tail = term(Term::Var(0));
        let body = if chars.len() <= CHUNK {
            sequence(chars, tail, cons, of_nat)?
        } else {
            let middle = chars.len() / 2;
            let left = builder(&chars[..middle], ty, cons, of_nat)?;
            let right = builder(&chars[middle..], ty, cons, of_nat)?;
            apps(left, &[apps(right, &[tail])])
        };
        Ok(term(Term::Lam(ty.clone(), body)))
    }
    let list = if chars.len() <= CHUNK {
        sequence(&chars, nil, &cons, &of_nat)?
    } else {
        apps(builder(&chars, &list_type, &cons, &of_nat)?, &[nil])
    };
    Ok(apps(global(OF_LIST), &[list]))
}

impl Replay {
    pub(super) fn ensure_string_signature(&mut self) -> Result<()> {
        if self.string_literals {
            return Ok(());
        }
        self.reset_budget()?;
        self.check_natural_signature()?;
        let type_zero = term(Term::Sort(Level::number(1)?));
        let list = list_global(LIST)?;
        let list_at = |index| apps(list.clone(), &[term(Term::Var(index))]);
        let list_char = apps(list.clone(), &[global(CHAR)]);
        let signatures = [
            (CHAR, vec![], type_zero.clone()),
            (STRING, vec![], type_zero.clone()),
            (
                LIST,
                vec![Level::number(0)?],
                term(Term::Pi(type_zero.clone(), type_zero.clone())),
            ),
            (
                NIL,
                vec![Level::number(0)?],
                term(Term::Pi(type_zero.clone(), list_at(0))),
            ),
            (
                CONS,
                vec![Level::number(0)?],
                term(Term::Pi(
                    type_zero,
                    term(Term::Pi(
                        term(Term::Var(0)),
                        term(Term::Pi(list_at(1), list_at(2))),
                    )),
                )),
            ),
            (OF_NAT, vec![], term(Term::Pi(global(NAT), global(CHAR)))),
            (OF_LIST, vec![], term(Term::Pi(list_char, global(STRING)))),
        ];
        for (name, levels, signature) in signatures {
            if !self.is_checked(name)? {
                return Err(format!(
                    "string literals require previously checked helper '{name}'"
                ));
            }
            self.kernel.sort(&[], &signature, 0)?;
            self.kernel
                .check(&[], &term(Term::Global(name.into(), levels)), &signature, 0)
                .map_err(|why| format!("invalid string literal helper '{name}': {why}"))?;
        }
        // Successful declarations are immutable. Cache only this closed
        // contract; declaration bodies still undergo ordinary type checking.
        self.string_literals = true;
        Ok(())
    }
}

#[cfg(test)]
#[path = "export_strings_tests.rs"]
mod tests;
