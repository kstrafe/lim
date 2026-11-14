//! Structural footprints only: this never infers semantic contracts.
use super::*;
use std::collections::{BTreeSet, HashSet};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(super) struct Location {
    pub root: String,
    pub path: Vec<String>,
}
impl Location {
    pub fn root(root: impl Into<String>) -> Self {
        Self {
            root: root.into(),
            path: Vec::new(),
        }
    }
    pub fn child(&self, field: impl Into<String>) -> Self {
        let mut p = self.clone();
        p.path.push(field.into());
        p
    }
    pub fn overlaps(&self, other: &Self) -> bool {
        // Unknown referents can alias other borrowed storage. Exact owned roots
        // remain distinct; distinct parameter roots are handled by the caller.
        if self.root != other.root {
            return false;
        }
        for (a, b) in self.path.iter().zip(&other.path) {
            if a == b {
                continue;
            }
            if a == "*" || b == "*" || a == "^" || b == "^" {
                return true;
            }
            if a.starts_with('[') && b.starts_with('[') {
                let ai = a.trim_matches(['[', ']']).parse::<u128>();
                let bi = b.trim_matches(['[', ']']).parse::<u128>();
                return !matches!((ai,bi),(Ok(x),Ok(y))if x!=y);
            }
            return false;
        }
        true
    }
}

// Forms whose effects are completely accounted for by their operands. Other
// primitives are opaque effect boundaries until their memory behavior is
// explicitly modeled here.
pub(super) fn observational(head: &str) -> bool {
    head.contains('.')
        || matches!(
            head,
            "" | "literal"
                | "if"
                | "if-valid"
                | "match"
                | "unsafe"
                | "borrow"
                | "borrow-mut"
                | "pin-borrow"
                | "pin-borrow-mut"
                | "deref"
                | "get"
                | "index"
                | "index-proven"
                | "clone"
                | "as"
                | "array"
                | "tuple"
                | "deref-set"
                | "struct"
                | "struct-literal"
                | "slice-idx"
                | "slice-mut-idx"
                | "slice-len"
                | "slice-mut-len"
                | "size-of"
                | "align-of"
                | "panic"
                | "unreachable"
                | "forget"
                | "drop"
                | "requires"
                | "ensures"
                | "preserves"
                | "assume"
                | "old"
                | "result"
                | "ptr-read"
                | "word-read"
                | "ptr-offset"
                | "ptr-borrow"
                | "ptr-borrow-mut"
        )
}
#[derive(Clone, Debug, Default)]
pub(super) struct Summary {
    pub reads: BTreeSet<Location>,
    pub writes: BTreeSet<Location>,
    pub returns: BTreeSet<Location>,
    pub pure: bool,
    pub unknown_write: bool,
    pub unknown_read: bool,
}

pub(super) fn all(program: &Program) -> HashMap<String, Summary> {
    let functions = program.contracts.originals.clone();
    let mut output = HashMap::new();
    for name in functions.keys() {
        build(name, &functions, &mut output, &mut HashSet::new(), program);
    }
    output
}
pub(super) fn local_effects(
    body: &[Statement],
    types: &HashMap<String, Type>,
    p: &Program,
    callees: &HashMap<String, Summary>,
) -> Summary {
    let mut env = types
        .keys()
        .map(|name| (name.clone(), Location::root(name)))
        .collect();
    let mut out = Summary::default();
    statements(body, &mut env, types, &mut out, callees, p);
    out
}
fn build(
    name: &str,
    functions: &BTreeMap<String, Function>,
    cache: &mut HashMap<String, Summary>,
    active: &mut HashSet<String>,
    p: &Program,
) -> Summary {
    if let Some(s) = cache.get(name) {
        return s.clone();
    }
    if active.len() >= 128 {
        return Summary {
            unknown_write: true,
            ..Summary::default()
        };
    }
    let Some(f) = functions.get(name) else {
        return Summary {
            unknown_write: true,
            ..Summary::default()
        };
    };
    if !active.insert(name.into()) {
        return Summary {
            unknown_write: true,
            ..Summary::default()
        };
    }
    let mut callees = HashSet::new();
    for s in &f.body {
        calls_statement(s, &mut callees);
    }
    for callee in callees {
        build(&callee, functions, cache, active, p);
    }
    let mut summary = Summary {
        pure: !f.external && !f.unsafe_call,
        unknown_write: f.external || f.unsafe_call,
        ..Summary::default()
    };
    let mut env = f
        .parameters
        .iter()
        .map(|arg| (arg.name.clone(), Location::root(&arg.name)))
        .collect::<HashMap<_, _>>();
    let types = f
        .parameters
        .iter()
        .map(|arg| (arg.name.clone(), arg.ty.clone()))
        .collect::<HashMap<_, _>>();
    statements(&f.body, &mut env, &types, &mut summary, cache, p);
    let parameters = f
        .parameters
        .iter()
        .map(|arg| arg.name.as_str())
        .collect::<HashSet<_>>();
    summary.unknown_read |= summary
        .reads
        .iter()
        .any(|place| place.root.starts_with('?') || place.path.contains(&"^".into()));
    summary.unknown_write |= summary
        .writes
        .iter()
        .any(|place| place.root.starts_with('?') || place.path.contains(&"^".into()));
    summary
        .reads
        .retain(|place| parameters.contains(place.root.as_str()));
    summary
        .writes
        .retain(|place| parameters.contains(place.root.as_str()));
    summary
        .returns
        .retain(|place| parameters.contains(place.root.as_str()));
    if !summary.writes.is_empty() {
        summary.pure = false;
    }
    if summary.unknown_write {
        summary.returns.clear();
    }
    active.remove(name);
    cache.insert(name.into(), summary.clone());
    summary
}
pub(super) fn calls_statement(s: &Statement, out: &mut HashSet<String>) {
    fn visit(e: &Expr, out: &mut HashSet<String>) {
        match e {
            Expr::List(xs) => {
                if let Some(Expr::Function(f)) = xs.first() {
                    out.insert(f.clone());
                }
                for x in xs {
                    visit(x, out)
                }
            }
            Expr::Block(ss) | Expr::Loop(ss) => {
                for s in ss {
                    calls_statement(s, out)
                }
            }
            Expr::Labeled { expression, .. } => visit(expression, out),
            _ => {}
        }
    }
    match s {
        Statement::Let { value, .. }
        | Statement::Assign { value, .. }
        | Statement::FieldAssign { value, .. }
        | Statement::TupleAssign { value, .. }
        | Statement::EnumPayloadAssign { value, .. }
        | Statement::Destructure { value, .. }
        | Statement::Return(Some(value))
        | Statement::Expr(value)
        | Statement::BreakValue(value)
        | Statement::BreakToValue { value, .. } => visit(value, out),
        Statement::ArrayAssign { index, value, .. } => {
            visit(index, out);
            visit(value, out)
        }
        Statement::While { condition, body } => {
            visit(condition, out);
            for s in body {
                calls_statement(s, out)
            }
        }
        Statement::Loop { body } => {
            for s in body {
                calls_statement(s, out)
            }
        }
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            calls_statement(init, out);
            visit(condition, out);
            calls_statement(step, out);
            for s in body {
                calls_statement(s, out)
            }
        }
        Statement::LetElse {
            value, else_body, ..
        } => {
            visit(value, out);
            for s in else_body {
                calls_statement(s, out)
            }
        }
        Statement::Labeled { statement, .. } => calls_statement(statement, out),
        _ => {}
    }
}
fn is_reference(ty: &Type, p: &Program) -> bool {
    let mut ty = ty.clone();
    let mut seen = HashSet::new();
    loop {
        match ty {
            Type::Reference { .. }
            | Type::PinnedReference { .. }
            | Type::Slice(_)
            | Type::MutableSlice(_) => return true,
            Type::Named(ref name) if seen.insert(name.clone()) => {
                if let Some(next) = p.items.iter().find_map(|i| match i {
                    Item::TypeAlias {
                        name: n, target, ..
                    } if n == name => Some(target.clone()),
                    _ => None,
                }) {
                    ty = next
                } else {
                    return false;
                }
            }
            _ => return false,
        }
    }
}
fn loaded_reference(e: &Expr, types: &HashMap<String, Type>, p: &Program) -> bool {
    matches!(
        head(e),
        "deref" | "get" | "index" | "index-proven" | "slice-idx" | "slice-mut-idx"
    ) && super::lowering::observation_type(e, types, p).is_some_and(|ty| is_reference(&ty, p))
}
fn place(
    e: &Expr,
    env: &HashMap<String, Location>,
    types: &HashMap<String, Type>,
    p: &Program,
) -> Option<Location> {
    if let Expr::Symbol(s) = e {
        return env.get(s).cloned();
    }
    let xs = parts(e);
    match head(e) {
        "borrow" | "borrow-mut" | "clone" | "pin-borrow" | "pin-borrow-mut" => {
            place(xs.get(1)?, env, types, p)
        }
        "deref" => {
            let mut root = place(xs.get(1)?, env, types, p)?;
            if loaded_reference(&xs[1], types, p) {
                root = root.child("^")
            }
            Some(root)
        }
        "get" | "index" | "index-proven" | "slice-idx" | "slice-mut-idx" => {
            let mut root = place(xs.get(1)?, env, types, p)?;
            if loaded_reference(&xs[1], types, p) {
                root = root.child("^");
            }
            let segment = if head(e) == "get" {
                match xs.get(2)? {
                    Expr::Symbol(s) => format!(".{s}"),
                    Expr::Integer(i) => format!(".{i}"),
                    _ => "*".into(),
                }
            } else {
                match xs.get(2)? {
                    Expr::Integer(i) => format!("[{i}]"),
                    Expr::UnsignedInteger(i) => format!("[{i}]"),
                    Expr::Symbol(s) => format!("[@{s}]"),
                    _ => "*".into(),
                }
            };
            Some(root.child(segment))
        }
        _ => None,
    }
}
fn mapped(
    relative: &Location,
    callee: &Function,
    args: &[Expr],
    env: &HashMap<String, Location>,
    types: &HashMap<String, Type>,
    p: &Program,
) -> Option<Location> {
    let i = callee
        .parameters
        .iter()
        .position(|p| p.name == relative.root)?;
    let arg = args.get(i)?;
    let mut root = place(arg, env, types, p)?;
    if loaded_reference(arg, types, p) && is_reference(&callee.parameters[i].ty, p) {
        root = root.child("^")
    }
    root.path.extend(relative.path.iter().cloned());
    Some(root)
}
fn statements(
    body: &[Statement],
    env: &mut HashMap<String, Location>,
    types: &HashMap<String, Type>,
    out: &mut Summary,
    callees: &HashMap<String, Summary>,
    p: &Program,
) {
    let mut types = types.clone();
    for s in body {
        match s {
            Statement::Let {
                name, ty, value, ..
            } => {
                expression(value, env, &types, out, callees, p);
                let alias = is_reference(ty, p);
                if alias {
                    if let Some(target) = returned_place(value, env, &types, callees, p) {
                        env.insert(name.clone(), target);
                    } else {
                        env.insert(name.clone(), Location::root(format!("?{name}")));
                    }
                } else {
                    env.insert(name.clone(), Location::root(format!("local:{name}")));
                }
                types.insert(name.clone(), ty.clone());
            }
            Statement::Assign { name, value } => {
                expression(value, env, &types, out, callees, p);
                if !env.contains_key(name) || types.get(name).is_some_and(|ty| is_reference(ty, p))
                {
                    out.unknown_write = true;
                    out.pure = false;
                    env.insert(name.clone(), Location::root(format!("?{name}")));
                }
            }
            Statement::FieldAssign { name, field, value } => {
                expression(value, env, &types, out, callees, p);
                if let Some(loc) = env.get(name) {
                    out.writes.insert(loc.child(format!(".{field}")));
                } else {
                    out.unknown_write = true;
                    out.pure = false;
                }
            }
            Statement::ArrayAssign { name, index, value } => {
                expression(index, env, &types, out, callees, p);
                expression(value, env, &types, out, callees, p);
                if let Some(loc) = env.get(name) {
                    out.writes.insert(loc.child(match index {
                        Expr::Integer(i) => format!("[{i}]"),
                        _ => "*".into(),
                    }));
                } else {
                    out.unknown_write = true;
                    out.pure = false;
                }
            }
            Statement::TupleAssign { name, index, value } => {
                expression(value, env, &types, out, callees, p);
                if let Some(loc) = env.get(name) {
                    out.writes.insert(loc.child(format!(".{index}")));
                } else {
                    out.unknown_write = true;
                    out.pure = false;
                }
            }
            Statement::EnumPayloadAssign { name, value, .. } => {
                expression(value, env, &types, out, callees, p);
                if let Some(loc) = env.get(name) {
                    out.writes.insert(loc.clone());
                } else {
                    out.unknown_write = true;
                    out.pure = false;
                }
            }
            Statement::Return(Some(value)) => {
                expression(value, env, &types, out, callees, p);
                if let Some(loc) = returned_place(value, env, &types, callees, p) {
                    out.returns.insert(loc);
                }
            }
            Statement::Expr(e) => expression(e, env, &types, out, callees, p),
            Statement::While { condition, body } => {
                expression(condition, env, &types, out, callees, p);
                statements(body, &mut env.clone(), &types, out, callees, p)
            }
            Statement::Loop { body } => statements(body, &mut env.clone(), &types, out, callees, p),
            Statement::For {
                init,
                condition,
                step,
                body,
            } => {
                statements(std::slice::from_ref(init), env, &types, out, callees, p);
                expression(condition, env, &types, out, callees, p);
                statements(body, &mut env.clone(), &types, out, callees, p);
                statements(std::slice::from_ref(step), env, &types, out, callees, p)
            }
            Statement::Labeled { statement, .. } => statements(
                std::slice::from_ref(statement),
                env,
                &types,
                out,
                callees,
                p,
            ),
            Statement::LetElse {
                value, else_body, ..
            } => {
                expression(value, env, &types, out, callees, p);
                statements(else_body, &mut env.clone(), &types, out, callees, p)
            }
            Statement::Destructure { value, .. }
            | Statement::BreakValue(value)
            | Statement::BreakToValue { value, .. } => {
                expression(value, env, &types, out, callees, p)
            }
            _ => {}
        }
    }
}
fn returned_place(
    e: &Expr,
    env: &HashMap<String, Location>,
    types: &HashMap<String, Type>,
    summaries: &HashMap<String, Summary>,
    p: &Program,
) -> Option<Location> {
    if let Some(Expr::Function(f)) = parts(e).first() {
        let callee = p.contracts.originals.get(f)?;
        let summary = summaries.get(f)?;
        if summary.returns.len() != 1 {
            return None;
        }
        return mapped(
            summary.returns.iter().next()?,
            callee,
            &parts(e)[1..],
            env,
            types,
            p,
        );
    }
    let mut root = place(e, env, types, p)?;
    if loaded_reference(e, types, p) {
        root = root.child("^")
    }
    Some(root)
}
fn expression(
    e: &Expr,
    env: &HashMap<String, Location>,
    types: &HashMap<String, Type>,
    out: &mut Summary,
    summaries: &HashMap<String, Summary>,
    p: &Program,
) {
    let xs = parts(e);
    let h = head(e);
    if matches!(h, "requires" | "ensures" | "preserves" | "assume") {
        return;
    }
    if h == "clone" {
        if let Some(Type::Named(owner)) = xs
            .get(1)
            .and_then(|e| super::lowering::observation_type(e, types, p))
            .and_then(|t| super::lowering::base_type(&t, p))
        {
            if p.contracts
                .originals
                .contains_key(&format!("{owner}::clone"))
            {
                out.pure = false;
                out.unknown_write = true;
            }
        }
    }
    if let Some(Expr::Function(f)) = xs.first() {
        if let (Some(s), Some(callee)) = (summaries.get(f), p.contracts.originals.get(f)) {
            out.pure &= s.pure;
            out.unknown_write |= s.unknown_write;
            out.unknown_read |= s.unknown_read;
            for r in &s.reads {
                if let Some(r) = mapped(r, callee, &xs[1..], env, types, p) {
                    out.reads.insert(r);
                } else {
                    out.unknown_read = true;
                    for a in &xs[1..] {
                        if let Some(r) = place(a, env, types, p) {
                            out.reads.insert(r);
                        }
                    }
                }
            }
            for w in &s.writes {
                if let Some(w) = mapped(w, callee, &xs[1..], env, types, p) {
                    out.writes.insert(w);
                } else {
                    out.unknown_write = true;
                }
            }
            // Passing an aggregate/reference is not reading all of its contents.
            for a in &xs[1..] {
                if place(a, env, types, p).is_none() {
                    expression(a, env, types, out, summaries, p)
                }
            }
        } else {
            out.pure = false;
            out.unknown_write = true;
        }
        return;
    }
    if !h.is_empty()
        && !observational(h)
        && !p.items.iter().any(|item| {
            matches!(item,Item::Enum{variants,..} if variants.iter().any(|v| v.name==h))
                || matches!(item,Item::Struct{name,..}if name==h)
        })
    {
        out.pure = false;
        out.unknown_write = true;
    }
    if matches!(
        h,
        "asm"
            | "ptr-write"
            | "atomic-store"
            | "atomic-exchange"
            | "atomic-fetch-add"
            | "atomic-compare-exchange"
            | "atomic-compare-exchange-weak"
    ) {
        out.pure = false;
        out.unknown_write = true;
    }
    if h.starts_with("ptr-") || h.starts_with("word-") {
        out.unknown_read = true;
    }
    if h.starts_with("atomic-") {
        out.pure = false;
        out.unknown_write = true;
    }
    if matches!(h, "deref-set" | "set-field" | "set-index" | "set-payload") {
        out.pure = false;
        if let Some(loc) = xs.get(1).and_then(|e| place(e, env, types, p)) {
            let loc = if h == "set-field" {
                xs.get(2).map_or(loc.clone(), |e| {
                    loc.child(format!(
                        ".{}",
                        match e {
                            Expr::Symbol(s) => s.as_str(),
                            _ => "*",
                        }
                    ))
                })
            } else if h == "deref-set" && loaded_reference(&xs[1], types, p) {
                loc.child("^")
            } else {
                loc
            };
            out.writes.insert(loc);
        } else {
            out.unknown_write = true
        }
    }
    if matches!(
        h,
        "deref"
            | "get"
            | "index"
            | "index-proven"
            | "slice-idx"
            | "slice-mut-idx"
            | "slice-len"
            | "slice-mut-len"
    ) {
        if let Some(loc) =
            place(e, env, types, p).or_else(|| xs.get(1).and_then(|e| place(e, env, types, p)))
        {
            out.reads.insert(loc);
        } else {
            out.unknown_read = true;
        }
        if let Some(base) = xs.get(1) {
            if place(base, env, types, p).is_none() {
                expression(base, env, types, out, summaries, p)
            }
        }
        if let Some(index) = xs.get(2) {
            if !matches!(index, Expr::Symbol(_))
                || h.contains("idx")
                || crate::is_array_index_head(h)
            {
                expression(index, env, types, out, summaries, p)
            }
        }
        return;
    }
    match e {
        Expr::Symbol(name) => {
            if let Some(loc) = env.get(name) {
                out.reads.insert(loc.clone());
            } else if p
                .items
                .iter()
                .any(|item| matches!(item,Item::Let{name:n,..}|Item::Static{name:n,..}if n==name))
            {
                // Immutable compile-time constants are allowed, atomic/global
                // storage and hidden dependencies are deliberately excluded.
                if p.items
                    .iter()
                    .any(|item| matches!(item,Item::Static{name:n,..}if n==name))
                {
                    out.pure = false;
                }
            }
        }
        Expr::Block(ss) | Expr::Loop(ss) => {
            statements(ss, &mut env.clone(), types, out, summaries, p)
        }
        Expr::Labeled { expression: e, .. } => expression(e, env, types, out, summaries, p),
        Expr::List(xs) => {
            for x in xs.iter().skip(1) {
                expression(x, env, types, out, summaries, p)
            }
        }
        _ => {}
    }
}
