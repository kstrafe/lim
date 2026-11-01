//! Source adapter for the independently checked dependent-type kernel.
//! Program facts are admitted here only after the ordinary program verifier
//! succeeds. They remain opaque propositions, never equations about Nat.
mod core;
use crate::{Expr, Item};
use core::{apps, term, Kernel, Level, Term, T};
use std::collections::{BTreeSet, HashSet};
type Result<T> = std::result::Result<T, String>;

pub(super) fn is_declaration(expr: &Expr) -> bool {
    matches!(expr,Expr::List(parts) if matches!(parts.first(),Some(Expr::Symbol(head)) if matches!(head.as_str(),"#proof-definition"|"#proof-theorem"|"#proof-inductive")))
}
enum Body {
    Definition {
        ty: T,
        value: T,
        theorem: bool,
    },
    Inductive {
        parameters: Vec<T>,
        sort: Level,
        constructors: Vec<(String, Vec<T>)>,
    },
}
struct Pending {
    name: String,
    universes: Vec<String>,
    dependencies: BTreeSet<String>,
    body: Body,
}

pub(super) fn check(
    program: &crate::Program,
    facts: &HashSet<String>,
) -> std::result::Result<(), (String, String)> {
    let mut kernel = Kernel::new();
    for fact in facts {
        kernel.certified_program_fact(fact);
    }
    let mut pending = Vec::new();
    for item in &program.items {
        let Item::Proof { name, proposition } = item else {
            continue;
        };
        if !is_declaration(proposition) {
            continue;
        }
        if pending.len() >= 4096 {
            return Err((name.clone(), "kernel declaration limit exceeded".into()));
        }
        let declaration =
            parse_declaration(name, proposition, facts).map_err(|why| (name.clone(), why))?;
        pending.push(declaration);
    }
    let declared = pending
        .iter()
        .map(|p| p.name.clone())
        .collect::<HashSet<_>>();
    for p in &pending {
        for dependency in &p.dependencies {
            if !declared.contains(dependency) && !kernel.contains(dependency) {
                return Err((
                    p.name.clone(),
                    format!("unknown kernel declaration '{dependency}'"),
                ));
            }
        }
    }
    while !pending.is_empty() {
        let Some(index) = pending
            .iter()
            .position(|p| p.dependencies.iter().all(|d| kernel.contains(d)))
        else {
            return Err((
                pending[0].name.clone(),
                "cyclic kernel declaration dependencies are forbidden; use structural induction"
                    .into(),
            ));
        };
        let p = pending.remove(index);
        kernel.reset_budget();
        let result = match p.body {
            Body::Definition { ty, value, theorem } => {
                kernel.definition(&p.name, p.universes, ty, value, theorem)
            }
            Body::Inductive {
                parameters,
                sort,
                constructors,
            } => kernel.inductive(&p.name, p.universes, parameters, sort, constructors),
        };
        result.map_err(|why| (p.name, why))?;
    }
    Ok(())
}

fn parse_declaration(name: &str, expr: &Expr, facts: &HashSet<String>) -> Result<Pending> {
    let (head, args) = form(expr)?;
    let expected = if head == "#proof-inductive" { 4 } else { 3 };
    arity(head, args, expected)?;
    let mut universes = vec![];
    for u in list(&args[0])? {
        let u = symbol(u)?;
        binder(u)?;
        if universes.iter().any(|a| a == u) {
            return Err("duplicate universe parameter".into());
        }
        universes.push(u.to_owned());
    }
    if universes.len() > 32 {
        return Err("kernel universe parameter limit exceeded".into());
    }
    let mut parser = Parser {
        universes: universes.iter().cloned().collect(),
        locals: vec![],
        dependencies: BTreeSet::new(),
        facts,
        nodes: 0,
    };
    let body = if head == "#proof-inductive" {
        let parameters = parser.bindings(&args[1], 0)?;
        let sort = parser.expression(&args[2], 0)?;
        let Term::Sort(sort) = sort.as_ref() else {
            return Err(
                "an inductive declaration requires an explicit #pt-type or #pt-prop sort".into(),
            );
        };
        let mut constructors = vec![];
        let mut labels = HashSet::new();
        for constructor in list(&args[3])? {
            let parts = list(constructor)?;
            if parts.len() != 2 {
                return Err("constructors have the form (name ((field Type)...))".into());
            }
            let label = symbol(&parts[0])?;
            binder(label)?;
            if !labels.insert(label.to_owned()) {
                return Err("duplicate inductive constructor".into());
            }
            let saved = parser.locals.clone();
            let fields = parser.bindings(&parts[1], 0)?;
            parser.locals = saved;
            constructors.push((label.into(), fields));
        }
        if constructors.len() > 64 {
            return Err("kernel constructor limit exceeded".into());
        }
        Body::Inductive {
            parameters,
            sort: sort.clone(),
            constructors,
        }
    } else {
        let ty = parser.expression(&args[1], 0)?;
        let value = parser.expression(&args[2], 0)?;
        Body::Definition {
            ty,
            value,
            theorem: head == "#proof-theorem",
        }
    };
    Ok(Pending {
        name: name.into(),
        universes,
        dependencies: parser.dependencies,
        body,
    })
}

struct Parser<'a> {
    universes: HashSet<String>,
    locals: Vec<String>,
    dependencies: BTreeSet<String>,
    facts: &'a HashSet<String>,
    nodes: usize,
}
impl Parser<'_> {
    fn tick(&mut self, depth: usize) -> Result<()> {
        self.nodes += 1;
        if self.nodes > 50_000 || depth > 64 {
            Err("kernel syntax resource limit exceeded".into())
        } else {
            Ok(())
        }
    }
    fn level(&mut self, expr: &Expr, depth: usize) -> Result<Level> {
        self.tick(depth)?;
        match expr {
            Expr::Integer(n) if *n >= 0 => {
                Level::number(u32::try_from(*n).map_err(|_| "universe level limit exceeded")?)
            }
            Expr::UnsignedInteger(n) => {
                Level::number(u32::try_from(*n).map_err(|_| "universe level limit exceeded")?)
            }
            Expr::Symbol(name) if self.universes.contains(name) => {
                Ok(Level::variable(name.clone()))
            }
            Expr::List(_) => {
                let (head, args) = form(expr)?;
                match head {
                "#pt-level-succ"=>{arity(head,args,1)?;self.level(&args[0],depth+1)?.successor()},
                "#pt-level-max"=>{if args.is_empty(){return Err("#pt-level-max requires explicit operands".into());}let mut level=Level::number(0)?;for arg in args {level=level.maximum(&self.level(arg,depth+1)?);}Ok(level)},
                _=>Err("universe levels require nonnegative integers or declared universe parameters".into())}
            }
            _ => Err(
                "universe levels require nonnegative integers or declared universe parameters"
                    .into(),
            ),
        }
    }
    fn bindings(&mut self, expr: &Expr, depth: usize) -> Result<Vec<T>> {
        let entries = list(expr)?;
        if entries.len() > 64 {
            return Err("kernel binder limit exceeded".into());
        }
        let mut domains = vec![];
        for entry in entries {
            let pair = list(entry)?;
            if pair.len() != 2 {
                return Err("kernel bindings require explicit (name Type) pairs".into());
            }
            let name = symbol(&pair[0])?;
            binder(name)?;
            if self.locals.iter().any(|n| n == name) || self.universes.contains(name) {
                return Err(format!(
                    "kernel binding '{name}' shadows an existing binding"
                ));
            }
            let ty = self.expression(&pair[1], depth + 1)?;
            self.locals.push(name.into());
            domains.push(ty);
        }
        Ok(domains)
    }
    fn levels(&mut self, expr: &Expr, depth: usize) -> Result<Vec<Level>> {
        if list(expr)?.len() > 32 {
            return Err("kernel universe argument limit exceeded".into());
        }
        list(expr)?
            .iter()
            .map(|e| self.level(e, depth + 1))
            .collect()
    }
    fn terms(&mut self, expr: &Expr, depth: usize) -> Result<Vec<T>> {
        if list(expr)?.len() > 64 {
            return Err("kernel argument limit exceeded".into());
        }
        list(expr)?
            .iter()
            .map(|e| self.expression(e, depth + 1))
            .collect()
    }
    fn global(&mut self, expr: &Expr) -> Result<String> {
        let name = symbol(expr)?;
        if name.starts_with('$') {
            return Err("reserved kernel identifiers cannot be referenced directly".into());
        }
        if !matches!(name, "#pt-nat" | "#pt-false") {
            self.dependencies.insert(name.into());
        }
        Ok(name.into())
    }
    fn expression(&mut self, expr: &Expr, depth: usize) -> Result<T> {
        self.tick(depth)?;
        if let Expr::Symbol(name) = expr {
            return Ok(term(match name.as_str() {
                "#pt-prop" => Term::Sort(Level::number(0)?),
                "#pt-nat" | "#pt-false" => Term::Global(name.clone(), vec![]),
                "#pt-self" => Term::SelfType,
                "#pt-zero" => return Ok(nat_constructor("zero", vec![])),
                _ => Term::Var(
                    self.locals
                        .iter()
                        .rev()
                        .position(|n| n == name)
                        .ok_or_else(|| {
                            format!("unbound proof-term name '{name}'; globals require #pt-use")
                        })?,
                ),
            }));
        }
        let (head, args) = form(expr)?;
        match head {
            "#pt-type"=>{arity(head,args,1)?;Ok(term(Term::Sort(self.level(&args[0],depth+1)?.successor()?)))},
            "#pt-use"=>{arity(head,args,2)?;let name=self.global(&args[0])?;let levels=self.levels(&args[1],depth+1)?;Ok(term(Term::Global(name,levels)))},
            "#pt-program"|"#pt-certificate"=>{arity(head,args,1)?;let name=symbol(&args[0])?;if !self.facts.contains(name){return Err(format!("'{name}' is not a checked procedural program proof"));}Ok(term(Term::Global(format!("{}:{name}",if head=="#pt-program"{"$program"}else{"$certificate"}),vec![])))},
            "#pt-pi"|"#pt-lambda"|"#pt-sigma"=>{
                arity(head,args,2)?;let previous=self.locals.clone();let domains=self.bindings(&args[0],depth+1)?;
                if domains.is_empty()||head=="#pt-sigma"&&domains.len()!=1{return Err("Pi/lambda require binders; Sigma requires exactly one binder".into());}
                let mut body=self.expression(&args[1],depth+1)?;self.locals=previous;
                for domain in domains.into_iter().rev(){body=term(match head{"#pt-pi"=>Term::Pi(domain,body),"#pt-lambda"=>Term::Lam(domain,body),_=>Term::Sigma(domain,body)});}Ok(body)
            }
            "#pt-app"=>{if args.len()>65{return Err("kernel application argument limit exceeded".into());}if args.len()<2{return Err("#pt-app requires a function and explicit arguments".into());}let f=self.expression(&args[0],depth+1)?;let args=args[1..].iter().map(|a|self.expression(a,depth+1)).collect::<Result<Vec<_>>>()?;Ok(apps(f,&args))},
            "#pt-eq"=>{arity(head,args,3)?;Ok(term(Term::Eq(self.expression(&args[0],depth+1)?,self.expression(&args[1],depth+1)?,self.expression(&args[2],depth+1)?)))},
            "#pt-refl"=>{arity(head,args,2)?;Ok(term(Term::Refl(self.expression(&args[0],depth+1)?,self.expression(&args[1],depth+1)?)))},
            "#pt-eq-elim"=>{arity(head,args,6)?;Ok(term(Term::EqElim{ty:self.expression(&args[0],depth+1)?,left:self.expression(&args[1],depth+1)?,motive:self.expression(&args[2],depth+1)?,base:self.expression(&args[3],depth+1)?,right:self.expression(&args[4],depth+1)?,proof:self.expression(&args[5],depth+1)?}))},
            "#pt-pair"=>{arity(head,args,3)?;Ok(term(Term::Pair(self.expression(&args[0],depth+1)?,self.expression(&args[1],depth+1)?,self.expression(&args[2],depth+1)?)))},
            "#pt-first"|"#pt-second"=>{arity(head,args,1)?;let value=self.expression(&args[0],depth+1)?;Ok(term(if head=="#pt-first"{Term::First(value)}else{Term::Second(value)}))},
            "#pt-succ"=>{arity(head,args,1)?;Ok(nat_constructor("succ",vec![self.expression(&args[0],depth+1)?]))},
            "#pt-numeral"=>{
                arity(head,args,1)?;let n=natural(&args[0])?;if n>128{return Err("kernel numeral abbreviation limit is 128; Nat itself is unbounded".into());}
                let mut value=nat_constructor("zero",vec![]);for _ in 0..n {value=nat_constructor("succ",vec![value]);}Ok(value)
            }
            "#pt-nat-induct"=>{arity(head,args,4)?;Ok(term(Term::Induct{family:"#pt-nat".into(),levels:vec![],parameters:vec![],motive:self.expression(&args[0],depth+1)?,branches:vec![self.expression(&args[1],depth+1)?,self.expression(&args[2],depth+1)?],subject:self.expression(&args[3],depth+1)?}))},
            "#pt-construct"=>{arity(head,args,5)?;let family=self.global(&args[0])?;Ok(term(Term::Ctor{family,levels:self.levels(&args[1],depth+1)?,parameters:self.terms(&args[2],depth+1)?,constructor:symbol(&args[3])?.into(),fields:self.terms(&args[4],depth+1)?}))},
            "#pt-induct"=>{arity(head,args,6)?;let family=self.global(&args[0])?;Ok(term(Term::Induct{family,levels:self.levels(&args[1],depth+1)?,parameters:self.terms(&args[2],depth+1)?,motive:self.expression(&args[3],depth+1)?,branches:self.terms(&args[4],depth+1)?,subject:self.expression(&args[5],depth+1)?}))},
            _=>Err(format!("unknown proof-term form '{head}'; no axioms, holes, or unchecked tactics are accepted")),
        }
    }
}
fn nat_constructor(constructor: &str, fields: Vec<T>) -> T {
    term(Term::Ctor {
        family: "#pt-nat".into(),
        levels: vec![],
        parameters: vec![],
        constructor: constructor.into(),
        fields,
    })
}
fn natural(expr: &Expr) -> Result<usize> {
    match expr {
        Expr::Integer(n) if *n >= 0 => {
            usize::try_from(*n).map_err(|_| "integer is too large".into())
        }
        Expr::UnsignedInteger(n) => usize::try_from(*n).map_err(|_| "integer is too large".into()),
        _ => Err("kernel numeral requires an untyped nonnegative integer".into()),
    }
}
fn binder(name: &str) -> Result<()> {
    if name.starts_with('#')
        || name.contains([':', '/', '.', '@'])
        || !name
            .chars()
            .next()
            .is_some_and(|c| c.is_alphabetic() || c == '_')
    {
        Err("kernel binders must be ordinary unqualified identifiers".into())
    } else {
        Ok(())
    }
}
fn form(expr: &Expr) -> Result<(&str, &[Expr])> {
    let parts = list(expr)?;
    let head = symbol(
        parts
            .first()
            .ok_or("an explicit proof-term form is required")?,
    )?;
    Ok((head, &parts[1..]))
}
fn list(expr: &Expr) -> Result<&[Expr]> {
    if let Expr::List(parts) = expr {
        Ok(parts)
    } else {
        Err("proof-term syntax requires a list".into())
    }
}
fn symbol(expr: &Expr) -> Result<&str> {
    if let Expr::Symbol(name) = expr {
        Ok(name)
    } else {
        Err("proof-term syntax requires an identifier".into())
    }
}
fn arity(head: &str, args: &[Expr], count: usize) -> Result<()> {
    if args.len() == count {
        Ok(())
    } else {
        Err(format!("{head} requires {count} explicit operand(s)"))
    }
}
