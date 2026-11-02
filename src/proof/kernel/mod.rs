//! Source adapter for the independently checked dependent-type kernel.
//! Program facts are admitted here only after the ordinary program verifier
//! succeeds. They remain opaque propositions, never equations about Nat.
mod core;
mod level;
mod schedule;
use crate::{Expr, Item};
pub use core::export::{
    check_lean_export, check_lean_export_receipt_with_budget, check_lean_export_with_budget,
    check_lean_export_with_policy, translate_lean_export, translate_lean_export_with_budget,
    translate_lean_export_with_policy, LeanDeclarationReport, LeanExportError, LeanExportReceipt,
    LeanExportReport, LeanExportTranslation, LeanFoundationPolicy,
};
use core::{
    apps, term, InductiveInput, Kernel, Level, Natural, NestedCase, RecursionCase, Term, T,
};
use std::collections::{BTreeSet, HashSet};
type Result<T> = std::result::Result<T, String>;

pub(super) fn is_declaration(expr: &Expr) -> bool {
    matches!(expr,Expr::List(parts) if matches!(parts.first(),Some(Expr::Symbol(head)) if matches!(head.as_str(),"#proof-definition"|"#proof-opaque"|"#proof-theorem"|"#proof-inductive")))
}

/// Called only after complete program validation. Audit declaration types and
/// bodies, including opaque/erased evidence, without treating comments as facts.
pub(super) fn foundation_dependencies(
    program: &crate::Program,
    target: &str,
) -> Result<Vec<String>> {
    let facts = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Proof { name, proposition } if !is_declaration(proposition) => Some(name.clone()),
            _ => None,
        })
        .collect::<HashSet<_>>();
    let mut graph = std::collections::HashMap::new();
    for item in &program.items {
        let Item::Proof { name, proposition } = item else {
            continue;
        };
        if !is_declaration(proposition) {
            continue;
        }
        let mut parsed = parse_declaration(name, proposition, &facts)?;
        if let Body::Inductive { members, .. } = &parsed.body {
            parsed
                .dependencies
                .extend(members.iter().filter(|member| *member != name).cloned());
        }
        if graph.insert(name.clone(), parsed.dependencies).is_some() {
            return Err("duplicate declaration during foundation audit".into());
        }
    }
    let mut pending = vec![target.to_owned()];
    let mut visited = HashSet::new();
    let mut foundations = BTreeSet::new();
    while let Some(name) = pending.pop() {
        if !visited.insert(name.clone()) {
            continue;
        }
        if let Some(label) = core::foundation::label(&name) {
            foundations.insert(label.to_owned());
        } else if let Some(dependencies) = graph.get(&name) {
            pending.extend(dependencies.iter().cloned());
        } else if !facts.contains(&name) && !matches!(name.as_str(), "#pt-nat" | "#pt-false") {
            return Err(format!("unknown declaration '{name}' in foundation audit"));
        }
    }
    Ok(foundations.into_iter().collect())
}
enum Body {
    Definition {
        ty: T,
        value: T,
        theorem: bool,
        opaque: bool,
    },
    Inductive {
        members: Vec<String>,
        parameters: Vec<T>,
        indices: Vec<T>,
        sort: Level,
        constructors: Vec<(String, Vec<T>)>,
        indexed_constructors: Vec<(String, Vec<T>, Vec<T>)>,
    },
}
struct Pending {
    name: String,
    universes: Vec<String>,
    dependencies: BTreeSet<String>,
    body: Body,
}

/// Parse only compiler-owned closed templates. Callers must relocate every
/// placeholder global/universe and check the resulting term in the kernel.
fn parse_closed_template(source: &str, universes: &[&str]) -> Result<T> {
    let forms = crate::parse(source)?;
    if forms.len() != 1 {
        return Err("kernel template must contain exactly one expression".into());
    }
    let facts = HashSet::new();
    let mut parser = Parser {
        locals: vec![],
        universes: universes.iter().map(|name| (*name).to_owned()).collect(),
        facts: &facts,
        dependencies: BTreeSet::new(),
        nodes: 0,
    };
    parser.expression(&forms[0].expr, 0)
}

pub(super) fn check(
    program: &crate::Program,
    facts: &HashSet<String>,
) -> std::result::Result<(), (String, String)> {
    let mut kernel = Kernel::with_budget(program.proof_budget);
    kernel.enable_declaration_spilling();
    for fact in facts {
        kernel.certified_program_fact(fact);
    }
    let mut declarations = Vec::new();
    let mut metadata = Vec::new();
    for item in &program.items {
        let Item::Proof { name, proposition } = item else {
            continue;
        };
        if !is_declaration(proposition) {
            continue;
        }
        if declarations.len() >= schedule::MAX_DECLARATIONS {
            return Err((name.clone(), "kernel declaration limit exceeded".into()));
        }
        let parsed =
            parse_declaration(name, proposition, facts).map_err(|why| (name.clone(), why))?;
        let members = match parsed.body {
            Body::Inductive { members, .. } => Some(members),
            _ => None,
        };
        metadata.push(schedule::Metadata {
            name: parsed.name,
            dependencies: parsed.dependencies,
            members,
        });
        declarations.push((name.as_str(), proposition));
        // The parsed type and proof are dropped here. Only immutable source
        // references and dependency metadata survive until a group is ready.
    }
    let diagnostic = |index: usize, message| {
        (
            declarations
                .get(index)
                .map_or("<unknown>", |(name, _)| *name)
                .to_owned(),
            message,
        )
    };
    let mut schedule = schedule::Schedule::new(metadata, |name| kernel.contains(name))
        .map_err(|(index, message)| diagnostic(index, message))?;
    let mut transformation_bytes = 0usize;
    while let Some(indices) = schedule
        .next()
        .map_err(|(index, message)| diagnostic(index, message))?
    {
        let first = indices
            .iter()
            .copied()
            .min()
            .ok_or_else(|| diagnostic(0, "empty kernel declaration group".into()))?;
        let diagnostic_name = declarations[first].0.to_owned();
        let mut pending = Vec::with_capacity(indices.len());
        for index in indices {
            let (name, proposition) = declarations[index];
            pending.push(
                parse_declaration(name, proposition, facts)
                    .map_err(|why| (name.to_owned(), why))?,
            );
        }
        let members = pending.iter().map(|p| p.name.clone()).collect::<Vec<_>>();
        // Scheduling cannot authorize a group. Recheck its explicit shape
        // before passing the original parsed declarations to the kernel.
        for p in &pending {
            match &p.body {
                Body::Inductive {
                    members: actual, ..
                } if actual == &members => {}
                Body::Definition { .. } if members.len() == 1 => {}
                _ => {
                    return Err((
                        diagnostic_name,
                        "mutual group membership must be identical on every inductive member"
                            .into(),
                    ))
                }
            }
        }
        kernel.reset_budget();
        let result = if pending.len() > 1 {
            let mut inputs = Vec::with_capacity(pending.len());
            for p in pending {
                let Body::Inductive {
                    parameters,
                    indices,
                    sort,
                    constructors,
                    indexed_constructors,
                    ..
                } = p.body
                else {
                    return Err((
                        diagnostic_name,
                        "noninductive member in a mutual group".into(),
                    ));
                };
                let constructors = if indices.is_empty() {
                    constructors
                        .into_iter()
                        .map(|(name, fields)| (name, fields, vec![]))
                        .collect()
                } else {
                    indexed_constructors
                };
                inputs.push(InductiveInput {
                    name: p.name,
                    universes: p.universes,
                    parameters,
                    indices,
                    sort,
                    constructors,
                });
            }
            kernel.mutual_inductive(inputs)
        } else {
            let p = pending.pop().ok_or_else(|| {
                (
                    diagnostic_name.clone(),
                    "empty kernel declaration group".into(),
                )
            })?;
            let result = match p.body {
                Body::Definition {
                    ty,
                    value,
                    theorem,
                    opaque,
                } => {
                    if opaque {
                        kernel.opaque_definition(&p.name, p.universes, ty, value)
                    } else {
                        kernel.definition(&p.name, p.universes, ty, value, theorem)
                    }
                }
                Body::Inductive {
                    parameters,
                    indices,
                    sort,
                    constructors,
                    indexed_constructors,
                    ..
                } => {
                    if indices.is_empty() {
                        kernel.inductive(&p.name, p.universes, parameters, sort, constructors)
                    } else {
                        kernel.indexed_inductive(
                            &p.name,
                            p.universes,
                            parameters,
                            indices,
                            sort,
                            indexed_constructors,
                        )
                    }
                }
            };
            result.map_err(|why| (diagnostic_name.clone(), why))
        };
        result?;
        transformation_bytes = transformation_bytes.saturating_add(kernel.transformation_bytes());
        if transformation_bytes > program.proof_budget.total_bytes() {
            return Err((diagnostic_name, format!("kernel cumulative transformation allocation limit exceeded ({transformation_bytes} > {} bytes); no theorem was established", program.proof_budget.total_bytes())));
        }
        kernel
            .trim_completed_declarations()
            .map_err(|why| (diagnostic_name, why))?;
    }
    Ok(())
}

fn parse_declaration(name: &str, expr: &Expr, facts: &HashSet<String>) -> Result<Pending> {
    let (head, args) = form(expr)?;
    if head == "#proof-inductive" {
        if !(4..=6).contains(&args.len()) {
            return Err("#proof-inductive requires parameters, optional #mutual then #indices clauses, sort, and constructors".into());
        }
    } else {
        arity(head, args, 3)?;
    }
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
        let mut offset = 2;
        let members = if matches!(args.get(offset), Some(Expr::List(parts)) if matches!(parts.first(), Some(Expr::Symbol(head)) if head == "#mutual"))
        {
            let clause = list(&args[offset])?;
            if !(3..=17).contains(&clause.len()) {
                return Err("#mutual requires between 2 and 16 explicit family names".into());
            }
            let members = clause[1..]
                .iter()
                .map(|member| parser.global(member))
                .collect::<Result<Vec<_>>>()?;
            if members.iter().collect::<HashSet<_>>().len() != members.len()
                || !members.iter().any(|member| member == name)
            {
                return Err(
                    "#mutual must list distinct families including this declaration".into(),
                );
            }
            offset += 1;
            members
        } else {
            vec![name.into()]
        };
        let indexed = matches!(args.get(offset), Some(Expr::List(parts)) if matches!(parts.first(), Some(Expr::Symbol(head)) if head == "#indices"));
        if args.len() != offset + usize::from(indexed) + 2 {
            return Err("invalid inductive header clauses or operand count".into());
        }
        let (indices, sort_arg, constructors_arg) = if indexed {
            let clause = list(&args[offset])?;
            if clause.first().map(|e| symbol(e)).transpose()? != Some("#indices") {
                return Err("indexed inductives require an explicit #indices clause".into());
            }
            if clause.len() < 2 || clause.len() > 65 {
                return Err(
                    "#indices requires between 1 and 64 explicit #parameter binders".into(),
                );
            }
            let mut indices = Vec::new();
            for entry in &clause[1..] {
                let parts = list(entry)?;
                if parts.len() != 3 || symbol(&parts[0])? != "#parameter" {
                    return Err("#indices entries have the form (#parameter name Type)".into());
                }
                let name = symbol(&parts[1])?;
                binder(name)?;
                if parser.locals.iter().any(|n| n == name) || parser.universes.contains(name) {
                    return Err(format!(
                        "kernel binding '{name}' shadows an existing binding"
                    ));
                }
                let ty = parser.expression(&parts[2], 1)?;
                parser.locals.push(name.into());
                indices.push(ty);
            }
            (indices, &args[offset + 1], &args[offset + 2])
        } else {
            (vec![], &args[offset], &args[offset + 1])
        };
        let sort = parser.expression(sort_arg, 0)?;
        let Term::Sort(sort) = sort.as_ref() else {
            return Err(
                "an inductive declaration requires an explicit #pt-type or #pt-prop sort".into(),
            );
        };
        let mut constructors = vec![];
        let mut labels = HashSet::new();
        let mut indexed_constructors = vec![];
        for constructor in list(constructors_arg)? {
            let parts = list(constructor)?;
            if parts.len() != if indexed { 3 } else { 2 } {
                return Err(if indexed {
                    "indexed constructors have the form (name ((field Type)...) (result-index...))"
                } else {
                    "constructors have the form (name ((field Type)...))"
                }
                .into());
            }
            let label = symbol(&parts[0])?;
            binder(label)?;
            if !labels.insert(label.to_owned()) {
                return Err("duplicate inductive constructor".into());
            }
            let saved = parser.locals.clone();
            parser.locals.truncate(parameters.len());
            let fields = parser.bindings(&parts[1], 0)?;
            let result_indices = if indexed {
                parser.terms(&parts[2], 0)?
            } else {
                vec![]
            };
            parser.locals = saved;
            if indexed && result_indices.len() != indices.len() {
                return Err(
                    "constructor result-index count must match the family's index count".into(),
                );
            }
            if indexed {
                indexed_constructors.push((label.into(), fields, result_indices));
            } else {
                constructors.push((label.into(), fields));
            }
        }
        if constructors.len().max(indexed_constructors.len()) > 64 {
            return Err("kernel constructor limit exceeded".into());
        }
        Body::Inductive {
            members,
            parameters,
            indices: indices.to_vec(),
            sort: sort.clone(),
            constructors,
            indexed_constructors,
        }
    } else {
        let ty = parser.expression(&args[1], 0)?;
        let value = parser.expression(&args[2], 0)?;
        Body::Definition {
            ty,
            value,
            theorem: head == "#proof-theorem",
            opaque: head == "#proof-opaque",
        }
    };
    if let Body::Inductive { members, .. } = &body {
        for member in members {
            parser.dependencies.remove(member);
        }
    }
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
                "#pt-level-max"=>{if args.is_empty(){return Err("#pt-level-max requires explicit operands".into());}let mut level=Level::number(0)?;for arg in args {level=level.maximum(&self.level(arg,depth+1)?)?;}Ok(level)},
                "#pt-level-imax"=>{arity(head,args,2)?;self.level(&args[0],depth+1)?.imax(&self.level(&args[1],depth+1)?)},
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
            "#pt-sort"=>{arity(head,args,1)?;Ok(term(Term::Sort(self.level(&args[0],depth+1)?)))},
            "#pt-type"=>{arity(head,args,1)?;Ok(term(Term::Sort(self.level(&args[0],depth+1)?.successor()?)))},
            "#pt-use"=>{arity(head,args,2)?;let name=self.global(&args[0])?;let levels=self.levels(&args[1],depth+1)?;Ok(term(Term::Global(name,levels)))},
            "#pt-project"=>{arity(head,args,3)?;let family=self.global(&args[0])?;let index=natural(&args[1])?;Ok(term(Term::Project{family,index,subject:self.expression(&args[2],depth+1)?}))},
            "#pt-let" => {
                arity(head, args, 3)?;
                let declaration = list(&args[0])?;
                if declaration.len() != 3 || symbol(&declaration[0])? != "#parameter" {
                    return Err("#pt-let requires (#parameter name Type), a value, and a body".into());
                }
                let name = symbol(&declaration[1])?;
                binder(name)?;
                if self.locals.iter().any(|local| local == name) || self.universes.contains(name) {
                    return Err(format!("kernel binding '{name}' shadows an existing binding"));
                }
                let ty = self.expression(&declaration[2], depth + 1)?;
                let value = self.expression(&args[1], depth + 1)?;
                self.locals.push(name.into());
                let body = self.expression(&args[2], depth + 1);
                self.locals.pop();
                Ok(term(Term::Let(ty, value, body?)))
            }
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
            "#pt-quot"|"#pt-quot-make"=>{
                arity(head,args,if head=="#pt-quot"{3}else{4})?;
                let l=self.level(&args[0],depth+1)?;let a=self.expression(&args[1],depth+1)?;let r=self.expression(&args[2],depth+1)?;
                Ok(term(if head=="#pt-quot"{Term::QuotType(l,a,r)}else{Term::QuotMake(l,a,r,self.expression(&args[3],depth+1)?)}))
            },
            "#pt-quot-lift"=>{
                arity(head,args,7)?;let levels=self.levels(&args[0],depth+1)?;
                if levels.len()!=2 {return Err("#pt-quot-lift requires exactly two explicit universe levels".into());}
                Ok(term(Term::QuotLift{source_level:levels[0].clone(),target_level:levels[1].clone(),
                    ty:self.expression(&args[1],depth+1)?,relation:self.expression(&args[2],depth+1)?,target:self.expression(&args[3],depth+1)?,
                    function:self.expression(&args[4],depth+1)?,respect:self.expression(&args[5],depth+1)?,subject:self.expression(&args[6],depth+1)?}))
            },
            "#pt-quot-induct"=>{
                arity(head,args,6)?;Ok(term(Term::QuotInduct{level:self.level(&args[0],depth+1)?,ty:self.expression(&args[1],depth+1)?,
                    relation:self.expression(&args[2],depth+1)?,motive:self.expression(&args[3],depth+1)?,branch:self.expression(&args[4],depth+1)?,subject:self.expression(&args[5],depth+1)?}))
            },
            "#pt-eq-elim"=>{arity(head,args,6)?;Ok(term(Term::EqElim{ty:self.expression(&args[0],depth+1)?,left:self.expression(&args[1],depth+1)?,motive:self.expression(&args[2],depth+1)?,base:self.expression(&args[3],depth+1)?,right:self.expression(&args[4],depth+1)?,proof:self.expression(&args[5],depth+1)?}))},
            "#pt-pair"=>{arity(head,args,3)?;Ok(term(Term::Pair(self.expression(&args[0],depth+1)?,self.expression(&args[1],depth+1)?,self.expression(&args[2],depth+1)?)))},
            "#pt-first"|"#pt-second"=>{arity(head,args,1)?;let value=self.expression(&args[0],depth+1)?;Ok(term(if head=="#pt-first"{Term::First(value)}else{Term::Second(value)}))},
            "#pt-succ"=>{arity(head,args,1)?;Ok(nat_constructor("succ",vec![self.expression(&args[0],depth+1)?]))},
            "#pt-numeral"=>{
                arity(head,args,1)?;let n=natural(&args[0])?;if n>128{return Err("kernel numeral abbreviation limit is 128; Nat itself is unbounded".into());}
                Ok(term(Term::NatLiteral {family:"#pt-nat".into(),value:Natural::parse(&n.to_string())?}))
            }
            "#pt-nat-literal" => {
                arity(head,args,2)?;
                let family = self.global(&args[0])?;
                let Expr::String(decimal) = &args[1] else {
                    return Err("#pt-nat-literal requires a family and a canonical decimal string".into());
                };
                Ok(term(Term::NatLiteral {family,value:Natural::parse(decimal)?}))
            }
            "#pt-nat-induct"=>{arity(head,args,4)?;Ok(term(Term::Induct{family:"#pt-nat".into(),levels:vec![],parameters:vec![],indices:vec![],motive:self.expression(&args[0],depth+1)?,branches:vec![self.expression(&args[1],depth+1)?,self.expression(&args[2],depth+1)?],subject:self.expression(&args[3],depth+1)?}))},
            "#pt-construct"=>{arity(head,args,5)?;let family=self.global(&args[0])?;Ok(term(Term::Ctor{family,levels:self.levels(&args[1],depth+1)?,parameters:self.terms(&args[2],depth+1)?,constructor:symbol(&args[3])?.into(),fields:self.terms(&args[4],depth+1)?}))},
            "#pt-self-at"=>{arity(head,args,1)?;Ok(term(Term::SelfAt(self.terms(&args[0],depth+1)?)))},
            "#pt-recur"=>{arity(head,args,2)?;Ok(term(Term::Recur(self.global(&args[0])?,self.terms(&args[1],depth+1)?)))},
            "#pt-mutual-induct" | "#pt-nested-induct" => {
                let nested = head == "#pt-nested-induct";
                let offset = usize::from(nested);
                arity(head, args, 6 + offset)?;
                let family = self.global(&args[0])?;
                let levels = self.levels(&args[1], depth + 1)?;
                let parameters = self.terms(&args[2], depth + 1)?;
                let clause = list(&args[3 + offset])?;
                if clause.first().map(symbol).transpose()? != Some("#indices") || clause.len() > 65 {
                    return Err(format!("{head} requires an explicit #indices clause with at most 64 values"));
                }
                let indices = clause[1..].iter().map(|index| self.expression(index, depth + 1)).collect::<Result<Vec<_>>>()?;
                let bundles = list(&args[4 + offset])?;
                if !(2..=16).contains(&bundles.len()) { return Err(format!("{head} requires between 2 and 16 family cases")); }
                if nested {
                    let selected = natural(&args[3])?;
                    let cases = bundles.iter().map(|bundle| {
                        let parts = list(bundle)?;
                        if parts.len() != 4 || symbol(&parts[0])? != "#pt-case" {
                            return Err("nested cases require (#pt-case FamilyType Motive (Branches...))".into());
                        }
                        Ok(NestedCase { selector: self.expression(&parts[1], depth + 1)?, motive: self.expression(&parts[2], depth + 1)?, branches: self.terms(&parts[3], depth + 1)? })
                    }).collect::<Result<Vec<_>>>()?;
                    return Ok(term(Term::NestedInduct { family, levels, parameters, selected, indices, cases, subject: self.expression(&args[6], depth + 1)? }));
                }
                let cases = bundles.iter().map(|bundle| {
                    let parts = list(bundle)?;
                    if parts.len() != 3 { return Err("mutual cases require (Family Motive (Branches...))".into()); }
                    Ok(RecursionCase { family: self.global(&parts[0])?, motive: self.expression(&parts[1], depth + 1)?, branches: self.terms(&parts[2], depth + 1)? })
                }).collect::<Result<Vec<_>>>()?;
                Ok(term(Term::MutualInduct { family, levels, parameters, indices, cases, subject: self.expression(&args[5], depth + 1)? }))
            },
            "#pt-induct"=>{if args.len()==6{let family=self.global(&args[0])?;Ok(term(Term::Induct{family,levels:self.levels(&args[1],depth+1)?,parameters:self.terms(&args[2],depth+1)?,indices:vec![],motive:self.expression(&args[3],depth+1)?,branches:self.terms(&args[4],depth+1)?,subject:self.expression(&args[5],depth+1)?}))}else if args.len()==7{let clause=list(&args[3])?;if clause.first().map(|e|symbol(e)).transpose()?!=Some("#indices"){return Err("indexed #pt-induct requires an explicit #indices clause".into());}if clause.len()<2||clause.len()>65{return Err("#pt-induct #indices requires between 1 and 64 index values".into());}let indices=clause[1..].iter().map(|e|self.expression(e,depth+1)).collect::<Result<Vec<_>>>()?;let family=self.global(&args[0])?;Ok(term(Term::Induct{family,levels:self.levels(&args[1],depth+1)?,parameters:self.terms(&args[2],depth+1)?,indices,motive:self.expression(&args[4],depth+1)?,branches:self.terms(&args[5],depth+1)?,subject:self.expression(&args[6],depth+1)?}))}else{Err("#pt-induct requires six operands, or seven with an explicit #indices clause".into())}},
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
