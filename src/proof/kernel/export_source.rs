//! Readable native source for checked export declarations. No trusted replay
//! directives or unchecked holes are emitted; the complete output is rechecked.
use super::*;
#[path = "export_correspondence.rs"]
pub(super) mod correspondence;

const SOURCE_BYTES: usize = 8 * 1024 * 1024;
const SOURCE_NODES: usize = 1_000_000;

#[derive(Clone, Debug)]
pub struct LeanExportTranslation {
    pub report: LeanExportReport,
    pub target: String,
    pub source: String,
}

pub(super) fn render(
    replay: &mut Replay,
    report: LeanExportReport,
    target_identity: &str,
) -> Result<LeanExportTranslation> {
    let names = report
        .declarations
        .iter()
        .enumerate()
        .map(|(index, declaration)| {
            let display = declaration
                .name
                .chars()
                .take(64)
                .map(|ch| {
                    if ch.is_ascii_alphanumeric() || ch == '_' {
                        ch
                    } else {
                        '-'
                    }
                })
                .collect::<String>();
            (
                declaration.identity.clone(),
                format!("lean-{index}-{display}"),
            )
        })
        .collect::<HashMap<_, _>>();
    let target = names
        .get(target_identity)
        .ok_or("missing translated theorem target")?
        .clone();
    let mut writer = Writer {
        kernel: &mut replay.kernel,
        names: &names,
        universes: HashMap::new(),
        output: String::new(),
        nodes: 0,
    };
    writer.push("; Checked native translation of a Lean export, not an admission.\n")?;
    writer.push(&format!("; Lean: {LEAN_EXPORT_VERSION} ({LEAN_EXPORT_GITHASH})\n; Exporter: {EXPORTER_REVISION}\n; Input SHA-256: {}\n; Native theorem: {target}\n", report.input_sha256))?;
    if report.budget != crate::ProofBudget::default() {
        writer.push(&format!(
            "; Proof budget: work={} phase-bytes={} total-bytes={}\n",
            report.budget.work(),
            report.budget.phase_bytes(),
            report.budget.total_bytes()
        ))?;
    }
    writer.push("; Keep the upstream source/license provenance with this translation.\n\n")?;
    if !report.axioms.is_empty() {
        writer.push(&format!(
            "; Declared logical axioms: {}\n; Target logical foundations: {}\n\n",
            Json::Array(report.axioms.iter().map(|name| text_json(name)).collect()).render(),
            Json::Array(
                report
                    .target_axioms
                    .iter()
                    .map(|name| text_json(name))
                    .collect()
            )
            .render()
        ))?;
    }
    if !report.foundations.is_empty() {
        writer.push(&format!(
            "; Checked primitive foundations: {}\n\n",
            Json::Array(
                report
                    .foundations
                    .iter()
                    .map(|name| text_json(name))
                    .collect()
            )
            .render()
        ))?;
    }
    for (index, declaration) in report.declarations.iter().enumerate() {
        let checked = writer
            .kernel
            .declarations
            .get(&declaration.identity)?
            .ok_or("checked source declaration is missing")?;
        writer.kernel.reset_budget();
        writer.universes = checked
            .universes
            .iter()
            .enumerate()
            .map(|(index, original)| (original.clone(), format!("u{index}")))
            .collect();
        writer.push(&format!(
            "; Lean declaration: {}\n; Identity: {}\n; Export line: {}\n; Prefix SHA-256: {}\n",
            text_json(&declaration.name).render(),
            text_json(&declaration.identity).render(),
            declaration.line,
            declaration.sha256
        ))?;
        if let Some(family) = &checked.family {
            writer.inductive(&declaration.identity, &checked.universes, family)?;
        } else {
            let retained = if checked.value.is_none() {
                replay.initializers.get(
                    index,
                    &replay.expressions,
                    &replay.names,
                    &replay.levels,
                )?
            } else {
                None
            };
            let value = checked
                .value
                .as_ref()
                .or(retained.as_ref())
                .ok_or("checked opaque/theorem initializer was not retained for translation")?;
            writer.definition(
                &declaration.identity,
                &checked.universes,
                &checked.ty,
                value,
                &declaration.kind,
            )?;
        }
        writer.push("\n\n")?;
        drop(checked);
        replay.expressions.end_record();
    }
    // The formatter and ordinary source checker have no export-specific trust
    // path. Resource failures and malformed generated source fail translation.
    let source = crate::format_source(&writer.output)
        .map_err(|why| format!("translated source formatting failed: {why}"))?;
    if source.len() > SOURCE_BYTES {
        return Err("formatted proof-source byte limit exceeded".into());
    }
    drop(writer);
    let mut config = crate::CompileConfig::default();
    config.set_proof_budget(report.budget);
    let program = crate::parse_program_with_config(&source, &config)
        .map_err(|why| format!("translated source parsing failed: {why}"))?;
    crate::check_types(&program)
        .map_err(|why| format!("translated source recheck failed: {why}"))?;
    if !program.items.iter().any(|item| {
        matches!(item, crate::Item::Proof { name, proposition }
        if name == &target && matches!(proposition,crate::Expr::List(parts)
            if matches!(parts.first(),Some(crate::Expr::Symbol(head)) if head == "#proof-theorem")))
    }) {
        return Err("translation did not preserve the selected theorem declaration".into());
    }
    correspondence::check(replay, &report, &names, &program)
        .map_err(|why| format!("translated source correspondence failed: {why}"))?;
    check_target_foundations(&program, &target, &report.target_axioms)?;
    Ok(LeanExportTranslation {
        report,
        target,
        source,
    })
}

fn check_target_foundations(
    program: &crate::Program,
    target: &str,
    expected: &[String],
) -> Result<()> {
    let actual = crate::proof::kernel::foundation_dependencies(program, target)?;
    if actual != expected {
        return Err(
            "translated theorem's logical foundations differ from the checked export".into(),
        );
    }
    Ok(())
}

#[cfg(test)]
mod foundation_audit_tests {
    use super::*;
    #[test]
    fn a_well_typed_proof_of_the_same_goal_cannot_silently_add_an_assumption() {
        let prefix = include_str!("../../../examples/proof_foundations.lim");
        for (body,expected) in [
            ("(#pt-refl #pt-nat #pt-zero)",true),
            ("(#pt-let (#parameter unused #pt-nat) (#pt-use selected-natural ()) (#pt-refl #pt-nat #pt-zero))",false),
        ] {
            let source=format!("{prefix}\n(#theorem audit-goal (#universes) (#parameters)
              (#statement (#pt-eq #pt-nat #pt-zero #pt-zero)) (#proof {body}))");
            let program=crate::parse_program(&source).unwrap();
            crate::check_types(&program).unwrap();
            let result=check_target_foundations(&program,"audit-goal",&[]);
            if expected {result.unwrap();} else {assert!(result.unwrap_err().contains("logical foundations differ"));}
        }
    }
}

struct Writer<'a> {
    kernel: &'a mut Kernel,
    names: &'a HashMap<String, String>,
    universes: HashMap<String, String>,
    output: String,
    nodes: usize,
}

impl Writer<'_> {
    fn node(&mut self, depth: usize) -> Result<()> {
        self.nodes = self.nodes.saturating_add(1);
        if self.nodes > SOURCE_NODES || depth > 96 {
            Err("proof-source node or depth limit exceeded".into())
        } else {
            Ok(())
        }
    }
    fn term(&mut self, value: &T, binders: usize, depth: usize) -> Result<()> {
        self.node(depth)?;
        match value.as_ref() {
            Term::NatLiteral { family, value } => self.push(&format!(
                "(#pt-nat-literal {} {})",
                self.name(family)?,
                text_json(value.decimal()).render()
            )),
            Term::Sort(level) => {
                self.push("(#pt-sort ")?;
                self.level(level)?;
                self.push(")")
            }
            Term::QuotType(l, a, r) | Term::QuotMake(l, a, r, _) => {
                self.push(if matches!(value.as_ref(), Term::QuotType(..)) {
                    "(#pt-quot "
                } else {
                    "(#pt-quot-make "
                })?;
                self.level(l)?;
                self.push(" ")?;
                self.term(a, binders, depth + 1)?;
                self.push(" ")?;
                self.term(r, binders, depth + 1)?;
                if let Term::QuotMake(_, _, _, x) = value.as_ref() {
                    self.push(" ")?;
                    self.term(x, binders, depth + 1)?;
                }
                self.push(")")
            }
            Term::QuotLift {
                source_level,
                target_level,
                ty,
                relation,
                target,
                function,
                respect,
                subject,
            } => {
                self.push("(#pt-quot-lift ")?;
                self.levels(&[source_level.clone(), target_level.clone()])?;
                for value in [ty, relation, target, function, respect, subject] {
                    self.push(" ")?;
                    self.term(value, binders, depth + 1)?;
                }
                self.push(")")
            }
            Term::QuotInduct {
                level,
                ty,
                relation,
                motive,
                branch,
                subject,
            } => {
                self.push("(#pt-quot-induct ")?;
                self.level(level)?;
                for value in [ty, relation, motive, branch, subject] {
                    self.push(" ")?;
                    self.term(value, binders, depth + 1)?;
                }
                self.push(")")
            }
            Term::Var(index) => {
                let number = index
                    .checked_add(1)
                    .and_then(|offset| binders.checked_sub(offset))
                    .ok_or("free variable in source translation")?;
                self.push(&format!("v{number}"))
            }
            Term::Global(name, levels) => {
                if matches!(name.as_str(), "#pt-nat" | "#pt-false") && levels.is_empty() {
                    return self.push(name);
                }
                self.push(&format!("(#pt-use {} ", self.name(name)?))?;
                self.levels(levels)?;
                self.push(")")
            }
            Term::Pi(..) | Term::Lam(..) => {
                let lambda = matches!(value.as_ref(), Term::Lam(..));
                self.push(if lambda { "(#pt-lambda (" } else { "(#pt-pi (" })?;
                let mut body = value.clone();
                let mut count = 0;
                while count < 64 {
                    let (domain, next) = match body.as_ref() {
                        Term::Lam(a, b) if lambda => (a.clone(), b.clone()),
                        Term::Pi(a, b) if !lambda => (a.clone(), b.clone()),
                        _ => break,
                    };
                    if count != 0 {
                        self.node(depth)?;
                        self.push(" ")?;
                    }
                    self.push(&format!("(v{} ", binders + count))?;
                    self.term(&domain, binders + count, depth + 1)?;
                    self.push(")")?;
                    body = next;
                    count += 1;
                }
                self.push(") ")?;
                self.term(&body, binders + count, depth + 1)?;
                self.push(")")
            }
            Term::Sigma(domain, body) => {
                self.push(&format!("(#pt-sigma ((v{binders} "))?;
                self.term(domain, binders, depth + 1)?;
                self.push(")) ")?;
                self.term(body, binders + 1, depth + 1)?;
                self.push(")")
            }
            Term::Let(ty, initializer, body) => {
                self.push(&format!("(#pt-let (#parameter v{binders} "))?;
                self.term(ty, binders, depth + 1)?;
                self.push(") ")?;
                self.term(initializer, binders, depth + 1)?;
                self.push(" ")?;
                self.term(body, binders + 1, depth + 1)?;
                self.push(")")
            }
            Term::App(..) => {
                let mut function = value.clone();
                let mut arguments = vec![];
                while arguments.len() < 64 {
                    let Term::App(f, a) = function.as_ref() else {
                        break;
                    };
                    arguments.push(a.clone());
                    function = f.clone();
                    if arguments.len() > 1 {
                        self.node(depth)?;
                    }
                }
                self.push("(#pt-app ")?;
                self.term(&function, binders, depth + 1)?;
                for argument in arguments.iter().rev() {
                    self.push(" ")?;
                    self.term(argument, binders, depth + 1)?;
                }
                self.push(")")
            }
            Term::Pair(a, b, c) => self.form("#pt-pair", &[a, b, c], binders, depth),
            Term::Eq(a, b, c) => self.form("#pt-eq", &[a, b, c], binders, depth),
            Term::Refl(a, b) => self.form("#pt-refl", &[a, b], binders, depth),
            Term::First(a) => self.form("#pt-first", &[a], binders, depth),
            Term::Second(a) => self.form("#pt-second", &[a], binders, depth),
            Term::EqElim {
                ty,
                left,
                motive,
                base,
                right,
                proof,
            } => self.form(
                "#pt-eq-elim",
                &[ty, left, motive, base, right, proof],
                binders,
                depth,
            ),
            Term::Project {
                family,
                index,
                subject,
            } => {
                self.push(&format!("(#pt-project {} {index} ", self.name(family)?))?;
                self.term(subject, binders, depth + 1)?;
                self.push(")")
            }
            Term::Ctor {
                family,
                levels,
                parameters,
                constructor,
                fields,
            } => {
                self.push(&format!("(#pt-construct {} ", self.name(family)?))?;
                self.levels(levels)?;
                self.push(" ")?;
                self.terms(parameters, binders, depth + 1)?;
                self.push(&format!(
                    " {} ",
                    if family == "#pt-nat" || family == "#pt-false" {
                        constructor.clone()
                    } else {
                        self.name(constructor)?
                    }
                ))?;
                self.terms(fields, binders, depth + 1)?;
                self.push(")")
            }
            Term::Induct {
                family,
                levels,
                parameters,
                indices,
                motive,
                branches,
                subject,
            } => {
                self.push(&format!("(#pt-induct {} ", self.name(family)?))?;
                self.levels(levels)?;
                self.push(" ")?;
                self.terms(parameters, binders, depth + 1)?;
                self.push(" ")?;
                if !indices.is_empty() {
                    self.indices(indices, binders, depth + 1)?;
                    self.push(" ")?;
                }
                self.term(motive, binders, depth + 1)?;
                self.push(" ")?;
                self.terms(branches, binders, depth + 1)?;
                self.push(" ")?;
                self.term(subject, binders, depth + 1)?;
                self.push(")")
            }
            Term::MutualInduct {
                family,
                levels,
                parameters,
                indices,
                cases,
                subject,
            } => self.group(
                family, levels, parameters, indices, cases, subject, binders, depth,
            ),
            Term::NestedInduct { .. } => {
                Err("unexpected source-only eliminator in an elaborated export".into())
            }
            Term::SelfType | Term::SelfAt(_) | Term::Recur(..) => {
                Err("unexpanded recursive marker in translated evidence".into())
            }
        }
    }
    fn form(&mut self, head: &str, terms: &[&T], binders: usize, depth: usize) -> Result<()> {
        self.push(&format!("({head}"))?;
        for term in terms {
            self.push(" ")?;
            self.term(term, binders, depth + 1)?;
        }
        self.push(")")
    }
    fn indices(&mut self, values: &[T], binders: usize, depth: usize) -> Result<()> {
        self.push("(#indices")?;
        for value in values {
            self.push(" ")?;
            self.term(value, binders, depth + 1)?;
        }
        self.push(")")
    }
    #[expect(clippy::too_many_arguments)]
    fn group(
        &mut self,
        family: &str,
        levels: &[Level],
        parameters: &[T],
        indices: &[T],
        cases: &[RecursionCase],
        subject: &T,
        binders: usize,
        depth: usize,
    ) -> Result<()> {
        let (description, _) = self.kernel.family(family, levels, 0)?;
        let nested = description
            .group
            .iter()
            .any(|name| self.kernel.nested.contains_key(name));
        if nested {
            let owner = description
                .group
                .iter()
                .find(|name| !self.kernel.nested.contains_key(*name))
                .ok_or("nested group lacks a public owner")?;
            let selected = description
                .group
                .iter()
                .position(|name| name == family)
                .ok_or("nested group lacks its selected case")?;
            self.push(&format!("(#pt-nested-induct {} ", self.name(owner)?))?;
            self.levels(levels)?;
            self.push(" ")?;
            self.terms(parameters, binders, depth + 1)?;
            self.push(&format!(" {selected} "))?;
        } else {
            self.push(&format!("(#pt-mutual-induct {} ", self.name(family)?))?;
            self.levels(levels)?;
            self.push(" ")?;
            self.terms(parameters, binders, depth + 1)?;
            self.push(" ")?;
        }
        self.indices(indices, binders, depth + 1)?;
        self.push(" (")?;
        for (index, case) in cases.iter().enumerate() {
            if index != 0 {
                self.push(" ")?;
            }
            if nested {
                self.push("(#pt-case ")?;
                let selector =
                    self.kernel
                        .family_application(&case.family, levels, parameters, &[], 0)?;
                self.term(&selector, binders, depth + 1)?;
            } else {
                self.push(&format!("({}", self.name(&case.family)?))?;
            }
            self.push(" ")?;
            self.term(&case.motive, binders, depth + 1)?;
            self.push(" ")?;
            self.terms(&case.branches, binders, depth + 1)?;
            self.push(")")?;
        }
        self.push(") ")?;
        self.term(subject, binders, depth + 1)?;
        self.push(")")
    }
    fn push(&mut self, text: &str) -> Result<()> {
        if self.output.len().saturating_add(text.len()) > SOURCE_BYTES {
            return Err("proof-source byte limit exceeded".into());
        }
        self.output.push_str(text);
        Ok(())
    }
    fn name(&self, original: &str) -> Result<String> {
        match original {
            "#pt-nat" | "#pt-false" => Ok(original.into()),
            _ if foundation::label(original).is_some() => Ok(original.into()),
            _ => self.names.get(original).cloned().ok_or_else(|| {
                format!("source translation encountered an unmapped declaration {original:?}")
            }),
        }
    }
    fn level(&mut self, level: &Level) -> Result<()> {
        self.push(&level.source(&self.universes)?)
    }
    fn levels(&mut self, levels: &[Level]) -> Result<()> {
        self.push("(")?;
        for (index, level) in levels.iter().enumerate() {
            if index != 0 {
                self.push(" ")?;
            }
            self.level(level)?;
        }
        self.push(")")
    }
    fn universe_binders(&mut self, universes: &[String]) -> Result<()> {
        self.push("(")?;
        for (index, _) in universes.iter().enumerate() {
            if index != 0 {
                self.push(" ")?;
            }
            self.push(&format!("u{index}"))?;
        }
        self.push(")")
    }
    fn terms(&mut self, values: &[T], binders: usize, depth: usize) -> Result<()> {
        self.push("(")?;
        for (index, value) in values.iter().enumerate() {
            if index != 0 {
                self.push(" ")?;
            }
            self.term(value, binders, depth + 1)?;
        }
        self.push(")")
    }
    fn domains(&mut self, values: &[T], binders: usize, indices: bool) -> Result<()> {
        self.push(if indices { "(#indices" } else { "(" })?;
        for (index, value) in values.iter().enumerate() {
            if indices || index != 0 {
                self.push(" ")?;
            }
            self.push(&format!(
                "({}v{} ",
                if indices { "#parameter " } else { "" },
                binders + index
            ))?;
            self.term(value, binders + index, 0)?;
            self.push(")")?;
        }
        self.push(")")
    }
    fn inductive(&mut self, name: &str, universes: &[String], family: &Family) -> Result<()> {
        self.push(&format!("(#math-inductive {} ", self.name(name)?))?;
        self.universe_binders(universes)?;
        self.push(" ")?;
        self.domains(&family.parameters, 0, false)?;
        let roots = family
            .group
            .iter()
            .filter(|name| !self.kernel.nested.contains_key(*name))
            .cloned()
            .collect::<Vec<_>>();
        if roots.len() > 1 {
            self.push(" (#mutual")?;
            for root in roots {
                self.push(&format!(" {}", self.name(&root)?))?;
            }
            self.push(")")?;
        }
        if !family.indices.is_empty() {
            self.push(" ")?;
            self.domains(&family.indices, family.parameters.len(), true)?;
        }
        self.push(" (#pt-sort ")?;
        self.level(&family.sort)?;
        self.push(") (")?;
        for (index, constructor) in family.constructors.iter().enumerate() {
            if index != 0 {
                self.push(" ")?;
            }
            self.push(&format!("({} ", self.name(&constructor.name)?))?;
            self.domains(&constructor.fields, family.parameters.len(), false)?;
            if !family.indices.is_empty() {
                self.push(" ")?;
                self.terms(
                    &constructor.result_indices,
                    family.parameters.len() + constructor.fields.len(),
                    0,
                )?;
            }
            self.push(")")?;
        }
        self.push("))")
    }
    fn definition(
        &mut self,
        name: &str,
        universes: &[String],
        ty: &T,
        value: &T,
        kind: &str,
    ) -> Result<()> {
        if kind == "theorem" {
            self.push(&format!("(#theorem {} (#universes", self.name(name)?))?;
            for index in 0..universes.len() {
                self.push(&format!(" u{index}"))?;
            }
            self.push(") (#parameters) (#statement ")?;
            self.term(ty, 0, 0)?;
            self.push(") (#proof ")?;
            self.term(value, 0, 0)?;
            self.push("))")
        } else {
            self.push(&format!(
                "({} {} ",
                if matches!(kind, "opaque" | "axiom") {
                    "#math-opaque"
                } else {
                    "#math-definition"
                },
                self.name(name)?
            ))?;
            self.universe_binders(universes)?;
            self.push(" ")?;
            self.term(ty, 0, 0)?;
            self.push(" ")?;
            self.term(value, 0, 0)?;
            self.push(")")
        }
    }
}
