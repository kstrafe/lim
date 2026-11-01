//! Bounded replay of lean4export 3.1.0 records. Export claims are not evidence:
//! every accepted declaration is checked by the ordinary dependent kernel.
use super::*;
use crate::lsp::json::Json;
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::io::BufRead;

#[cfg(test)]
#[path = "export_fixtures_tests.rs"]
mod fixtures_tests;
#[path = "export_hash.rs"]
mod hash;
#[path = "export_inductive.rs"]
mod inductives;
#[path = "export_terms.rs"]
mod terms;

pub const LEAN_EXPORT_FORMAT: &str = "3.1.0";
pub const LEAN_EXPORT_VERSION: &str = "4.33.1";
pub const LEAN_EXPORT_GITHASH: &str = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6";
const EXPORTER_REVISION: &str = "15f6055e299ad5b89345e533cc2192f4cc00f659";
const MAX_LINE: usize = 8 * 1024 * 1024;
const MAX_BYTES: u64 = 64 * 1024 * 1024;
const MAX_NAMES: usize = 100_000;
const MAX_NAME_BYTES: usize = 16 * 1024 * 1024;
const MAX_LEVELS: usize = 20_000;
const MAX_EXPRESSIONS: usize = 200_000;
const MAX_EXPRESSION_DEPTH: usize = 256;
const MAX_DECLARATIONS: usize = 4096;
const MAX_DEPENDENCIES: usize = 1_000_000;

#[derive(Clone, Debug)]
pub struct LeanDeclarationReport {
    pub name: String,
    pub identity: String,
    pub kind: String,
    pub line: usize,
    pub sha256: String,
    pub dependencies: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct LeanExportReport {
    pub target: String,
    pub input_sha256: String,
    pub bytes: u64,
    pub records: u64,
    pub declarations: Vec<LeanDeclarationReport>,
}
impl LeanExportReport {
    /// A replay receipt, not a certificate that can bypass later checking.
    pub fn render_json(&self) -> String {
        object([
            ("schema", text_json("lim-lean-replay-v1")),
            ("target", text_json(&self.target)),
            ("input_sha256", text_json(&self.input_sha256)),
            ("bytes", number_json(self.bytes)),
            ("records", number_json(self.records)),
            ("lean_version", text_json(LEAN_EXPORT_VERSION)),
            ("lean_githash", text_json(LEAN_EXPORT_GITHASH)),
            ("format_version", text_json(LEAN_EXPORT_FORMAT)),
            ("exporter_revision", text_json(EXPORTER_REVISION)),
            (
                "declaration_hash_scope",
                text_json("export-prefix-through-record"),
            ),
            ("axioms", Json::Array(vec![])),
            (
                "declarations",
                Json::Array(
                    self.declarations
                        .iter()
                        .map(|decl| {
                            object([
                                ("name", text_json(&decl.name)),
                                ("identity", text_json(&decl.identity)),
                                ("kind", text_json(&decl.kind)),
                                ("line", number_json(decl.line as u64)),
                                ("sha256", text_json(&decl.sha256)),
                                (
                                    "dependencies",
                                    Json::Array(
                                        decl.dependencies.iter().map(|d| text_json(d)).collect(),
                                    ),
                                ),
                            ])
                        })
                        .collect(),
                ),
            ),
        ])
        .render()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeanExportError {
    pub line: usize,
    pub message: String,
}
impl std::fmt::Display for LeanExportError {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(out, "Lean export line {}: {}", self.line, self.message)
    }
}
impl std::error::Error for LeanExportError {}

#[derive(Clone)]
struct Name {
    key: String,
    display: String,
    depth: usize,
}
struct Replay {
    kernel: Kernel,
    names: Vec<Name>,
    name_keys: HashSet<String>,
    name_bytes: usize,
    levels: Vec<Level>,
    expressions: Vec<(T, usize)>,
    reports: Vec<LeanDeclarationReport>,
    checked: HashMap<String, usize>,
    dependency_count: usize,
    payload_bytes: usize,
    dependency_bytes: usize,
    transformation_bytes: usize,
    natural_literals: bool,
    line: usize,
    digest: String,
}

/// Reads the actual pinned NDJSON protocol without executing Lean or trusting
/// a claimed check result. There is no admission/axiom or cache input mode.
pub fn check_lean_export<R: BufRead>(
    mut reader: R,
    target: &str,
) -> std::result::Result<LeanExportReport, LeanExportError> {
    let _stage = crate::timing::stage("lean_export_replay");
    let mut replay = Replay::new();
    let mut input_hash = hash::Sha256::new();
    let mut total = 0u64;
    let mut line = Vec::new();
    loop {
        line.clear();
        let count = std::io::Read::take(&mut reader, (MAX_LINE + 1) as u64)
            .read_until(b'\n', &mut line)
            .map_err(|why| LeanExportError {
                line: replay.line + 1,
                message: format!("input read failed: {why}"),
            })?;
        if count == 0 {
            break;
        }
        replay.line += 1;
        let result = (|| {
            if line.len() > MAX_LINE {
                return Err("export line byte limit exceeded".into());
            }
            total = total
                .checked_add(line.len() as u64)
                .ok_or("export byte count overflow")?;
            if total > MAX_BYTES {
                return Err("export total byte limit exceeded; no theorem was established".into());
            }
            let text = std::str::from_utf8(&line).map_err(|_| "export must be UTF-8")?;
            let record = crate::lsp::json::parse(text)
                .map_err(|why| format!("invalid export JSON: {why}"))?;
            input_hash.update(&line);
            // A declaration hash includes its primitive tables and preceding
            // checked environment, not only JSON IDs in its final record.
            replay.digest = hash::hex(&input_hash.clone().finish());
            if replay.line == 1 {
                replay.metadata(&record)
            } else {
                replay.record(&record)
            }
        })();
        result.map_err(|message| LeanExportError {
            line: replay.line,
            message,
        })?;
    }
    let end_line = replay.line.saturating_add(1);
    let failure = |message| LeanExportError {
        line: end_line,
        message,
    };
    if replay.line == 0 {
        return Err(failure("missing export metadata".into()));
    }
    replay.reset_budget().map_err(failure)?;
    if replay.natural_literals {
        replay.check_natural_signature().map_err(failure)?;
    }
    let matches = replay
        .reports
        .iter()
        .filter(|decl| decl.name == target || decl.identity == target)
        .collect::<Vec<_>>();
    if matches.len() != 1 {
        return Err(failure("theorem target is missing or ambiguous".into()));
    }
    if matches[0].kind != "theorem" {
        return Err(failure(
            "the selected export declaration is not a theorem".into(),
        ));
    }
    Ok(LeanExportReport {
        target: matches[0].name.clone(),
        input_sha256: hash::hex(&input_hash.finish()),
        bytes: total,
        records: replay.line as u64,
        declarations: replay.reports,
    })
}

impl Replay {
    fn new() -> Self {
        Self {
            kernel: Kernel::new(),
            names: vec![Name {
                key: "$lean:".into(),
                display: String::new(),
                depth: 0,
            }],
            name_keys: HashSet::from(["$lean:".into()]),
            name_bytes: 0,
            levels: vec![Level::number(0).expect("zero universe")],
            expressions: vec![],
            reports: vec![],
            checked: HashMap::new(),
            dependency_count: 0,
            payload_bytes: 0,
            dependency_bytes: 0,
            transformation_bytes: 0,
            natural_literals: false,
            line: 0,
            digest: String::new(),
        }
    }
    fn reset_budget(&mut self) -> Result<()> {
        // Count even temporary transformations across declarations. A stream
        // cannot retain many individually permitted expanded declarations.
        self.transformation_bytes = self
            .transformation_bytes
            .saturating_add(self.kernel.transformed_bytes);
        if self.transformation_bytes > 256 * 1024 * 1024 {
            return Err("export cumulative transformation allocation limit exceeded; no theorem was established".into());
        }
        self.kernel.reset_budget();
        Ok(())
    }
    fn metadata(&self, value: &Json) -> Result<()> {
        let meta = fields(value, &["meta"])?;
        let meta = fields(&meta["meta"], &["lean", "exporter", "format"])?;
        let lean = fields(&meta["lean"], &["version", "githash"])?;
        let exporter = fields(&meta["exporter"], &["name", "version"])?;
        let format = fields(&meta["format"], &["version"])?;
        if string(&lean["version"])? != LEAN_EXPORT_VERSION
            || string(&lean["githash"])? != LEAN_EXPORT_GITHASH
            || string(&exporter["name"])? != "lean4export"
            || string(&exporter["version"])? != LEAN_EXPORT_FORMAT
            || string(&format["version"])? != LEAN_EXPORT_FORMAT
        {
            return Err(
                "export metadata does not match pinned Lean 4.33.1 / lean4export NDJSON 3.1.0"
                    .into(),
            );
        }
        Ok(())
    }
    fn record(&mut self, value: &Json) -> Result<()> {
        let Json::Object(record) = value else {
            return Err("an export record must be an object".into());
        };
        if record.len() == 2 {
            if record.contains_key("in") {
                return self.name_record(value);
            }
            if record.contains_key("il") {
                return self.level_record(value);
            }
            if record.contains_key("ie") {
                return self.expression_record(value);
            }
        }
        if record.len() != 1 {
            return Err(
                "export records require exactly one tagged form and its matching index".into(),
            );
        }
        let (tag, body) = record.iter().next().ok_or("empty export record")?;
        match tag.as_str() {
            "def" | "thm" | "opaque" => self.definition(tag, body),
            "inductive" => self.inductive(body),
            "axiom" => Err("export axioms are not authorized; no theorem was established".into()),
            "quot" => Err(
                "quotient declarations require an implemented and audited foundation policy".into(),
            ),
            "meta" => Err("export metadata is permitted only as the first record".into()),
            _ => Err(format!("unsupported export record '{tag}'")),
        }
    }
    fn name(&self, value: &Json) -> Result<Name> {
        let id = index(value)?;
        self.names
            .get(id)
            .cloned()
            .ok_or_else(|| "name reference must refer to an earlier record".into())
    }
    fn level(&self, value: &Json) -> Result<Level> {
        self.levels
            .get(index(value)?)
            .cloned()
            .ok_or_else(|| "universe reference must refer to an earlier record".into())
    }
    fn expression(&self, value: &Json) -> Result<T> {
        self.expressions
            .get(index(value)?)
            .map(|(value, _)| value.clone())
            .ok_or_else(|| "expression reference must refer to an earlier record".into())
    }
    fn expression_depth(&self, value: &Json) -> Result<usize> {
        self.expressions
            .get(index(value)?)
            .map(|(_, depth)| *depth)
            .ok_or_else(|| "expression reference must refer to an earlier record".into())
    }
    fn universes(&self, value: &Json) -> Result<Vec<String>> {
        let values = array(value, 32)?;
        let mut names = vec![];
        for value in values {
            let name = self.name(value)?;
            if name.depth == 0 || names.contains(&name.key) {
                return Err("universe parameters must be distinct nonanonymous names".into());
            }
            names.push(name.key);
        }
        Ok(names)
    }
    fn definition(&mut self, tag: &str, body: &Json) -> Result<()> {
        let keys = match tag {
            "def" => &[
                "name",
                "levelParams",
                "type",
                "value",
                "all",
                "hints",
                "safety",
            ][..],
            "opaque" => &["name", "levelParams", "type", "value", "all", "isUnsafe"][..],
            _ => &["name", "levelParams", "type", "value", "all"][..],
        };
        let data = fields(body, keys)?;
        let name = self.name(&data["name"])?;
        if tag == "def" {
            if string(&data["safety"])? != "safe" {
                return Err("unsafe and partial definitions cannot enter the proof kernel".into());
            }
            match &data["hints"] {
                Json::String(hint) if matches!(hint.as_str(), "opaque" | "abbrev") => {}
                Json::Object(_) => {
                    let hints = fields(&data["hints"], &["regular"])?;
                    index(&hints["regular"])?;
                }
                _ => return Err("invalid definition reducibility hint".into()),
            }
        } else if tag == "opaque" && boolean(&data["isUnsafe"])? {
            return Err("unsafe opaque declarations are forbidden".into());
        }
        let group = self.name_list(&data["all"], 64)?;
        if !group.iter().any(|member| member.key == name.key)
            || group.iter().map(|n| &n.key).collect::<HashSet<_>>().len() != group.len()
        {
            return Err(
                "declaration provenance 'all' must contain distinct names including itself".into(),
            );
        }
        let universes = self.universes(&data["levelParams"])?;
        let ty = self.expression(&data["type"])?;
        let value = self.expression(&data["value"])?;
        let dependencies = dependencies(&[ty.clone(), value.clone()])?;
        self.dependencies_known(&dependencies, &[])?;
        self.room(1)?;
        self.reset_budget()?;
        self.kernel
            .definition(&name.key, universes, ty, value, tag == "thm")
            .map_err(|why| format!("declaration '{}': {why}", name.display))?;
        if tag == "opaque" {
            self.kernel
                .declarations
                .get_mut(&name.key)
                .ok_or("missing checked opaque")?
                .value = None;
        }
        self.remember(
            &name,
            if tag == "thm" {
                "theorem"
            } else if tag == "def" {
                "definition"
            } else {
                "opaque"
            },
            dependencies,
        )
    }
    fn name_list(&self, value: &Json, limit: usize) -> Result<Vec<Name>> {
        array(value, limit)?
            .iter()
            .map(|value| self.name(value))
            .collect()
    }
    fn dependencies_known(&self, dependencies: &[String], local: &[String]) -> Result<()> {
        for dependency in dependencies {
            if !self.checked.contains_key(dependency) && !local.contains(dependency) {
                return Err(format!(
                    "unknown or unchecked declaration dependency '{dependency}'"
                ));
            }
        }
        Ok(())
    }
    fn room(&self, more: usize) -> Result<()> {
        if self
            .reports
            .len()
            .checked_add(more)
            .is_none_or(|n| n > MAX_DECLARATIONS)
        {
            return Err("export declaration limit exceeded".into());
        }
        Ok(())
    }
    fn remember(&mut self, name: &Name, kind: &str, dependencies: Vec<String>) -> Result<()> {
        self.dependency_count = self
            .dependency_count
            .checked_add(dependencies.len())
            .ok_or("dependency count overflow")?;
        self.dependency_bytes = dependencies
            .iter()
            .fold(self.dependency_bytes, |total, name| {
                total.saturating_add(name.len() + 32)
            });
        if self.dependency_count > MAX_DEPENDENCIES || self.dependency_bytes > MAX_NAME_BYTES {
            return Err("export dependency manifest limit exceeded".into());
        }
        if name.depth == 0 || self.checked.contains_key(&name.key) {
            return Err("duplicate or anonymous declaration".into());
        }
        self.checked.insert(name.key.clone(), self.reports.len());
        self.reports.push(LeanDeclarationReport {
            name: name.display.clone(),
            identity: name.key.clone(),
            kind: kind.into(),
            line: self.line,
            sha256: self.digest.clone(),
            dependencies,
        });
        Ok(())
    }
}

fn fields<'a>(value: &'a Json, keys: &[&str]) -> Result<&'a BTreeMap<String, Json>> {
    let Json::Object(data) = value else {
        return Err("export form requires an object".into());
    };
    if data.len() != keys.len() || !keys.iter().all(|key| data.contains_key(*key)) {
        return Err(format!(
            "export form requires exactly these fields: {}",
            keys.join(", ")
        ));
    }
    Ok(data)
}
fn array(value: &Json, limit: usize) -> Result<&[Json]> {
    let Json::Array(values) = value else {
        return Err("export form requires an array".into());
    };
    if values.len() > limit {
        return Err("export array limit exceeded".into());
    }
    Ok(values)
}
fn index(value: &Json) -> Result<usize> {
    let Json::Number(value) = value else {
        return Err("export indices require unsigned decimal integers".into());
    };
    if value.is_empty() || !value.bytes().all(|b| b.is_ascii_digit()) {
        return Err("export indices require unsigned decimal integers".into());
    }
    let value: u32 = value.parse().map_err(|_| "export index exceeds u32")?;
    Ok(value as usize)
}
fn string(value: &Json) -> Result<&str> {
    value
        .string()
        .ok_or_else(|| "export form requires a string".into())
}
fn boolean(value: &Json) -> Result<bool> {
    if let Json::Bool(value) = value {
        Ok(*value)
    } else {
        Err("export form requires a boolean".into())
    }
}
fn text_json(value: &str) -> Json {
    Json::String(value.into())
}
fn number_json(value: u64) -> Json {
    Json::Number(value.to_string())
}
fn object<const N: usize>(values: [(&str, Json); N]) -> Json {
    Json::Object(values.into_iter().map(|(k, v)| (k.into(), v)).collect())
}

fn dependencies(roots: &[T]) -> Result<Vec<String>> {
    let mut stack = roots.to_vec();
    let mut seen = HashSet::new();
    let mut names = BTreeSet::new();
    let mut bytes = 0usize;
    while let Some(value) = stack.pop() {
        if !seen.insert(Arc::as_ptr(&value) as usize) {
            continue;
        }
        if seen.len() > MAX_EXPRESSIONS {
            return Err("export dependency traversal limit exceeded".into());
        }
        match value.as_ref() {
            Term::Global(name, _) => {
                names.insert(name.clone());
            }
            Term::Pi(a, b)
            | Term::Lam(a, b)
            | Term::App(a, b)
            | Term::Sigma(a, b)
            | Term::Refl(a, b) => {
                stack.push(a.clone());
                stack.push(b.clone());
            }
            Term::Let(a, b, c) | Term::Pair(a, b, c) | Term::Eq(a, b, c) => {
                stack.extend([a.clone(), b.clone(), c.clone()])
            }
            Term::First(a) | Term::Second(a) => stack.push(a.clone()),
            Term::Project {
                family, subject, ..
            } => {
                names.insert(family.clone());
                stack.push(subject.clone());
            }
            Term::Ctor {
                family,
                constructor,
                parameters,
                fields,
                ..
            } => {
                names.insert(family.clone());
                names.insert(constructor.clone());
                stack.extend(parameters.iter().chain(fields).cloned());
            }
            Term::Induct {
                family,
                parameters,
                indices,
                motive,
                branches,
                subject,
                ..
            } => {
                names.insert(family.clone());
                stack.extend(parameters.iter().chain(indices).chain(branches).cloned());
                stack.extend([motive.clone(), subject.clone()]);
            }
            Term::MutualInduct {
                family,
                parameters,
                indices,
                cases,
                subject,
                ..
            } => {
                names.insert(family.clone());
                stack.extend(parameters.iter().chain(indices).cloned());
                stack.push(subject.clone());
                for case in cases {
                    names.insert(case.family.clone());
                    stack.push(case.motive.clone());
                    stack.extend(case.branches.iter().cloned());
                }
            }
            Term::EqElim {
                ty,
                left,
                motive,
                base,
                right,
                proof,
            } => stack.extend([
                ty.clone(),
                left.clone(),
                motive.clone(),
                base.clone(),
                right.clone(),
                proof.clone(),
            ]),
            Term::Recur(..) | Term::SelfType | Term::SelfAt(_) => {
                return Err("unexpanded recursive marker in export evidence".into())
            }
            Term::Sort(_) | Term::Var(_) => {}
        }
    }
    for name in &names {
        bytes = bytes.saturating_add(name.len() + 32);
        if bytes > MAX_NAME_BYTES {
            return Err("export dependency byte limit exceeded".into());
        }
    }
    Ok(names.into_iter().collect())
}
