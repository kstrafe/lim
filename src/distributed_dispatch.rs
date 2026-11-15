//! Final, closed dispatch collection. The emitted ordinary function is the
//! implementation consumed by the normal compiler, including cache hits.
use crate::{
    source_error::SourceError, DiagnosticCode, Expr, Function, Item, SourceFile, Span, SpannedExpr,
    Type,
};
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    path::{Path, PathBuf},
};

fn parts(form: &SpannedExpr) -> &[Expr] {
    match &form.expr {
        Expr::List(items) => items,
        _ => &[],
    }
}
fn child(form: &SpannedExpr, index: usize) -> &SpannedExpr {
    form.children.get(index).unwrap_or(form)
}
fn head(form: &SpannedExpr) -> &str {
    match parts(form).first() {
        Some(Expr::Symbol(name)) => name,
        _ => "",
    }
}
fn name(form: &SpannedExpr) -> Result<String, SourceError> {
    match &form.expr {
        Expr::Symbol(name)
            if crate::file_access::split(name).is_some()
                || (!name.starts_with(['#', '@']) && name != "$") =>
        {
            Ok(name.clone())
        }
        _ => Err(error("expected a declaration name", form.span)),
    }
}
fn error(message: impl Into<String>, span: Span) -> SourceError {
    SourceError::new(message, DiagnosticCode::Generator).at(span)
}
fn sym(name: &str) -> Expr {
    Expr::Symbol(name.to_owned())
}
fn list(items: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::List(items.into_iter().collect())
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Registration {
    pub dispatcher: String,
    pub variant: String,
    pub handler: String,
    pub source: SpannedExpr,
    pub generated_case: Option<Span>,
    pub generated_case_keyword: Option<Span>,
    pub generated_variant: Option<Span>,
    pub generated_handler: Option<Span>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Manifest {
    pub name: String,
    pub declaration: SpannedExpr,
    pub generated_path: PathBuf,
    pub source_id: u32,
    pub registrations: Vec<Registration>,
}

impl Manifest {
    pub(crate) fn remap_sources(&mut self, sources: &[u32]) {
        fn remap(span: &mut Span, sources: &[u32]) {
            span.source_id = sources[span.source_id as usize];
        }
        fn tree(node: &mut SpannedExpr, sources: &[u32]) {
            remap(&mut node.span, sources);
            for child in &mut node.children {
                tree(child, sources);
            }
        }
        self.source_id = sources[self.source_id as usize];
        tree(&mut self.declaration, sources);
        for registration in &mut self.registrations {
            tree(&mut registration.source, sources);
            for span in [
                &mut registration.generated_case,
                &mut registration.generated_case_keyword,
                &mut registration.generated_variant,
                &mut registration.generated_handler,
            ]
            .into_iter()
            .flatten()
            {
                remap(span, sources);
            }
        }
    }
}

/// Attach current-compilation registration and handler origins to emitted-case
/// errors. Cache comments are display data, never a source of authority/spans.
pub(crate) fn diagnostic_origins(
    program: &crate::Program,
    span: Span,
) -> Vec<(Span, &'static str)> {
    let mut result = Vec::new();
    for manifest in &program.dispatch_manifests {
        for registration in &manifest.registrations {
            let Some(case) = registration.generated_case else {
                continue;
            };
            if case.source_id != span.source_id || case.start > span.start || span.end > case.end {
                continue;
            }
            result.push((registration.source.span, "dispatch case registered here"));
            if let Some(handler) = program
                .declaration_expressions
                .get(&registration.handler)
                .and_then(|node| node.children.get(1))
            {
                result.push((handler.span, "dispatch handler defined here"));
            }
        }
    }
    result.sort_by_key(|(span, message)| (span.source_id, span.start, span.end, *message));
    result.dedup();
    result
}

thread_local! {
    static MANIFESTS: RefCell<Option<Vec<Manifest>>> = const { RefCell::new(None) };
}

/// Editor callers can capture the current compilation's map without expanding
/// Program's construction interface or trusting persisted origin comments.
pub fn with_manifest<R>(operation: impl FnOnce() -> R) -> (R, Vec<Manifest>) {
    struct Restore(Option<Vec<Manifest>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            MANIFESTS.with(|maps| {
                maps.replace(self.0.take());
            });
        }
    }
    let _restore = Restore(MANIFESTS.with(|maps| maps.replace(Some(Vec::new()))));
    let result = operation();
    let maps = MANIFESTS.with(|maps| maps.borrow_mut().take().unwrap());
    (result, maps)
}

fn record_manifest(artifact: &Artifact, files: &[SourceFile]) {
    MANIFESTS.with(|maps| {
        if let Some(maps) = maps.borrow_mut().as_mut() {
            maps.push(artifact.manifest(files));
        }
    });
}

fn generated_case(
    form: &SpannedExpr,
    variant: &str,
    handler: &str,
) -> Option<(Span, Span, Span, Span)> {
    if matches!(
        head(form),
        "#case" | "#case-ref" | "#case-ref-mut" | "#case-pin" | "#case-pin-mut"
    ) {
        let pattern = child(form, 1);
        let selected = if matches!(pattern.expr, Expr::List(_)) {
            child(pattern, 0)
        } else {
            pattern
        };
        if matches!(&selected.expr, Expr::Symbol(name) if name == variant) {
            fn handler_span(form: &SpannedExpr, handler: &str) -> Option<Span> {
                if head(form) == "#call"
                    && matches!(&child(form, 1).expr, Expr::Symbol(name) if name == handler)
                {
                    return Some(child(form, 1).span);
                }
                form.children
                    .iter()
                    .find_map(|child| handler_span(child, handler))
            }
            return Some((
                form.span,
                child(form, 0).span,
                selected.span,
                handler_span(child(form, 2), handler)?,
            ));
        }
    }
    form.children
        .iter()
        .find_map(|child| generated_case(child, variant, handler))
}

/// Current-compilation manifest for editor sidecars. It does not confer
/// authority; all handler access is checked before materialization.
pub(crate) struct Artifact {
    pub(crate) key: String,
    pub(crate) source: String,
    pub(crate) origins: Vec<String>,
    pub(crate) declaration: SpannedExpr,
    pub(crate) registrations: Vec<Registration>,
    pub(crate) source_id: u32,
    pub(crate) name: String,
}

impl Artifact {
    pub(crate) fn manifest(&self, files: &[SourceFile]) -> Manifest {
        Manifest {
            name: self.name.clone(),
            declaration: self.declaration.clone(),
            generated_path: files[self.source_id as usize].path.clone(),
            source_id: self.source_id,
            registrations: self.registrations.clone(),
        }
    }

    pub(crate) fn publish(
        &self,
        directory: &Path,
        files: &[SourceFile],
        invocations: &HashMap<u32, Span>,
    ) -> Result<(), SourceError> {
        let materialized = files.get(self.source_id as usize).ok_or_else(|| {
            error(
                "missing materialized dispatch source",
                self.declaration.span,
            )
        })?;
        if materialized.source != self.source {
            return Err(error(
                "dispatch source changed after materialization",
                self.declaration.span,
            ));
        }
        crate::generator::cached_generated_source_with_origins(
            directory,
            &self.key,
            &self.origins,
            || Ok(self.source.clone()),
        )?;
        let path = crate::generator::cached_generated_source_path(directory, &self.key);
        let paths = files
            .iter()
            .map(|file| file.path.clone())
            .collect::<Vec<_>>();
        for source in std::iter::once(&self.declaration).chain(
            self.registrations
                .iter()
                .map(|registration| &registration.source),
        ) {
            let mut span = source.span;
            let mut nested = false;
            for _ in 0..=files.len() {
                crate::generated_lookup::record(
                    span,
                    &paths,
                    &path,
                    &format!("#dispatch-fn {}", self.name),
                    nested,
                );
                let Some(parent) = invocations.get(&span.source_id) else {
                    break;
                };
                span = *parent;
                nested = true;
            }
        }
        Ok(())
    }
}

struct Declaration {
    source: SpannedExpr,
    function: Function,
    fields: HashMap<String, SpannedExpr>,
    controlled: String,
    enum_name: String,
    mode: Mode,
}

#[derive(Clone, Copy)]
enum Mode {
    Owned,
    Ref(bool),
    Pin(bool),
}
impl Mode {
    fn case(self) -> &'static str {
        match self {
            Self::Owned => "#case",
            Self::Ref(false) => "#case-ref",
            Self::Ref(true) => "#case-ref-mut",
            Self::Pin(false) => "#case-pin",
            Self::Pin(true) => "#case-pin-mut",
        }
    }
    fn payload(self, ty: Type) -> Type {
        match self {
            Self::Owned => ty,
            Self::Ref(mutable) => Type::Reference {
                mutable,
                target: Box::new(ty),
            },
            Self::Pin(mutable) => Type::PinnedReference {
                mutable,
                target: Box::new(ty),
            },
        }
    }
}

fn signature(expression: &Expr, external: bool) -> Result<Function, String> {
    let header = match expression {
        Expr::List(items) => list(items.iter().take(if external { 5 } else { 4 }).cloned()),
        _ => expression.clone(),
    };
    let Expr::List(items) = crate::normalize_keywords(header) else {
        unreachable!()
    };
    crate::parse_function_parts(&items, external, false)
}

fn declaration(
    source: &SpannedExpr,
    aliases: &HashMap<String, Type>,
) -> Result<Declaration, SourceError> {
    if parts(source).len() != 3 {
        return Err(error(
            "#dispatch-fn requires a name and declaration record",
            source.span,
        ));
    }
    let function_name = name(child(source, 1))?;
    crate::names::require(&function_name, "value")
        .map_err(|message| error(message, child(source, 1).span))?;
    let record = child(source, 2);
    if !matches!(record.expr, Expr::List(_)) {
        return Err(error(
            "#dispatch-fn requires a declaration record",
            record.span,
        ));
    }
    let mut fields = HashMap::new();
    for field in &record.children {
        if parts(field).len() != 2 {
            return Err(error(
                "dispatch declaration fields require (key value) pairs",
                field.span,
            ));
        }
        let key = match &child(field, 0).expr {
            Expr::Symbol(name) => name.as_str(),
            _ => "",
        };
        if !matches!(
            key,
            "#params"
                | "#returns"
                | "#dispatch-on"
                | "#effects"
                | "#requires"
                | "#ensures"
                | "#preserves"
        ) {
            return Err(error(
                format!("unknown #dispatch-fn section '{key}'"),
                child(field, 0).span,
            ));
        }
        if fields
            .insert(key.to_owned(), child(field, 1).clone())
            .is_some()
        {
            return Err(error(
                format!("duplicate #dispatch-fn section '{key}'"),
                child(field, 0).span,
            ));
        }
    }
    for key in ["#params", "#returns", "#dispatch-on"] {
        if !fields.contains_key(key) {
            return Err(error(
                format!("#dispatch-fn record requires '{key}'"),
                record.span,
            ));
        }
    }
    let controlled = name(&fields["#dispatch-on"])?;
    let fn_expr = list([
        sym("#fn"),
        sym(&function_name),
        fields["#params"].expr.clone(),
        fields["#returns"].expr.clone(),
    ]);
    let function =
        signature(&fn_expr, false).map_err(|message| error(message, fields["#params"].span))?;
    let Some(parameter) = function
        .parameters
        .iter()
        .find(|parameter| parameter.name == controlled)
    else {
        return Err(error(
            format!("dispatch parameter '{controlled}' is not declared in #params"),
            fields["#dispatch-on"].span,
        ));
    };
    let ty = crate::typed_ir::resolve_type(&parameter.ty, aliases)
        .map_err(|message| error(message, fields["#params"].span))?;
    let (mode, selected) = match ty {
        Type::Reference { mutable, target } => (Mode::Ref(mutable), *target),
        Type::PinnedReference { mutable, target } => (Mode::Pin(mutable), *target),
        ty => (Mode::Owned, ty),
    };
    let Type::Named(enum_name) = selected else {
        return Err(error(
            "dispatch parameter must be an enum or an ordinary/pinned reference to an enum",
            fields["#params"].span,
        ));
    };
    Ok(Declaration {
        source: source.clone(),
        function,
        fields,
        controlled,
        enum_name,
        mode,
    })
}

fn location(files: &[SourceFile], mut span: Span, invocations: &HashMap<u32, Span>) -> String {
    for _ in 0..=files.len() {
        let Some(parent) = invocations.get(&span.source_id) else {
            break;
        };
        span = *parent;
    }
    let path = files.get(span.source_id as usize).map_or_else(
        || "<source>".to_owned(),
        |file| file.path.display().to_string(),
    );
    format!("{}:{}", path.replace(['\r', '\n'], " "), span.line)
}

/// Render structural schemas rather than compiler-owned interning names. The
/// resulting source still passes the ordinary record lowering and validation.
struct RecordSource<'a> {
    shapes: &'a HashMap<String, Vec<crate::Field>>,
    aliases: &'a HashMap<String, Type>,
}
impl RecordSource<'_> {
    fn type_expression(&self, ty: &Type) -> Result<Expr, String> {
        // Equivalent structural layouts may retain field spellings from a
        // different module. Emit resolved types rather than that module's
        // private scalar aliases; ordinary underlying-type visibility remains.
        let resolved = crate::typed_ir::resolve_type(ty, self.aliases)?;
        Ok(crate::parse(&crate::type_source(&resolved))?.remove(0).expr)
    }

    fn fields(&self, name: &str) -> Option<&[crate::Field]> {
        let Type::Named(owner) =
            crate::typed_ir::resolve_type(&Type::Named(name.into()), self.aliases).ok()?
        else {
            return None;
        };
        self.shapes.get(&owner).map(Vec::as_slice)
    }

    fn pairs(&self, expression: &Expr) -> Result<String, String> {
        let Expr::List(entries) = expression else {
            return Err("expected generated record pairs".into());
        };
        let mut source = String::from("{");
        for entry in entries {
            let Expr::List(pair) = entry else {
                return Err("expected generated record entry".into());
            };
            if pair.len() != 2 {
                return Err("expected generated record key and value".into());
            }
            source.push_str(&format!(
                " {} = {};",
                crate::expression_source(&pair[0])?,
                self.expression(&pair[1])?
            ));
        }
        source.push_str(" }");
        Ok(source)
    }

    fn expression(&self, expression: &Expr) -> Result<String, String> {
        if let Expr::Symbol(name) = expression {
            if let Some(fields) = self.fields(name) {
                let entries = fields
                    .iter()
                    .map(|field| Ok(list([sym(&field.name), self.type_expression(&field.ty)?])))
                    .collect::<Result<Vec<_>, String>>()?;
                return self.pairs(&list(entries));
            }
        }
        let Expr::List(parts) = expression else {
            return crate::expression_source(expression);
        };
        match parts.as_slice() {
            [Expr::Symbol(head), pattern, Expr::Symbol(equal), call]
                if head == "#let" && equal == "=" =>
            {
                Ok(format!(
                    "(#let {} = {})",
                    self.pairs(pattern)?,
                    self.expression(call)?
                ))
            }
            [Expr::Symbol(head), schema, values] if head == "#record-literal" => Ok(format!(
                "(#record-literal {} {})",
                self.expression(schema)?,
                self.pairs(values)?
            )),
            _ => Ok(format!(
                "({})",
                parts
                    .iter()
                    .map(|part| self.expression(part))
                    .collect::<Result<Vec<_>, _>>()?
                    .join(" ")
            )),
        }
    }

    fn function(&self, expression: &Expr) -> Result<String, String> {
        if self.shapes.is_empty() {
            return crate::declaration_source(expression);
        }
        let Expr::List(parts) = expression else {
            unreachable!()
        };
        let parameters = match &parts[2] {
            Expr::List(parameters) if parameters.iter().all(|parameter| matches!(parameter,
                Expr::List(pair) if pair.len() == 2 && matches!(pair.first(), Some(Expr::Symbol(name)) if !name.starts_with('#')))) => self.pairs(&parts[2])?,
            parameters => self.expression(parameters)?,
        };
        let mut source = format!(
            "#fn {} {{\n  #params = {parameters};\n  #returns = {};\n",
            crate::expression_source(&parts[1])?,
            self.expression(&parts[3])?
        );
        let mut index = 4;
        if let Some(Expr::List(clause)) = parts
            .get(index)
            .filter(|part| crate::effects::is_clause(part))
        {
            source.push_str(&format!("  #effects = {};\n", self.expression(&clause[1])?));
            index += 1;
        }
        let mut contracts: BTreeMap<&str, Vec<Expr>> = BTreeMap::new();
        while let Some(Expr::List(clause)) = parts.get(index) {
            let Some(Expr::Symbol(head)) = clause.first() else {
                break;
            };
            if !matches!(head.as_str(), "#requires" | "#ensures" | "#preserves") {
                break;
            }
            contracts.entry(head).or_default().push(clause[1].clone());
            index += 1;
        }
        for (head, predicates) in contracts {
            source.push_str(&format!(
                "  {head} = {};\n",
                self.expression(&list(predicates))?
            ));
        }
        source.push_str("  #body = (\n");
        for statement in &parts[index..] {
            source.push_str(&format!("    {}\n", self.expression(statement)?));
        }
        source.push_str("  );\n}");
        Ok(source)
    }
}

fn emit(
    declaration: &Declaration,
    variants: &[crate::EnumVariant],
    registrations: &BTreeMap<String, Vec<Registration>>,
    forbidden: &HashSet<String>,
    records: &RecordSource<'_>,
) -> Result<Expr, SourceError> {
    let mut used = forbidden.clone();
    used.extend(
        declaration
            .function
            .parameters
            .iter()
            .map(|parameter| parameter.name.clone()),
    );
    let mut serial = 0;
    let mut cases = vec![sym("#match"), sym(&declaration.controlled)];
    for variant in variants {
        let payload = if variant.fields.is_empty() {
            None
        } else {
            loop {
                let candidate = format!("dispatch-payload-{serial}");
                serial += 1;
                if used.insert(candidate.clone()) {
                    break Some(candidate);
                }
            }
        };
        let registration = &registrations[&variant.name][0];
        let mut arguments = Vec::new();
        for parameter in &declaration.function.parameters {
            let value = if parameter.name == declaration.controlled {
                let Some(payload) = &payload else {
                    continue;
                };
                payload.as_str()
            } else {
                parameter.name.as_str()
            };
            arguments.push(list([sym(&parameter.name), sym(value)]));
        }
        let pattern = match payload {
            Some(payload) => list([sym(&variant.name), sym(&payload)]),
            None => sym(&variant.name),
        };
        let mut result = list([sym("#call"), sym(&registration.handler), list(arguments)]);
        let returned =
            crate::typed_ir::resolve_type(&declaration.function.return_type, records.aliases)
                .map_err(|message| error(message, declaration.fields["#returns"].span))?;
        if let Type::Named(owner) = &returned {
            if let Some(fields) = records.shapes.get(owner) {
                let mut bindings = Vec::new();
                let mut values = Vec::new();
                for field in fields {
                    let local = loop {
                        let candidate = format!("dispatch-result-{serial}");
                        serial += 1;
                        if used.insert(candidate.clone()) {
                            break candidate;
                        }
                    };
                    bindings.push(list([
                        sym(&field.name),
                        list([
                            sym("#bind"),
                            sym(&local),
                            records.type_expression(&field.ty)?,
                        ]),
                    ]));
                    values.push(list([sym(&field.name), sym(&local)]));
                }
                result = list([
                    sym("#block"),
                    list([sym("#let"), list(bindings), sym("="), result]),
                    list([sym("#record-literal"), sym(owner), list(values)]),
                ]);
            }
        }
        cases.push(list([sym(declaration.mode.case()), pattern, result]));
    }
    let mut function = vec![
        sym("#fn"),
        sym(&declaration.function.name),
        declaration.fields["#params"].expr.clone(),
        declaration.fields["#returns"].expr.clone(),
    ];
    if let Some(effects) = declaration.fields.get("#effects") {
        crate::effects::Declaration::parse(&effects.expr)
            .map_err(|message| error(message, effects.span))?;
        function.push(list([sym("#effects"), effects.expr.clone()]));
    }
    for section in ["#requires", "#ensures", "#preserves"] {
        if let Some(value) = declaration.fields.get(section) {
            let Expr::List(predicates) = &value.expr else {
                return Err(error(
                    "contract sections require predicate lists",
                    value.span,
                ));
            };
            if matches!(predicates.first(), Some(Expr::Symbol(_))) {
                function.push(list([sym(section), value.expr.clone()]));
            } else {
                for predicate in predicates {
                    function.push(list([sym(section), predicate.clone()]));
                }
            }
        }
    }
    function.push(list([sym("#return"), list(cases)]));
    Ok(list(function))
}

pub(crate) fn materialize(
    forms: Vec<SpannedExpr>,
    files: &mut Vec<SourceFile>,
    invocations: &mut HashMap<u32, Span>,
    origins: &mut crate::generator::Origins,
    cache: Option<&Path>,
) -> Result<(Vec<SpannedExpr>, Vec<Artifact>), SourceError> {
    if !forms
        .iter()
        .any(|form| matches!(head(form), "#dispatch-fn" | "#dispatch-case"))
    {
        return Ok((forms, Vec::new()));
    }
    let mut aliases = HashMap::new();
    let mut enums = HashMap::new();
    let mut functions = HashMap::new();
    let mut record_shapes = HashMap::new();
    let mut forbidden = HashSet::new();
    for form in &forms {
        for name in crate::generator_provenance::declared_names(&form.expr) {
            forbidden.insert(crate::file_access::local_name(name).to_owned());
        }
        match head(form) {
            "#type" | "#enum" | "#struct"
                if head(form) != "#struct"
                    || matches!(&child(form, 1).expr,
                    Expr::Symbol(name) if crate::anonymous_records::is_record(name)) =>
            {
                let item = crate::parse_item(&crate::normalize_keywords(form.expr.clone()))
                    .map_err(|message| error(message, form.span))?;
                match item {
                    Item::TypeAlias { name, target, .. } => {
                        aliases.insert(name, target);
                    }
                    Item::Enum { name, variants, .. } => {
                        enums.insert(name, (variants, form.clone()));
                    }
                    Item::Struct { name, fields, .. }
                        if crate::anonymous_records::is_record(&name) =>
                    {
                        record_shapes.insert(name, fields);
                    }
                    _ => {}
                }
            }
            "#fn" | "#unsafe-fn" | "#extern-fn" => {
                let external = head(form) == "#extern-fn";
                let mut function = signature(&form.expr, external)
                    .map_err(|message| error(message, child(form, 1).span))?;
                function.unsafe_call |= head(form) == "#unsafe-fn";
                functions.insert(function.name.clone(), (function, form.clone()));
            }
            _ => {}
        }
    }
    // Parser-backed builtins expose concrete declarations without executing
    // another user-generator phase. Keep their ordinary enum/alias/signature
    // metadata available to dispatch just as it is to the later parser.
    for form in &forms {
        if !matches!(parts(form).first(), Some(Expr::Generate)) {
            continue;
        }
        let kind = match parts(form).get(1) {
            Some(Expr::Symbol(name)) => name.as_str(),
            _ => continue,
        };
        if !matches!(
            kind,
            "#optional" | "#result" | "#array" | "#vec" | "#vec-alloc" | "#vec-sort"
        ) {
            continue;
        }
        let invocation =
            crate::generator::builtins::normalize_builtin_generator_invocation(&form.expr)?;
        let Expr::List(items) = crate::normalize_keywords(invocation) else {
            unreachable!()
        };
        for item in
            crate::parse_generated_items(&items).map_err(|message| error(message, form.span))?
        {
            match item {
                Item::Enum { name, variants, .. } => {
                    enums.insert(name, (variants, form.clone()));
                }
                Item::TypeAlias { name, target, .. } => {
                    aliases.insert(name, target);
                }
                Item::Function(function) => {
                    functions.insert(function.name.clone(), (function, form.clone()));
                }
                _ => {}
            }
        }
    }
    let mut declarations = BTreeMap::new();
    for form in forms.iter().filter(|form| head(form) == "#dispatch-fn") {
        let declaration = declaration(form, &aliases)?;
        let name = declaration.function.name.clone();
        if let Some((_, previous)) = functions.get(&name) {
            return Err(error(
                format!("dispatch function '{name}' conflicts with an ordinary function"),
                child(form, 1).span,
            )
            .with_label(child(previous, 1).span, "ordinary function declaration"));
        }
        if let Some(previous) = declarations.insert(name.clone(), declaration) {
            return Err(error(
                format!("duplicate dispatch declaration '{name}'"),
                child(form, 1).span,
            )
            .with_label(previous.source.span, "previous dispatcher declaration"));
        }
    }
    for declaration in declarations.values() {
        functions.insert(
            declaration.function.name.clone(),
            (declaration.function.clone(), declaration.source.clone()),
        );
    }
    let mut extra_declarations = HashMap::new();
    for (name, (_, source)) in &functions {
        extra_declarations.insert(name.clone(), source.span);
    }
    for (name, (variants, source)) in &enums {
        extra_declarations.insert(name.clone(), source.span);
        for variant in variants {
            extra_declarations.insert(variant.name.clone(), source.span);
        }
    }
    let visibility = crate::library::Visibility::for_dispatch(
        &forms,
        files,
        invocations,
        &origins.definitions,
        &extra_declarations,
    )?;
    let mut cases: BTreeMap<String, BTreeMap<String, Vec<Registration>>> = BTreeMap::new();
    for source in forms.iter().filter(|form| head(form) == "#dispatch-case") {
        if parts(source).len() != 4 {
            return Err(error(
                "#dispatch-case requires dispatcher, variant and handler names",
                source.span,
            ));
        }
        let dispatcher = name(child(source, 1))?;
        let variant = name(child(source, 2))?;
        let handler = name(child(source, 3))?;
        let Some(declaration) = declarations.get(&dispatcher) else {
            return Err(error(
                format!("unknown dispatch function '{dispatcher}'"),
                child(source, 1).span,
            ));
        };
        let Some((variants, enum_source)) = enums.get(&declaration.enum_name) else {
            return Err(error(
                format!(
                    "dispatch parameter type '{}' is not a concrete enum",
                    declaration.enum_name
                ),
                declaration.fields["#params"].span,
            ));
        };
        let Some(payload) = variants.iter().find(|candidate| candidate.name == variant) else {
            return Err(error(
                format!(
                    "variant '{variant}' is not in dispatch enum '{}'",
                    declaration.enum_name
                ),
                child(source, 2).span,
            )
            .with_label(enum_source.span, "dispatch enum"));
        };
        visibility.access(&dispatcher, child(source, 1).span, false)?;
        visibility.access(&variant, child(source, 2).span, false)?;
        visibility.access(&variant, declaration.source.span, false)?;
        visibility.access(&handler, child(source, 3).span, false)?;
        visibility
            .access(&handler, declaration.source.span, false)
            .map_err(|failure| {
                failure.with_label(
                    child(source, 3).span,
                    "handler registered here; registration grants no additional authority",
                )
            })?;
        let Some((function, handler_source)) = functions.get(&handler) else {
            return Err(error(
                format!("unknown dispatch handler '{handler}'"),
                child(source, 3).span,
            ));
        };
        let mismatch = |message: String| {
            error(message, child(source, 3).span)
                .with_label(declaration.source.span, "dispatcher declaration")
                .with_label(
                    child(handler_source, if function.external { 2 } else { 1 }).span,
                    "handler declaration",
                )
        };
        if function.external || function.unsafe_call {
            return Err(mismatch(format!(
                "dispatch handler '{handler}' must be an ordinary safe function"
            )));
        }
        if payload.fields.len() > 1 {
            return Err(mismatch(format!(
                "dispatch variant '{variant}' must have zero or one payload"
            )));
        }
        let resolve = |ty: &Type| {
            crate::typed_ir::resolve_type(ty, &aliases).map_err(|message| mismatch(message))
        };
        if resolve(&function.return_type)? != resolve(&declaration.function.return_type)? {
            return Err(mismatch(format!(
                "dispatch handler '{handler}' has an incompatible return type"
            )));
        }
        let mut expected = BTreeMap::new();
        for parameter in &declaration.function.parameters {
            if parameter.name == declaration.controlled {
                if let Some(ty) = payload.fields.first() {
                    expected.insert(
                        parameter.name.as_str(),
                        declaration.mode.payload(ty.clone()),
                    );
                }
            } else {
                expected.insert(parameter.name.as_str(), parameter.ty.clone());
            }
        }
        if function.parameters.len() != expected.len() {
            return Err(mismatch(format!(
                "dispatch handler '{handler}' has incompatible named parameters"
            )));
        }
        for parameter in &function.parameters {
            let Some(expected) = expected.get(parameter.name.as_str()) else {
                return Err(mismatch(format!(
                    "dispatch handler '{handler}' has unexpected parameter '{}'",
                    parameter.name
                )));
            };
            if resolve(&parameter.ty)? != resolve(expected)? {
                return Err(mismatch(format!("dispatch handler '{handler}' parameter '{}' has an incompatible payload or forwarding type", parameter.name)));
            }
        }
        let registration = Registration {
            dispatcher: dispatcher.clone(),
            variant: variant.clone(),
            handler: handler.clone(),
            source: source.clone(),
            generated_case: None,
            generated_case_keyword: None,
            generated_variant: None,
            generated_handler: None,
        };
        let previous = cases
            .entry(dispatcher)
            .or_default()
            .entry(variant.clone())
            .or_default();
        if let Some(first) = previous.first() {
            if first.handler != handler {
                return Err(error(
                    format!("conflicting handlers for dispatch variant '{variant}'"),
                    child(source, 3).span,
                )
                .with_label(first.source.span, "previous dispatch registration"));
            }
        }
        previous.push(registration);
    }
    let mut replacements = HashMap::new();
    let mut artifacts = Vec::new();
    for (name, declaration) in declarations {
        let Some((variants, enum_source)) = enums.get(&declaration.enum_name) else {
            return Err(error(
                format!(
                    "dispatch parameter type '{}' is not a concrete enum",
                    declaration.enum_name
                ),
                declaration.fields["#params"].span,
            ));
        };
        let registrations = cases.remove(&name).unwrap_or_default();
        for (index, variant) in variants.iter().enumerate() {
            if !registrations.contains_key(&variant.name) {
                return Err(error(
                    format!(
                        "dispatch function '{name}' is missing a handler for '{}'",
                        variant.name
                    ),
                    child(&declaration.source, 1).span,
                )
                .with_label(
                    child(child(enum_source, 3), index).span,
                    "uncovered enum variant",
                ));
            }
        }
        let record_source = RecordSource {
            shapes: &record_shapes,
            aliases: &aliases,
        };
        let expression = emit(
            &declaration,
            variants,
            &registrations,
            &forbidden,
            &record_source,
        )?;
        let definition = crate::generator_authority::source_context(
            declaration.source.span,
            &origins.definitions,
        )
        .unwrap_or(declaration.source.span);
        let context_header =
            origins.context_header("#dispatch-fn", definition, declaration.source.span);
        let header = &context_header[1..context_header.len() - 1];
        let mut registrations = registrations.into_values().flatten().collect::<Vec<_>>();
        let locations = std::iter::once(declaration.source.span)
            .chain(
                registrations
                    .iter()
                    .map(|registration| registration.source.span),
            )
            .chain(registrations.iter().filter_map(|registration| {
                functions
                    .get(&registration.handler)
                    .map(|(_, source)| child(source, 1).span)
            }))
            .map(|span| location(files, span, invocations))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        // Origin comments are outside key material; adding an identical
        // registration preserves the same implementation and artifact path.
        let resolved_cases = registrations
            .iter()
            .map(|registration| {
                (
                    &registration.dispatcher,
                    &registration.variant,
                    &registration.handler,
                )
            })
            .collect::<BTreeSet<_>>();
        let resolved_enum = variants
            .iter()
            .map(|variant| {
                Ok((
                    variant.name.clone(),
                    variant
                        .fields
                        .iter()
                        .map(|ty| crate::typed_ir::resolve_type(ty, &aliases))
                        .collect::<Result<Vec<_>, _>>()?,
                ))
            })
            .collect::<Result<Vec<_>, String>>()?;
        let raw = format!("{header}\n{}", record_source.function(&expression)?);
        // Alias names alone do not identify an expanded structural schema.
        // Hash the actual emitted implementation before origin comments so a
        // warm cache cannot retain an earlier return layout behind that alias.
        let key = format!("lim-distributed-dispatch-v1\ncompiler={}\nimplementation={}\ndeclaration={:?}\nenum={:?}\nresolved-enum={resolved_enum:?}\ncases={resolved_cases:?}\nsource={:032x}\nlowering={:032x}\ncontext={context_header}", env!("CARGO_PKG_VERSION"), env!("LIM_BUILD_FINGERPRINT"), declaration.source.expr, enum_source.expr, crate::generator::stable_hash(raw.as_bytes()), crate::generator::stable_hash(include_bytes!("distributed_dispatch.rs")));
        let text = if let Some(cache) = cache {
            crate::generator::cached_generated_source_with_origins(cache, &key, &locations, || {
                Ok(raw.clone())
            })?
        } else {
            crate::generator::annotate_generated_source(
                &crate::generator::format_generated_source(&raw)?,
                &locations,
            )
        };
        let path = cache
            .map(|cache| crate::generator::cached_generated_source_path(cache, &key))
            .unwrap_or_else(|| PathBuf::from(format!("<dispatch {name}>")));
        let source_id = u32::try_from(files.len())
            .map_err(|_| error("too many dispatch source files", declaration.source.span))?;
        let mut parsed = crate::parse_source_unit(&text)
            .map_err(|message| error(message, declaration.source.span))?;
        parsed.retain(|form| !crate::generator_authority::is_header(&form.expr));
        if parsed.len() != 1 {
            return Err(error(
                "dispatch artifact must contain exactly one ordinary function",
                declaration.source.span,
            ));
        }
        let mut generated = parsed.remove(0);
        crate::set_source_id(&mut generated, source_id);
        for registration in &mut registrations {
            let (case, keyword, variant, handler) =
                generated_case(&generated, &registration.variant, &registration.handler)
                    .ok_or_else(|| {
                        error(
                            "missing generated dispatch case origin",
                            registration.source.span,
                        )
                    })?;
            registration.generated_case = Some(case);
            registration.generated_case_keyword = Some(keyword);
            registration.generated_variant = Some(variant);
            registration.generated_handler = Some(handler);
        }
        files.push(SourceFile {
            file_scope: None,
            path,
            source: text.clone(),
        });
        invocations.insert(source_id, declaration.source.span);
        origins.definitions.insert(source_id, definition);
        origins.generation.record_in_source(
            &generated.expr,
            &[crate::generator_provenance::Origin {
                producer: "#dispatch-fn".into(),
                invocation: key.clone().into(),
            }],
            source_id,
        );
        replacements.insert(name.clone(), generated);
        let artifact = Artifact {
            key,
            source: text,
            origins: locations,
            declaration: declaration.source,
            registrations,
            source_id,
            name,
        };
        if let Some(cache) = cache {
            artifact.publish(cache, files, invocations)?;
        }
        record_manifest(&artifact, files);
        artifacts.push(artifact);
    }
    let output = forms
        .into_iter()
        .filter_map(|form| match head(&form) {
            "#dispatch-case" => None,
            "#dispatch-fn" => name(child(&form, 1))
                .ok()
                .and_then(|name| replacements.remove(&name)),
            _ => Some(form),
        })
        .collect();
    Ok((output, artifacts))
}
