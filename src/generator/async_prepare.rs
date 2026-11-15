//! Type/evaluation planning before an async frame has a physical layout.
//! Implementation detail of built-in code generation, not runtime semantics.
//!
//! All checked identities remain in this owned context. Deferred interfaces
//! are signatures, not fake executable definitions or empty frame layouts.
//! This boundary cannot authorize emission: the original ownership proof and
//! the final generated ordinary-code proof are still mandatory.
#![allow(dead_code)] // Planning facts are also inspected by structural tests.

use std::{cell::OnceCell, collections::HashSet};

use crate::generator::async_interfaces::Registry;
use crate::generator::async_source::{Lowered, Source};
use crate::source_error::SourceError;
use crate::{DiagnosticCode, Item, PreparedProgramSyntax, Program, SpannedExpr};

pub(crate) struct Function {
    pub cancel: Option<crate::Expr>,
    pub source: Source,
    pub model: Lowered,
    pub graph: crate::generator::async_exec::Graph,
}

/// This is deliberately not CheckedProgram. In particular, no method exposes
/// native code generation or claims that deferred layouts can be accessed.
pub(crate) struct Planning {
    pub program: Program,
    pub interfaces: Registry,
    pub declarations: crate::typed_ir::Declarations,
    pub functions: Vec<Function>,
    pub(crate) layout_items: Vec<Item>,
    linear_types: OnceCell<crate::linearcheck::LinearTypes>,
}

impl Planning {
    /// Validate source moves before choosing a physical frame representation.
    /// Deferred interfaces still need final ordinary-code validation; these
    /// checks only establish the original body's local ownership obligations.
    pub(crate) fn validate_source_ownership(&self) -> Result<(), SourceError> {
        let _timing = crate::timing::detail("generator.async.source_ownership");
        for function in &self.functions {
            let name = &function.model.body_name;
            let body = &self.declarations.bodies[name];
            let flow = &self.declarations.flows[name];
            let (results, _) = flow.check_linear_ownership_with_local_pin_accesses(
                body,
                self.linear_types(),
                &self.declarations,
            );
            for result in results {
                if let Err(conflict) = result {
                    let mut error = SourceError::new(conflict.message, DiagnosticCode::Linear)
                        .at(conflict.span.unwrap_or(function.source.function.span));
                    for (span, message) in conflict.labels {
                        error = error.with_label(span, message);
                    }
                    return Err(attach(error, &self.program));
                }
            }
        }
        Ok(())
    }

    /// Immutable declarative classification shared by source ownership and
    /// every emitter in this planning arena. Classification alone is not an
    /// ownership proof; source validation also runs on generated cache hits.
    pub(crate) fn linear_types(&self) -> &crate::linearcheck::LinearTypes {
        self.linear_types.get_or_init(|| {
            crate::linearcheck::LinearTypes::from_items(
                self.program.items.iter().chain(&self.layout_items),
            )
        })
    }

    pub(crate) fn install_generated_layouts(&mut self, source: &str) -> Result<(), String> {
        let items = super::async_layout::declarations(source)?;
        self.declarations.install_generated_layouts(&items)?;
        self.layout_items.extend(items);
        self.linear_types.take();
        Ok(())
    }

    /// Check source discards before emission or a generated-source cache hit.
    pub(crate) fn validate_discarded_results(&self) -> Result<(), SourceError> {
        for function in &self.functions {
            for value in &function.graph.discarded_values {
                let value = &function.graph.values[value.0];
                // Primitive values and references need no destruction. Keep
                // declarative classification lazy for ordinary scalar polls.
                if !matches!(
                    &value.ty,
                    crate::Type::Named(_)
                        | crate::Type::Tuple(_)
                        | crate::Type::Array(..)
                        | crate::Type::MutableSlice(_)
                        | crate::Type::Atomic(_)
                        | crate::Type::PinOwned(_)
                        | crate::Type::PinShared(_)
                ) || !self.linear_types().is_linear(&value.ty)
                {
                    continue;
                }
                return Err(attach(
                    SourceError::new(
                        "linear expression result must be consumed explicitly; use #forget or a destruction function",
                        DiagnosticCode::Linear,
                    )
                    .at(value.span.unwrap_or(function.source.function.span)),
                    &self.program,
                ));
            }
        }
        Ok(())
    }
}

/// Generator output can itself be an async invocation. Reparse its own text
/// into a generated source file instead of pretending its nodes have original
/// source offsets. Original source trees (including expanded syntax bundles)
/// are retained unchanged.
fn invocation_tree(
    program: &mut Program,
    invocation: &SpannedExpr,
) -> Result<SpannedExpr, SourceError> {
    if !invocation.children.is_empty() {
        return Ok(invocation.clone());
    }
    let text = crate::declaration_source(&invocation.expr)?;
    let mut parsed = crate::parse_source_unit(&text)?;
    if parsed.len() != 1 {
        return Err(SourceError::new(
            "generated async invocation must contain exactly one form",
            DiagnosticCode::Parse,
        )
        .at(invocation.span));
    }
    let source_id = u32::try_from(program.source_files.len())
        .map_err(|_| "too many source files while planning async code".to_owned())?;
    let mut tree = parsed.remove(0);
    crate::set_source_id(&mut tree, source_id);
    let origin = invocation.span;
    let path = program
        .source_files
        .get(origin.source_id as usize)
        .map_or_else(
            || "<source>".to_owned(),
            |file| file.path.display().to_string(),
        );
    program.source_files.push(crate::SourceFile {
        file_scope: None,
        path: format!("<generated from {path}:{}:{}>", origin.line, origin.column).into(),
        source: text,
    });
    program
        .generated_source_invocations
        .insert(source_id, origin);
    Ok(tree)
}

fn attach(error: SourceError, program: &Program) -> SourceError {
    let mut error = error;
    if let Some(origin) = error.span.and_then(|span| {
        program
            .generated_source_invocations
            .get(&span.source_id)
            .copied()
    }) {
        error = error.with_label(origin, "generated while analyzing this async invocation");
    }
    error.attach(&program.source_files)
}

pub(crate) fn prepare(prepared: &PreparedProgramSyntax) -> Result<Planning, SourceError> {
    let mut program = crate::parse_prepared_async_declarations(prepared)?;
    let invocations = prepared
        .expressions
        .iter()
        .filter(|node| crate::is_async_invocation(node))
        .map(|node| invocation_tree(&mut program, node))
        .collect::<Result<Vec<_>, _>>()?;
    let mut interfaces = Registry::from_program_invocations(&program, &invocations)
        .map_err(|error| attach(error, &program))?;
    interfaces.graph_cleanup_interfaces().map_err(|error| {
        attach(
            SourceError::new(error.message, DiagnosticCode::Type),
            &program,
        )
    })?;
    interfaces
        .graph_parameter_interfaces(&program)
        .map_err(|error| {
            let mut error_source = SourceError::new(error.message, DiagnosticCode::Type);
            if let Some(span) = error.span {
                error_source = error_source.at(span);
            }
            attach(error_source, &program)
        })?;
    let mut selected = HashSet::new();
    let mut models = Vec::with_capacity(invocations.len());
    for invocation in &invocations {
        let cancel = match crate::normalize_builtin_generator_invocation(&invocation.expr)? {
            crate::Expr::List(parts) => parts.get(5).cloned(),
            _ => None,
        };
        let source = Source::from_invocation(invocation)
            .map_err(|message| {
                attach(
                    SourceError::new(message, DiagnosticCode::Parse).at(invocation.span),
                    &program,
                )
            })?
            .ok_or_else(|| {
                attach(
                    SourceError::new(
                        "async planning needs a #fn declaration with an original source tree",
                        DiagnosticCode::Parse,
                    )
                    .at(invocation.span),
                    &program,
                )
            })?;
        let model = crate::generator::async_source::lower_in_registry(
            &source.function,
            source.waker.clone(),
            &program,
            &interfaces,
        )
        .map_err(|error| {
            attach(
                SourceError::new(error.message, DiagnosticCode::Type).at(error.span),
                &program,
            )
        })?;
        let count = program.items.len();
        model
            .append_with_interfaces(&mut program, &interfaces)
            .map_err(|error| attach(error, &program))?;
        selected.extend(program.items[count..].iter().filter_map(|item| match item {
            Item::Function(function) => Some(function.name.clone()),
            _ => None,
        }));
        models.push((source, model, cancel));
    }
    let declarations = crate::typecheck::resolve_generation_planning(
        &program,
        &interfaces.interfaces(),
        &selected,
    )
    .map_err(|(message, code, span, labels)| {
        let mut error = SourceError::new(message, code);
        if let Some(span) = span {
            error = error.at(span);
        }
        for (span, message) in labels {
            error = error.with_label(span, message);
        }
        attach(error, &program)
    })?;
    let mut functions = Vec::with_capacity(models.len());
    for (source, model, cancel) in models {
        let body = declarations.bodies.get(&model.body_name).ok_or_else(|| {
            attach(
                SourceError::new(
                    "async planning lost the checked source body",
                    DiagnosticCode::Type,
                )
                .at(source.function.span),
                &program,
            )
        })?;
        let flow = declarations.flows.get(&model.body_name).ok_or_else(|| {
            attach(
                SourceError::new(
                    "async planning lost the checked source flow",
                    DiagnosticCode::Type,
                )
                .at(source.function.span),
                &program,
            )
        })?;
        let sites = model.map(body, flow, &declarations).map_err(|error| {
            attach(
                SourceError::new(error.message, DiagnosticCode::Type).at(error.span),
                &program,
            )
        })?;
        let graph = crate::generator::async_exec::build(body, &sites).map_err(|error| {
            let span = error
                .source
                .and_then(|node| body.nodes.get(node.0))
                .and_then(|node| node.span)
                .unwrap_or(source.function.span);
            attach(
                SourceError::new(error.message, DiagnosticCode::Type).at(span),
                &program,
            )
        })?;
        functions.push(Function {
            cancel,
            source,
            model,
            graph,
        });
    }
    let planning = Planning {
        program,
        interfaces,
        declarations,
        functions,
        layout_items: Vec::new(),
        linear_types: OnceCell::new(),
    };
    planning.validate_discarded_results()?;
    planning.validate_source_ownership()?;
    Ok(planning)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::generator::async_exec::Terminator;
    use crate::Type;

    const CONTEXT: &str = "
#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.ChildPending Child) (ChildPoll.ChildReady #u64))
#fn step-poll ((task Child) (waker (#ref #u64))) ChildPoll
          (#return (#match task (#case (Child.Waiting count) (ChildPoll.ChildReady count))))\n";

    fn syntax(source: &str) -> PreparedProgramSyntax {
        crate::prepare_program_syntax(
            source,
            std::path::Path::new("."),
            None,
            &crate::CompileConfig::default(),
            None,
        )
        .unwrap()
    }

    fn work(body: &str) -> String {
        format!(
            "{CONTEXT}\n
#generate #async-fn ((protocol work-await) (waker #u64)
              (function (#fn work ((choose #bool)) #u64 {body})))\n"
        )
    }

    #[test]
    fn source_ownership_and_emission_share_classification_for_all_functions() {
        let text = format!(
            "{}
#generate #async-fn ((protocol OtherAwait) (waker #u64)
              (function (#fn other () #u64 (#return 42u64))))\n",
            work("1u64 (#return (#await Child ChildPoll.ChildPending ChildPoll.ChildReady step-poll (Child.Waiting 1u64)))")
        );
        let planning = prepare(&syntax(&text)).unwrap();
        assert_eq!(planning.functions.len(), 2);
        assert!(!planning.functions[0].graph.discarded_values.is_empty());
        assert!(planning.linear_types.get().is_some());
        let types = planning.linear_types();
        assert!(std::ptr::eq(types, planning.linear_types()));
        assert!(types.is_linear(&Type::Named("Child".into())));
        assert!(types.can_repeat(&Type::U64));
    }

    #[test]
    fn plans_arbitrary_nested_control_without_legacy_frame_emission() {
        let text = work(
            "
          (#let-mut total #u64 0u64)
          (#label outer (#loop
            (#if choose
              (#block
                (#for-range (index #usize) 0usize 3usize
                  (#set total (#await Child ChildPoll.ChildPending ChildPoll.ChildReady step-poll (Child.Waiting 1u64)))
                  (#if (#usize::eq index 1usize) (#block (#break-to outer) (#unreachable)) ()))
                (#continue-to outer))
              (#block (#break-to outer) (#unreachable)))))
          (#return total)",
        );
        let planning = prepare(&syntax(&text)).unwrap();
        assert!(planning.declarations.planning_only);
        assert_eq!(planning.functions.len(), 1);
        let function = &planning.functions[0];
        assert_eq!(function.graph.awaits.len(), 1);
        assert!(function
            .graph
            .blocks
            .iter()
            .any(|block| matches!(block.terminator, Terminator::Await { .. })));
        assert!(!planning.program.items.iter().any(|item|
            matches!(item, Item::Struct { name, .. } | Item::Enum { name, .. } if name == "Work::Task")));
        assert!(!planning.declarations.bodies.contains_key("work"));
        assert!(!planning.declarations.bodies.contains_key("step-poll"));
        assert!(planning
            .declarations
            .bodies
            .contains_key(&function.model.body_name));
        assert!(!planning.program.items.iter().any(|item|
            matches!(item, Item::Function(function) if function.name == "work" || function.name == "poll")));
    }

    #[test]
    fn reports_exact_original_type_mismatch_before_shape_lowering() {
        let text = work(
            "
          (#let value #u64 (#if choose
            (#await Child ChildPoll.ChildPending ChildPoll.ChildReady step-poll (Child.Waiting 1u64))
            true))
          (#return value)",
        );
        let error = prepare(&syntax(&text)).err().unwrap();
        assert_eq!(error.code, DiagnosticCode::Type);
        let span = error.span.unwrap();
        assert_eq!(span.source_id, 0);
        assert_eq!(&text[span.start..span.end], "true");
    }

    #[test]
    fn async_calls_use_deferred_interfaces_not_fake_definitions() {
        let text = format!(
            "{CONTEXT}
#generate #async-fn ((protocol FirstAwait) (waker #u64) (function (#fn first ((seed #u64)) #u64
                (#return (#await Child ChildPoll.ChildPending ChildPoll.ChildReady step-poll (Child.Waiting seed))))))
#generate #async-fn ((protocol SecondAwait) (waker #u64) (function (#fn second ((seed #u64)) #u64
                (#return (#await First::Task First::Poll.Pending First::Poll.Ready First::poll
                  (#call first ((seed seed))))))))\n"
        );
        let planning = prepare(&syntax(&text)).unwrap();
        assert_eq!(planning.functions.len(), 2);
        assert_eq!(
            planning.functions[1].graph.awaits[0].child_type,
            Type::Named("First::Task".into())
        );
        assert_eq!(planning.functions[1].graph.awaits[0].result_type, Type::U64);
        assert!(planning
            .declarations
            .deferred_layouts
            .contains_key("First::Task"));
        assert!(!planning.declarations.bodies.contains_key("First::poll"));
    }

    #[test]
    fn deferred_frame_has_no_fields_until_physical_layout_exists() {
        let text = format!(
            "{CONTEXT}
#generate #async-fn ((protocol FirstAwait) (waker #u64) (function (#fn first () #u64 (#return 1u64))))
#generate #async-fn ((protocol SecondAwait) (waker #u64) (function (#fn second ((child First::Task)) #u64
                (#return (#get child state)))))\n"
        );
        let error = prepare(&syntax(&text)).err().unwrap();
        assert!(error.message.contains("deferred"), "{error:?}");
        assert!(error.span.is_some());
    }

    #[test]
    fn rejects_generated_name_conflicting_with_non_async_builtin() {
        let text = format!(
            "#generate #optional ((type #u64) (name Work::Task))\n {}",
            work("(#return 1u64)")
        );
        let error = prepare(&syntax(&text)).err().unwrap();
        assert!(error.message.contains("conflict"), "{error:?}");
    }

    #[test]
    fn non_async_generated_declarations_are_available_before_source_planning() {
        let text = format!(
            "#generate #optional ((type #u64) (name Maybe))\n {}",
            work(
                "
          (#let optional Maybe (#call Maybe::construct ((value
            (#await Child ChildPoll.ChildPending ChildPoll.ChildReady step-poll (Child.Waiting 1u64))))))
          (#return (#call Maybe::unwrap-or ((value optional) (fallback 0u64))))"
            )
        );
        let planning = prepare(&syntax(&text)).unwrap();
        assert!(planning
            .program
            .items
            .iter()
            .any(|item| matches!(item, Item::Enum { name, .. } if name == "Maybe")));
        assert!(planning
            .declarations
            .function_id("Maybe::construct")
            .is_some());
        assert!(!planning
            .declarations
            .bodies
            .contains_key("Maybe::construct"));
        assert_eq!(planning.functions[0].graph.awaits.len(), 1);
    }

    #[test]
    fn duplicate_async_interfaces_fail_before_any_body_is_emitted() {
        let second =
            work("(#return 2u64)").replace("(protocol work-await)", "(protocol work-await-2)");
        let text = format!("{}\n{}", work("(#return 1u64)"), &second[CONTEXT.len()..]);
        let error = prepare(&syntax(&text)).err().unwrap();
        assert!(error.message.contains("conflict"), "{error:?}");
        let span = error.span.unwrap();
        assert!(span.start > text.find("#generate #async-fn").unwrap());
    }

    #[test]
    fn generator_produced_async_invocation_gets_a_real_source_tree() {
        let text = format!(
            "{CONTEXT}
#gn produce ()
              `( (#generate #async-fn
                ((protocol work-await) (waker #u64)
                 (function (#fn work ((seed #u64)) #u64
                   (#return (#await Child ChildPoll.ChildPending ChildPoll.ChildReady step-poll (Child.Waiting seed))))))) )\n#generate produce\n"
        );
        let planning = prepare(&syntax(&text)).unwrap();
        assert_eq!(planning.functions.len(), 1);
        let function = &planning.functions[0];
        let source_id = function.source.function.span.source_id;
        assert!(source_id > 0);
        assert!(planning
            .program
            .generated_source_invocations
            .contains_key(&source_id));
        let site = &function.model.awaits[0];
        let file = &planning.program.source_files[site.span.source_id as usize];
        assert!(file.source[site.span.start..site.span.end].starts_with("(#await"));
    }

    #[test]
    fn unsafe_child_poll_requires_explicit_original_unsafe_scope() {
        let text =
            work("(#return (#await Child ChildPoll.ChildPending ChildPoll.ChildReady step-poll (Child.Waiting 1u64)))")
                .replace("#fn step-poll", "#unsafe-fn step-poll");
        let error = prepare(&syntax(&text)).err().unwrap();
        assert_eq!(error.code, DiagnosticCode::Unsafe);
        assert!(error.message.contains("unsafe"), "{error:?}");
        let safe = text
            .replace("(#return (#await", "(#return (#unsafe (#await")
            .replace("(Child.Waiting 1u64)))))", "(Child.Waiting 1u64))))))");
        prepare(&syntax(&safe)).unwrap();
    }
}
