//! Type/evaluation planning before an async frame has a physical layout.
//!
//! All checked identities remain in this owned context. Deferred interfaces
//! are signatures, not fake executable definitions or empty frame layouts.
//! This boundary cannot authorize emission: the original ownership proof and
//! the final generated ordinary-code proof are still mandatory.
#![allow(dead_code)] // Consumed by the general state-machine emitter.

use std::collections::HashSet;

use crate::async_interfaces::Registry;
use crate::async_source::{Lowered, Source};
use crate::source_error::SourceError;
use crate::{DiagnosticCode, Item, PreparedProgramSyntax, Program, SpannedExpr};

pub(crate) struct Function {
    pub source: Source,
    pub model: Lowered,
    pub graph: crate::async_exec::Graph,
}

/// This is deliberately not CheckedProgram. In particular, no method exposes
/// native code generation or claims that deferred layouts can be accessed.
pub(crate) struct Planning {
    pub program: Program,
    pub interfaces: Registry,
    pub declarations: crate::typed_ir::Declarations,
    pub functions: Vec<Function>,
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
    let text = crate::expression_source(&invocation.expr)?;
    let mut parsed = crate::parse(&text)?;
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
    let interfaces = Registry::from_program_invocations(&program, &invocations)
        .map_err(|error| attach(error, &program))?;
    let mut selected = HashSet::new();
    let mut models = Vec::with_capacity(invocations.len());
    for invocation in &invocations {
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
        let model = crate::async_source::lower_in_registry(
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
        models.push((source, model));
    }
    let declarations = crate::typecheck::resolve_async_planning(&program, &interfaces, &selected)
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
    for (source, model) in models {
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
        let graph = crate::async_exec::build(body, &sites).map_err(|error| {
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
            source,
            model,
            graph,
        });
    }
    Ok(Planning {
        program,
        interfaces,
        declarations,
        functions,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::async_exec::Terminator;
    use crate::Type;

    const CONTEXT: &str = "
      (#enum Child ((Waiting #u64))) (#linear Child)
      (#enum ChildPoll ((ChildPending Child) (ChildReady #u64)))
      (#fn step-poll ((task Child) (waker (#ref #u64))) ChildPoll
        (#return (#match task (#case (Waiting count) (ChildReady count)))))";

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
          (@async-fn (: protocol work-await : waker #u64
            : function (#fn work ((choose #bool)) #u64 {body})))"
        )
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
                  (#set total (#await Child ChildPending ChildReady step-poll (Waiting 1u64)))
                  (#if (#usize.== index 1usize) (#block (#break-to outer) (#unreachable)) ()))
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
            matches!(item, Item::Struct { name, .. } | Item::Enum { name, .. } if name == "work-task")));
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
            (#await Child ChildPending ChildReady step-poll (Waiting 1u64))
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
          (@async-fn (: protocol FirstAwait : waker #u64 : function (#fn first ((seed #u64)) #u64
              (#return (#await Child ChildPending ChildReady step-poll (Waiting seed))))))
          (@async-fn (: protocol SecondAwait : waker #u64 : function (#fn second ((seed #u64)) #u64
              (#return (#await first-task first-pending first-ready first-poll
                (#call first (: seed seed)))))))"
        );
        let planning = prepare(&syntax(&text)).unwrap();
        assert_eq!(planning.functions.len(), 2);
        assert_eq!(
            planning.functions[1].graph.awaits[0].child_type,
            Type::Named("first-task".into())
        );
        assert_eq!(planning.functions[1].graph.awaits[0].result_type, Type::U64);
        assert!(planning
            .declarations
            .deferred_layouts
            .contains_key("first-task"));
        assert!(!planning.declarations.bodies.contains_key("first-poll"));
    }

    #[test]
    fn deferred_frame_has_no_fields_until_physical_layout_exists() {
        let text = format!(
            "{CONTEXT}
          (@async-fn (: protocol FirstAwait : waker #u64 : function (#fn first () #u64 (#return 1u64))))
          (@async-fn (: protocol SecondAwait : waker #u64 : function (#fn second ((child first-task)) #u64
              (#return (#get child state)))))"
        );
        let error = prepare(&syntax(&text)).err().unwrap();
        assert!(error.message.contains("deferred"), "{error:?}");
        assert!(error.span.is_some());
    }

    #[test]
    fn rejects_generated_name_conflicting_with_non_async_builtin() {
        let text = format!(
            "(@optional (: type #u64 : name work-task)) {}",
            work("(#return 1u64)")
        );
        let error = prepare(&syntax(&text)).err().unwrap();
        assert!(error.message.contains("conflict"), "{error:?}");
    }

    #[test]
    fn non_async_generated_declarations_are_available_before_source_planning() {
        let text = format!(
            "(@optional (: type #u64 : name Maybe)) {}",
            work(
                "
          (#let optional Maybe (#call Maybe-construct (: value
            (#await Child ChildPending ChildReady step-poll (Waiting 1u64)))))
          (#return (#call Maybe-unwrap-or (: value optional : fallback 0u64)))"
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
            .function_id("Maybe-construct")
            .is_some());
        assert!(!planning.declarations.bodies.contains_key("Maybe-construct"));
        assert_eq!(planning.functions[0].graph.awaits.len(), 1);
    }

    #[test]
    fn duplicate_async_interfaces_fail_before_any_body_is_emitted() {
        let second =
            work("(#return 2u64)").replace(": protocol work-await", ": protocol work-await-2");
        let text = format!("{}\n{}", work("(#return 1u64)"), &second[CONTEXT.len()..]);
        let error = prepare(&syntax(&text)).err().unwrap();
        assert!(error.message.contains("conflict"), "{error:?}");
        let span = error.span.unwrap();
        assert!(span.start > text.find("(@async-fn").unwrap());
    }

    #[test]
    fn generator_produced_async_invocation_gets_a_real_source_tree() {
        let text = format!(
            "{CONTEXT}
          (#gn produce ()
            `( (@async-fn
              (: protocol work-await : waker #u64
               : function (#fn work ((seed #u64)) #u64
                 (#return (#await Child ChildPending ChildReady step-poll (Waiting seed)))))) ))
          (@produce)"
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
            work("(#return (#await Child ChildPending ChildReady step-poll (Waiting 1u64)))")
                .replace("(#fn step-poll", "(#unsafe-fn step-poll");
        let error = prepare(&syntax(&text)).err().unwrap();
        assert_eq!(error.code, DiagnosticCode::Unsafe);
        assert!(error.message.contains("unsafe"), "{error:?}");
        let safe = text
            .replace("(#return (#await", "(#return (#unsafe (#await")
            .replace("(Waiting 1u64)))))", "(Waiting 1u64))))))");
        prepare(&syntax(&safe)).unwrap();
    }
}
