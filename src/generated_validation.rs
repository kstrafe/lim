//! Ordinary source witnesses emitted by generators, independent of generator kind.
//!
//! A witness can add checks, never relax the rules applied to runtime code.
use std::collections::HashSet;

use crate::{
    typecheck::{resolve_program_for_analysis, AnalysisError},
    Program, Span, SpannedExpr,
};

fn remap_span(mut span: Span, sources: &[u32]) -> Span {
    span.source_id = sources[span.source_id as usize];
    span
}

fn remap_expression(mut expression: SpannedExpr, sources: &[u32]) -> SpannedExpr {
    fn visit(expression: &mut SpannedExpr, sources: &[u32]) {
        expression.span = remap_span(expression.span, sources);
        for child in &mut expression.children {
            visit(child, sources);
        }
    }
    visit(&mut expression, sources);
    expression
}

pub(crate) fn resolve(program: &Program) -> Result<crate::typed_ir::Declarations, AnalysisError> {
    let Some(validation) = &program.generator_validation else {
        return resolve_program_for_analysis(program, true);
    };
    let witnesses = validation.as_ref().map_err(Clone::clone)?;
    let mut analysis = program.clone();
    analysis.generator_validation = None;
    // Use the current runtime items, not a snapshot retained at expansion time.
    analysis.items.splice(0..0, witnesses.items.iter().cloned());
    // Runtime sources may have been appended after expansion. Never replace
    // their IDs with a witness snapshot's table; rebase only witness spans.
    let sources = witnesses
        .source_files
        .iter()
        .enumerate()
        .map(|(index, file)| {
            let index = if analysis.source_files.get(index) == Some(file) {
                index
            } else if let Some(index) = analysis
                .source_files
                .iter()
                .position(|candidate| candidate == file)
            {
                index
            } else {
                analysis.source_files.push(file.clone());
                analysis.source_files.len() - 1
            };
            u32::try_from(index).expect("checked source file count")
        })
        .collect::<Vec<_>>();
    analysis.statement_spans.extend(
        witnesses
            .statement_spans
            .iter()
            .map(|(key, span)| (key.clone(), remap_span(*span, &sources))),
    );
    analysis.statement_expressions.extend(
        witnesses
            .statement_expressions
            .iter()
            .map(|(key, expression)| (key.clone(), remap_expression(expression.clone(), &sources))),
    );
    analysis.declaration_spans.extend(
        witnesses
            .declaration_spans
            .iter()
            .map(|(key, span)| (key.clone(), remap_span(*span, &sources))),
    );
    analysis.declaration_expressions.extend(
        witnesses
            .declaration_expressions
            .iter()
            .map(|(key, expression)| (key.clone(), remap_expression(expression.clone(), &sources))),
    );
    analysis
        .declaration_occurrences
        .extend(
            witnesses
                .declaration_occurrences
                .iter()
                .map(|(key, expressions)| {
                    (
                        key.clone(),
                        expressions
                            .iter()
                            .map(|expression| remap_expression(expression.clone(), &sources))
                            .collect(),
                    )
                }),
        );
    analysis.generated_source_invocations.extend(
        witnesses
            .generated_source_invocations
            .iter()
            .map(|(source, span)| (sources[*source as usize], remap_span(*span, &sources))),
    );
    analysis.generated_definition_contexts.extend(
        witnesses
            .generated_definition_contexts
            .iter()
            .map(|(source, author)| (sources[*source as usize], remap_span(*author, &sources))),
    );
    analysis
        .syntax_bundle_uses
        .extend(witnesses.syntax_bundle_uses.iter().map(|(span, uses)| {
            (
                remap_span(*span, &sources),
                uses.iter()
                    .map(|span| remap_span(*span, &sources))
                    .collect(),
            )
        }));
    let mut declarations = resolve_program_for_analysis(&analysis, true)
        .and_then(|declarations| crate::typecheck::check_resolved_proofs(&analysis, declarations))
        .map_err(|mut error| {
            if let Some(span) = error.2 {
                if span.source_id as usize >= program.source_files.len() {
                    error.2 = analysis
                        .generated_source_invocations
                        .get(&span.source_id)
                        .copied();
                }
            }
            for (span, _) in &mut error.3 {
                if span.source_id as usize >= program.source_files.len() {
                    if let Some(origin) = analysis.generated_source_invocations.get(&span.source_id)
                    {
                        *span = *origin;
                    }
                }
            }
            error
        })?;
    let names = program
        .items
        .iter()
        .flat_map(crate::item_declared_names)
        .collect::<HashSet<_>>();
    declarations.bodies.retain(|name, _| names.contains(name));
    declarations.flows.retain(|name, _| names.contains(name));
    declarations.liveness.retain(|name, _| names.contains(name));
    Ok(declarations)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture(body: &str) -> Program {
        let mut runtime = crate::parse_program(&format!(
            "(#fn main () #u64 (#return 42u64))\n(#fn witness () #u64 {body})"
        ))
        .unwrap();
        let witness = runtime.items.pop().unwrap();
        let mut validation = runtime.clone();
        validation.items = vec![witness];
        runtime.generator_validation = Some(Ok(std::sync::Arc::new(validation)));
        runtime
    }

    #[test]
    fn ordinary_generator_witnesses_are_checked_without_being_emitted() {
        let runtime = fixture("(#return 1u64)");
        let checked = crate::CheckedProgram::validate(&runtime).unwrap();
        assert!(!checked.dump_typed_ir().contains("function witness"));
        let assembly = checked
            .generate_assembly(crate::TargetDescription::X86_64_SYSTEM_V)
            .unwrap();
        assert!(!assembly.contains("witness"));
        let invalid = fixture("(#return #true)");
        assert!(crate::CheckedProgram::validate(&invalid).is_err());
    }

    #[test]
    fn witnesses_do_not_replace_current_runtime_definitions() {
        let mut runtime = fixture("(#return 1u64)");
        let crate::Item::Function(function) = &mut runtime.items[0] else {
            unreachable!()
        };
        function.return_type = crate::Type::Bool;
        assert!(crate::CheckedProgram::validate(&runtime).is_err());
    }

    fn move_source_ids(program: &mut Program, sources: &[u32]) {
        for span in program
            .statement_spans
            .values_mut()
            .chain(program.declaration_spans.values_mut())
        {
            *span = remap_span(*span, sources);
        }
        for expression in program
            .statement_expressions
            .values_mut()
            .chain(program.declaration_expressions.values_mut())
        {
            *expression = remap_expression(expression.clone(), sources);
        }
        for expressions in program.declaration_occurrences.values_mut() {
            for expression in expressions {
                *expression = remap_expression(expression.clone(), sources);
            }
        }
    }

    #[test]
    fn witness_source_ids_are_rebased_without_replacing_runtime_sources() {
        let mut runtime = crate::parse_program("(#fn main () #u64 (#return 42u64))").unwrap();
        let invocation = runtime.declaration_spans["main"];
        let mut witness = crate::parse_program("(#fn witness () #u64 (#return #true))").unwrap();
        move_source_ids(&mut witness, &[1]);
        witness
            .source_files
            .insert(0, runtime.source_files[0].clone());
        witness.generated_source_invocations.insert(1, invocation);
        runtime.generator_validation = Some(Ok(std::sync::Arc::new(witness)));
        runtime.source_files.push(crate::SourceFile {
            file_scope: None,
            path: "later-runtime.lim".into(),
            source: "; not the witness source\n".into(),
        });
        let error = resolve(&runtime)
            .err()
            .expect("invalid witness must still be checked");
        assert_eq!(
            error.2,
            Some(invocation),
            "witness error must map to its invocation"
        );
        assert_eq!(
            runtime.source_files[1].path,
            std::path::Path::new("later-runtime.lim")
        );
    }

    #[test]
    fn runtime_diagnostics_keep_sources_added_after_witness_creation() {
        let mut runtime = fixture("(#return 1u64)");
        let extra_source = "(#fn extra () #bool (#return 42u64))";
        let mut extra = crate::parse_program(extra_source).unwrap();
        move_source_ids(&mut extra, &[1]);
        runtime.items.extend(extra.items);
        runtime.source_files.push(crate::SourceFile {
            file_scope: None,
            path: "extra.lim".into(),
            source: extra_source.into(),
        });
        runtime.statement_spans.extend(extra.statement_spans);
        runtime
            .statement_expressions
            .extend(extra.statement_expressions);
        runtime.declaration_spans.extend(extra.declaration_spans);
        runtime
            .declaration_expressions
            .extend(extra.declaration_expressions);
        runtime
            .declaration_occurrences
            .extend(extra.declaration_occurrences);
        let error = resolve(&runtime)
            .err()
            .expect("bad runtime return must be checked");
        let span = error.2.expect("runtime diagnostic must have a span");
        assert_eq!(span.source_id, 1);
        assert_eq!(
            &runtime.source_files[1].source[span.start..span.end],
            "42u64"
        );
    }
}
