//! Lexical borrow checking for Lim's first borrow model.
//!
//! References are explicit values, while expression-form borrows still provide
//! a scoped way to access an owner: `(#borrow owner body)` or
//! `(#borrow-mut owner body)`. The owner is borrowed for exactly the duration
//! of `body`, and two-expression borrows retain provenance in the surrounding
//! context for the lifetime of their binding.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use crate::analysis_error::{failure, Error, Site};

use crate::{Expr, Function, Item, Program, Statement};

#[cfg(test)]
#[test]
fn borrow_released_on_every_if_branch_allows_later_mutation() {
    let program = crate::parse_program(
        "(#fn main () u64
           (#let-mut owner u64 1u64)
           (#let view (#ref u64) (#borrow owner))
           (#let released ()
             (#if true
               (#block (#forget view) ())
               (#block (#forget view) ())))
           (#set owner 2u64)
           (#return owner))",
    )
    .unwrap();
    check_program(&program).unwrap_or_else(|error| panic!("{}", error.message));
    assert!(crate::typecheck::CheckedProgram::validate(&program).is_ok());
}

#[cfg(test)]
#[test]
fn borrow_released_on_only_one_branch_still_blocks_mutation() {
    let program = crate::parse_program(
        "(#fn main () u64
           (#let-mut owner u64 1u64)
           (#let view (#ref u64) (#borrow owner))
           (#let released ()
             (#if true
               (#block (#forget view) ())
               ()))
           (#set owner 2u64)
           (#return owner))",
    )
    .unwrap();
    let error = check_program(&program).unwrap_err();
    assert!(error.message.contains("cannot mutate 'owner'"));
}

#[cfg(test)]
#[test]
fn aggregate_reference_released_on_every_branch_allows_mutation() {
    let program = crate::parse_program(
        "(#struct Holder ((view (#ref u64))))
         (#fn main () u64
           (#let-mut owner u64 1u64)
           (#let holder Holder
             (#struct-literal Holder ((view (#borrow owner)))))
           (#let released ()
             (#if true
               (#block (#forget holder) ())
               (#block (#forget holder) ())))
           (#set owner 2u64)
           (#return owner))",
    )
    .unwrap();
    check_program(&program).unwrap_or_else(|error| panic!("{}", error.message));
    assert!(crate::typecheck::CheckedProgram::validate(&program).is_ok());
}

#[cfg(test)]
#[test]
fn block_local_reference_cannot_escape_into_outer_binding() {
    let program = crate::parse_program(
        "(#fn main () u64
           (#let escaped (#ref u64)
             (#block
               (#let local u64 7u64)
               (#borrow local)))
           (#return (#deref escaped)))",
    )
    .unwrap();
    let error = match crate::typecheck::CheckedProgram::validate(&program) {
        Ok(_) => panic!("block-local reference escaped"),
        Err(error) => error,
    };
    assert!(error.contains("reference to block-local variable 'local' escapes its scope"));
}

#[cfg(test)]
#[test]
fn destructured_block_local_reference_cannot_escape() {
    let program = crate::parse_program(
        "(#fn main () u64
           (#let escaped (#ref u64)
             (#block
               (#let (#tuple local) (#tuple u64) (#tuple 7u64))
               (#borrow local)))
           (#return (#deref escaped)))",
    )
    .unwrap();
    assert!(check_program(&program).is_err());
    assert!(crate::typecheck::CheckedProgram::validate(&program).is_err());
}

#[cfg(test)]
#[test]
fn block_reference_alias_cannot_escape_its_owner() {
    let program = crate::parse_program(
        "(#fn main () u64
           (#let escaped (#ref u64)
             (#block
               (#let (#tuple local) (#tuple u64) (#tuple 7u64))
               (#let alias (#ref u64) (#borrow local))
               alias))
           (#return (#deref escaped)))",
    )
    .unwrap();
    let error = check_program(&program).unwrap_err();
    assert!(error.message.contains("block-local variable 'local'"));
}

#[cfg(test)]
#[test]
fn block_reference_to_outer_owner_can_escape() {
    let program = crate::parse_program(
        "(#fn main () u64
           (#let owner u64 42u64)
           (#let escaped (#ref u64)
             (#block
               (#let alias (#ref u64) (#borrow owner))
               alias))
           (#return (#deref escaped)))",
    )
    .unwrap();
    assert!(crate::typecheck::CheckedProgram::validate(&program).is_ok());
}

#[cfg(test)]
#[test]
fn block_local_reference_cannot_be_passed_to_a_call() {
    let program = crate::parse_program(
        "(#fn read ((value (#ref u64))) u64 (#return (#deref value)))
         (#fn main () u64
           (#return (#call read (: value (#block
               (#let (#tuple local) (#tuple u64) (#tuple 7u64))
               (#borrow local))))))",
    )
    .unwrap();
    let error = check_program(&program).unwrap_err();
    assert!(error.message.contains("block-local variable 'local'"));
    assert!(crate::typecheck::CheckedProgram::validate(&program).is_err());
}

#[cfg(test)]
#[test]
fn aliased_reference_parameter_cannot_hide_block_local_escape() {
    let program = crate::parse_program(
        "(#type WordRef (#ref u64))
         (#fn read ((value WordRef)) u64 (#return (#deref value)))
         (#fn main () u64
           (#return (#call read (: value (#block
               (#let (#tuple local) (#tuple u64) (#tuple 7u64))
               (#borrow local))))))",
    )
    .unwrap();
    let error = check_program(&program).unwrap_err();
    assert!(error.message.contains("block-local variable 'local'"));
}

#[cfg(test)]
#[test]
fn scalar_result_from_block_local_reference_can_be_passed_to_a_call() {
    let program = crate::parse_program(
        "(#fn identity ((value u64)) u64 (#return value))
         (#fn main () u64
           (#return (#call identity (: value (#block
               (#let local u64 42u64)
               (#let alias (#ref u64) (#borrow local))
               (#deref alias))))))",
    )
    .unwrap();
    assert!(crate::typecheck::CheckedProgram::validate(&program).is_ok());
}

#[cfg(test)]
#[test]
fn matched_reference_payload_cannot_escape_local_owner() {
    let program = crate::parse_program(
        "(#enum Holder ((Has (#ref u64))))
         (#fn escape () (#ref u64)
           (#let owner u64 7u64)
           (#let holder Holder (Has (#borrow owner)))
           (#return (#match holder
             (#case (Has view) view))))",
    )
    .unwrap();
    let borrow_error = check_program(&program).unwrap_err();
    assert!(borrow_error.message.contains("local 'owner'"));
    let error = match crate::typecheck::CheckedProgram::validate(&program) {
        Ok(_) => panic!("matched reference payload escaped"),
        Err(error) => error,
    };
    assert!(error.contains("local 'owner'"), "{error}");
}

#[cfg(test)]
#[test]
fn matched_reference_payload_from_parameter_can_return() {
    let program = crate::parse_program(
        "(#enum Holder ((Has (#ref u64))))
         (#fn select ((source (#ref u64))) (#ref u64)
           (#let holder Holder (Has source))
           (#return (#match holder
             (#case (Has view) view))))
         (#fn main () u64
           (#let owner u64 42u64)
           (#let selected (#ref u64)
             (#call select (: source (#borrow owner))))
           (#return (#deref selected)))",
    )
    .unwrap();
    assert!(crate::typecheck::CheckedProgram::validate(&program).is_ok());
}

#[cfg(test)]
#[test]
fn direct_matched_payload_cannot_hide_block_local_reference() {
    let program = crate::parse_program(
        "(#enum Holder ((Has (#ref u64))))
         (#fn main () u64
           (#let escaped (#ref u64)
             (#match (Has (#block
               (#let (#tuple local) (#tuple u64) (#tuple 7u64))
               (#borrow local)))
               (#case (Has view) view)))
           (#return (#deref escaped)))",
    )
    .unwrap();
    let error = check_program(&program).unwrap_err();
    assert!(error.message.contains("block-local variable 'local'"));
    assert!(crate::typecheck::CheckedProgram::validate(&program).is_err());
}

#[cfg(test)]
#[test]
fn struct_literal_cannot_hide_block_local_reference() {
    let program = crate::parse_program(
        "(#struct Holder ((view (#ref u64))))
         (#fn main () u64
           (#let holder Holder
             (#struct-literal Holder
               ((view (#block
                 (#let (#tuple local) (#tuple u64) (#tuple 7u64))
                 (#borrow local))))))
           (#let result u64 (#deref (#get holder view)))
           (#forget holder)
           (#return result))",
    )
    .unwrap();
    let error = check_program(&program).unwrap_err();
    assert!(error.message.contains("block-local variable 'local'"));
}

#[cfg(test)]
#[test]
fn block_local_reference_cannot_be_stored_in_a_field() {
    let program = crate::parse_program(
        "(#struct Holder ((view (#ref u64))))
         (#fn main () u64
           (#let owner u64 1u64)
           (#let-mut holder Holder
             (#struct-literal Holder ((view (#borrow owner)))))
           (#set-field holder view
             (#block
               (#let (#tuple local) (#tuple u64) (#tuple 7u64))
               (#borrow local)))
           (#let result u64 (#deref (#get holder view)))
           (#forget holder)
           (#return result))",
    )
    .unwrap();
    let error = check_program(&program).unwrap_err();
    assert!(error.message.contains("local variable 'local'"));
    assert!(crate::typecheck::CheckedProgram::validate(&program).is_err());
}

const PLACE_SEPARATOR: char = '\u{1f}';

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LoanKind {
    Shared(usize),
    Mutable,
}

#[derive(Clone, Default)]
struct Loans {
    active: std::collections::BTreeMap<String, LoanKind>,
    origins: HashMap<String, Site>,
}

#[derive(Clone)]
struct Context {
    loans: Loans,
    // Imported globals never change; function and branch contexts share them.
    globals: Arc<HashSet<String>>,
    returnable: HashSet<String>,
    scope_bindings: HashSet<String>,
    mutable: HashSet<String>,
    mutable_references: HashSet<String>,
    reference_bindings: HashSet<String>,
    suspended_references: HashSet<String>,
    scoped_mutable_owners: HashSet<String>,
    reference_origins: HashMap<String, HashSet<String>>,
    reference_loans: HashMap<String, Vec<(String, String)>>,
    reference_fields:
        HashMap<String, HashMap<Vec<usize>, (HashSet<String>, Vec<(String, String)>)>>,
    reference_parents: HashMap<String, String>,
    allow_local_reference: bool,
    reference_types: Arc<HashSet<String>>,
    reference_variants: Arc<HashSet<String>>,
    reference_functions: Arc<HashSet<String>>,
    function_names: Arc<HashSet<String>>,
    reference_parameters: Arc<HashMap<String, Vec<bool>>>,
    typed_reference_return_parameters:
        Arc<HashMap<String, Vec<crate::typed_body::ParameterLoanSummary>>>,
    thread_spawn_functions: Arc<HashMap<String, Vec<crate::Type>>>,
    thread_join_functions: Arc<HashSet<String>>,
    thread_task_loans: HashMap<String, Vec<(String, LoanKind)>>,
    thread_exclusive_owners: HashMap<String, usize>,
    return_contains_references: bool,
    typed_return_escapes: bool,
    typed_scope_escapes: bool,
    mutable_reference_types: Arc<HashSet<String>>,
    program_items: Arc<Vec<Item>>,
    typed_reborrow_parents: HashMap<usize, String>,
}

impl Loans {
    fn borrow(&mut self, place: &str, kind: LoanKind) -> Result<(), Error> {
        if let Some(active) = self.active.iter().find_map(|(active, active_kind)| {
            (active.as_str() != place
                && places_conflict(active, place)
                && !matches!(
                    (active_kind, kind),
                    (LoanKind::Shared(_), LoanKind::Shared(_))
                ))
            .then_some(active.clone())
        }) {
            return Err(failure!(
                "cannot borrow '{}' because '{}' is already borrowed",
                display_place(place),
                display_place(&active)
            )
            .related(self.origins.get(&active).copied()));
        }
        match (self.active.get(place).copied(), kind) {
            (None, kind) => {
                self.active.insert(place.to_owned(), kind);
                if let Some(site) = Site::current() {
                    self.origins.insert(place.to_owned(), site);
                }
                Ok(())
            }
            (Some(LoanKind::Shared(count)), LoanKind::Shared(_)) => {
                self.active
                    .insert(place.to_owned(), LoanKind::Shared(count + 1));
                Ok(())
            }
            (Some(LoanKind::Shared(_)), LoanKind::Mutable) => Err(failure!(
                "cannot borrow '{}' mutably because it is already borrowed",
                display_place(place)
            )
            .related(self.origins.get(place).copied())),
            (Some(LoanKind::Mutable), LoanKind::Shared(_)) => Err(failure!(
                "cannot borrow '{}' because it is already borrowed mutably",
                display_place(place)
            )
            .related(self.origins.get(place).copied())),
            (Some(LoanKind::Mutable), LoanKind::Mutable) => Err(failure!(
                "cannot borrow '{}' mutably because it is already borrowed mutably",
                display_place(place)
            )
            .related(self.origins.get(place).copied())),
        }
    }

    fn end(&mut self, place: &str) {
        match self.active.get_mut(place) {
            Some(LoanKind::Shared(count)) if *count > 1 => *count -= 1,
            Some(_) => {
                self.active.remove(place);
                self.origins.remove(place);
            }
            None => {}
        }
    }
}

fn places_conflict(left: &str, right: &str) -> bool {
    let left = left.split(PLACE_SEPARATOR).collect::<Vec<_>>();
    let right = right.split(PLACE_SEPARATOR).collect::<Vec<_>>();
    let common = left.len().min(right.len());
    left[..common]
        .iter()
        .zip(&right[..common])
        .all(|(left, right)| left == right || *left == "*" || *right == "*")
}

fn display_place(place: &str) -> String {
    place.split(PLACE_SEPARATOR).collect::<Vec<_>>().join(".")
}

fn has_child_loan(loans: &Loans, owner: &str) -> bool {
    loans
        .active
        .keys()
        .any(|active| active.starts_with(&format!("{owner}{PLACE_SEPARATOR}")))
}

impl Context {
    fn is_returnable(&self, owner: &str) -> bool {
        self.globals.contains(owner) || self.returnable.contains(owner)
    }

    fn is_in_scope(&self, owner: &str) -> bool {
        self.globals.contains(owner) || self.scope_bindings.contains(owner)
    }

    fn write(&self, owner: &str) -> Result<(), Error> {
        self.write_place(owner, None)
    }

    fn write_place(&self, owner: &str, field: Option<&str>) -> Result<(), Error> {
        if self.thread_exclusive_owners.contains_key(owner) {
            return Err(failure!(
                "cannot mutate '{owner}' while it is mutably borrowed by a running thread"
            ));
        }
        let place = field.map_or_else(
            || owner.to_owned(),
            |field| format!("{owner}{PLACE_SEPARATOR}{field}"),
        );
        for (loan, kind) in &self.loans.active {
            if !places_conflict(loan, &place) {
                continue;
            }
            if matches!(kind, LoanKind::Shared(_)) {
                return Err(failure!(
                    "cannot mutate '{}' while it is immutably borrowed",
                    if loan == owner {
                        owner.to_owned()
                    } else {
                        display_place(&place)
                    }
                )
                .related(self.loans.origins.get(loan).copied()));
            }
            if !self.scoped_mutable_owners.contains(owner) {
                return Err(failure!(
                    "cannot mutate '{}' while it is mutably borrowed",
                    if loan == owner {
                        owner.to_owned()
                    } else {
                        display_place(&place)
                    }
                )
                .related(self.loans.origins.get(loan).copied()));
            }
        }
        Ok(())
    }

    fn read_place(
        &self,
        owner: &str,
        field: Option<&str>,
        through_mutable_reference: bool,
    ) -> Result<(), Error> {
        if self.thread_exclusive_owners.contains_key(owner) {
            return Err(failure!(
                "cannot access '{owner}' while it is mutably borrowed by a running thread"
            ));
        }
        let place = field.map_or_else(
            || owner.to_owned(),
            |field| format!("{owner}{PLACE_SEPARATOR}{field}"),
        );
        for (loan, kind) in &self.loans.active {
            if places_conflict(loan, &place)
                && *kind == LoanKind::Mutable
                && (!through_mutable_reference || loan != owner)
                && (!self.scoped_mutable_owners.contains(owner) || loan != owner)
            {
                return Err(failure!(
                    "cannot access '{}' while it is mutably borrowed",
                    display_place(&place)
                )
                .related(self.loans.origins.get(loan).copied()));
            }
        }
        Ok(())
    }
}

pub(crate) struct BorrowDiagnostic {
    pub message: String,
    pub span: Option<crate::Span>,
    pub labels: Vec<(crate::Span, String)>,
}

impl From<String> for BorrowDiagnostic {
    fn from(message: String) -> Self {
        Self {
            message,
            span: None,
            labels: Vec::new(),
        }
    }
}

#[cfg(test)]
pub(crate) fn check_program(program: &Program) -> Result<(), BorrowDiagnostic> {
    check_program_impl(program, false, None)
}

/// The ordinary compilation path has already checked return escapes against
/// typed places and loan origins; standalone callers retain the legacy rule.
pub(crate) fn check_program_with_typed_returns(
    program: &Program,
    declarations: &crate::typed_ir::Declarations,
) -> Result<(), BorrowDiagnostic> {
    check_program_impl(program, true, Some(declarations))
}

fn check_program_impl(
    program: &Program,
    typed_return_escapes: bool,
    declarations: Option<&crate::typed_ir::Declarations>,
) -> Result<(), BorrowDiagnostic> {
    let globals = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Let { name, .. } | Item::Static { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect::<HashSet<_>>();
    let globals = Arc::new(globals);
    let reference_types = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::TypeAlias { name, target, .. }
                if type_contains_reference(target, &program.items, &mut HashSet::new()) =>
            {
                Some(name.clone())
            }
            Item::Struct { name, fields, .. }
                if fields.iter().any(|field| {
                    type_contains_reference(&field.ty, &program.items, &mut HashSet::new())
                }) =>
            {
                Some(name.clone())
            }
            Item::Enum { name, variants, .. }
                if variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|ty| type_contains_reference(ty, &program.items, &mut HashSet::new())) =>
            {
                Some(name.clone())
            }
            _ => None,
        })
        .collect::<HashSet<_>>();
    let mutable_reference_types = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::TypeAlias { name, target, .. }
                if type_contains_mutable_reference(target, &program.items, &mut HashSet::new()) =>
            {
                Some(name.clone())
            }
            Item::Struct { name, .. } | Item::Enum { name, .. }
                if type_contains_mutable_reference(
                    &crate::Type::Named(name.clone()),
                    &program.items,
                    &mut HashSet::new(),
                ) =>
            {
                Some(name.clone())
            }
            _ => None,
        })
        .collect::<HashSet<_>>();
    let reference_variants = Arc::new(
        program
            .items
            .iter()
            .filter_map(|item| match item {
                Item::Enum { variants, .. } => Some(variants.iter().filter_map(|variant| {
                    variant
                        .fields
                        .iter()
                        .any(|field| {
                            type_contains_reference(field, &program.items, &mut HashSet::new())
                        })
                        .then(|| variant.name.clone())
                })),
                _ => None,
            })
            .flatten()
            .collect::<HashSet<_>>(),
    );
    let reference_functions = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Function(function)
                if contains_reference_type(&function.return_type, &reference_types) =>
            {
                Some(function.name.clone())
            }
            _ => None,
        })
        .collect::<HashSet<_>>();
    let function_names = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Function(function) => Some(function.name.clone()),
            _ => None,
        })
        .collect::<HashSet<_>>();
    let mut thread_spawn_functions = HashMap::new();
    let mut thread_join_functions = HashSet::new();
    for item in &program.items {
        let Item::ThreadTask { name, worker, .. } = item else {
            continue;
        };
        let parameters = program.items.iter().find_map(|item| match item {
            Item::Function(function) if function.name == *worker => Some(
                function
                    .parameters
                    .iter()
                    .map(|parameter| parameter.ty.clone())
                    .collect::<Vec<_>>(),
            ),
            _ => None,
        });
        if let Some(parameters) = parameters {
            thread_spawn_functions.insert(format!("{name}-spawn"), parameters);
        }
        thread_join_functions.insert(format!("{name}-join"));
    }
    let mut reference_parameters = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Function(function) => Some((
                function.name.clone(),
                function
                    .parameters
                    .iter()
                    .map(|parameter| contains_reference_type(&parameter.ty, &reference_types))
                    .collect::<Vec<_>>(),
            )),
            _ => None,
        })
        .collect::<HashMap<_, _>>();
    for (name, parameters) in &thread_spawn_functions {
        reference_parameters.insert(
            name.clone(),
            parameters
                .iter()
                .map(|ty| contains_reference_type(ty, &reference_types))
                .collect(),
        );
    }
    let reference_parameters = Arc::new(reference_parameters);
    let function_names = function_names
        .into_iter()
        .chain(thread_spawn_functions.keys().cloned())
        .chain(thread_join_functions.iter().cloned())
        .collect::<HashSet<_>>();
    // Branch contexts need shared ownership, not a fresh copy of every
    // imported function body for every function being checked.
    let program_items = Arc::new(program.items.clone());
    let reference_types = Arc::new(reference_types);
    let mutable_reference_types = Arc::new(mutable_reference_types);
    let reference_functions = Arc::new(reference_functions);
    let function_names = Arc::new(function_names);
    let thread_spawn_functions = Arc::new(thread_spawn_functions);
    let thread_join_functions = Arc::new(thread_join_functions);
    // Typed bodies share the finalized interprocedural summary table. Adapt
    // its IDs to legacy names once, not once per checked function.
    let typed_reference_return_parameters = declarations.map(|declarations| {
        let summaries = declarations
            .bodies
            .values()
            .next()
            .map(|body| &body.call_return_origins);
        Arc::new(
            program
                .items
                .iter()
                .filter_map(|item| {
                    let Item::Function(callee) = item else {
                        return None;
                    };
                    let id = declarations.function_id(&callee.name)?;
                    let origins = summaries?.get(&id)?;
                    Some((callee.name.clone(), origins.clone()))
                })
                .collect::<HashMap<_, _>>(),
        )
    });
    for item in &program.items {
        if let Item::Function(function) = item {
            if !function.external {
                let typed_reborrow_parents = if let Some(declarations) = declarations {
                    let body = declarations.bodies.get(&function.name).ok_or_else(|| {
                        BorrowDiagnostic::from(format!(
                            "internal error: typed body missing for '{}'",
                            function.name
                        ))
                    })?;
                    typed_reborrow_parents(
                        function,
                        body,
                        declarations.flows.get(&function.name),
                        &reference_types,
                        &mutable_reference_types,
                    )?
                } else {
                    HashMap::new()
                };
                check_function(
                    function,
                    program,
                    &program_items,
                    &globals,
                    &reference_types,
                    &reference_variants,
                    &mutable_reference_types,
                    &reference_functions,
                    &function_names,
                    &reference_parameters,
                    &thread_spawn_functions,
                    &thread_join_functions,
                    &program.statement_spans,
                    &program.statement_expressions,
                    typed_return_escapes
                        && (direct_reference_return(
                            &function.return_type,
                            &program.items,
                            &mut HashSet::new(),
                        ) || typed_aggregate_return_is_complete(
                            function,
                            declarations,
                            &reference_types,
                            &program.items,
                        )),
                    declarations.is_some(),
                    typed_reborrow_parents,
                    typed_reference_return_parameters.clone(),
                )?;
            }
        }
    }
    Ok(())
}

/// Typed return provenance is complete for an aggregate result only when all
/// reference-bearing aggregate calls in the body have an implementation
/// summary. Keep the legacy escape check for opaque external aggregate calls.
fn typed_aggregate_return_is_complete(
    function: &Function,
    declarations: Option<&crate::typed_ir::Declarations>,
    reference_types: &HashSet<String>,
    items: &[Item],
) -> bool {
    if !contains_reference_type(&function.return_type, reference_types)
        || direct_reference_return(&function.return_type, items, &mut HashSet::new())
    {
        return false;
    }
    let Some(declarations) = declarations else {
        return false;
    };
    let Some(body) = declarations.bodies.get(&function.name) else {
        return false;
    };
    !body.nodes.iter().any(|node| {
        let (
            Some(ty),
            crate::typed_body::NodeKind::Form {
                callee: Some(callee),
                ..
            },
        ) = (&node.ty, &node.kind)
        else {
            return false;
        };
        let reference_bearing_aggregate = match ty {
            crate::Type::Named(name) => reference_types.contains(name),
            crate::Type::Array(element, _) => contains_reference_type(element, reference_types),
            crate::Type::Tuple(elements) => elements
                .iter()
                .any(|element| contains_reference_type(element, reference_types)),
            _ => false,
        };
        reference_bearing_aggregate && !body.call_return_origins.contains_key(callee)
    })
}

fn check_function(
    function: &Function,
    program: &Program,
    program_items: &Arc<Vec<Item>>,
    globals: &Arc<HashSet<String>>,
    reference_types: &Arc<HashSet<String>>,
    reference_variants: &Arc<HashSet<String>>,
    mutable_reference_types: &Arc<HashSet<String>>,
    reference_functions: &Arc<HashSet<String>>,
    function_names: &Arc<HashSet<String>>,
    reference_parameters: &Arc<HashMap<String, Vec<bool>>>,
    thread_spawn_functions: &Arc<HashMap<String, Vec<crate::Type>>>,
    thread_join_functions: &Arc<HashSet<String>>,
    statement_spans: &HashMap<(String, usize), crate::Span>,
    _statement_expressions: &HashMap<(String, usize), crate::SpannedExpr>,
    typed_return_escapes: bool,
    typed_scope_escapes: bool,
    typed_reborrow_parents: HashMap<usize, String>,
    typed_reference_return_parameters: Option<
        Arc<HashMap<String, Vec<crate::typed_body::ParameterLoanSummary>>>,
    >,
) -> Result<(), BorrowDiagnostic> {
    let mut returnable = HashSet::new();
    let mut mutable = std::collections::HashSet::new();
    let mut mutable_references = HashSet::new();
    let mut reference_bindings = HashSet::new();
    let mut reference_origins = HashMap::new();
    for parameter in &function.parameters {
        returnable.insert(parameter.name.clone());
        if contains_reference_type(&parameter.ty, reference_types) {
            reference_origins.insert(
                parameter.name.clone(),
                HashSet::from([parameter.name.clone()]),
            );
            if matches!(
                parameter.ty,
                crate::Type::Reference { .. } | crate::Type::PinnedReference { .. }
            ) {
                reference_bindings.insert(parameter.name.clone());
            }
            let contains_mutable_references =
                contains_mutable_reference(&parameter.ty, reference_types, mutable_reference_types);
            if contains_mutable_references || matches!(parameter.ty, crate::Type::MutableSlice(_)) {
                mutable_references.insert(parameter.name.clone());
            }
            // Moving or matching an aggregate transfers its contained mutable
            // references; it is not a read through those referents.
            if contains_mutable_references {
                reference_bindings.insert(parameter.name.clone());
            }
        }
        if parameter.mutable {
            mutable.insert(parameter.name.clone());
        }
    }
    let mut context = Context {
        loans: Loans::default(),
        globals: Arc::clone(globals),
        returnable,
        scope_bindings: function
            .parameters
            .iter()
            .map(|parameter| parameter.name.clone())
            .collect(),
        mutable,
        mutable_references,
        reference_bindings,
        suspended_references: HashSet::new(),
        scoped_mutable_owners: HashSet::new(),
        reference_origins,
        reference_loans: HashMap::new(),
        reference_fields: HashMap::new(),
        reference_parents: HashMap::new(),
        allow_local_reference: false,
        reference_types: reference_types.clone(),
        reference_variants: reference_variants.clone(),
        mutable_reference_types: mutable_reference_types.clone(),
        reference_functions: reference_functions.clone(),
        function_names: function_names.clone(),
        reference_parameters: reference_parameters.clone(),
        typed_reference_return_parameters: typed_reference_return_parameters.unwrap_or_default(),
        thread_spawn_functions: thread_spawn_functions.clone(),
        thread_join_functions: thread_join_functions.clone(),
        thread_task_loans: HashMap::new(),
        thread_exclusive_owners: HashMap::new(),
        return_contains_references: contains_reference_type(&function.return_type, reference_types),
        typed_return_escapes,
        typed_scope_escapes,
        program_items: Arc::clone(program_items),
        typed_reborrow_parents,
    };
    for parameter in &function.parameters {
        if contains_reference_type(&parameter.ty, reference_types) {
            let kind = if contains_mutable_reference(
                &parameter.ty,
                reference_types,
                mutable_reference_types,
            ) {
                LoanKind::Mutable
            } else {
                LoanKind::Shared(1)
            };
            context
                .loans
                .borrow(&parameter.name, kind)
                .map_err(|error| BorrowDiagnostic::from(error.message))?;
        }
    }
    for (statement_index, statement) in function.body.iter().enumerate() {
        if let Err(error) = check_statement(statement, &mut context) {
            return Err(BorrowDiagnostic {
                message: format!(
                    "E4100 borrow-checker diagnostic in function '{}' statement {}: {}",
                    function.name, statement_index, error.message
                ),
                span: error.site.and_then(|site| site.span(program)).or_else(|| {
                    statement_spans
                        .get(&(function.name.clone(), statement_index))
                        .copied()
                }),
                labels: error
                    .related
                    .into_iter()
                    .filter_map(|site| site.span(program))
                    .map(|span| (span, "borrow begins here".into()))
                    .collect(),
            });
        }
    }
    Ok(())
}

fn check_statement(statement: &Statement, context: &mut Context) -> Result<(), Error> {
    let _site = Site::statement(statement).enter();
    match statement {
        Statement::Let {
            name,
            ty,
            value,
            mutable,
        } => {
            let _origin = Site::expression(value).enter();
            let contains_references = contains_reference_type(ty, &context.reference_types);
            let origins = reference_origins(value, context, contains_references);
            if !context.typed_scope_escapes {
                ensure_origins_in_scope(&origins, context)?;
            }
            let derived_parent = context_reborrow_parent(value, context);
            let contains_mutable_references = contains_mutable_reference(
                ty,
                &context.reference_types,
                &context.mutable_reference_types,
            );
            let is_reference_binding = matches!(
                ty,
                crate::Type::Reference { .. } | crate::Type::PinnedReference { .. }
            );
            let mut reference_fields = HashMap::new();
            if contains_references {
                collect_reference_fields(
                    ty,
                    value,
                    context,
                    &mut Vec::new(),
                    &mut reference_fields,
                );
                if matches!(value, Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(head)) if head == "match"))
                {
                    for (_, loans) in reference_fields.values_mut() {
                        *loans = flatten_transferred_loans(loans.clone(), context);
                    }
                }
            }
            let task_loans = thread_spawn_origins(value, context);
            context.allow_local_reference = true;
            let checked = check_expression(value, context);
            context.allow_local_reference = false;
            checked?;
            let match_transferred_loans = contains_references
                && matches!(value, Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(head)) if head == "match"));
            let moves_thread_task = if let Expr::Symbol(source) = value {
                context.thread_task_loans.contains_key(source).then(|| {
                    move_thread_task_loans(source, name, context);
                })
            } else {
                None
            }
            .is_some();
            if let Some(task_loans) = task_loans {
                for (owner, kind) in &task_loans {
                    context.loans.borrow(owner, *kind)?;
                    if *kind == LoanKind::Mutable {
                        *context
                            .thread_exclusive_owners
                            .entry(owner.clone())
                            .or_default() += 1;
                    }
                }
                context.reference_origins.insert(
                    name.clone(),
                    task_loans.iter().map(|(owner, _)| owner.clone()).collect(),
                );
                context.thread_task_loans.insert(name.clone(), task_loans);
            } else if !moves_thread_task {
                if let Some(parent) = derived_parent.as_ref() {
                    if context.mutable_references.contains(parent) {
                        context.suspended_references.insert(parent.clone());
                    }
                }
                let mut loans = if contains_references {
                    let mut paths = reference_fields.keys().collect::<Vec<_>>();
                    paths.sort();
                    paths
                        .into_iter()
                        .flat_map(|path| reference_fields[path].1.iter().cloned())
                        .collect::<Vec<_>>()
                } else {
                    Vec::new()
                };
                if loans.is_empty() && contains_references {
                    loans = borrow_place_loans(value, context);
                }
                if loans.is_empty() {
                    loans = origins
                        .iter()
                        .cloned()
                        .map(|owner| (owner.clone(), owner))
                        .collect();
                }
                let mut transferred_loans = existing_reference_value_loans(value, context);
                if match_transferred_loans {
                    loans = flatten_transferred_loans(loans, context);
                }
                for (owner, loan) in &loans {
                    let kind = if contains_mutable_references {
                        LoanKind::Mutable
                    } else {
                        LoanKind::Shared(1)
                    };
                    // A linear value containing an existing `&mut` moves
                    // that loan into the new aggregate; it does not create a
                    // second borrow. The source value cannot be used again
                    // after this move, which is enforced by linearity.
                    if contains_mutable_references
                        && context.loans.active.get(loan) == Some(&LoanKind::Mutable)
                    {
                        if let Some(index) = transferred_loans
                            .iter()
                            .position(|transferred| transferred == &(owner.clone(), loan.clone()))
                        {
                            transferred_loans.swap_remove(index);
                            continue;
                        }
                    }
                    if match_transferred_loans
                        && context.loans.active.get(loan).is_some_and(|active| {
                            matches!((active, kind), (LoanKind::Mutable, LoanKind::Mutable))
                                || matches!(
                                    (active, kind),
                                    (LoanKind::Shared(_), LoanKind::Shared(_))
                                )
                        })
                    {
                        continue;
                    }
                    if derived_parent
                        .as_ref()
                        .is_some_and(|parent| context.mutable_references.contains(parent))
                    {
                        if loan != owner {
                            context.loans.active.remove(owner);
                        }
                        if contains_mutable_references {
                            context.loans.borrow(loan, kind)?;
                        } else {
                            context.loans.borrow(loan, kind)?;
                        }
                    } else {
                        context.loans.borrow(loan, kind)?;
                    }
                }
                if origins.is_empty() || !contains_references {
                    context.reference_origins.remove(name);
                } else {
                    context.reference_origins.insert(name.clone(), origins);
                }
                if !loans.is_empty() {
                    context.reference_loans.insert(name.clone(), loans);
                }
                if let Some(parent) = derived_parent {
                    context.reference_parents.insert(name.clone(), parent);
                }
            }
            if *mutable {
                context.mutable.insert(name.clone());
            }
            context.scope_bindings.insert(name.clone());
            if contains_mutable_references || matches!(ty, crate::Type::MutableSlice(_)) {
                context.mutable_references.insert(name.clone());
            }
            if is_reference_binding {
                context.reference_bindings.insert(name.clone());
            }
            if !reference_fields.is_empty() {
                context
                    .reference_fields
                    .insert(name.clone(), reference_fields);
            }
        }
        Statement::Destructure {
            pattern,
            ty,
            value,
            mutable,
        } => {
            check_expression(value, context)?;
            if !context.typed_scope_escapes {
                ensure_origins_in_scope(
                    &reference_origins(
                        value,
                        context,
                        contains_reference_type(ty, &context.reference_types),
                    ),
                    context,
                )?;
            }
            bind_pattern_references(pattern, ty, value, context)?;
            let mut names = Vec::new();
            pattern_names(pattern, &mut names);
            context.scope_bindings.extend(names);
            if *mutable {
                let mut names = Vec::new();
                pattern_names(pattern, &mut names);
                context.mutable.extend(names);
            }
        }
        Statement::LetElse {
            pattern, ty, value, ..
        } => {
            check_expression(value, context)?;
            if !context.typed_scope_escapes {
                ensure_origins_in_scope(
                    &reference_origins(
                        value,
                        context,
                        contains_reference_type(ty, &context.reference_types),
                    ),
                    context,
                )?;
            }
            bind_pattern_references(pattern, ty, value, context)?;
            let mut names = Vec::new();
            pattern_names(pattern, &mut names);
            context.scope_bindings.extend(names);
        }
        Statement::Assign { name, value } => {
            let transfers_existing_reference_owner = matches!(value, Expr::List(items)
                if items.len() >= 3
                    && matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#match" | "match"))
                    && matches!(items.get(1), Some(Expr::Symbol(scrutinee)) if scrutinee == name));
            if context.reference_origins.contains_key(name) && !transfers_existing_reference_owner {
                return Err(failure!(
                    "cannot replace '{name}' while it retains references"
                ));
            }
            check_expression(value, context)?;
            context.write(name)?;
        }
        Statement::FieldAssign { name, field, value } => {
            check_expression(value, context)?;
            context.write_place(name, Some(field))?;
        }
        Statement::TupleAssign { name, index, value } => {
            check_expression(value, context)?;
            context.write_place(name, Some(&index.to_string()))?;
        }
        Statement::EnumPayloadAssign {
            name,
            variant,
            index,
            value,
        } => {
            check_expression(value, context)?;
            context.write_place(name, Some(&format!("{variant}.{index}")))?;
        }
        Statement::ArrayAssign { name, index, value } => {
            check_expression(index, context)?;
            check_expression(value, context)?;
            if let Some(index) = static_index_segment(index) {
                context.write_place(name, Some(&index))?;
            } else {
                context.write(name)?;
            }
        }
        Statement::While { condition, body } => {
            check_expression(condition, context)?;
            check_loop_iteration(body, context)?;
        }
        Statement::Loop { body } => check_loop_iteration(body, context)?,
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            check_statement(init, context)?;
            check_expression(condition, context)?;
            let mut iteration = context.clone();
            check_statements(body, &mut iteration)?;
            check_statement(step, &mut iteration)?;
            ensure_loop_thread_state(context, &iteration)?;
        }
        Statement::Labeled { statement, .. } => check_statement(statement, context)?,
        Statement::Return(Some(value)) => {
            check_expression(value, context)?;
            if !context.typed_return_escapes {
                for owner in reference_origins(value, context, context.return_contains_references) {
                    if !context.is_returnable(&owner) {
                        return Err(failure!(
                            "cannot return a value retaining a reference to local '{owner}'"
                        ));
                    }
                }
            }
        }
        Statement::BreakValue(value) | Statement::BreakToValue { value, .. } => {
            check_expression(value, context)?
        }
        Statement::Expr(value) => {
            if thread_spawn_origins(value, context).is_some() {
                return Err(
                    "thread spawn results must be stored in a task binding and joined before the binding is discarded"
                        .into(),
                );
            }
            check_expression(value, context)?
        }
        Statement::Return(None)
        | Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_) => {}
    }
    if let Statement::LetElse { else_body, .. } = statement {
        check_statements(else_body, context)?;
    }
    Ok(())
}

fn existing_reference_value_loans(expression: &Expr, context: &Context) -> Vec<(String, String)> {
    match expression {
        Expr::Symbol(name) if context.reference_bindings.contains(name) => context
            .reference_loans
            .get(name)
            .cloned()
            .unwrap_or_else(|| {
                context
                    .reference_origins
                    .get(name)
                    .into_iter()
                    .flatten()
                    .map(|owner| (owner.clone(), owner.clone()))
                    .collect()
            }),
        Expr::List(items)
            if items.len() == 2
                && matches!(items.first(), Some(Expr::Symbol(operator)) if matches!(operator.as_str(), "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut")) =>
        {
            Vec::new()
        }
        Expr::List(items)
            if items.len() == 3
                && matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "#get" || operator == "get") =>
        {
            let (Expr::Symbol(base), Some(index)) = (&items[1], static_index_segment(&items[2]))
            else {
                return Vec::new();
            };
            let Ok(index) = index.parse::<usize>() else {
                return Vec::new();
            };
            context
                .reference_fields
                .get(base)
                .and_then(|fields| fields.get(&vec![index]))
                .map(|(_, loans)| loans.clone())
                .unwrap_or_default()
        }
        Expr::List(items) => items
            .iter()
            .skip(1)
            .flat_map(|item| existing_reference_value_loans(item, context))
            .collect(),
        Expr::Block(statements) | Expr::Loop(statements) => statements
            .iter()
            .flat_map(|statement| match statement {
                Statement::Expr(value)
                | Statement::Return(Some(value))
                | Statement::BreakValue(value)
                | Statement::BreakToValue { value, .. } => {
                    existing_reference_value_loans(value, context)
                }
                _ => Vec::new(),
            })
            .collect(),
        Expr::Labeled { expression, .. }
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => existing_reference_value_loans(expression, context),
        Expr::Quote(_) | Expr::QuasiQuote(_) | Expr::At => Vec::new(),
        Expr::Symbol(_) => Vec::new(),
        Expr::Integer(_)
        | Expr::UnsignedInteger(_)
        | Expr::Float(_)
        | Expr::Char(_)
        | Expr::String(_) => Vec::new(),
    }
}

fn pattern_names(pattern: &Expr, names: &mut Vec<String>) {
    match pattern {
        Expr::Symbol(name) if name != "_" => names.push(name.clone()),
        Expr::List(items) => {
            for child in items.iter().skip(1) {
                pattern_names(child, names);
            }
        }
        _ => {}
    }
}

fn bind_pattern_references(
    pattern: &Expr,
    ty: &crate::Type,
    value: &Expr,
    context: &mut Context,
) -> Result<(), Error> {
    let inherited_origins = reference_origins(value, context, true);
    let mut inherited_fields = match value {
        Expr::Symbol(name) => context
            .reference_fields
            .get(name)
            .cloned()
            .unwrap_or_default(),
        _ => HashMap::new(),
    };
    let mut inherited_loans = match value {
        Expr::Symbol(name) => context
            .reference_loans
            .get(name)
            .cloned()
            .unwrap_or_default(),
        _ => borrow_place_loans(value, context),
    };
    if let Expr::List(items) = value {
        if matches!(items.first(), Some(Expr::Symbol(op)) if op == "slice-mut-split")
            && items.len() == 3
        {
            if let Expr::Symbol(parent) = &items[1] {
                if let Some(parent_loans) = context.reference_loans.get(parent) {
                    inherited_loans.clone_from(parent_loans);
                }
                release_dropped_value(&items[1], context);
            }
            if inherited_loans.is_empty() {
                inherited_loans = reference_origins(value, context, true)
                    .into_iter()
                    .map(|owner| (owner.clone(), owner))
                    .collect();
            }
            let left = inherited_loans
                .iter()
                .map(|(owner, loan)| (owner.clone(), format!("{loan}{PLACE_SEPARATOR}split-left")))
                .collect::<Vec<_>>();
            let right = inherited_loans
                .iter()
                .map(|(owner, loan)| (owner.clone(), format!("{loan}{PLACE_SEPARATOR}split-right")))
                .collect::<Vec<_>>();
            let origins = reference_origins(value, context, true);
            inherited_fields.insert(vec![0], (origins.clone(), left));
            inherited_fields.insert(vec![1], (origins, right));
            inherited_loans.clear();
        }
    }
    if matches!(value, Expr::Symbol(_)) {
        release_dropped_value(value, context);
    }
    if let Expr::Symbol(name) = value {
        context.reference_fields.remove(name);
    }
    bind_pattern_reference_fields(
        pattern,
        ty,
        value,
        context,
        &inherited_origins,
        &inherited_loans,
        &inherited_fields,
        &mut Vec::new(),
    )
}

fn collect_reference_fields(
    ty: &crate::Type,
    value: &Expr,
    context: &Context,
    path: &mut Vec<usize>,
    result: &mut HashMap<Vec<usize>, (HashSet<String>, Vec<(String, String)>)>,
) {
    if !type_contains_reference(ty, &context.program_items, &mut HashSet::new()) {
        return;
    }
    if let Expr::Symbol(name) = value {
        if let Some(existing) = context
            .reference_fields
            .get(name)
            .and_then(|fields| fields.get(path))
        {
            result.insert(path.clone(), existing.clone());
            return;
        }
    }
    if let (crate::Type::Array(element, 1), Expr::List(items)) = (ty, value) {
        if matches!(items.first(), Some(Expr::Symbol(head)) if head == "array-repeat") {
            if let Some(child) = items.get(if items.len() == 3 { 2 } else { 1 }) {
                path.push(0);
                collect_reference_fields(element, child, context, path, result);
                path.pop();
            }
            return;
        }
    }
    let children = match ty {
        crate::Type::Tuple(fields) => fields.clone(),
        crate::Type::Array(element, count) => {
            std::iter::repeat_n((**element).clone(), *count).collect()
        }
        crate::Type::Named(name) => context
            .program_items
            .iter()
            .find_map(|item| match item {
                Item::Struct {
                    name: struct_name,
                    fields,
                    ..
                } if struct_name == name => Some(
                    fields
                        .iter()
                        .map(|field| field.ty.clone())
                        .collect::<Vec<_>>(),
                ),
                Item::Enum {
                    name: enum_name,
                    variants,
                    ..
                } if enum_name == name => {
                    let variant_name = match value {
                        Expr::List(items) => items.first().and_then(|head| match head {
                            Expr::Symbol(name) => Some(name.as_str()),
                            _ => None,
                        }),
                        _ => None,
                    }?;
                    variants
                        .iter()
                        .find(|variant| variant.name == variant_name)
                        .map(|variant| variant.fields.clone())
                }
                _ => None,
            })
            .unwrap_or_default(),
        _ => Vec::new(),
    };
    if !children.is_empty() {
        if let Expr::List(items) = value {
            let value_start = match ty {
                crate::Type::Array(_, _) => 2,
                crate::Type::Tuple(_) if items.len() == children.len() + 2 => 2,
                _ => 1,
            };
            for (index, child_type) in children.iter().enumerate() {
                if let Some(child_value) = items.get(index + value_start) {
                    path.push(index);
                    collect_reference_fields(child_type, child_value, context, path, result);
                    path.pop();
                }
            }
            return;
        }
    }
    let origins = reference_origins(value, context, true);
    if origins.is_empty() {
        return;
    }
    let mut loans = borrow_place_loans(value, context);
    if loans.is_empty() {
        if let Expr::Symbol(name) = value {
            loans = context
                .reference_loans
                .get(name)
                .cloned()
                .unwrap_or_default();
        }
    }
    if loans.is_empty() {
        loans.extend(origins.iter().cloned().map(|owner| (owner.clone(), owner)));
    }
    result.insert(path.clone(), (origins, loans));
}

fn bind_pattern_reference_fields(
    pattern: &Expr,
    ty: &crate::Type,
    value: &Expr,
    context: &mut Context,
    inherited_origins: &HashSet<String>,
    inherited_loans: &[(String, String)],
    inherited_fields: &HashMap<Vec<usize>, (HashSet<String>, Vec<(String, String)>)>,
    path: &mut Vec<usize>,
) -> Result<(), Error> {
    if let Expr::Symbol(name) = pattern {
        if name == "_" || !type_contains_reference(ty, &context.program_items, &mut HashSet::new())
        {
            return Ok(());
        }
        let mut origins = reference_origins(value, context, true);
        if origins.is_empty() {
            origins.clone_from(inherited_origins);
        }
        let mut loans = match value {
            // `bind_pattern_references` snapshots provenance and then retires
            // the moved scrutinee before recursing into its payloads. Once
            // retired, a symbol-only fallback from `borrow_place_loans` would
            // incorrectly make the consumed local itself the loan owner.
            Expr::Symbol(name)
                if !context.reference_loans.contains_key(name) && !inherited_loans.is_empty() =>
            {
                inherited_loans.to_vec()
            }
            _ => borrow_place_loans(value, context),
        };
        if let Some((field_origins, field_loans)) = inherited_fields.get(path) {
            origins.clone_from(field_origins);
            loans.clone_from(field_loans);
        }
        if loans.is_empty() {
            loans.extend_from_slice(inherited_loans);
        }
        if loans.is_empty() {
            loans.extend(origins.iter().cloned().map(|owner| (owner.clone(), owner)));
        }
        let mutable =
            type_contains_mutable_reference(ty, &context.program_items, &mut HashSet::new());
        let kind = if mutable {
            LoanKind::Mutable
        } else {
            LoanKind::Shared(1)
        };
        for (owner, loan) in &loans {
            context.loans.borrow(loan, kind).map_err(|mut error| {
                error.message = format!(
                    "cannot destructure reference into '{name}': {}",
                    error.message
                );
                error
            })?;
            if mutable && loan != owner {
                context.loans.active.remove(owner);
            }
        }
        context.reference_origins.insert(name.clone(), origins);
        context.reference_loans.insert(name.clone(), loans);
        if matches!(
            ty,
            crate::Type::Reference { .. }
                | crate::Type::PinnedReference { .. }
                | crate::Type::Slice(_)
                | crate::Type::MutableSlice(_)
        ) {
            context.reference_bindings.insert(name.clone());
        }
        if mutable {
            context.mutable_references.insert(name.clone());
        }
        let nested_fields = inherited_fields
            .iter()
            .filter_map(|(field_path, state)| {
                field_path
                    .strip_prefix(path.as_slice())
                    .filter(|suffix| !suffix.is_empty())
                    .map(|suffix| (suffix.to_vec(), state.clone()))
            })
            .collect::<HashMap<_, _>>();
        if !nested_fields.is_empty() {
            context.reference_fields.insert(name.clone(), nested_fields);
        }
        return Ok(());
    }

    let Expr::List(pattern_items) = pattern else {
        return Ok(());
    };
    let Some(Expr::Symbol(pattern_head)) = pattern_items.first() else {
        return Ok(());
    };
    let value_items = match value {
        Expr::List(items) => Some(items),
        _ => None,
    };
    let pattern_children = &pattern_items[1..];
    let mut child_types = Vec::new();
    match ty {
        crate::Type::Tuple(fields) => child_types.extend(fields.iter().cloned()),
        crate::Type::Array(element, count) => {
            child_types.extend(std::iter::repeat_n((**element).clone(), *count));
        }
        crate::Type::Named(name) => {
            for item in context.program_items.iter() {
                match item {
                    Item::Struct {
                        name: struct_name,
                        fields,
                        ..
                    } if struct_name == name && pattern_head == name => {
                        child_types.extend(fields.iter().map(|field| field.ty.clone()));
                    }
                    Item::Enum {
                        name: enum_name,
                        variants,
                        ..
                    } if enum_name == name => {
                        if let Some(variant) = variants
                            .iter()
                            .find(|variant| variant.name == *pattern_head)
                        {
                            child_types.extend(variant.fields.iter().cloned());
                        }
                    }
                    _ => {}
                }
            }
        }
        _ => {}
    }
    let value_start = match ty {
        crate::Type::Array(_, _) => 2,
        crate::Type::Tuple(_)
            if value_items.is_some_and(|items| items.len() == child_types.len() + 2) =>
        {
            2
        }
        _ => 1,
    };
    for (index, (child_pattern, child_type)) in
        pattern_children.iter().zip(child_types.iter()).enumerate()
    {
        let child_value = value_items
            .and_then(|items| items.get(index + value_start))
            .unwrap_or(value);
        path.push(index);
        bind_pattern_reference_fields(
            child_pattern,
            child_type,
            child_value,
            context,
            inherited_origins,
            inherited_loans,
            inherited_fields,
            path,
        )?;
        path.pop();
    }
    Ok(())
}

fn check_statements(statements: &[Statement], context: &mut Context) -> Result<(), Error> {
    for statement in statements {
        check_statement(statement, context)?;
    }
    Ok(())
}

fn check_loop_iteration(statements: &[Statement], context: &Context) -> Result<(), Error> {
    let mut iteration = context.clone();
    check_statements(statements, &mut iteration)?;
    ensure_loop_thread_state(context, &iteration)
}

fn ensure_loop_thread_state(before: &Context, after: &Context) -> Result<(), Error> {
    if before.thread_task_loans != after.thread_task_loans
        || before.thread_exclusive_owners != after.thread_exclusive_owners
    {
        return Err(
            "thread task borrows must be spawned and joined within the same loop iteration".into(),
        );
    }
    Ok(())
}

fn check_expression(expression: &Expr, context: &mut Context) -> Result<(), Error> {
    let _site = Site::expression(expression).enter();
    match expression {
        Expr::List(items) => {
            if let Some(Expr::Symbol(operator)) = items.first() {
                if matches!(operator.as_str(), "drop" | "forget") && items.len() == 2 {
                    check_expression(&items[1], context)?;
                    release_dropped_value(&items[1], context);
                } else if operator == "if" && items.len() == 4 {
                    check_expression(&items[1], context)?;
                    let base = context.clone();
                    let mut then_context = base.clone();
                    let mut else_context = base.clone();
                    check_expression(&items[2], &mut then_context)?;
                    check_expression(&items[3], &mut else_context)?;
                    merge_branch_context(context, &[then_context, else_context]);
                } else if operator == "match" && items.len() >= 3 {
                    let thread_operation = thread_match_operation(&items[1], context);
                    check_expression(&items[1], context)?;
                    let scrutinee_origins = reference_origins(&items[1], context, true);
                    let result_origins = reference_origins(expression, context, true);
                    let scrutinee_loans = match &items[1] {
                        Expr::Symbol(name) => context.reference_loans.get(name).cloned(),
                        _ => None,
                    }
                    .unwrap_or_else(|| {
                        scrutinee_origins
                            .iter()
                            .cloned()
                            .map(|owner| (owner.clone(), owner))
                            .collect()
                    });
                    let patterns_transfer_known_payloads = items[2..].iter().all(|arm| {
                        let Expr::List(parts) = arm else {
                            return false;
                        };
                        let Some(pattern) = parts.first() else {
                            return false;
                        };
                        let mut names = Vec::new();
                        pattern_names(pattern, &mut names);
                        match pattern {
                            Expr::List(pattern) => pattern
                                .first()
                                .and_then(|head| match head {
                                    Expr::Symbol(variant) => Some(variant),
                                    _ => None,
                                })
                                .is_some_and(|variant| {
                                    !context.reference_variants.contains(variant)
                                        || names.len() <= 1
                                }),
                            _ => names.is_empty(),
                        }
                    });
                    let release_scrutinee = thread_operation.is_none()
                        && (result_origins.is_empty() || context.typed_scope_escapes)
                        && patterns_transfer_known_payloads
                        && matches!(items[1], Expr::Symbol(_));
                    if release_scrutinee {
                        release_dropped_value(&items[1], context);
                    }
                    let base = context.clone();
                    let mut branches = Vec::with_capacity(items.len() - 2);
                    for arm in &items[2..] {
                        let Expr::List(parts) = arm else {
                            return Err("match arms must be lists".into());
                        };
                        if parts.len() != 2 && parts.len() != 3 {
                            return Err("match arms must contain a pattern and body".into());
                        }
                        let mut branch = base.clone();
                        let mut names = Vec::new();
                        pattern_names(&parts[0], &mut names);
                        let selected_variant = match &parts[0] {
                            Expr::List(pattern) => pattern.first().and_then(|head| match head {
                                Expr::Symbol(variant) => Some(variant),
                                _ => None,
                            }),
                            _ => None,
                        };
                        let carries_references = selected_variant
                            .is_none_or(|variant| context.reference_variants.contains(variant));
                        let variant_has_mutable_references = selected_variant.is_some_and(|name| {
                            context.program_items.iter().any(|item| match item {
                                Item::Enum { variants, .. } => variants
                                    .iter()
                                    .find(|variant| variant.name == *name)
                                    .is_some_and(|variant| {
                                        variant.fields.iter().any(|field| {
                                            type_contains_mutable_reference(
                                                field,
                                                &context.program_items,
                                                &mut HashSet::new(),
                                            )
                                        })
                                    }),
                                _ => false,
                            })
                        });
                        if release_scrutinee && carries_references && names.len() == 1 {
                            let kind = if variant_has_mutable_references {
                                LoanKind::Mutable
                            } else {
                                LoanKind::Shared(1)
                            };
                            for (_, loan) in &scrutinee_loans {
                                branch.loans.borrow(loan, kind)?;
                            }
                        }
                        for name in &names {
                            if carries_references && !scrutinee_origins.is_empty() {
                                branch
                                    .reference_origins
                                    .insert(name.clone(), scrutinee_origins.clone());
                                if names.len() == 1 && !scrutinee_loans.is_empty() {
                                    branch
                                        .reference_loans
                                        .insert(name.clone(), scrutinee_loans.clone());
                                }
                            }
                        }
                        branch.scope_bindings.extend(names);
                        if let Some(operation) = &thread_operation {
                            apply_thread_match_arm(
                                operation,
                                &parts[0],
                                parts.len() == 3,
                                &mut branch,
                            )?;
                        }
                        if parts.len() == 3 {
                            check_expression(&parts[1], &mut branch)?;
                        }
                        check_expression(parts.last().expect("validated match arm"), &mut branch)?;
                        branches.push(branch);
                    }
                    merge_branch_context(context, &branches);
                } else if matches!(
                    operator.as_str(),
                    "atomic-load"
                        | "atomic-store"
                        | "atomic-fetch-add"
                        | "atomic-exchange"
                        | "atomic-compare-exchange"
                        | "atomic-compare-exchange-weak"
                ) && items.len() >= 3
                {
                    let previous = context.allow_local_reference;
                    context.allow_local_reference = true;
                    let reference_result = check_expression(&items[1], context);
                    context.allow_local_reference = previous;
                    reference_result?;
                    for argument in items.iter().skip(2).take(items.len() - 3) {
                        check_expression(argument, context)?;
                    }
                } else if matches!(
                    operator.as_str(),
                    "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut"
                ) {
                    if items.len() != 3 {
                        if items.len() == 2 {
                            let origins = borrow_place_origins(&items[1], context);
                            if origins.is_empty() {
                                return Err(failure!("{operator} place has no tracked owner"));
                            }
                            if !context.allow_local_reference {
                                if let Some(owner) =
                                    origins.iter().find(|owner| !context.is_returnable(owner))
                                {
                                    return Err(failure!(
                                        "cannot return a reference to local variable '{owner}'"
                                    )
                                    .child(1));
                                }
                            }
                            if let Some((base, path)) = projection_path(&items[1]) {
                                if path.is_empty() {
                                    check_expression(&items[1], context)?;
                                } else {
                                    check_projection_base(base, context)?;
                                }
                            } else {
                                check_expression(&items[1], context)?;
                            }
                            return Ok(());
                        }
                        return Err(failure!(
                            "{operator} requires a place, with an optional body"
                        ));
                    }
                    let origins = borrow_place_origins(&items[1], context);
                    if origins.is_empty() {
                        return Err(failure!("{operator} place has no tracked owner"));
                    }
                    let loans = borrow_place_loans(&items[1], context);
                    let kind = if matches!(operator.as_str(), "borrow" | "pin-borrow") {
                        LoanKind::Shared(1)
                    } else {
                        LoanKind::Mutable
                    };
                    let parent = context_reborrow_parent(expression, context);
                    if let Some((base, path)) = projection_path(&items[1]) {
                        if path.is_empty() {
                            check_expression(&items[1], context)?;
                        } else {
                            check_projection_base(base, context)?;
                        }
                    } else {
                        check_expression(&items[1], context)?;
                    }
                    let reborrow_mutable_parent = parent
                        .as_ref()
                        .is_some_and(|parent| context.mutable_references.contains(parent));
                    for (owner, loan) in &loans {
                        if reborrow_mutable_parent {
                            // A field reborrow temporarily suspends the parent
                            // loan.  Keeping the whole-owner loan active would
                            // make an access to a disjoint field appear to
                            // overlap the reborrowed field.
                            if matches!(context.loans.active.get(owner), Some(LoanKind::Mutable)) {
                                context.loans.active.remove(owner);
                            }
                            context.loans.active.insert(loan.clone(), kind);
                        } else {
                            context.loans.borrow(loan, kind)?;
                        }
                        if matches!(operator.as_str(), "borrow-mut" | "pin-borrow-mut") {
                            context.scoped_mutable_owners.insert(owner.clone());
                        }
                    }
                    if let Some(parent) = &parent {
                        if reborrow_mutable_parent {
                            context.suspended_references.insert(parent.clone());
                        }
                    }
                    let result = check_expression(&items[2], context);
                    for (owner, loan) in &loans {
                        if matches!(operator.as_str(), "borrow-mut" | "pin-borrow-mut") {
                            context.scoped_mutable_owners.remove(owner);
                        }
                        if reborrow_mutable_parent {
                            context.loans.end(loan);
                            if !has_child_loan(&context.loans, owner) {
                                context
                                    .loans
                                    .active
                                    .insert(owner.clone(), LoanKind::Mutable);
                            }
                        } else {
                            context.loans.end(loan);
                        }
                    }
                    if let Some(parent) = &parent {
                        context.suspended_references.remove(parent);
                    }
                    result?
                } else if context.function_names.contains(operator) {
                    let previous = context.allow_local_reference;
                    context.allow_local_reference = true;
                    let reference_parameters = context.reference_parameters.get(operator).cloned();
                    let checked = items[1..].iter().enumerate().try_for_each(|(index, item)| {
                        let _argument_site = Site::expression(item).enter();
                        check_expression(item, context)?;
                        if !context.typed_scope_escapes
                            && reference_parameters
                                .as_ref()
                                .and_then(|parameters| parameters.get(index))
                                .copied()
                                .unwrap_or_else(|| context.thread_join_functions.contains(operator))
                        {
                            ensure_origins_in_scope(
                                &reference_origins(item, context, true),
                                context,
                            )?;
                        }
                        let transfers_reference_ownership = context
                            .program_items
                            .iter()
                            .find_map(|declaration| match declaration {
                                Item::Function(function) if function.name == *operator => {
                                    function.parameters.get(index).map(|parameter| {
                                        contains_mutable_reference(
                                            &parameter.ty,
                                            &context.reference_types,
                                            &context.mutable_reference_types,
                                        ) || (contains_reference_type(
                                            &parameter.ty,
                                            &context.reference_types,
                                        ) && type_is_explicitly_linear(
                                            &parameter.ty,
                                            &context.program_items,
                                        ))
                                    })
                                }
                                _ => None,
                            })
                            .unwrap_or(false);
                        // A by-value mutable-reference aggregate, or any
                        // explicitly linear aggregate containing references,
                        // is moved into the callee. Retire its caller-side
                        // loan at the call; if the result carries it onward,
                        // the enclosing let reconstructs it from provenance.
                        // Typed borrow checking independently validates this
                        // transfer and the returned lifetime.
                        if transfers_reference_ownership {
                            release_dropped_value(item, context);
                        }
                        Ok::<(), Error>(())
                    });
                    context.allow_local_reference = previous;
                    checked?;
                } else if matches!(operator.as_str(), "deref-set" | "pin-write") && items.len() == 3
                {
                    // The target reference is used locally, never returned
                    // by this unit-valued operation. Typed write events still
                    // check conflicts with retained and derived loans.
                    let previous = context.allow_local_reference;
                    context.allow_local_reference = true;
                    let target = check_expression(&items[1], context);
                    context.allow_local_reference = previous;
                    target?;
                    check_expression(&items[2], context)?;
                } else if operator == "pin-set-field" && items.len() == 4 {
                    // The checked-place analysis records this as a write to
                    // one projected field of the pinned referent. Treating
                    // the pin handle as an unprojected read here would reject
                    // safe updates to a disjoint reference field whenever a
                    // sibling field is borrowed.
                    check_expression(&items[3], context)?;
                } else if matches!(
                    operator.as_str(),
                    "get" | "index" | "get-payload" | "pin-get-payload" | "pin-get-payload-mut"
                ) {
                    if let Some((base, path)) = projection_path(expression) {
                        let through_mutable_reference = matches!(base, Expr::Symbol(name)
                            if context.reference_bindings.contains(name));
                        let place = path.join(&PLACE_SEPARATOR.to_string());
                        if through_mutable_reference {
                            for source in reference_origins(base, context, true) {
                                context.read_place(&source, Some(&place), true)?;
                            }
                        } else if let Expr::Symbol(owner) = base {
                            context.read_place(owner, Some(&place), false)?;
                        } else {
                            check_expression(&items[1], context)?;
                        }
                    } else {
                        for item in &items[1..] {
                            check_expression(item, context)?;
                        }
                    }
                } else {
                    let arguments = if operator == "get" && items.len() >= 3 {
                        &items[1..items.len() - 1]
                    } else {
                        &items[1..]
                    };
                    for item in arguments {
                        check_expression(item, context)?;
                    }
                }
            } else {
                for item in items {
                    check_expression(item, context)?;
                }
            }
        }
        Expr::Block(statements) => {
            // Locals created by a block do not escape it, but consuming an
            // outer reference does. Carry those releases into the parent
            // context after checking the block's statements.
            let mut scoped = context.clone();
            check_statements(statements, &mut scoped)?;
            let mut outer_references = context
                .reference_origins
                .keys()
                .chain(context.reference_loans.keys())
                .cloned()
                .collect::<Vec<_>>();
            outer_references.sort();
            outer_references.dedup();
            for name in outer_references {
                if !scoped.reference_origins.contains_key(&name)
                    && !scoped.reference_loans.contains_key(&name)
                {
                    release_dropped_value(&Expr::Symbol(name), context);
                }
            }
        }
        Expr::Loop(statements) => {
            let mut scoped = context.clone();
            check_statements(statements, &mut scoped)?;
        }
        Expr::Labeled { expression, .. } => check_expression(expression, context)?,
        Expr::Quote(value) => check_expression(value, context)?,
        Expr::QuasiQuote(value) | Expr::Unquote(value) | Expr::UnquoteSplicing(value) => {
            check_expression(value, context)?
        }
        Expr::Symbol(name) => {
            if context.suspended_references.contains(name) {
                return Err(failure!(
                    "cannot use reference '{name}' while a derived field reference is active"
                ));
            }
            if matches!(context.loans.active.get(name), Some(LoanKind::Mutable))
                && !context.scoped_mutable_owners.contains(name)
                && !context.reference_bindings.contains(name)
            {
                return Err(failure!(
                    "cannot access '{name}' while it is mutably borrowed"
                ));
            }
            if context.thread_exclusive_owners.contains_key(name) {
                return Err(failure!(
                    "cannot access '{name}' while it is mutably borrowed by a running thread"
                ));
            }
        }
        Expr::Integer(_)
        | Expr::UnsignedInteger(_)
        | Expr::Float(_)
        | Expr::Char(_)
        | Expr::String(_)
        | Expr::At => {}
    }
    Ok(())
}

/// Join the dynamic borrow state after control-flow branches. A loan that is
/// active on any branch must be considered active after the join; otherwise a
/// later write could be accepted even though one runtime path still holds the
/// borrow. Shared-loan counts use the maximum branch count because branches
/// are mutually exclusive.
fn merge_branch_context(context: &mut Context, branches: &[Context]) {
    let base = context.clone();
    let mut merged = base.clone();
    merged.loans.active.clear();
    merged.loans.origins.clear();
    merged.reference_origins.clear();
    merged.reference_loans.clear();
    merged.reference_fields.clear();
    merged.reference_parents.clear();
    merged.suspended_references.clear();
    merged.thread_task_loans.clear();
    merged.thread_exclusive_owners.clear();
    for branch in branches {
        for (owner, kind) in &branch.loans.active {
            let next = match (merged.loans.active.get(owner).copied(), *kind) {
                (Some(LoanKind::Mutable), _) | (_, LoanKind::Mutable) => LoanKind::Mutable,
                (Some(LoanKind::Shared(existing)), LoanKind::Shared(count)) => {
                    LoanKind::Shared(existing.max(count))
                }
                (None, LoanKind::Shared(count)) => LoanKind::Shared(count),
            };
            merged.loans.active.insert(owner.clone(), next);
            if let Some(site) = branch.loans.origins.get(owner) {
                merged.loans.origins.entry(owner.clone()).or_insert(*site);
            }
        }
        for (name, origins) in &branch.reference_origins {
            if base.reference_origins.contains_key(name) {
                merged
                    .reference_origins
                    .entry(name.clone())
                    .or_default()
                    .extend(origins.iter().cloned());
            }
        }
        for (name, loans) in &branch.reference_loans {
            if base.reference_loans.contains_key(name) {
                let entry = merged.reference_loans.entry(name.clone()).or_default();
                for loan in loans {
                    if !entry.contains(loan) {
                        entry.push(loan.clone());
                    }
                }
            }
        }
        for (name, fields) in &branch.reference_fields {
            if base.reference_fields.contains_key(name) {
                let entry = merged.reference_fields.entry(name.clone()).or_default();
                for (path, (origins, loans)) in fields {
                    let (joined_origins, joined_loans) = entry.entry(path.clone()).or_default();
                    joined_origins.extend(origins.iter().cloned());
                    for loan in loans {
                        if !joined_loans.contains(loan) {
                            joined_loans.push(loan.clone());
                        }
                    }
                }
            }
        }
        for (name, parent) in &branch.reference_parents {
            if base.reference_parents.contains_key(name) {
                merged
                    .reference_parents
                    .entry(name.clone())
                    .or_insert_with(|| parent.clone());
            }
        }
        merged
            .suspended_references
            .extend(branch.suspended_references.iter().cloned());
        for (name, loans) in &branch.thread_task_loans {
            merged
                .thread_task_loans
                .entry(name.clone())
                .or_insert_with(|| loans.clone());
        }
        for (owner, count) in &branch.thread_exclusive_owners {
            let entry = merged
                .thread_exclusive_owners
                .entry(owner.clone())
                .or_default();
            *entry = (*entry).max(*count);
        }
    }
    *context = merged;
}

fn release_dropped_value(expression: &Expr, context: &mut Context) {
    let Expr::Symbol(name) = expression else {
        release_projected_value(expression, context);
        return;
    };
    let name = name.clone();
    if let Some(parent) = context.reference_parents.remove(&name) {
        context.suspended_references.remove(&parent);
    }
    let origins = context.reference_origins.remove(&name).unwrap_or_default();
    context.reference_fields.remove(&name);
    if let Some(loans) = context.reference_loans.remove(&name) {
        for (owner, loan) in loans {
            context.loans.end(&loan);
            if loan != owner
                && !context.loans.active.keys().any(|active| {
                    active != &owner && active.starts_with(&format!("{owner}{PLACE_SEPARATOR}"))
                })
            {
                context.loans.active.insert(owner, LoanKind::Mutable);
            }
        }
    } else {
        for owner in origins {
            context.loans.end(&owner);
        }
    }
    if let Some(loans) = context.thread_task_loans.remove(&name) {
        for (owner, kind) in loans {
            context.loans.end(&owner);
            if kind == LoanKind::Mutable {
                let remove_owner =
                    if let Some(count) = context.thread_exclusive_owners.get_mut(&owner) {
                        *count -= 1;
                        *count == 0
                    } else {
                        false
                    };
                if remove_owner {
                    context.thread_exclusive_owners.remove(&owner);
                }
            }
        }
    }
    context.mutable_references.remove(&name);
    context.reference_bindings.remove(&name);
}

/// Collapse loan chains when a reference-bearing value is moved out of another
/// reference-bearing value (for example, an enum payload extracted by match).
/// The destination then owns the actual referent loan rather than a loan whose
/// identity is the now-consumed wrapper binding.
fn flatten_transferred_loans(
    loans: Vec<(String, String)>,
    context: &Context,
) -> Vec<(String, String)> {
    fn flatten(
        owner: String,
        loan: String,
        context: &Context,
        seen: &mut HashSet<String>,
        output: &mut Vec<(String, String)>,
    ) {
        if owner == loan && seen.insert(loan.clone()) {
            if let Some(nested) = context.reference_loans.get(&loan) {
                for (nested_owner, nested_loan) in nested {
                    flatten(
                        nested_owner.clone(),
                        nested_loan.clone(),
                        context,
                        seen,
                        output,
                    );
                }
                seen.remove(&loan);
                return;
            }
            seen.remove(&loan);
        }
        let pair = (owner, loan);
        if !output.contains(&pair) {
            output.push(pair);
        }
    }

    let mut result = Vec::new();
    for (owner, loan) in loans {
        flatten(owner, loan, context, &mut HashSet::new(), &mut result);
    }
    result
}

fn release_projected_value(expression: &Expr, context: &mut Context) {
    let Some((Expr::Symbol(root), segments)) = projection_path(expression) else {
        return;
    };
    if segments.is_empty() {
        return;
    }
    let Some(path) = segments
        .iter()
        .map(|segment| segment.parse::<usize>().ok())
        .collect::<Option<Vec<_>>>()
    else {
        return;
    };
    let Some(fields) = context.reference_fields.get(root) else {
        return;
    };
    let selected = fields
        .keys()
        .filter(|field_path| field_path.starts_with(&path))
        .cloned()
        .collect::<Vec<_>>();
    if selected.is_empty() {
        return;
    }
    let released_loans = selected
        .iter()
        .flat_map(|field_path| &fields[field_path].1)
        .cloned()
        .collect::<Vec<_>>();
    // A field origin alone is not authority to retire a loan: ensure this
    // binding still owns every matching loan, including repeated references.
    let Some(mut remaining) = context.reference_loans.get(root).cloned() else {
        return;
    };
    for loan in &released_loans {
        let Some(index) = remaining.iter().position(|held| held == loan) else {
            return;
        };
        remaining.remove(index);
    }
    let fields = context.reference_fields.get_mut(root).unwrap();
    for field_path in selected {
        fields.remove(&field_path);
    }
    if fields.is_empty() {
        context.reference_fields.remove(root);
    }
    // Keep an empty entry: dropping the aggregate later must not fall back
    // to its conservative, possibly stale origin set and end an alias's loan.
    context.reference_loans.insert(root.clone(), remaining);
    for (_, loan) in released_loans {
        context.loans.end(&loan);
    }
}

enum ThreadMatchOperation {
    Spawn {
        source: Option<String>,
        loans: Vec<(String, LoanKind)>,
    },
    Join {
        handle: String,
    },
}

fn thread_match_operation(expression: &Expr, context: &Context) -> Option<ThreadMatchOperation> {
    if let Expr::Symbol(source) = expression {
        if let Some(loans) = context.thread_task_loans.get(source) {
            return Some(ThreadMatchOperation::Spawn {
                source: Some(source.clone()),
                loans: loans.clone(),
            });
        }
    }
    let Expr::List(items) = expression else {
        return None;
    };
    let Expr::Symbol(function) = items.first()? else {
        return None;
    };
    if context.thread_join_functions.contains(function) {
        if let Some(Expr::Symbol(handle)) = items.get(1) {
            return Some(ThreadMatchOperation::Join {
                handle: handle.clone(),
            });
        }
    }
    context
        .thread_spawn_functions
        .get(function)
        .map(|_| ThreadMatchOperation::Spawn {
            source: None,
            loans: thread_spawn_origins(expression, context).unwrap_or_default(),
        })
}

fn apply_thread_match_arm(
    operation: &ThreadMatchOperation,
    pattern: &Expr,
    guarded: bool,
    context: &mut Context,
) -> Result<(), Error> {
    if guarded {
        return Err("thread result matches cannot use guarded arms".into());
    }
    let Expr::List(parts) = pattern else {
        return Ok(());
    };
    let Some(Expr::Symbol(variant)) = parts.first() else {
        return Ok(());
    };
    match operation {
        ThreadMatchOperation::Spawn { source, loans } if variant.ends_with("-spawn-ok") => {
            let destination = parts.get(1).and_then(pattern_binding).ok_or_else(|| {
                "thread spawn success pattern must bind its task handle".to_owned()
            })?;
            if let Some(source) = source {
                move_thread_task_loans(source, &destination, context);
            } else {
                start_thread_task_loans(&destination, loans, context)?;
            }
        }
        ThreadMatchOperation::Spawn { source, .. } if variant.ends_with("-spawn-error") => {
            if let Some(source) = source {
                release_thread_task_loans(source, context);
            }
        }
        ThreadMatchOperation::Join { handle } if variant.ends_with("-join-ok") => {
            release_thread_task_loans(handle, context);
        }
        ThreadMatchOperation::Join { handle } if variant.ends_with("-join-error") => {
            let destination = parts.get(1).and_then(pattern_binding).ok_or_else(|| {
                "thread join error pattern must bind the returned task handle".to_owned()
            })?;
            move_thread_task_loans(handle, &destination, context);
        }
        _ => {}
    }
    Ok(())
}

fn pattern_binding(pattern: &Expr) -> Option<String> {
    match pattern {
        Expr::Symbol(name) if name != "_" && name != "tuple" => Some(name.clone()),
        Expr::List(items) => items.iter().find_map(pattern_binding),
        _ => None,
    }
}

fn start_thread_task_loans(
    destination: &str,
    loans: &[(String, LoanKind)],
    context: &mut Context,
) -> Result<(), Error> {
    for (owner, kind) in loans {
        context.loans.borrow(owner, *kind)?;
        if *kind == LoanKind::Mutable {
            *context
                .thread_exclusive_owners
                .entry(owner.clone())
                .or_default() += 1;
        }
    }
    context.reference_origins.insert(
        destination.to_owned(),
        loans.iter().map(|(owner, _)| owner.clone()).collect(),
    );
    context
        .thread_task_loans
        .insert(destination.to_owned(), loans.to_vec());
    Ok(())
}

fn move_thread_task_loans(source: &str, destination: &str, context: &mut Context) {
    if let Some(loans) = context.thread_task_loans.remove(source) {
        context.reference_origins.remove(source);
        context.reference_origins.insert(
            destination.to_owned(),
            loans.iter().map(|(owner, _)| owner.clone()).collect(),
        );
        context
            .thread_task_loans
            .insert(destination.to_owned(), loans);
    }
}

fn release_thread_task_loans(source: &str, context: &mut Context) {
    if let Some(loans) = context.thread_task_loans.remove(source) {
        context.reference_origins.remove(source);
        for (owner, _) in &loans {
            context.loans.end(owner);
        }
        for (owner, kind) in loans {
            if kind == LoanKind::Mutable {
                let remove_owner =
                    if let Some(count) = context.thread_exclusive_owners.get_mut(&owner) {
                        *count -= 1;
                        *count == 0
                    } else {
                        false
                    };
                if remove_owner {
                    context.thread_exclusive_owners.remove(&owner);
                }
            }
        }
    }
}

fn thread_spawn_origins(expression: &Expr, context: &Context) -> Option<Vec<(String, LoanKind)>> {
    let Expr::List(items) = expression else {
        return None;
    };
    let Expr::Symbol(function) = items.first()? else {
        return None;
    };
    let parameters = context.thread_spawn_functions.get(function)?;
    let mut loans = Vec::new();
    for (argument, parameter) in items[1..].iter().zip(parameters) {
        if !contains_reference_type(parameter, &context.reference_types) {
            continue;
        }
        let kind = if contains_mutable_reference(
            parameter,
            &context.reference_types,
            &context.mutable_reference_types,
        ) {
            LoanKind::Mutable
        } else {
            LoanKind::Shared(1)
        };
        loans.extend(
            reference_origins(argument, context, true)
                .into_iter()
                .map(|owner| (owner, kind)),
        );
    }
    Some(loans)
}

fn contains_mutable_reference(
    ty: &crate::Type,
    reference_types: &HashSet<String>,
    mutable_reference_types: &HashSet<String>,
) -> bool {
    match ty {
        crate::Type::Reference { mutable, .. } | crate::Type::PinnedReference { mutable, .. } => {
            *mutable
        }
        crate::Type::Array(element, _) => {
            contains_mutable_reference(element, reference_types, mutable_reference_types)
        }
        crate::Type::Tuple(fields) => fields.iter().any(|field| {
            contains_mutable_reference(field, reference_types, mutable_reference_types)
        }),
        crate::Type::Named(name) => {
            reference_types.contains(name) && mutable_reference_types.contains(name)
        }
        _ => false,
    }
}

fn type_is_explicitly_linear(ty: &crate::Type, declarations: &[Item]) -> bool {
    match ty {
        crate::Type::Named(name) => declarations.iter().any(|declaration| {
            matches!(declaration, Item::LinearAnnotation { type_name } if type_name == name)
        }),
        crate::Type::Tuple(fields) => fields
            .iter()
            .any(|field| type_is_explicitly_linear(field, declarations)),
        crate::Type::Array(element, _) => type_is_explicitly_linear(element, declarations),
        _ => false,
    }
}

fn static_index_segment(expression: &Expr) -> Option<String> {
    match expression {
        Expr::Integer(index) if *index >= 0 => Some(index.to_string()),
        Expr::UnsignedInteger(index) => Some(index.to_string()),
        Expr::List(items)
            if items.len() == 3
                && matches!(items.first(), Some(Expr::Symbol(head)) if head == "literal") =>
        {
            static_index_segment(&items[2])
        }
        _ => None,
    }
}

fn check_projection_base(base: &Expr, context: &mut Context) -> Result<(), Error> {
    if matches!(base, Expr::Symbol(name) if context.suspended_references.contains(name)) {
        Ok(())
    } else {
        check_expression(base, context)
    }
}

fn projection_path(expression: &Expr) -> Option<(&Expr, Vec<String>)> {
    match expression {
        Expr::Symbol(_) => Some((expression, Vec::new())),
        Expr::List(items)
            if items.len() == 2
                && matches!(items.first(), Some(Expr::Symbol(name)) if matches!(name.as_str(), "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut")) =>
        {
            projection_path(&items[1])
        }
        Expr::List(items)
            if items.len() == 3
                && matches!(items.first(), Some(Expr::Symbol(name)) if name == "get" || name == "index") =>
        {
            let (base, mut path) = projection_path(&items[1])?;
            let is_index =
                matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "index");
            let segment = if is_index {
                static_index_segment(&items[2]).unwrap_or_else(|| "*".into())
            } else {
                match &items[2] {
                    Expr::Symbol(name) => name.clone(),
                    Expr::Integer(index) => index.to_string(),
                    Expr::UnsignedInteger(index) => index.to_string(),
                    _ => return None,
                }
            };
            path.push(segment);
            Some((base, path))
        }
        Expr::List(items)
            if items.len() == 4
                && matches!(items.first(), Some(Expr::Symbol(name)) if matches!(name.as_str(), "get-payload" | "pin-get-payload" | "pin-get-payload-mut")) =>
        {
            let (base, mut path) = projection_path(&items[1])?;
            let Expr::Symbol(variant) = &items[2] else {
                return None;
            };
            path.push(variant.clone());
            path.push(static_index_segment(&items[3]).unwrap_or_else(|| "*".into()));
            Some((base, path))
        }
        _ => None,
    }
}

fn context_reborrow_parent(expression: &Expr, context: &Context) -> Option<String> {
    if context.typed_scope_escapes {
        return context
            .typed_reborrow_parents
            .get(&(std::ptr::from_ref(expression) as usize))
            .cloned();
    }
    borrowed_field_parent(expression)
}

fn typed_reborrow_parents(
    function: &Function,
    body: &crate::typed_body::Body,
    flow: Option<&crate::typed_flow::FlowGraph>,
    reference_types: &HashSet<String>,
    mutable_reference_types: &HashSet<String>,
) -> Result<HashMap<usize, String>, String> {
    let flow = flow.ok_or_else(|| {
        format!(
            "internal error: typed flow missing for '{}' while resolving reborrows",
            function.name
        )
    })?;
    let emission = body.emission_types(function)?;
    let loan_origins = flow.loan_origins(body);
    let mut parent_by_expression = HashMap::new();
    for (index, node) in flow.nodes.iter().enumerate() {
        let crate::typed_flow::FlowAction::Borrow { value, place, .. } = &node.action else {
            continue;
        };
        let borrowed_from = loan_origins
            .value_before(body, flow, crate::typed_flow::FlowNodeId(index), *value)
            .into_iter()
            .find_map(|origin| origin.borrowed_from);
        if let Some(binding) = borrowed_from {
            if let Some(binding_info) = body.bindings.get(binding.0) {
                parent_by_expression.insert(
                    body.nodes[value.0]
                        .expression_id
                        .expect("checked borrow expression identity"),
                    binding_info.name.clone(),
                );
                continue;
            }
        }
        let crate::typed_body::PlaceRoot::Local(binding) = place.root else {
            continue;
        };
        let Some(binding_info) = body.bindings.get(binding.0) else {
            continue;
        };
        let has_mutable_reference =
            contains_mutable_reference(&binding_info.ty, reference_types, mutable_reference_types);
        let mutable_slice = matches!(binding_info.ty, crate::Type::MutableSlice(_));
        if !has_mutable_reference || (place.segments.is_empty() && !mutable_slice) {
            continue;
        }
        let Some(expression_id) = body.nodes.get(value.0).and_then(|node| node.expression_id)
        else {
            continue;
        };
        parent_by_expression.insert(expression_id, binding_info.name.clone());
    }
    Ok(emission
        .address_to_id
        .into_iter()
        .filter_map(|(address, expression_id)| {
            parent_by_expression
                .get(&expression_id)
                .cloned()
                .map(|parent| (address, parent))
        })
        .collect())
}

#[cfg(test)]
#[test]
fn projected_reborrow_parent_comes_from_checked_binding_identity() {
    let source = "(#struct Pair ((left u64) (right u64)))
      (#fn main () u64
        (#let-mut pair Pair (#struct-literal Pair ((left 1u64) (right 2u64))))
        (#let parent (#ref-mut Pair) (#borrow-mut pair))
        (#let child (#ref-mut u64) (#borrow-mut (#get parent left)))
        (#drop child) (#drop parent) (#forget pair) (#return 0u64))";
    let program = crate::parse_program(source).unwrap();
    let checked = crate::CheckedProgram::validate(&program).unwrap();
    let function = program
        .items
        .iter()
        .find_map(|item| match item {
            Item::Function(function) if function.name == "main" => Some(function),
            _ => None,
        })
        .unwrap();
    let body = &checked.declarations().bodies["main"];
    let parents = typed_reborrow_parents(
        function,
        body,
        checked.declarations().flows.get("main"),
        &HashSet::new(),
        &HashSet::new(),
    )
    .unwrap();
    assert!(
        typed_reborrow_parents(function, body, None, &HashSet::new(), &HashSet::new(),).is_err()
    );
    let Statement::Let { value, .. } = &function.body[2] else {
        unreachable!()
    };
    assert_eq!(
        parents
            .get(&(std::ptr::from_ref(value) as usize))
            .map(String::as_str),
        Some("parent")
    );

    let slice_source = "(#fn main () u64
      (#let-mut values (#array u64 2) (#array-of (#array u64 2) 1u64 2u64))
      (#let view (#slice-mut u64) (#slice-mut-of (#borrow-mut values)))
      (#let item (#ref-mut u64) (#slice-mut-idx view 0usize))
      (#forget item) (#forget view) (#forget values) (#return 0u64))";
    let slice_program = crate::parse_program(slice_source).unwrap();
    let checked = crate::CheckedProgram::validate(&slice_program).unwrap();
    let slice_function = slice_program
        .items
        .iter()
        .find_map(|item| match item {
            Item::Function(function) if function.name == "main" => Some(function),
            _ => None,
        })
        .unwrap();
    let body = &checked.declarations().bodies["main"];
    let parents = typed_reborrow_parents(
        slice_function,
        body,
        checked.declarations().flows.get("main"),
        &HashSet::new(),
        &HashSet::new(),
    )
    .unwrap();
    let Statement::Let { value, .. } = &slice_function.body[2] else {
        unreachable!()
    };
    assert_eq!(
        parents
            .get(&(std::ptr::from_ref(value) as usize))
            .map(String::as_str),
        Some("view")
    );
}

fn borrowed_field_parent(expression: &Expr) -> Option<String> {
    let Expr::List(items) = expression else {
        return None;
    };
    if items.len() == 3
        && matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "slice-mut-idx")
    {
        return match &items[1] {
            Expr::Symbol(name) => Some(name.clone()),
            _ => None,
        };
    }
    if !matches!(items.first(), Some(Expr::Symbol(operator)) if matches!(operator.as_str(), "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut"))
        || (items.len() != 2 && items.len() != 3)
    {
        return None;
    }
    let (base, path) = projection_path(&items[1])?;
    if path.is_empty() {
        return None;
    }
    let Expr::Symbol(name) = base else {
        return None;
    };
    Some(name.clone())
}

fn borrow_place_origins(place: &Expr, context: &Context) -> HashSet<String> {
    if let Expr::List(items) = place {
        if items.len() == 2 && matches!(items.first(), Some(Expr::Symbol(name)) if name == "unsafe")
        {
            return borrow_place_origins(&items[1], context);
        }
    }
    let Some((base, path)) = projection_path(place) else {
        return HashSet::new();
    };
    if let Expr::Symbol(owner) = base {
        if path.is_empty() {
            HashSet::from([owner.clone()])
        } else if context.reference_origins.contains_key(owner) {
            reference_origins(base, context, true)
        } else {
            HashSet::from([owner.clone()])
        }
    } else {
        HashSet::new()
    }
}

fn borrow_place_loans(place: &Expr, context: &Context) -> Vec<(String, String)> {
    if let Expr::List(items) = place {
        if items.len() == 3
            && matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "slice-mut-idx")
        {
            let index = static_index_segment(&items[2]).unwrap_or_else(|| "*".into());
            return reference_origins(&items[1], context, true)
                .into_iter()
                .map(|owner| {
                    let loan = format!("{owner}{PLACE_SEPARATOR}slice-index-{index}");
                    (owner, loan)
                })
                .collect();
        }
    }
    let Some((base, path)) = projection_path(place) else {
        return Vec::new();
    };
    let owners = if let Expr::Symbol(owner) = base {
        if path.is_empty() {
            HashSet::from([owner.clone()])
        } else if context.reference_origins.contains_key(owner) {
            reference_origins(base, context, true)
        } else {
            HashSet::from([owner.clone()])
        }
    } else {
        HashSet::new()
    };
    owners
        .into_iter()
        .map(|owner| {
            let loan = if path.is_empty() {
                owner.clone()
            } else {
                format!(
                    "{owner}{PLACE_SEPARATOR}{}",
                    path.join(&PLACE_SEPARATOR.to_string())
                )
            };
            (owner, loan)
        })
        .collect()
}

fn ensure_origins_in_scope(origins: &HashSet<String>, context: &Context) -> Result<(), Error> {
    if let Some(owner) = origins
        .iter()
        .filter(|owner| !context.is_in_scope(owner))
        .min()
    {
        return Err(failure!(
            "reference to block-local variable '{owner}' escapes its scope"
        ));
    }
    Ok(())
}

fn scoped_result_origins(statements: &[Statement], context: &Context) -> HashSet<String> {
    let mut scoped = context.clone();
    let mut result = HashSet::new();
    for statement in statements {
        match statement {
            Statement::Let {
                name, ty, value, ..
            } => {
                let origins = reference_origins(
                    value,
                    &scoped,
                    contains_reference_type(ty, &scoped.reference_types),
                );
                if !origins.is_empty() {
                    scoped.reference_origins.insert(name.clone(), origins);
                }
                scoped.scope_bindings.insert(name.clone());
            }
            Statement::Destructure {
                pattern, ty, value, ..
            }
            | Statement::LetElse {
                pattern, ty, value, ..
            } => {
                let origins = reference_origins(
                    value,
                    &scoped,
                    contains_reference_type(ty, &scoped.reference_types),
                );
                let mut names = Vec::new();
                pattern_names(pattern, &mut names);
                for name in names {
                    if !origins.is_empty() {
                        scoped
                            .reference_origins
                            .insert(name.clone(), origins.clone());
                    }
                    scoped.scope_bindings.insert(name);
                }
            }
            Statement::Expr(value)
            | Statement::Return(Some(value))
            | Statement::BreakValue(value)
            | Statement::BreakToValue { value, .. } => {
                result = reference_origins(value, &scoped, true);
            }
            _ => {}
        }
    }
    result
}

fn reference_origins(
    expression: &Expr,
    context: &Context,
    result_contains_references: bool,
) -> HashSet<String> {
    if let Expr::List(items) = expression {
        if items.len() == 2 && matches!(items.first(), Some(Expr::Symbol(name)) if name == "unsafe")
        {
            return reference_origins(&items[1], context, result_contains_references);
        }
    }
    if !result_contains_references {
        return HashSet::new();
    }
    match expression {
        Expr::Symbol(name) => {
            let mut origins = context
                .reference_origins
                .get(name)
                .cloned()
                .unwrap_or_default();
            if let Some(fields) = context.reference_fields.get(name) {
                for (field_origins, _) in fields.values() {
                    origins.extend(field_origins.iter().cloned());
                }
            }
            origins
        }
        Expr::List(items) => {
            let Some(Expr::Symbol(operator)) = items.first() else {
                return HashSet::new();
            };
            if matches!(
                operator.as_str(),
                "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut"
            ) && items.len() == 2
            {
                return borrow_place_origins(&items[1], context);
            }
            if matches!(
                operator.as_str(),
                "slice-of"
                    | "slice-idx"
                    | "slice-range"
                    | "slice-mut-of"
                    | "slice-mut-idx"
                    | "slice-mut-split"
            ) && items.len() >= 2
            {
                return reference_origins(&items[1], context, true);
            }
            if matches!(
                operator.as_str(),
                "ptr-borrow" | "ptr-borrow-mut" | "pin-ptr-borrow" | "pin-ptr-borrow-mut"
            ) && items.len() == 3
            {
                return reference_origins(&items[1], context, true);
            }
            if operator == "get" && items.len() == 3 {
                return reference_origins(&items[1], context, true);
            }
            if operator == "clone" && items.len() == 2 {
                return reference_origins(&items[1], context, true);
            }
            if operator == "match" && items.len() >= 3 {
                let scrutinee_origins = reference_origins(&items[1], context, true);
                return items[2..]
                    .iter()
                    .filter_map(|arm| match arm {
                        Expr::List(parts) if parts.len() >= 2 => Some(parts),
                        _ => None,
                    })
                    .flat_map(|parts| {
                        let mut arm_context = context.clone();
                        let mut bindings = Vec::new();
                        pattern_names(&parts[0], &mut bindings);
                        let carries_references = match &parts[0] {
                            Expr::List(pattern) => pattern
                                .first()
                                .and_then(|head| match head {
                                    Expr::Symbol(variant) => Some(variant),
                                    _ => None,
                                })
                                .is_none_or(|variant| context.reference_variants.contains(variant)),
                            _ => true,
                        };
                        if carries_references {
                            for binding in bindings {
                                arm_context
                                    .reference_origins
                                    .insert(binding, scrutinee_origins.clone());
                            }
                        }
                        reference_origins(
                            parts.last().expect("validated match arm has a result"),
                            &arm_context,
                            true,
                        )
                    })
                    .collect();
            }
            if operator == "as" && items.len() == 3 {
                return reference_origins(&items[1], context, true);
            }
            if operator == "index" && items.len() == 3 {
                return reference_origins(&items[1], context, true);
            }
            if operator == "deref" && items.len() == 2 {
                return reference_origins(&items[1], context, true);
            }
            if matches!(operator.as_str(), "tuple" | "array" | "array-repeat") {
                return items
                    .iter()
                    .skip(1)
                    .flat_map(|item| reference_origins(item, context, true))
                    .collect();
            }
            if operator == "struct-literal" {
                return items
                    .get(2)
                    .and_then(|fields| match fields {
                        Expr::List(fields) => Some(fields),
                        _ => None,
                    })
                    .into_iter()
                    .flatten()
                    .filter_map(|field| match field {
                        Expr::List(parts) => parts.get(1),
                        _ => None,
                    })
                    .flat_map(|value| reference_origins(value, context, true))
                    .collect();
            }
            if context.reference_variants.contains(operator) {
                return items
                    .iter()
                    .skip(1)
                    .flat_map(|value| reference_origins(value, context, true))
                    .collect();
            }
            if operator == "if" {
                return items
                    .iter()
                    .skip(2)
                    .flat_map(|item| reference_origins(item, context, true))
                    .collect();
            }
            if context.reference_functions.contains(operator) {
                if let Some(parameters) = context.typed_reference_return_parameters.get(operator) {
                    // Use the typed parameter summary for exclusive returns:
                    // conservatively treating unrelated shared inputs (such
                    // as a waker) as origins creates false mutable aliases.
                    // Keep the legacy conservative rule for shared returns;
                    // it also protects existing aggregate-loan diagnostics.
                    if parameters.iter().any(|summary| summary.mutable) {
                        return parameters
                            .iter()
                            .filter(|summary| summary.mutable)
                            .filter(|summary| summary.global.is_none())
                            .filter_map(|summary| items.get(summary.parameter + 1))
                            .flat_map(|argument| reference_origins(argument, context, true))
                            .collect();
                    }
                }
            }
            if context.reference_types.contains(operator)
                || context.reference_functions.contains(operator)
            {
                return items
                    .iter()
                    .skip(1)
                    .flat_map(|item| reference_origins(item, context, true))
                    .collect();
            }
            HashSet::new()
        }
        Expr::Block(statements) | Expr::Loop(statements) => {
            scoped_result_origins(statements, context)
        }
        Expr::Labeled { expression, .. }
        | Expr::Quote(expression)
        | Expr::QuasiQuote(expression)
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => reference_origins(expression, context, true),
        _ => HashSet::new(),
    }
}

fn direct_reference_return(ty: &crate::Type, items: &[Item], seen: &mut HashSet<String>) -> bool {
    match ty {
        crate::Type::Reference { .. }
        | crate::Type::PinnedReference { .. }
        | crate::Type::Slice(_)
        | crate::Type::MutableSlice(_) => true,
        crate::Type::Named(name) if seen.insert(name.clone()) => items.iter().any(|item| {
            matches!(item, Item::TypeAlias { name: alias, target, .. }
                if alias == name && direct_reference_return(target, items, seen))
        }),
        _ => false,
    }
}

fn type_contains_reference(ty: &crate::Type, items: &[Item], seen: &mut HashSet<String>) -> bool {
    match ty {
        crate::Type::Reference { .. }
        | crate::Type::PinnedReference { .. }
        | crate::Type::Slice(_)
        | crate::Type::MutableSlice(_) => true,
        crate::Type::Array(element, _) => type_contains_reference(element, items, seen),
        crate::Type::Tuple(fields) => fields
            .iter()
            .any(|field| type_contains_reference(field, items, seen)),
        crate::Type::Named(name) if seen.insert(name.clone()) => {
            let result = items.iter().any(|item| match item {
                Item::Struct {
                    name: struct_name,
                    fields,
                    ..
                } if struct_name == name => fields
                    .iter()
                    .any(|field| type_contains_reference(&field.ty, items, seen)),
                Item::Enum {
                    name: enum_name,
                    variants,
                    ..
                } if enum_name == name => variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|field| type_contains_reference(field, items, seen)),
                Item::TypeAlias {
                    name: alias_name,
                    target,
                    ..
                } if alias_name == name => type_contains_reference(target, items, seen),
                _ => false,
            });
            seen.remove(name);
            result
        }
        _ => false,
    }
}

fn type_contains_mutable_reference(
    ty: &crate::Type,
    items: &[Item],
    seen: &mut HashSet<String>,
) -> bool {
    match ty {
        crate::Type::Reference { mutable: true, .. }
        | crate::Type::PinnedReference { mutable: true, .. } => true,
        crate::Type::Slice(_) => false,
        crate::Type::MutableSlice(_) => true,
        crate::Type::Reference { mutable: false, .. }
        | crate::Type::PinnedReference { mutable: false, .. }
        | crate::Type::RawPointer { .. } => false,
        crate::Type::Array(element, _) => type_contains_mutable_reference(element, items, seen),
        crate::Type::Tuple(fields) => fields
            .iter()
            .any(|field| type_contains_mutable_reference(field, items, seen)),
        crate::Type::Named(name) if seen.insert(name.clone()) => {
            let result = items.iter().any(|item| match item {
                Item::Struct {
                    name: struct_name,
                    fields,
                    ..
                } if struct_name == name => fields
                    .iter()
                    .any(|field| type_contains_mutable_reference(&field.ty, items, seen)),
                Item::Enum {
                    name: enum_name,
                    variants,
                    ..
                } if enum_name == name => variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|field| type_contains_mutable_reference(field, items, seen)),
                Item::TypeAlias {
                    name: alias_name,
                    target,
                    ..
                } if alias_name == name => type_contains_mutable_reference(target, items, seen),
                _ => false,
            });
            seen.remove(name);
            result
        }
        _ => false,
    }
}

fn contains_reference_type(ty: &crate::Type, reference_types: &HashSet<String>) -> bool {
    match ty {
        crate::Type::Reference { .. }
        | crate::Type::PinnedReference { .. }
        | crate::Type::Slice(_)
        | crate::Type::MutableSlice(_) => true,
        crate::Type::Array(element, _) => contains_reference_type(element, reference_types),
        crate::Type::Tuple(fields) => fields
            .iter()
            .any(|field| contains_reference_type(field, reference_types)),
        crate::Type::Named(name) => reference_types.contains(name),
        _ => false,
    }
}
