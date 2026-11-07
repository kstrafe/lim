//! Conservative equality of original source closures in one delayed machine.
//! Code identity and its actual free bindings suffice; no thunk is forced and
//! no memoized head or incomplete neutral syntax is used as a source value.
use super::*;

/// Compare the same immutable code under its captured environments. Cache
/// entries retain their code owner so pointer identities cannot be recycled.
/// Different code and unsupported distinct thunks conservatively miss.
#[expect(clippy::too_many_arguments)]
pub(super) fn same_closure(
    kernel: &mut Kernel,
    nodes: &[Thunk],
    bindings: &[Binding],
    free_cache: &mut Vec<(T, Vec<usize>)>,
    left: &T,
    left_env: Environment,
    right: &T,
    right_env: Environment,
    depth: usize,
) -> Result<bool> {
    kernel.tick(depth)?;
    if !Arc::ptr_eq(left, right) {
        return Ok(false);
    }
    if left_env == right_env {
        return Ok(true);
    }
    let free = free_variables(kernel, free_cache, left, depth + 1)?;
    let count = match &free {
        FreeVariables::Cached(entry) => free_cache[*entry].1.len(),
        FreeVariables::Uncached(indices) => indices.len(),
    };
    for position in 0..count {
        kernel.tick(depth)?;
        // Copy one index before recursion: recursion can grow the cache and
        // move its storage, but entries are only appended, never replaced.
        let index = match &free {
            FreeVariables::Cached(entry) => free_cache[*entry].1[position],
            FreeVariables::Uncached(indices) => indices[position],
        };
        let Some(left_slot) = binding_slot(kernel, bindings, left_env, index, depth + 1)? else {
            return Ok(false);
        };
        let Some(right_slot) = binding_slot(kernel, bindings, right_env, index, depth + 1)? else {
            return Ok(false);
        };
        if left_slot == right_slot {
            continue;
        }
        let (Some(Thunk::Source(left, left_env)), Some(Thunk::Source(right, right_env))) =
            (nodes.get(left_slot), nodes.get(right_slot))
        else {
            return Ok(false);
        };
        if !same_closure(
            kernel,
            nodes,
            bindings,
            free_cache,
            left,
            *left_env,
            right,
            *right_env,
            depth + 1,
        )? {
            return Ok(false);
        }
    }
    Ok(true)
}

enum FreeVariables {
    Cached(usize),
    Uncached(Vec<usize>),
}

/// Collect exactly the root-relative free indices, including annotations and
/// let definitions. The kernel walker supplies every node's binder scope.
fn free_variables(
    kernel: &mut Kernel,
    cache: &mut Vec<(T, Vec<usize>)>,
    value: &T,
    depth: usize,
) -> Result<FreeVariables> {
    for (index, (source, _)) in cache.iter().enumerate() {
        kernel.tick(depth)?;
        if Arc::ptr_eq(source, value) {
            return Ok(FreeVariables::Cached(index));
        }
    }
    let mut free = Vec::new();
    kernel.transform_shared(
        value,
        0,
        depth + 1,
        &mut |kernel, index, binders| {
            if index >= binders {
                let index = index - binders;
                // Charge the entire possible duplicate scan before doing it.
                kernel.charge_work(free.len())?;
                if !free.contains(&index) {
                    reserve(kernel, &mut free)?;
                    free.push(index);
                }
            }
            Ok(term(Term::Var(index)))
        },
        &mut |level| Ok(level.clone()),
    )?;
    if cache.len() >= 64 {
        return Ok(FreeVariables::Uncached(free));
    }
    reserve(kernel, cache)?;
    let entry = cache.len();
    cache.push((value.clone(), free));
    Ok(FreeVariables::Cached(entry))
}

fn binding_slot(
    kernel: &mut Kernel,
    bindings: &[Binding],
    mut environment: Environment,
    mut index: usize,
    depth: usize,
) -> Result<Option<Slot>> {
    while let Some(at) = environment {
        kernel.tick(depth)?;
        let Some(binding) = bindings.get(at) else {
            return Ok(None);
        };
        if index == 0 {
            return Ok(Some(binding.value));
        }
        index -= 1;
        environment = binding.parent;
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn variable(index: usize) -> T {
        term(Term::Var(index))
    }
    fn natural(name: &str) -> T {
        term(Term::Global(name.into(), vec![]))
    }
    fn compare(source: &T, left: T, right: T) -> bool {
        let mut kernel = Kernel::new();
        let nodes = [Thunk::Source(left, None), Thunk::Source(right, None)];
        let bindings = [
            Binding {
                value: 0,
                parent: None,
            },
            Binding {
                value: 1,
                parent: None,
            },
        ];
        same_closure(
            &mut kernel,
            &nodes,
            &bindings,
            &mut vec![],
            source,
            Some(0),
            source,
            Some(1),
            0,
        )
        .unwrap()
    }

    #[test]
    fn local_binders_ignore_unrelated_captures_but_annotations_do_not() {
        let local = term(Term::Lam(natural("#pt-nat"), variable(0)));
        assert!(compare(&local, natural("#pt-nat"), natural("Other")));
        let annotation = term(Term::Lam(variable(0), variable(0)));
        assert!(!compare(&annotation, natural("#pt-nat"), natural("Other")));
    }

    #[test]
    fn erased_let_values_and_nested_outer_references_remain_dependencies() {
        let erased = term(Term::Let(
            natural("#pt-nat"),
            variable(0),
            natural("#pt-nat"),
        ));
        assert!(!compare(&erased, natural("#pt-nat"), natural("Other")));
        let nested = term(Term::Lam(natural("#pt-nat"), variable(1)));
        assert!(!compare(&nested, natural("#pt-nat"), natural("Other")));
    }

    #[test]
    fn equal_code_reuses_identical_captures_and_different_code_misses() {
        let source = variable(0);
        let captured = natural("#pt-nat");
        assert!(compare(&source, captured.clone(), captured));
        let mut kernel = Kernel::new();
        assert!(!same_closure(
            &mut kernel,
            &[],
            &[],
            &mut vec![],
            &source,
            None,
            &variable(0),
            None,
            0
        )
        .unwrap());
    }
}
