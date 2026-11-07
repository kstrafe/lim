//! Borrow checked declaration metadata through its existing shared owner.
//! Only specialized universe maps copy owned payloads.
use super::*;

fn string_bytes(value: &String) -> usize {
    if value.is_empty() {
        0
    } else {
        64usize.saturating_add(value.capacity())
    }
}

pub(super) fn specialization(
    kernel: &mut Kernel,
    name: &str,
    levels: &[Level],
    depth: usize,
) -> Result<(Arc<Declaration>, HashMap<String, Level>)> {
    kernel.tick(depth)?;
    kernel.ensure_logical_foundation(name, depth + 1)?;
    let declaration = if let Some(declaration) = kernel.declarations.get(name)? {
        declaration
    } else {
        // Scoped nested descriptors now share their checked storage owner too.
        kernel
            .nested
            .declaration(name)?
            .ok_or_else(|| format!("unknown or unchecked kernel declaration '{name}'"))?
    };
    if declaration.universes.len() != levels.len() {
        return Err(format!(
            "'{name}' requires {} explicit universe argument(s)",
            declaration.universes.len()
        ));
    }
    if levels.is_empty() {
        return Ok((declaration, HashMap::new()));
    }
    kernel.charge_work(levels.len())?;

    // Four buckets per input entry conservatively covers HashMap's power-of-
    // two table, load-factor slack and control bytes. Reserve the full table
    // and every owned key/level payload before allocating or cloning any of it.
    let bucket_bytes = std::mem::size_of::<(String, Level)>().saturating_add(1);
    let mut bytes =
        256usize.saturating_add(levels.len().saturating_mul(4).saturating_mul(bucket_bytes));
    for (universe, level) in declaration.universes.iter().zip(levels) {
        bytes = bytes
            .saturating_add(string_bytes(universe))
            .saturating_add(level.storage_memory_weight());
    }
    kernel.charge_transformation(bytes)?;
    let mut values = HashMap::with_capacity(levels.len());
    for (universe, level) in declaration.universes.iter().zip(levels) {
        values.insert(universe.clone(), level.clone());
    }
    Ok((declaration, values))
}

pub(super) fn family(
    kernel: &mut Kernel,
    name: &str,
    levels: &[Level],
    depth: usize,
) -> Result<(Arc<Declaration>, HashMap<String, Level>)> {
    let (declaration, map) = specialization(kernel, name, levels, depth)?;
    if declaration.family.is_none() {
        return Err("an inductive datatype is required".into());
    }
    Ok((declaration, map))
}

pub(super) fn natural(
    kernel: &mut Kernel,
    name: &str,
    depth: usize,
) -> Result<Option<Arc<Declaration>>> {
    kernel.tick(depth)?;
    if kernel.provisional_family(name) || kernel.nested.contains_key(name)? {
        return Ok(None);
    }
    let Some(declaration) = kernel.declarations.get(name)? else {
        return Ok(None);
    };
    if !declaration.universes.is_empty() {
        return Ok(None);
    }
    let Some(family) = &declaration.family else {
        return Ok(None);
    };
    if natural_shape(name, family)? {
        Ok(Some(declaration))
    } else {
        Ok(None)
    }
}
