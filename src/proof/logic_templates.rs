//! Bounded reusable Boolean circuit fragments.
//!
//! A template stores only the transitive cone of its roots. Its input list
//! records the source circuit's input node IDs in sorted order; replay maps
//! those input leaves to arbitrary bits in the destination circuit.
use super::{Bit, Circuit, Error, Gate, Result, FALSE, NODE_LIMIT};

#[derive(Clone, Debug)]
pub(in crate::proof) struct Template {
    /// Original circuit input node IDs, in deterministic source order.
    inputs: Vec<usize>,
    /// Compact, topologically ordered gates. Gate::Input entries correspond
    /// one-to-one with `input_slots` entries containing Some(slot).
    nodes: Vec<Gate>,
    input_slots: Vec<Option<usize>>,
    roots: Vec<Bit>,
}

impl Template {
    pub(in crate::proof) fn inputs(&self) -> &[usize] {
        &self.inputs
    }

    pub(in crate::proof) fn node_count(&self) -> usize {
        self.nodes.len()
    }

    pub(in crate::proof) fn retained_bytes(&self) -> usize {
        std::mem::size_of::<Self>()
            .saturating_add(
                self.inputs
                    .capacity()
                    .saturating_mul(std::mem::size_of::<usize>()),
            )
            .saturating_add(
                self.nodes
                    .capacity()
                    .saturating_mul(std::mem::size_of::<Gate>()),
            )
            .saturating_add(
                self.input_slots
                    .capacity()
                    .saturating_mul(std::mem::size_of::<Option<usize>>()),
            )
            .saturating_add(
                self.roots
                    .capacity()
                    .saturating_mul(std::mem::size_of::<Bit>()),
            )
    }

    fn validate(&self) -> Result<()> {
        if self.nodes.len() > NODE_LIMIT
            || self.roots.len() > NODE_LIMIT
            || self.inputs.len() > NODE_LIMIT
            || self.input_slots.len() != self.nodes.len()
        {
            return Err(Error::limit(
                "Boolean circuit template exceeds its node budget",
            ));
        }
        if self.inputs.iter().any(|&id| id == 0 || id > NODE_LIMIT)
            || self.inputs.windows(2).any(|pair| pair[0] >= pair[1])
        {
            return Err(Error::checker("malformed Boolean circuit template inputs"));
        }

        let mut slots = vec![false; self.inputs.len()];
        for (index, (&gate, &slot)) in self.nodes.iter().zip(&self.input_slots).enumerate() {
            let node_id = index + 1;
            match gate {
                Gate::Input => {
                    let Some(slot) = slot else {
                        return Err(Error::checker(
                            "Boolean circuit template input has no binding slot",
                        ));
                    };
                    let Some(seen) = slots.get_mut(slot) else {
                        return Err(Error::checker(
                            "Boolean circuit template input slot is out of range",
                        ));
                    };
                    if *seen {
                        return Err(Error::checker(
                            "Boolean circuit template repeats an input slot",
                        ));
                    }
                    *seen = true;
                }
                Gate::And(a, b) | Gate::Xor(a, b) => {
                    if slot.is_some()
                        || !template_bit_is_prior(a, node_id)
                        || !template_bit_is_prior(b, node_id)
                    {
                        return Err(Error::checker(
                            "Boolean circuit template has a non-topological gate edge",
                        ));
                    }
                }
            }
        }
        if slots.iter().any(|seen| !seen)
            || self
                .roots
                .iter()
                .any(|&root| !template_bit_is_prior(root, self.nodes.len() + 1))
        {
            return Err(Error::checker(
                "Boolean circuit template has an invalid input or root",
            ));
        }
        Ok(())
    }
}

fn template_bit_is_prior(bit: Bit, exclusive_node_id: usize) -> bool {
    ((bit >> 1) as usize) < exclusive_node_id
}

fn remap_bit(bit: Bit, nodes: &[Bit]) -> Option<Bit> {
    let old_id = (bit >> 1) as usize;
    let mapped = *nodes.get(old_id)?;
    Some(mapped ^ (bit & 1))
}

impl Circuit {
    pub(in crate::proof) fn template(&mut self, roots: &[Bit]) -> Result<Template> {
        if let Some(error) = &self.failure {
            return Err(error.clone());
        }
        if !self.valid_bits(roots) {
            let error = Error::checker("invalid root in Boolean circuit template");
            self.poison(error.clone());
            return Err(error);
        }

        let node_count = self.nodes.len();
        if node_count > NODE_LIMIT || roots.len() > NODE_LIMIT {
            let error = Error::limit("Boolean circuit template exceeds its node budget");
            self.poison(error.clone());
            return Err(error);
        }
        let mut needed = vec![false; node_count + 1];
        let mut pending = roots
            .iter()
            .map(|root| (root >> 1) as usize)
            .filter(|&id| id != 0)
            .collect::<Vec<_>>();
        while let Some(id) = pending.pop() {
            if id == 0 {
                continue;
            }
            if id > node_count {
                let error = Error::checker("invalid Boolean circuit template dependency");
                self.poison(error.clone());
                return Err(error);
            }
            if needed[id] {
                continue;
            }
            needed[id] = true;
            match self.nodes[id - 1] {
                Gate::Input => {}
                Gate::And(a, b) | Gate::Xor(a, b) => {
                    if !template_bit_is_prior(a, id) || !template_bit_is_prior(b, id) {
                        let error =
                            Error::checker("non-topological Boolean circuit template source");
                        self.poison(error.clone());
                        return Err(error);
                    }
                    pending.push((a >> 1) as usize);
                    pending.push((b >> 1) as usize);
                }
            }
        }

        let inputs = (1..=node_count)
            .filter(|&id| needed[id] && matches!(self.nodes[id - 1], Gate::Input))
            .collect::<Vec<_>>();
        let mut input_lookup = vec![None; node_count + 1];
        for (slot, &id) in inputs.iter().enumerate() {
            input_lookup[id] = Some(slot);
        }
        // Each compact ID maps back to its original circuit bit. ID zero is
        // retained as the false constant, so complements remain bitwise exact.
        let mut compact = vec![FALSE; node_count + 1];
        let mut nodes = Vec::new();
        let mut input_slots = Vec::new();
        for id in 1..=node_count {
            if !needed[id] {
                continue;
            }
            let gate = match self.nodes[id - 1] {
                Gate::Input => {
                    input_slots.push(input_lookup[id]);
                    Gate::Input
                }
                Gate::And(a, b) => {
                    input_slots.push(None);
                    Gate::And(
                        remap_bit(a, &compact).expect("circuit gates reference earlier nodes"),
                        remap_bit(b, &compact).expect("circuit gates reference earlier nodes"),
                    )
                }
                Gate::Xor(a, b) => {
                    input_slots.push(None);
                    Gate::Xor(
                        remap_bit(a, &compact).expect("circuit gates reference earlier nodes"),
                        remap_bit(b, &compact).expect("circuit gates reference earlier nodes"),
                    )
                }
            };
            nodes.push(gate);
            compact[id] = (nodes.len() as Bit) << 1;
        }
        if nodes.len() > NODE_LIMIT {
            let error = Error::limit("Boolean circuit template exceeds its node budget");
            self.poison(error.clone());
            return Err(error);
        }
        let mapped_roots = roots
            .iter()
            .map(|&root| {
                remap_bit(root, &compact)
                    .ok_or_else(|| Error::checker("invalid root in Boolean circuit template"))
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(Template {
            inputs,
            nodes,
            input_slots,
            roots: mapped_roots,
        })
    }

    pub(in crate::proof) fn instantiate_template(
        &mut self,
        template: &Template,
        bindings: &[Bit],
    ) -> Result<Vec<Bit>> {
        if let Some(error) = &self.failure {
            return Err(error.clone());
        }
        if let Err(error) = template.validate() {
            self.poison(error.clone());
            return Err(error);
        }
        if bindings.len() != template.inputs.len() {
            let error = Error::checker("Boolean circuit template binding count mismatch");
            self.poison(error.clone());
            return Err(error);
        }
        if !self.valid_bits(bindings) {
            let error = Error::checker("invalid Boolean circuit template binding");
            self.poison(error.clone());
            return Err(error);
        }

        let mut values = Vec::with_capacity(template.nodes.len() + 1);
        values.push(FALSE);
        for (&gate, &slot) in template.nodes.iter().zip(&template.input_slots) {
            let value = match gate {
                Gate::Input => bindings[slot.expect("validated input slot")],
                Gate::And(a, b) => {
                    let a = remap_bit(a, &values).expect("validated topological template edge");
                    let b = remap_bit(b, &values).expect("validated topological template edge");
                    self.and(a, b)
                }
                Gate::Xor(a, b) => {
                    let a = remap_bit(a, &values).expect("validated topological template edge");
                    let b = remap_bit(b, &values).expect("validated topological template edge");
                    self.xor(a, b)
                }
            };
            if let Some(error) = &self.failure {
                return Err(error.clone());
            }
            values.push(value);
        }
        template
            .roots
            .iter()
            .map(|&root| {
                remap_bit(root, &values)
                    .ok_or_else(|| Error::checker("invalid Boolean circuit template root"))
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proof::logic::TRUE;
    use crate::proof::ProofOutcome;
    use std::collections::HashMap;

    fn evaluate(circuit: &Circuit, bit: Bit, inputs: &HashMap<usize, bool>) -> bool {
        let mut values = Vec::with_capacity(circuit.nodes.len() + 1);
        values.push(false);
        for (index, gate) in circuit.nodes.iter().enumerate() {
            let value = match *gate {
                Gate::Input => *inputs.get(&(index + 1)).expect("assigned circuit input"),
                Gate::And(a, b) => evaluate_node(a, &values) && evaluate_node(b, &values),
                Gate::Xor(a, b) => evaluate_node(a, &values) ^ evaluate_node(b, &values),
            };
            values.push(value);
        }
        evaluate_node(bit, &values)
    }

    fn evaluate_node(bit: Bit, values: &[bool]) -> bool {
        values[(bit >> 1) as usize] ^ (bit & 1 != 0)
    }

    #[test]
    fn exhaustive_roundtrip_preserves_roots_complements_and_shared_cones() {
        let mut source = Circuit::new();
        let x = source.fresh();
        let y = source.fresh();
        let unused = source.fresh();
        let shared = source.xor(x, y);
        let left = source.and(shared ^ 1, x);
        let right = source.xor(shared, y ^ 1);
        let roots = [left, right, shared ^ 1, FALSE, TRUE];
        let template = source.template(&roots).unwrap();
        assert_eq!(template.inputs(), &[(x >> 1) as usize, (y >> 1) as usize]);
        assert_eq!(template.node_count(), 5);
        assert!(template.retained_bytes() >= std::mem::size_of::<Template>());
        assert!(!template.inputs().contains(&((unused >> 1) as usize)));

        let mut destination = Circuit::new();
        let p = destination.fresh();
        let q = destination.fresh();
        let binding = destination.xor(p, q);
        let bindings = [binding ^ 1, q];
        let replayed = destination
            .instantiate_template(&template, &bindings)
            .unwrap();
        assert_eq!(replayed.len(), roots.len());

        for mask in 0..4 {
            let p_value = mask & 1 != 0;
            let q_value = mask & 2 != 0;
            let destination_values =
                HashMap::from([((p >> 1) as usize, p_value), ((q >> 1) as usize, q_value)]);
            let bound_x = p_value ^ q_value ^ true;
            let bound_y = q_value;
            let expected_inputs = HashMap::from([
                ((x >> 1) as usize, bound_x),
                ((y >> 1) as usize, bound_y),
                ((unused >> 1) as usize, false),
            ]);
            for index in 0..roots.len() {
                assert_eq!(
                    evaluate(&destination, replayed[index], &destination_values),
                    evaluate(&source, roots[index], &expected_inputs),
                    "root {index}, assignment {mask}"
                );
            }
            // Confirm the chosen bindings are independently represented by the
            // destination circuit, including the complemented first binding.
            assert_eq!(
                evaluate(&destination, bindings[0], &destination_values),
                bound_x
            );
            assert_eq!(
                evaluate(&destination, bindings[1], &destination_values),
                bound_y
            );
        }
    }

    #[test]
    fn roots_can_be_replayed_with_zero_inputs_and_constants_only() {
        let mut source = Circuit::new();
        let template = source.template(&[FALSE, TRUE]).unwrap();
        assert_eq!(template.inputs(), &[]);
        assert_eq!(template.node_count(), 0);
        let mut destination = Circuit::new();
        assert_eq!(
            destination.instantiate_template(&template, &[]).unwrap(),
            [FALSE, TRUE]
        );
    }

    #[test]
    fn malformed_template_is_checker_error_and_poison_is_sticky() {
        let mut source = Circuit::new();
        let x = source.fresh();
        let template = source.template(&[x]).unwrap();
        let mut malformed = template.clone();
        malformed.input_slots[0] = None;

        let mut destination = Circuit::new();
        let error = destination
            .instantiate_template(&malformed, &[TRUE])
            .unwrap_err();
        assert_eq!(
            error.diagnostic_code().proof_outcome(),
            Some(ProofOutcome::CheckerError)
        );
        assert!(destination
            .instantiate_template(&template, &[TRUE])
            .is_err());
    }

    #[test]
    fn malformed_edges_and_binding_shapes_poison_the_destination() {
        let mut source = Circuit::new();
        let x = source.fresh();
        let y = source.fresh();
        let root = source.and(x, y);
        let template = source.template(&[root]).unwrap();

        let mut bad_edge = template.clone();
        bad_edge.nodes[2] = Gate::And((4 << 1) as Bit, FALSE);
        let mut destination = Circuit::new();
        let error = destination
            .instantiate_template(&bad_edge, &[FALSE, FALSE])
            .unwrap_err();
        assert_eq!(
            error.diagnostic_code().proof_outcome(),
            Some(ProofOutcome::CheckerError)
        );

        let mut destination = Circuit::new();
        assert!(destination
            .instantiate_template(&template, &[FALSE])
            .is_err());
        assert!(destination.failure.is_some());
    }

    #[test]
    fn invalid_export_root_poison_is_sticky() {
        let mut circuit = Circuit::new();
        let invalid = 2;
        let error = circuit.template(&[invalid]).unwrap_err();
        assert_eq!(
            error.diagnostic_code().proof_outcome(),
            Some(ProofOutcome::CheckerError)
        );
        assert!(circuit.template(&[]).is_err());
    }

    #[test]
    fn export_handles_constant_edges_and_rejects_forward_dependencies() {
        let mut circuit = Circuit::new();
        let input = circuit.fresh();
        circuit.nodes.push(Gate::And(input, TRUE));
        let template = circuit.template(&[4]).unwrap();
        let mut destination = Circuit::new();
        assert_eq!(
            destination
                .instantiate_template(&template, &[TRUE])
                .unwrap(),
            [TRUE]
        );
        let mut malformed = Circuit::new();
        malformed.nodes.push(Gate::And(4, FALSE));
        let error = malformed.template(&[2]).unwrap_err();
        assert_eq!(
            error.diagnostic_code().proof_outcome(),
            Some(crate::ProofOutcome::CheckerError)
        );
        assert!(malformed.template(&[]).is_err());
    }
}
