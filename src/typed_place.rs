//! Resolved place identity for typed ownership analyses. Identifier punctuation
//! is never interpreted as a projection, and member IDs include their owner.

use crate::typed_body::{Body, NodeId, NodeKind, PlaceRoot, Projection};
use crate::typed_ir::{DeclarationId, FieldId, VariantId};
use crate::Expr;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum Segment {
    Dereference,
    Field(FieldId),
    Tuple(usize),
    Payload(VariantId, usize),
    Index(u128),
    DynamicIndex,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct Place {
    pub root: PlaceRoot,
    pub segments: Vec<Segment>,
}

impl Place {
    pub fn root(root: PlaceRoot) -> Self {
        Self {
            root,
            segments: Vec::new(),
        }
    }

    pub fn from_assignment(body: &Body, root: &PlaceRoot, projection: &Projection) -> Self {
        let mut place = Self::root(root.clone());
        match projection {
            Projection::Local => {}
            Projection::Array(index) => place.segments.push(index_segment(body, *index)),
            Projection::Field(id) => place.segments.push(Segment::Field(*id)),
            Projection::Tuple(index) => place.segments.push(Segment::Tuple(*index)),
            Projection::Payload(variant, index) => {
                place.segments.push(Segment::Payload(*variant, *index));
            }
        }
        place
    }

    pub fn from_expression(body: &Body, id: NodeId) -> Option<Self> {
        match &body.nodes.get(id.0)?.kind {
            NodeKind::Symbol {
                binding: Some(binding),
                ..
            } => Some(Self::root(PlaceRoot::Local(*binding))),
            NodeKind::Declaration(DeclarationId::Global(id)) => {
                Some(Self::root(PlaceRoot::Global(*id)))
            }
            NodeKind::Form { head, children, .. } => {
                let mut place = Self::from_expression(body, *children.get(1)?)?;
                match head.as_str() {
                    "deref" if children.len() == 2 => {
                        place.segments.push(Segment::Dereference);
                    }
                    "get" if children.len() == 3 => match &body.nodes[children[2].0].kind {
                        NodeKind::Declaration(DeclarationId::Field(id)) => {
                            place.segments.push(Segment::Field(*id));
                        }
                        _ => place.segments.push(Segment::Tuple(
                            usize::try_from(literal_index(body, children[2])?).ok()?,
                        )),
                    },
                    "get-payload" if children.len() == 4 => {
                        let NodeKind::Declaration(DeclarationId::Variant(variant)) =
                            body.nodes[children[2].0].kind
                        else {
                            return None;
                        };
                        let index = usize::try_from(literal_index(body, children[3])?).ok()?;
                        place.segments.push(Segment::Payload(variant, index));
                    }
                    "index" if children.len() == 3 => {
                        place.segments.push(index_segment(body, children[2]));
                    }
                    _ => return None,
                }
                Some(place)
            }
            _ => None,
        }
    }

    pub fn from_dereference_write(body: &Body, target: NodeId) -> Option<Self> {
        if let NodeKind::Form { head, children, .. } = &body.nodes.get(target.0)?.kind {
            if head == "slice-mut-idx" {
                // Mutable split-slice elements carry a partition projection
                // that is not yet represented by ordinary place segments.
                return None;
            }
            if matches!(head.as_str(), "borrow" | "borrow-mut") && children.len() >= 2 {
                return Self::from_expression(body, children[1]);
            }
        }
        let mut place = Self::from_expression(body, target)?;
        place.segments.push(Segment::Dereference);
        Some(place)
    }

    /// A parent place overlaps any descendant. A dynamic index may name any
    /// element of the same array, while distinct concrete indices do not
    /// overlap. This is about identity, not whether a particular loan is live.
    pub fn overlaps(&self, other: &Self) -> bool {
        self.root == other.root
            && self
                .segments
                .iter()
                .zip(&other.segments)
                .all(|(left, right)| {
                    left == right
                        || matches!(left, Segment::DynamicIndex)
                        || matches!(right, Segment::DynamicIndex)
                })
    }
}

fn literal_index(body: &Body, id: NodeId) -> Option<u128> {
    match &body.nodes.get(id.0)?.kind {
        NodeKind::Literal(Expr::Integer(index)) => (*index).try_into().ok(),
        NodeKind::Literal(Expr::UnsignedInteger(index)) => Some(*index),
        NodeKind::Form { head, children, .. } if head == "literal" => {
            literal_index(body, *children.get(2)?)
        }
        _ => None,
    }
}

fn index_segment(body: &Body, id: NodeId) -> Segment {
    literal_index(body, id).map_or(Segment::DynamicIndex, Segment::Index)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn punctuation_is_part_of_binding_identity_not_a_projection() {
        let source = "(#struct A ((b u64)))
          (#fn main () u64
            (#let a A (#struct-literal A ((b 4u64))))
            (#let a.b u64 8u64)
            (#return (#u64.+.wrap a.b (#get a b))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let dotted = body
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match &node.kind {
                NodeKind::Symbol { name, .. } if name == "a.b" => Some(NodeId(index)),
                _ => None,
            })
            .unwrap();
        let field = body
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match &node.kind {
                NodeKind::Form { head, .. } if head == "get" => Some(NodeId(index)),
                _ => None,
            })
            .unwrap();
        let dotted = Place::from_expression(body, dotted).unwrap();
        let field = Place::from_expression(body, field).unwrap();
        assert_ne!(dotted, field);
        assert_ne!(dotted.root, field.root);
    }

    #[test]
    fn dynamic_and_concrete_indices_have_distinct_identities() {
        let root = PlaceRoot::Local(crate::typed_body::BindingId(0));
        let dynamic = Place {
            root: root.clone(),
            segments: vec![Segment::DynamicIndex],
        };
        let first = Place {
            root: root.clone(),
            segments: vec![Segment::Index(0)],
        };
        let second = Place {
            root,
            segments: vec![Segment::Index(1)],
        };
        assert_ne!(dynamic, first);
        assert_ne!(first, second);
        assert!(dynamic.overlaps(&first));
        assert!(!first.overlaps(&second));
    }

    #[test]
    fn same_spelled_fields_on_different_owners_keep_distinct_ids() {
        let source = "(#struct A ((value u64))) (#struct B ((value u64)))
          (#fn main () u64
            (#let a A (#struct-literal A ((value 1u64))))
            (#let b B (#struct-literal B ((value 2u64))))
            (#return (#u64.+.wrap (#get a value) (#get b value))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let fields = body
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| match &node.kind {
                NodeKind::Form { head, .. } if head == "get" => {
                    Place::from_expression(body, NodeId(index))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(fields.len(), 2);
        assert_ne!(fields[0].segments, fields[1].segments);
    }

    #[test]
    fn checked_array_and_payload_projections_have_structural_segments() {
        let array = crate::parse_program(include_str!("../examples/array.lim")).unwrap();
        let checked = crate::CheckedProgram::validate(&array).unwrap();
        let graph = &checked.declarations().flows["main"];
        assert!(graph.nodes.iter().any(|node| matches!(
            &node.action,
            crate::typed_flow::FlowAction::Assign {
                place: Place { root: PlaceRoot::Local(_), segments },
                ..
            } if segments == &[Segment::Index(1)]
        )));

        let payload =
            crate::parse_program(include_str!("../examples/large_reference_projections.lim"))
                .unwrap();
        let checked = crate::CheckedProgram::validate(&payload).unwrap();
        let body = &checked.declarations().bodies["main"];
        let projection = body
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match &node.kind {
                NodeKind::Form { head, .. } if head == "get-payload" => {
                    Place::from_expression(body, NodeId(index))
                }
                _ => None,
            })
            .unwrap();
        assert!(matches!(
            projection.segments.as_slice(),
            [Segment::Payload(_, 0)]
        ));
    }
}
