//! Declaration interfaces shared by generated-code planning passes.
//!
//! These signatures and deferred layouts describe names and types only. They
//! do not provide executable bodies or authorize access to deferred storage.
use std::collections::HashMap;

use crate::{EnumVariant, Function, Span};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum LayoutKind {
    Enum,
    Struct,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DeferredLayout {
    pub kind: LayoutKind,
    pub span: Span,
    pub linear: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct FunctionInterface {
    /// Signature only; generated interfaces never stand in for checked bodies.
    pub declaration: Function,
    pub span: Option<Span>,
    pub is_generated: bool,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct DeclarationInterfaces {
    pub functions: HashMap<String, FunctionInterface>,
    pub protocols: HashMap<String, Vec<EnumVariant>>,
    pub deferred_layouts: HashMap<String, DeferredLayout>,
    pub generated_names: HashMap<String, Span>,
}
