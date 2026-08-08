//! prod-ir: Intermediate Representation for Lean 4 → Rust extraction
//!
//! Defines the AST types and a `nom` parser for a compact sexp-like IR format
//! that Lean 4 exports. This crate is `#![no_std]` (with `alloc`) so it can
//! run on wasm32 and embedded targets.

#![no_std]

extern crate alloc;

pub mod parser;

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use serde::{Deserialize, Serialize};

/// A typed definition exported from Lean 4
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Definition {
    pub name: String,
    pub params: Vec<(String, Type)>,
    pub ret: Type,
    pub body: Expr,
}

/// Lean types mapped to Rust-targeted types
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Type {
    Nat,
    Int,
    Bool,
    /// A type declared in this module's `types` list, by full Lean name.
    /// Renders as a generated Rust struct or enum.
    Named(String),
    Option(Box<Type>),
    Vec(Box<Type>),
    /// Lean `List α`. Allocation-free by policy, so the rendering depends on
    /// position: a parameter becomes a borrowed `&[α]` slice (matched with
    /// slice patterns), and a return type becomes a caller-owned
    /// `output: &mut [α]` buffer plus a written-length result. See
    /// `prod_codegen` for the lowering.
    List(Box<Type>),
    Tuple(Vec<Type>),
    /// Unmapped or complex type requiring manual handling
    Opaque(String),
}

/// A match alternative: `(alt "CtorName" (binders...) <body>)`
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Alt {
    pub ctor: String,
    pub binders: Vec<String>,
    pub body: Expr,
}

/// Expression AST — a simplified lambda calculus with constants,
/// extended with LCNF-flavored nodes (cases/ctor/proj/jp/jmp/unreachable)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Expr {
    Nat(u64),
    Int(i64),
    Bool(bool),
    Var(String),
    Param(usize),             // De Bruijn-style parameter index
    Field(Box<Expr>, String), // e.g., (field (param 0) "stride")
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Mod(Box<Expr>, Box<Expr>),
    Shl(Box<Expr>, Box<Expr>),
    Pow(Box<Expr>, Box<Expr>),
    Eq(Box<Expr>, Box<Expr>),
    Lt(Box<Expr>, Box<Expr>),
    Le(Box<Expr>, Box<Expr>),
    Gt(Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Let(String, Box<Expr>, Box<Expr>),
    Call(String, Vec<Expr>),
    /// LCNF `cases_on`: scrutinee, constructor alternatives, optional default
    Match {
        scrut: Box<Expr>,
        alts: Vec<Alt>,
        default: Option<Box<Expr>>,
    },
    /// Constructor application: `(ctor "Name" args...)`
    Ctor(String, Vec<Expr>),
    /// Structure projection: `(proj "TypeName" "fieldName" <expr>)`.
    ///
    /// The field *name*, not an index: the exporter resolves it against Lean's
    /// own structure info, so the declaration and the projection cannot
    /// disagree. An index-based form would need a second table in codegen that
    /// has to be kept in sync, and getting that wrong swaps fields silently.
    Proj(String, String, Box<Expr>),
    /// LCNF join point declaration: `(jp <name> (params...) <body>)`
    Jp {
        name: String,
        params: Vec<String>,
        body: Box<Expr>,
    },
    /// LCNF jump to a join point: `(jmp <name> args...)`
    Jmp(String, Vec<Expr>),
    /// LCNF `Unreachable` (dead branch)
    Unreachable,
    /// Placeholder for unhandled constructs
    Opaque(String),
    /// A call the exporter could not resolve: the callee is neither
    /// `@[prod]`-tagged nor on the operator whitelist. Deliberately distinct
    /// from `Call` so codegen rejects it instead of emitting a Rust call to a
    /// function that does not exist.
    Extern(String, Vec<Expr>),
}

/// One constructor of a generated type: `(ctor "Full.Name.mk" (field Type)...)`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CtorDecl {
    /// Full Lean constructor name, e.g. `UorAtlas.Instance.mk`.
    pub name: String,
    /// Value fields in declaration order. `Prop` fields are erased by the
    /// exporter and never appear here.
    pub fields: Vec<(String, Type)>,
}

/// A Lean inductive rendered as a Rust type: one ctor means a struct, several
/// mean an enum with named-field variants.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TypeDecl {
    /// Full Lean type name, e.g. `UorAtlas.Instance`.
    pub name: String,
    pub ctors: Vec<CtorDecl>,
    /// Set when the exporter reached this type but cannot describe it, with
    /// the reason. The type is still declared so that codegen can reject a
    /// reference to it *precisely* rather than reporting a generic unknown
    /// name. `ctors` is empty when this is set.
    pub unsupported: Option<String>,
}

/// A module is a collection of definitions
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Module {
    pub name: String,
    /// Type declarations, emitted before the definitions that use them.
    pub types: Vec<TypeDecl>,
    pub definitions: Vec<Definition>,
}

impl Module {
    pub fn find_def(&self, name: &str) -> Option<&Definition> {
        self.definitions.iter().find(|d| d.name == name)
    }
}
