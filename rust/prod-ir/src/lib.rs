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
    Instance,
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
    /// Structure projection: `(proj "TypeName" <idx> <expr>)`
    Proj(String, u64, Box<Expr>),
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
}

/// A module is a collection of definitions
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Module {
    pub name: String,
    pub definitions: Vec<Definition>,
}

impl Module {
    pub fn find_def(&self, name: &str) -> Option<&Definition> {
        self.definitions.iter().find(|d| d.name == name)
    }
}
