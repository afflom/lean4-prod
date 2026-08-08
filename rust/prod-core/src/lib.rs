#![allow(non_snake_case)] // generated names mirror Lean definitions
#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

pub mod coordinate;
pub mod spectral;

pub use coordinate::Instance;
pub use spectral::SpectralOperator;

// `Box` must be nameable by macro-expanded generated code (`List::Cons`
// reconstruction) under both std and no_std builds.
use alloc::boxed::Box;

/// Runtime representation of Lean's `List α` for generated definitions:
/// `List.nil`/`List.cons` lower to `List::Nil`/`List::Cons(head, Box<tail>)`,
/// so structural recursion on Lean lists maps to Rust `match` without cloning.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

// The executable definitions in this crate come from the current Lean
// export. `just prod` runs the exporter before Cargo compiles this macro.
prod_macros::prod_defs! { ir = "kernel.ir" }
