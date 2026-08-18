#![allow(non_snake_case)] // generated names mirror Lean definitions
#![cfg_attr(not(feature = "std"), no_std)]

//! Runtime support for the definitions generated from Lean.
//!
//! # Memory profile
//!
//! This crate — including everything `prod_defs!` expands into — is
//! **allocation-free**. There is no `extern crate alloc`, so a heap-allocating
//! generated type could not compile even by accident. Lean `List α` therefore
//! never becomes an owned linked list: it arrives as a borrowed `&[α]` slice
//! and leaves through a caller-owned `&mut [α]` buffer (see
//! [`ComputeError::OutputTooSmall`]).
//!
//! # Error contract
//!
//! Generated functions do not panic on caller-controlled input. A definition
//! whose body performs a partial `Nat` operation — or that calls one that does,
//! or that writes a list into a caller buffer — returns
//! `Result<_, ComputeError>`; every other definition keeps its plain return
//! type. See [`error`].

pub mod error;
pub mod spectral;

pub use error::ComputeError;
pub use spectral::SpectralOperator;

// The executable definitions in this crate come from the current Lean
// export. `just prod` runs the exporter before Cargo compiles this macro.
prod_macros::prod_defs! { ir = "kernel.ir" }
