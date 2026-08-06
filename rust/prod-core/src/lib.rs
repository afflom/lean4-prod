#![allow(non_snake_case)] // generated names mirror Lean definitions
#![cfg_attr(not(feature = "std"), no_std)]

pub mod coordinate;
pub mod spectral;

pub use coordinate::Instance;
pub use spectral::SpectralOperator;

// The executable definitions in this crate come from the current Lean
// export. `just prod` runs the exporter before Cargo compiles this macro.
prod_macros::prod_defs! { ir = "kernel.ir" }
