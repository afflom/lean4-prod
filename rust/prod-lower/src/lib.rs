//! Language-neutral lowering: IR → Target IR.
//!
//! Everything in this crate is shared by every backend. A backend's own
//! opinions live in a [`profile::TargetProfile`] it hands in, never in
//! branches here on which language is being generated.
#![no_std]

extern crate alloc;

pub mod names;
pub mod profile;
pub mod shape;
