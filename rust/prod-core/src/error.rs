//! The error contract of generated code.
//!
//! Generated functions never panic on caller-controlled input: every partial
//! operation the Nat lowering emits (`checked_add`/`checked_mul`/`checked_shl`/
//! `checked_pow`, and writing a list into a caller-owned buffer) reports
//! failure through [`ComputeError`] instead.
//!
//! The type is deliberately a small `Copy` C-like enum with no payload: it is
//! allocation-free, cheap to propagate through `?`, and `Display` writes
//! straight into the formatter without building a `String`, so the whole error
//! path stays within the crate's heapless memory profile.

use core::fmt;

/// Every way a generated function can fail.
///
/// `OutputTooSmall` is a unit variant on purpose. A generated list builder
/// discovers exhaustion one element at a time while recursing into the tail of
/// a caller-owned slice, so at the point of failure it knows only that at least
/// one more element was needed — not the total the whole call would have
/// required. Reporting a fabricated `required` count would be worse than
/// reporting none; the caller knows the length it provided.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ComputeError {
    /// `a + b` exceeded `u64::MAX` (Lean `Nat` addition is total; `u64` is not).
    AddOverflow,
    /// `a * b` exceeded `u64::MAX`.
    MulOverflow,
    /// `a <<< b` shifted bits past the width of `u64`.
    ShiftOverflow,
    /// `a ^ b` exceeded `u64::MAX`.
    PowOverflow,
    /// A shift amount did not fit in `u32`.
    ShiftExponentTooLarge,
    /// A power exponent did not fit in `u32`.
    PowExponentTooLarge,
    /// A caller-supplied output slice ran out of room for the produced list.
    OutputTooSmall,
    /// `a - b` on `Int` underflowed `i64`. `Nat` subtraction saturates and
    /// cannot reach this.
    SubOverflow,
    /// `a / b` on `Int` overflowed `i64` — only `i64::MIN / -1`.
    DivOverflow,
    /// `-a` on `Int` overflowed `i64` — only `-i64::MIN`.
    NegOverflow,
}

impl ComputeError {
    /// The `Display` text, also usable in `const` contexts and by callers that
    /// want the message without a formatter.
    pub const fn as_str(self) -> &'static str {
        match self {
            ComputeError::AddOverflow => "Nat addition overflowed u64",
            ComputeError::MulOverflow => "Nat multiplication overflowed u64",
            ComputeError::ShiftOverflow => "Nat shift overflowed u64",
            ComputeError::PowOverflow => "Nat power overflowed u64",
            ComputeError::ShiftExponentTooLarge => "Nat shift amount exceeds u32",
            ComputeError::PowExponentTooLarge => "Nat power exponent exceeds u32",
            ComputeError::OutputTooSmall => "output slice too small for the produced list",
            ComputeError::SubOverflow => "Int subtraction overflowed i64",
            ComputeError::DivOverflow => "Int division overflowed i64",
            ComputeError::NegOverflow => "Int negation overflowed i64",
        }
    }
}

impl fmt::Display for ComputeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl core::error::Error for ComputeError {}

#[cfg(test)]
mod tests {
    use super::ComputeError;

    #[test]
    fn display_is_allocation_free_and_distinct() {
        // `as_str` is the single source of truth for both `Display` and
        // callers; every variant must carry its own message.
        let all = [
            ComputeError::AddOverflow,
            ComputeError::MulOverflow,
            ComputeError::ShiftOverflow,
            ComputeError::PowOverflow,
            ComputeError::ShiftExponentTooLarge,
            ComputeError::PowExponentTooLarge,
            ComputeError::OutputTooSmall,
            ComputeError::SubOverflow,
            ComputeError::DivOverflow,
            ComputeError::NegOverflow,
        ];
        for (i, a) in all.iter().enumerate() {
            for b in &all[i + 1..] {
                assert_ne!(a.as_str(), b.as_str());
            }
        }
    }
}
