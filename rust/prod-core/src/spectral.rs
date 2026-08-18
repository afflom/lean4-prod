//! S-10: Spectral operator M = (O+2)I - T·Pi_T - O·Pi_O
//! Eigenblocks and projectors for the Atlas carrier
//!
//! Hand-written analysis support. Unlike everything else in this crate, this
//! module is NOT downstream of Lean — `SpectralOperator` has no `@[prod]`
//! counterpart yet. Port it to Lean and delete this file when it does.

use crate::Instance;

/// S-23: M is a separability form.
/// The four eigenvalues at the canonical instance (q=4, T=3, O=8):
/// [10, 7, 2, -1] with multiplicities [1, 2, 7, 14]
pub struct SpectralOperator;

impl SpectralOperator {
    /// Eigenvalues for a given instance (T must be 3 for spectral validity)
    pub const fn eigenvalues(inst: &Instance) -> [i64; 4] {
        let o = inst.O as i64;
        let t = inst.T as i64;
        [
            o + 2,     // global
            o + 2 - t, // modality
            2,         // context (O+2-O = 2)
            2 - t,     // interaction
        ]
    }

    /// Saturating, not bare, subtraction. `Instance`'s Lean invariant
    /// (`q ≥ 1 ∧ T ≥ 1 ∧ O ≥ 1`) is a `Prop` field, erased on export, and
    /// re-checked by the generated `Instance::new` — but only at the crate
    /// boundary. `Instance`'s fields are `pub(crate)`, so *in this crate*
    /// `Instance { q: 0, T: 0, O: 0 }` is still constructible without going
    /// through `new`, and the test below does exactly that. With `T = 0`,
    /// `inst.T - 1` underflows: a panic under debug and the
    /// `release-assertions` lane, a silent wrap in release. This crate denies
    /// `clippy::panic`, so saturating at zero is the only honest option.
    /// External callers cannot reach this state at all, since `new` rejects
    /// it; this is defence for the in-crate literal, not for them.
    pub const fn multiplicities(inst: &Instance) -> [u64; 4] {
        let t = inst.T.saturating_sub(1);
        let o = inst.O.saturating_sub(1);
        [1, t, o, t.saturating_mul(o)]
    }

    /// Check spectral validity: T = 3 and indefiniteness (negative eigendirection exists)
    pub const fn is_spectrally_valid(inst: &Instance) -> bool {
        inst.T == 3 && inst.O >= 3
    }

    /// S-23: signature defect = negative_dim - positive_dim = (T-1)(O-1) - (T+O-1)
    /// At canonical instance: 14 - 10 = 4 = scope q
    ///
    /// Saturating for the same reason as [`Self::multiplicities`]: the Lean
    /// `q ≥ 1 ∧ T ≥ 1 ∧ O ≥ 1` invariant is an erased `Prop`, and the checked
    /// `Instance::new` that re-checks it guards the crate boundary only — an
    /// in-crate struct literal with `T = O = 0` still reaches this arithmetic.
    pub const fn signature_defect(inst: &Instance) -> i64 {
        let pos = inst.T.saturating_add(inst.O).saturating_sub(1) as i64;
        let neg = (inst.T.saturating_sub(1)).saturating_mul(inst.O.saturating_sub(1)) as i64;
        neg - pos
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_canonical_spectrum() {
        let inst = Instance { q: 4, T: 3, O: 8 };
        assert!(SpectralOperator::is_spectrally_valid(&inst));
        let vals = SpectralOperator::eigenvalues(&inst);
        let mults = SpectralOperator::multiplicities(&inst);
        assert_eq!(vals, [10, 7, 2, -1]);
        assert_eq!(mults, [1, 2, 7, 14]);
    }

    #[test]
    fn test_signature_defect() {
        let inst = Instance { q: 4, T: 3, O: 8 };
        assert_eq!(SpectralOperator::signature_defect(&inst), 4);
        assert_eq!(inst.q as i64, 4);
    }

    #[test]
    fn test_degenerate_instance_does_not_underflow() {
        // `Instance::new` would reject this — that is what
        // `checked_constructor_accepts_valid_and_rejects_each_violation` in
        // `tests/macro_generation.rs` asserts. This is a unit test *inside*
        // the crate, where the fields are visible and a struct literal
        // bypasses `new`, which is exactly the state the saturating
        // arithmetic above exists for. It must not panic here (debug /
        // release-assertions) nor wrap silently (release).
        let zero = Instance { q: 0, T: 0, O: 0 };
        assert_eq!(SpectralOperator::multiplicities(&zero), [1, 0, 0, 0]);
        assert_eq!(SpectralOperator::signature_defect(&zero), 0);
        assert!(!SpectralOperator::is_spectrally_valid(&zero));
    }

    #[test]
    fn test_spectral_validity() {
        assert!(SpectralOperator::is_spectrally_valid(&Instance {
            q: 4,
            T: 3,
            O: 8
        }));
        assert!(!SpectralOperator::is_spectrally_valid(&Instance {
            q: 2,
            T: 2,
            O: 4
        }));
    }
}
