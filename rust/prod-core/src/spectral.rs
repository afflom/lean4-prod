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

    pub const fn multiplicities(inst: &Instance) -> [u64; 4] {
        [1, inst.T - 1, inst.O - 1, (inst.T - 1) * (inst.O - 1)]
    }

    /// Check spectral validity: T = 3 and indefiniteness (negative eigendirection exists)
    pub const fn is_spectrally_valid(inst: &Instance) -> bool {
        inst.T == 3 && inst.O >= 3
    }

    /// S-23: signature defect = negative_dim - positive_dim = (T-1)(O-1) - (T+O-1)
    /// At canonical instance: 14 - 10 = 4 = scope q
    pub const fn signature_defect(inst: &Instance) -> i64 {
        let pos = (inst.T + inst.O - 1) as i64;
        let neg = ((inst.T - 1) * (inst.O - 1)) as i64;
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
