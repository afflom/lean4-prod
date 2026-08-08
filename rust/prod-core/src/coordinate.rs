//! D-1: The coordinate system
//! Mixed-radix addressing and class indexing

/// Instance parameters: (q, T, O)
///
/// Field names mirror the Lean structure's own declared spelling
/// (`UorAtlas.Instance` in `lean/Example/Kernel.lean`: `q`, `T`, `O`)
/// exactly, so `Lower.lean`'s structure-projection lowering — which passes
/// declared field names through unmodified — and this struct can never
/// disagree on what a projection index means.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Instance {
    pub q: u64, // scope
    pub T: u64, // modality
    pub O: u64, // context
}

impl Instance {
    pub const fn stride(&self) -> u64 {
        self.T * self.O
    }

    pub const fn class_count(&self) -> u64 {
        self.q * self.stride()
    }

    pub const fn belt(&self) -> u64 {
        self.class_count() * (1 << (self.O - 1))
    }

    pub const fn is_valid(&self) -> bool {
        self.q >= 1 && self.T >= 1 && self.O >= 1
    }
}

/// S-1: classIndex(h2, d, l) = stride·h2 + O·d + l
pub const fn class_index(h2: u64, d: u64, l: u64, inst: &Instance) -> u64 {
    inst.stride() * h2 + inst.O * d + l
}

/// Inverse: index → (h2, d, l)
pub fn class_decode(idx: u64, inst: &Instance) -> (u64, u64, u64) {
    let h2 = idx / inst.stride();
    let rem = idx % inst.stride();
    let d = rem / inst.O;
    let l = rem % inst.O;
    (h2, d, l)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_class_index_roundtrip() {
        let inst = Instance { q: 4, T: 3, O: 8 };
        for h2 in 0..inst.q {
            for d in 0..inst.T {
                for l in 0..inst.O {
                    let idx = class_index(h2, d, l, &inst);
                    let (h2_out, d_out, l_out) = class_decode(idx, &inst);
                    assert_eq!((h2, d, l), (h2_out, d_out, l_out));
                }
            }
        }
    }

    #[test]
    fn test_belt_formula() {
        let inst = Instance { q: 4, T: 3, O: 8 };
        assert_eq!(inst.belt(), 12288);
    }

    #[test]
    fn test_instance_validity() {
        assert!(Instance { q: 4, T: 3, O: 8 }.is_valid());
        assert!(!Instance { q: 0, T: 3, O: 8 }.is_valid());
    }
}
