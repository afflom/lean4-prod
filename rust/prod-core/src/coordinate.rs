//! D-1: The coordinate system
//! Mixed-radix addressing and class indexing

/// Instance parameters: (q, T, O)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Instance {
    pub q: u64,  // scope
    pub t: u64,  // modality
    pub o: u64,  // context
}

impl Instance {
    pub const fn stride(&self) -> u64 {
        self.t * self.o
    }

    pub const fn class_count(&self) -> u64 {
        self.q * self.stride()
    }

    pub const fn belt(&self) -> u64 {
        self.class_count() * (1 << (self.o - 1))
    }

    pub const fn is_valid(&self) -> bool {
        self.q >= 1 && self.t >= 1 && self.o >= 1
    }
}

/// S-1: classIndex(h2, d, l) = stride·h2 + O·d + l
pub const fn class_index(h2: u64, d: u64, l: u64, inst: &Instance) -> u64 {
    inst.stride() * h2 + inst.o * d + l
}

/// Inverse: index → (h2, d, l)
pub fn class_decode(idx: u64, inst: &Instance) -> (u64, u64, u64) {
    let h2 = idx / inst.stride();
    let rem = idx % inst.stride();
    let d = rem / inst.o;
    let l = rem % inst.o;
    (h2, d, l)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_class_index_roundtrip() {
        let inst = Instance { q: 4, t: 3, o: 8 };
        for h2 in 0..inst.q {
            for d in 0..inst.t {
                for l in 0..inst.o {
                    let idx = class_index(h2, d, l, &inst);
                    let (h2_out, d_out, l_out) = class_decode(idx, &inst);
                    assert_eq!((h2, d, l), (h2_out, d_out, l_out));
                }
            }
        }
    }

    #[test]
    fn test_belt_formula() {
        let inst = Instance { q: 4, t: 3, o: 8 };
        assert_eq!(inst.belt(), 12288);
    }

    #[test]
    fn test_instance_validity() {
        assert!(Instance { q: 4, t: 3, o: 8 }.is_valid());
        assert!(!Instance { q: 0, t: 3, o: 8 }.is_valid());
    }
}
