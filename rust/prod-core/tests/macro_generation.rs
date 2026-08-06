#![allow(non_snake_case)] // generated code mirrors Lean definition names

use prod_core::{belt, classDecode, classIndex, class_count, stride, Instance};

// Golden values computed by the compiled Lean kernel defs (lake exe
// prod-export → goldens.ir, next to prod-core's Cargo.toml). Same IR module
// format, consumed through the same macro — nothing hand-written downstream.
prod_macros::prod_defs! { ir = "goldens.ir" }

const CANONICAL: Instance = Instance { q: 4, t: 3, o: 8 };
const DEMO_SMALL: Instance = Instance { q: 2, t: 2, o: 4 };
const THIRD: Instance = Instance { q: 5, t: 1, o: 3 };

#[test]
fn generated_definitions_compile_and_run() {
    assert_eq!(classIndex(1, 2, 3, CANONICAL), 43);
    assert_eq!(stride(CANONICAL), 24);
    assert_eq!(class_count(CANONICAL), 96);
    assert_eq!(belt(CANONICAL), 12_288);
    assert_eq!(classDecode(43, CANONICAL), (1, (2, 3)));
}

#[test]
fn golden_values_are_the_hand_checked_tf1_numbers() {
    // Hand-checked: stride = T·O, class_count = q·stride, belt = class_count·2^(O-1),
    // classIndex(h2,d,l) = stride·h2 + O·d + l.
    assert_eq!(golden_stride_canonical(), 24);
    assert_eq!(golden_class_count_canonical(), 96);
    assert_eq!(golden_belt_canonical(), 12_288);
    assert_eq!(golden_stride_demo_small(), 8);
    assert_eq!(golden_class_count_demo_small(), 16);
    assert_eq!(golden_belt_demo_small(), 128);
    assert_eq!(golden_stride_third(), 3);
    assert_eq!(golden_class_count_third(), 15);
    assert_eq!(golden_belt_third(), 60);
    assert_eq!(golden_classIndex_1_2_3_canonical(), 43);
    assert_eq!(golden_classDecode_43_canonical(), (1, (2, 3)));
}

#[test]
fn generated_definitions_match_lean_goldens() {
    for (inst, g_stride, g_class_count, g_belt) in [
        (
            CANONICAL,
            golden_stride_canonical(),
            golden_class_count_canonical(),
            golden_belt_canonical(),
        ),
        (
            DEMO_SMALL,
            golden_stride_demo_small(),
            golden_class_count_demo_small(),
            golden_belt_demo_small(),
        ),
        (
            THIRD,
            golden_stride_third(),
            golden_class_count_third(),
            golden_belt_third(),
        ),
    ] {
        assert_eq!(stride(inst), g_stride);
        assert_eq!(class_count(inst), g_class_count);
        assert_eq!(belt(inst), g_belt);
    }
    assert_eq!(
        classIndex(1, 2, 3, CANONICAL),
        golden_classIndex_1_2_3_canonical()
    );
    assert_eq!(
        classDecode(43, CANONICAL),
        golden_classDecode_43_canonical()
    );
}

#[test]
fn generated_definitions_roundtrip_lean_examples() {
    for inst in [CANONICAL, DEMO_SMALL, THIRD] {
        for h2 in 0..inst.q {
            for d in 0..inst.t {
                for l in 0..inst.o {
                    let idx = classIndex(h2, d, l, inst);
                    assert_eq!(classDecode(idx, inst), (h2, (d, l)));
                }
            }
        }
    }
}

#[test]
fn decode_encode_roundtrip_full_index_sweep() {
    // decode∘encode is the identity on every valid index of each instance.
    for inst in [CANONICAL, DEMO_SMALL, THIRD] {
        for idx in 0..class_count(inst) {
            let (h2, (d, l)) = classDecode(idx, inst);
            assert_eq!(classIndex(h2, d, l, inst), idx);
        }
    }
}
