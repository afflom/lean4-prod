#![allow(non_snake_case)] // generated code mirrors Lean definition names

use prod_core::Instance;
use prod_macros::prod_defs;

prod_defs! { ir = "../sample.ir" }

#[test]
fn generated_definitions_compile_and_run() {
    let inst = Instance { q: 4, t: 3, o: 8 };

    assert_eq!(classIndex(1, 2, 3, inst), 43);
    assert_eq!(stride(inst), 24);
    assert_eq!(class_count(inst), 96);
    assert_eq!(belt(inst), 12_288);
}
