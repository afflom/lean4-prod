//! The companion to `src/lib.rs`: what must NOT generate.
//!
//! `lean/ConformanceRejected/` holds definitions whose lowering is pinned by a
//! committed golden but whose codegen is a deliberate rejection. Pinning the
//! lowering catches exporter regressions; asserting the rejection here catches
//! codegen quietly starting to emit *something* for a construct it has no
//! lowering for — which is the failure this whole crate exists to prevent,
//! just in the other direction.
//!
//! If a construct here gains real support, move its definition into
//! `lean/Conformance/` and delete the assertion. The main golden is compiled by
//! `src/lib.rs`, so the move is what proves the support is real.

use std::path::Path;

/// Read the rejected golden relative to this crate, so the test does not
/// depend on the working directory the harness happens to use.
fn rejected_golden() -> String {
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean/Conformance/golden-rejected.ir");
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()))
}

#[test]
fn rejected_golden_parses_but_does_not_generate() {
    let source = rejected_golden();
    let (rest, module) = prod_ir::parser::parse_module(&source)
        .unwrap_or_else(|e| panic!("rejected golden must still PARSE: {e:?}"));
    assert!(rest.trim().is_empty(), "trailing input in rejected golden");
    assert!(
        !module.definitions.is_empty(),
        "rejected golden is empty — if the last case gained support it should \
         have moved to lean/Conformance/, not vanished"
    );

    let error = prod_codegen::generate_module(&module).expect_err(
        "the rejected golden generated. If a construct gained support, move its \
         Lean definition to lean/Conformance/ so src/lib.rs compiles the result, \
         and drop it from this assertion — do not silently widen this test.",
    );

    // Named precisely, not merely "some error": a different rejection would
    // mean the corpus is failing for a reason nobody intended.
    assert_eq!(
        error,
        prod_codegen::Error::UnsupportedJoinPoint("_jp_19".to_string()),
        "rejected for an unexpected reason"
    );
}
