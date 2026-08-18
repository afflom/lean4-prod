//! Every Lean-computed golden must be compared against something.
//!
//! # Why this test exists
//!
//! The one defect this milestone shipped was a sized shift rendered backwards.
//! Lean had already computed the right answer — `golden_u8_shl_1_8 = 1` sat in
//! `goldens.ir` — while the Rust assertion next to it said `0`. Nothing
//! compared the two, so the build stayed green.
//!
//! The cause is structural, not a lapse of attention. `goldenEntries`
//! (`lean/Prod/Emit.lean`) and the assertions in `tests/smoke.rs` /
//! `../prod-core/tests/macro_generation.rs` are two hand-maintained lists with
//! no mechanical relationship: adding a golden and consuming it are separate
//! acts, and skipping the second one is invisible. A golden nobody reads is
//! not evidence — it is a value Lean computed into a file.
//!
//! This test supplies the missing relationship. It is deliberately a *text*
//! check rather than a call graph: the consumers are compiled by two different
//! crates (`prod-core` cannot see `prod-codegen-compile-tests`, and neither is
//! the other's dependency), so mentioning the name is the strongest link that
//! can be checked from one place. That is enough — the failure mode being
//! prevented is a golden mentioned *nowhere*, and any mention is an assertion
//! someone wrote on purpose.

use std::path::{Path, PathBuf};

/// Read a file relative to this crate, so the test does not depend on the
/// working directory the harness happens to use (same approach as
/// `tests/rejected.rs`).
fn read_relative(relative: &str) -> String {
    let path: PathBuf = Path::new(env!("CARGO_MANIFEST_DIR")).join(relative);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()))
}

/// Every `golden_*` definition name in `goldens.ir`, in file order.
///
/// Parsed from the IR text rather than from a parsed module so the test keeps
/// working if the golden module ever holds something the `prod-ir` grammar
/// does not model; the shape it depends on — `(def <name> () ...` — is the one
/// `emitGoldensIr` writes for every entry.
fn golden_names(ir: &str) -> Vec<String> {
    ir.lines()
        .filter_map(|line| line.trim().strip_prefix("(def "))
        .filter_map(|rest| rest.split_whitespace().next())
        .filter(|name| name.starts_with("golden_"))
        .map(String::from)
        .collect()
}

#[test]
fn every_golden_has_a_consumer() {
    let ir = read_relative("../prod-core/goldens.ir");
    let names = golden_names(&ir);
    assert!(
        !names.is_empty(),
        "no golden_* definitions found in ../prod-core/goldens.ir — either the \
         goldens vanished or `(def <name> ()` is no longer how prod-export \
         writes them, and this test has stopped checking anything"
    );

    // The two hand-maintained consumer lists this test exists to bind to
    // `goldenEntries`.
    let consumers = [
        (
            "prod-codegen-compile-tests/tests/smoke.rs",
            "tests/smoke.rs",
        ),
        (
            "prod-core/tests/macro_generation.rs",
            "../prod-core/tests/macro_generation.rs",
        ),
    ]
    .map(|(label, path)| (label, read_relative(path)));

    let orphans: Vec<&String> = names
        .iter()
        .filter(|name| {
            !consumers
                .iter()
                .any(|(_, text)| text.contains(name.as_str()))
        })
        .collect();

    assert!(
        orphans.is_empty(),
        "these goldens are computed by Lean and read by nobody: {orphans:?}\n\
         \n\
         A golden with no consumer is how a wrong rendering shipped green: \
         `golden_u8_shl_1_8` was 1 in goldens.ir while the assertion beside it \
         said 0, and because nothing compared them the build passed. Add an \
         assertion comparing the generated function against the golden in one \
         of: {}. Do not delete the golden to silence this — the golden is the \
         Lean-computed answer; the missing assertion is the defect.",
        consumers
            .iter()
            .map(|(label, _)| *label)
            .collect::<Vec<_>>()
            .join(" or ")
    );
}
