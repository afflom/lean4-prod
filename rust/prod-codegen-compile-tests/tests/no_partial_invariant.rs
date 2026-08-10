//! The fragment's central safety property: never a partially-enforced shape.
//!
//! `specs/lean-for-production.md` publishes it as *"There is no third shape and
//! no partially-enforced one: a type re-checks its whole proposition or none of
//! it"*, and `AGENTS.md` as *"Never a partial check."* A partial invariant is
//! the one outcome that is actively WRONG rather than merely weak: a generated
//! `new` that returns `Ok` while a conjunct Lean proved goes unchecked, while
//! the type's documentation says the whole proposition was re-checked.
//!
//! `UnlowerableProp` and `NonNumericCompare` cannot see it. Each has a single,
//! wholly-unlowerable `Prop` field, so both only exercise "zero conjuncts
//! survive" — under which a lowerer that emitted whatever survived would emit
//! nothing, and look correct. `Conformance.PartialProp` (`h1 : x ≥ 1`, which
//! lowers; `h2 : x ≠ y`, which does not) is the only input in the corpus where
//! the two behaviours differ, so it is the only thing that can check the claim.

use std::path::Path;

/// Read the conformance golden relative to this crate, so the test does not
/// depend on the working directory the harness happens to use (same approach
/// as `tests/rejected.rs`).
fn conformance_golden() -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean/Conformance/golden.ir");
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()))
}

#[test]
fn a_partly_lowerable_proposition_is_declined_whole() {
    let source = conformance_golden();
    let (_, module) = prod_ir::parser::parse_module(&source)
        .unwrap_or_else(|e| panic!("the conformance golden must parse: {e:?}"));

    let decl = module
        .types
        .iter()
        .find(|t| t.name == "Conformance.PartialProp")
        .unwrap_or_else(|| {
            panic!(
                "Conformance.PartialProp is missing from the golden. It is the \
                 only structure with one lowerable and one unlowerable `Prop` \
                 field, so it is the only thing that can tell a whole decline \
                 from a partial invariant. Do not delete it; see its doc \
                 comment in lean/Conformance/Structures.lean."
            )
        });

    // Declared, with its computational fields — the weaker shape, not absence.
    // A type dropped from the golden would fail the `find` above; a type whose
    // fields were dropped would fail here.
    let fields: Vec<&str> = decl
        .ctors
        .iter()
        .flat_map(|c| c.fields.iter().map(|(name, _)| name.as_str()))
        .collect();
    assert_eq!(
        fields,
        vec!["x", "y"],
        "PartialProp must keep its computational fields; `Prop` fields are erased"
    );

    // And with NO invariant at all. `(invariant (le 1 x))` — the surviving
    // conjunct on its own — is the failure this test exists to catch: it parses,
    // it generates a `new` that compiles, and that `new` accepts `x = 1, y = 1`,
    // which violates the `h2 : x ≠ y` that Lean proved.
    assert!(
        decl.invariant.is_none(),
        "PartialProp has one lowerable `Prop` field (`x >= 1`) and one \
         unlowerable one (`x != y`), so the WHOLE invariant must be declined. \
         Found: {:?}. A partial invariant is a check presented as complete.",
        decl.invariant
    );
}
