-- Conformance cases whose LOWERING is pinned but whose CODEGEN is a deliberate
-- rejection.
--
-- The main `Conformance` corpus carries a stronger promise: everything in it
-- must lower AND generate Rust that compiles, which
-- `rust/prod-codegen-compile-tests` enforces by feeding the whole golden
-- through `prod_defs!` and letting rustc read the result. A definition that
-- codegen rejects cannot live there — it would break that crate's build — but
-- deleting it would lose a lowering case worth pinning.
--
-- So it lives here. Everything in this module:
--   * lowers, and its IR shape is pinned by `Conformance/golden-rejected.ir`;
--   * is EXPECTED to fail codegen, with the specific error asserted by
--     `rust/prod-codegen-compile-tests/tests/rejected.rs`.
--
-- Both halves matter. Pinning the lowering catches exporter regressions;
-- asserting the rejection catches codegen quietly starting to emit something
-- for a construct it has no lowering for. If a construct here ever gains real
-- support, move it to `Conformance` and delete its rejection assertion — the
-- compile-tests crate then proves it generates.
import Prod.Attribute

namespace ConformanceRejected

/-- A purely intermediate structure: no `@[prod]` definition mentions it in a
    parameter or return type, so it exists in the IR only because a *body*
    constructs and projects it. `Conformance.MidProp`/`NoProp` cannot pin this —
    both are parameters of their conformance defs.

    The exporter's type collection (`Prod.declTypeNames`) used to walk
    signatures alone, so this lowered to `(ctor "…BodyOnly.mk" ...)` with no
    matching `(type ...)` declaration, and codegen rendered the dotted Lean name
    as a Rust path — `ConformanceRejected.BodyOnly.mk(a, b)`, which is not Rust
    — and exited 0. The golden must show a `(type "…BodyOnly" ...)`
    declaration; if the body walk regresses, it disappears and
    `just conformance` fails. -/
structure BodyOnly where
  alpha : Nat
  beta  : Nat

/-- Kept out of the optimizer's reach on purpose. The obvious spelling,
    `(BodyOnly.mk a b).alpha`, is folded by LCNF to `a` and the constructor
    never reaches the IR at all; branching first forces the structure to be a
    real intermediate value. The `match` is on `Nat` rather than a decidable
    comparison so the case stays inside the published subset (a `let`-bound `if`
    lands its `cases` behind a join point, where `decidableIf?` no longer
    recognizes it, and the decider surfaces as an extern).

    Why this is a rejection: branching first is exactly what produces a
    TWO-CALLER join point — both match arms feed one continuation — and codegen
    rejects those as `UnsupportedJoinPoint`, because the skeleton it used to
    emit did not compile. The two properties are inseparable here: the join
    point IS the mechanism that keeps the constructor alive for the test.

    The codegen half of the body-only story is pinned separately by
    `test_ctor_in_a_definition_body_only_renders_when_declared` in
    `rust/prod-codegen/src/tests.rs`, so nothing is lost. -/
@[prod] def r_ctor_body_only (fuel a b : Nat) : Nat :=
  let s := match fuel with
    | 0 => BodyOnly.mk a b
    | _ + 1 => BodyOnly.mk b a
  s.alpha + s.beta

end ConformanceRejected
