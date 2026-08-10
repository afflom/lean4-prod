# Design: S2 — scalar completeness and invariant-carrying types

**Date:** 2026-08-09
**Status:** Phase A (the arithmetic layer, migration steps 1–5) is DONE —
implemented by `specs/plans/2026-08-09-s2-phase-a-arithmetic.md`'s five
tasks (Bool-connective probe, kind tags, `Int` arithmetic, sized integers,
conversions). The published contract's `Int` qualifier from S1 ("no Int
operators are whitelisted") is gone, all three arithmetic policies in the
table below match the shipped rendering, and `specs/lean-for-production.md`
now lists the kinds, operators, conversions, and deciders it actually
accepts.
Phase B1 (invariant-carrying types, migration steps 6–7) is DONE —
implemented by
`.superpowers/sdd/2026-08-10-s2-phase-b1-invariants/`. A structure whose
`Prop` fields all lower gets `pub(crate)` fields, a checked
`new(..) -> Result<Self, ComputeError>` and per-field accessors; one whose
`Prop` fields do not lower keeps public fields and no constructor, as
before. The rule and the bypass rationale below match what shipped; the one
correction is that the fields are `pub(crate)`, not private, so in-crate
generated code can keep building these types by struct literal.
Phase B2 (`Fin` with a literal bound, migration step 8) is now **unblocked**
and should be planned against the B1 machinery as it actually shipped —
`lowerProp`/`propCmpKinds` in `lean/Prod/Lower.lean` and the `(invariant
...)` clause on `(type ...)` declarations — rather than against this design's
prediction of it. In particular `Fin n`'s `val < n` is already expressible in
the fragment B1 implements, so B2 is likely a lowering question (recognising
`Fin` and its literal bound) rather than a new enforcement mechanism.
**Scope:** Milestone S2 of the coverage roadmap in
`specs/designs/2026-08-08-lean-for-production-coverage.md`, extended to include
`Fin` and the first piece of the invariant subsystem.
**Depends on:** S0 + S1 (PR #1) and the compile-tests crate (PR #2).

## Why this exists

The published contract currently qualifies `Int` as "renders as i64; no Int
operators are whitelisted, so Int arithmetic is rejected as UnresolvedCall".
That is the most visible hole in it. S2 closes it, adds `Bool` connectives and
sized integers, and — because `Fin` turns out to be the same problem as
generated invariants — delivers the first invariant-carrying types.

This is really two subsystems: an arithmetic layer, and invariant-carrying
types. They are not independent — the invariant predicates are built from the
comparisons and connectives the arithmetic layer provides — so they share one
spec, and the plan sequences them as phases.

They should probably be **two implementation plans**, not one. Phase A is
migration steps 1–5 and is already a full plan's worth of work; Phase B is
steps 6–8 and has a different risk profile (blast radius rather than churn).
Splitting them means Phase A can land and be reviewed while Phase B is still
being written, and Phase B's plan can be written against the arithmetic layer
as it actually shipped rather than as designed. The decision belongs to the
planning step; the design is written so either choice works.

## Facts established from Lean 4.30.0's source

These were read from the toolchain's own source, not assumed. Three of them
would have produced silently wrong generated code if defaulted.

**`Int` division and modulo are Euclidean.**
`Init/Data/Int/DivMod/Basic.lean:108-118`: *"The `Div Int` and `Mod Int`
instances use `Int.ediv` and `Int.emod` for compatibility with SMT-LIB."* The
file's own doctest gives `(-12) % 7 = 2`; Rust's `%` gives `-5`. Rendering `/`
and `%` would be wrong for every negative operand, and every test with
non-negative inputs would still pass.

**`Int.ediv` by zero is total.** Line 76 is explicit: `| -[_+1], 0 => 0`, and
the non-negative case reduces to `Nat` division, which is also `0`. So `Int`
division needs the same zero-guard `Nat` already has.

**Modulo by zero is the dividend, not zero.** CORRECTED AFTER THE FACT — this
section originally said only the division half, and the `div`/`mod` table row
below generalised `0` to both. `Int.emod`'s `emod_zero` gives
`(7 : Int) % (0 : Int) = 7`, and `Nat.mod`'s own doc comment says *"When the
divisor is `0`, the result is the dividend rather than an error"* (doctest
`5 % 0 = 5`); sized `mod` inherits `Nat`'s answer through
`BitVec.umod`. So `div` and `mod` need *different* zero-guard values — a shared
guard rendering `0` for both is right for division and wrong for modulo, which
is precisely the Critical defect fixed on this branch.

**Sized integers wrap by definition.**
`Init/Data/UInt/Basic.lean:33`: `UInt8.add a b = ⟨a.toBitVec + b.toBitVec⟩`.
BitVec arithmetic wraps. So `UIntN` must render `wrapping_*` in exactly the
positions where `Nat` renders `checked_*(..).ok_or(..)?`.

**Sized-integer division is total too.**
`Init/Data/BitVec/Basic.lean:271`: `udiv x y = (x.toNat / y.toNat)`, so a zero
divisor yields `0`, matching `Nat`. Sized *modulo* is total in the same way and
by the same route (`umod x y = (x.toNat % y.toNat)`), which means it also
inherits `Nat`'s answer for a zero divisor — the dividend, not `0`; see the
correction above.

**`Fin n` is a structure with a `Prop` bound.**
`Init/Prelude.lean:2306`: `structure Fin (n : Nat) where val : Nat; isLt : val < n`.
It is therefore the canonical invariant-carrying type, not a special case — but
`n` is a *value* type-parameter, so `Fin` is currently rejected as
`PolymorphicType`.

## Decisions

**1. All four items, with `Fin` scoped to literal bounds.** `Fin n` is only
useful when `n` is concrete. Specialising one known type on a literal value
argument is much narrower than S5's general monomorphisation, and it is
tractable now.

**2. Numeric kinds become explicit in the IR.** Arithmetic nodes carry a kind
tag. The alternative — inferring the kind in codegen — recreates exactly the
derive-it-twice pattern that the projection work removed, and that pattern has
already produced silently swapped struct fields once in this project.

**3. Invariant enforcement is uniform, not opt-in.** A structure whose `Prop`
fields are all lowerable gets private fields and a checked constructor. No
attribute, no per-type decision: behaviour is predictable from the type.

**4. Conversions cover the lossless and total set only.** `Nat`↔`Int`,
`UIntN`→`Nat`, `Nat`→`UIntN`. Cross-width sized-integer conversions wait until
something needs them.

## Goals

- `Int` arithmetic works and is faithful to Lean's Euclidean semantics.
- Sized integers work and are faithful to Lean's wrapping semantics.
- A structure's erased `Prop` invariant is re-checked at the crate boundary.
- `Fin` with a literal bound generates a real type.
- The published contract describes all three arithmetic policies truthfully.

## Non-goals

- **Bitwise operations** (`land`, `lor`, `xor`) on any kind. Rejected
  precisely; trivially addable later.
- **Shifts on `Int`.** Rejected precisely.
- **Cross-width sized-integer conversions** (`UInt8`↔`UInt32`).
- **Signed sized integers** (`Int8`/`Int16`/`Int32`/`Int64`). Lean has them and
  they are symmetric with the unsigned kinds, so they cost roughly one row per
  kind once the tag exists — but nothing needs them yet.
- **General monomorphisation** (S5). `Fin` with a non-literal bound stays
  rejected.
- **Floats, `String`, `Array`.** Unchanged from the S0/S1 non-goals.

## Phase A — the arithmetic layer

### Numeric kinds in the IR

Arithmetic nodes gain an explicit kind: `(add Nat a b)`, `(add Int a b)`,
`(add U8 a b)`. The kind enum is `Nat | Int | U8 | U16 | U32 | U64`. Lean emits
it because it sees `Nat.add` versus `Int.add` versus `UInt8.add` and never has
to guess.

An unhandled (operation, kind) combination must be a compile error in codegen,
not a fallback rendering.

### Three policies

| | `Nat` → `u64` | `Int` → `i64` | `UIntN` → `uN` |
|---|---|---|---|
| `add` `mul` | checked → error | checked → error | wrapping |
| `pow` | checked → error | checked → error | rejected (see below) |
| `sub` | saturating at 0 | checked → error | wrapping |
| `div` | total, ÷0 ⇒ 0 | **Euclidean**, total, ÷0 ⇒ 0 | total, ÷0 ⇒ 0 |
| `mod` | total, %0 ⇒ **dividend** | **Euclidean**, total, %0 ⇒ **dividend** | total, %0 ⇒ **dividend** |
| `shl` | checked → error | not supported | wrapping (masks mod width) |
| `shr` | total, ≥ width ⇒ 0 | not supported | wrapping (masks mod width) |
| unary `neg` | n/a | checked → error | n/a |

CORRECTED AFTER THE FACT — two cells above were wrong, in the same direction
each time (assuming the zero/out-of-range case is absorbing):

- The `shr`/`UIntN` cell said *"total, ≥ width ⇒ 0"*, copying `Nat`'s row.
  Sized right shifts mask exactly like sized left shifts —
  `Init/Data/UInt/Basic.lean:133` defines `UInt8.shiftRight a b =
  ⟨a.toBitVec >>> (UInt8.mod b 8).toBitVec⟩`, the mirror of `shiftLeft` seven
  lines above it — so `(1 : UInt8) >>> 8 = 1`, not
  `0`. This is the same inverted premise that shipped this milestone's only
  defect on the `shl` side; the correction pass that fixed the `shl` and `pow`
  cells did not reach this one. `Nat`'s cell is right as written: `Nat` is
  unbounded, so there is no width to mask by.
- The single `div`/`mod` row said *"total, 0 ⇒ 0"* for all three kinds. Only
  division gives `0`. **Modulo by a zero divisor returns the dividend**, for
  every kind: `Nat.mod`'s own doctest is `5 % 0 = 5`, and `Int`'s `emod_zero`
  gives `(7 : Int) % (0 : Int) = 7`. Rendering `0` there was a Critical defect
  fixed on this branch; the row is split in two so the two policies can no
  longer share a cell.

Sized `pow` is rejected rather than rendered: `wrapping_pow` takes a `u32`
exponent and, unlike `checked_shl`, has no absorbing behaviour at large
exponents, so narrowing a `u64` exponent to it would silently change the
answer. Lean whitelists no sized `pow`, so nothing is lost.

`Int` division renders `checked_div_euclid`/`checked_rem_euclid` behind a
zero-guard. The `checked_` prefix covers `i64::MIN / -1`, which overflows where
Lean's unbounded `Int` does not.

**Sized integers are entirely infallible.** Wrapping is the semantics rather
than a failure, and division is total, so a definition using only `UIntN` keeps
a plain return type through the existing fallibility fixpoint.

### The `as` receiver pin becomes kind-aware

`checked_binop` currently renders `((a) as u64).checked_add(b)`. The cast pins
the receiver's type, because LCNF emits let-bound integer literals whose type is
ambiguous and which fail method resolution (E0689). With three kinds, `as u64`
is wrong for `i64` and `uN` operands; the cast must use the kind's Rust type.
This also handles literals in non-`Nat` positions.

### Unary negation

`Expr` has only binary operators today, so `Int.neg` has nowhere to go. Phase A
adds a unary node; it is where `NegOverflow` originates.

### Decidable guards per kind

`deciderNames` recognises only `Nat.decLt`/`decLe`/`decEq`/`instDecidableEqNat`.
`Int` and `UIntN` comparisons use different decider constants, so without a row
per kind, `if a < b` on an `Int` surfaces as `UnresolvedCall` — arithmetic would
work but branching on it would not, which guts the feature.

### Conversions

`Int.ofNat` (widens), `Int.toNat` (clamps negatives to `0`, Lean's own
semantics), `UIntN.toNat` (widens), `Nat.toUIntN` (wraps, matching BitVec
truncation). All total; no new error variants.

### Bool connectives — verify before implementing

`&&` and `||` are `@[macro_inline]` in Lean and elaborate through `match`, so
they most likely reach LCNF as `cases` on `Bool.true`/`Bool.false`, which
codegen already renders. **The plan's first step is an empirical probe**, and a
node is added only if the probe shows one is needed.

RESOLVED (Task 1): Bool connectives lower to cases over existing nodes.
Evidence: `c_bool_and`/`c_bool_or`/`c_bool_not` in
lean/Conformance/golden.ir. No IR change is needed.

## Phase B — invariant-carrying types

**B1 DONE; B2 (`Fin`) unblocked.** Phase A shipped exactly the arithmetic
layer this phase is built on: comparisons per kind (`Eq`/`Lt`/`Le`/`Gt`,
kind-less by design), the deciders per kind that make `∧`/`∨`/`¬`-shaped
predicates lowerable, and `NumKind` itself for describing a bound like
`Fin`'s `val < n`.

B1 built on it as predicted — `lowerProp` is a straight recursive match over
`And`/`Or`/`Not` and a comparison table, with `propCmpKinds = [Nat, Int] ++
sizedKinds` gating which kinds a comparison may be lowered on (`Bool` is
excluded on purpose, so a `Bool` equality invariant is simply not enforced).
Three things B1 learned that this design did not anticipate, and that B2 should
carry forward:

1. **The fields are `pub(crate)`, not private.** Generated code inside the
   crate keeps constructing these types by struct literal; only the crate
   boundary is guarded. See "Generated code bypasses the check" below, which
   was right about the *why* and wrong about the visibility.
2. **A lowered comparison must be tested by running it, not by reading it.**
   Reversed operands compile and produce a `bool`. `Conformance.MixedCompare`
   (`lo ≥ 2 ∧ hi ≤ 7 ∧ lo < hi`) exists because `UorAtlas.Instance`'s three
   same-direction conjuncts cannot distinguish a blanket operand swap from a
   correct per-operator one. Any B2 bound needs the same treatment.
3. **`Fin`'s bound is a type parameter, and that is a case `lowerProp` has
   never been given.** Every `bvar` inside a proposition today is an earlier
   *field*, because `lowerTypeDecl` rejects `numParams != 0` before it walks
   the telescope. `Fin n`'s `isLt : val < n` references `n`, a binder outside
   the field telescope, so B2 is the first input where an index can point past
   the fields. `lowerPropOperand` now declines such an index explicitly; before
   this branch's final wave it computed `depth - 1 - i` unguarded, and `Nat`
   subtraction truncates, so `n` would have resolved to `fields[0]` — which for
   `Fin` is `val`, lowering `val < n` to `(lt val val)`: a comparison that
   compiles, returns a `bool`, and is always false. B2 must *supply* the bound
   (recognise `Fin`'s parameter and substitute the literal), not rely on the
   telescope walk to find it.

Plan B2 against what actually shipped, not this design's prediction of it.

### The rule

A structure gets crate-visible fields and a generated checked constructor **iff
every one of its `Prop` fields is lowerable to a runtime predicate over that
structure's own fields**. Otherwise it keeps public fields and its `Prop` is
erased and documented, exactly as today. (Shipped as `pub(crate)`, not
private — see the note above.)

A `Prop` is lowerable when it is built from comparisons on supported numeric
kinds, `∧`, `∨`, and `¬` — which is precisely what Phase A delivers. `∀`, `∃`,
arbitrary predicates, and propositions mentioning anything other than the
structure's own fields (or its literal type arguments) are not lowerable.
As shipped, "supported numeric kinds" is `propCmpKinds = [Nat, Int] ++
sizedKinds`: `Bool` equality is outside the fragment, so a structure whose
only `Prop` field compares `Bool`s takes the unenforced shape.

### Generated code bypasses the check

When Lean constructs a value it supplies a proof: the invariant is already
established. Re-checking at every internal construction would be wasteful and
would turn proved-total functions into fallible ones. So:

- fields become `pub(crate)`, and generated code constructs via struct literal
  exactly as it does now;
- a `pub fn new(..) -> Result<Self, ComputeError>` exists for the crate
  boundary.

Inside the generated world the proof holds; at the boundary it is re-checked.
That is the honest reading of what erasure means.

### `Fin`

`Fin 8` specialises to a generated type named `Fin8`: `val` is `pub(crate)`
like any other invariant-carrying field, with a `new` checking `val < 8` and a
public `val()` accessor. Collisions with a user type of that spelling are
caught by the existing `DuplicateTypeName`.

The same in-crate/boundary split applies to reads as to construction:
**generated code projects the `pub(crate)` field directly**, exactly as it does
today, and the accessor exists for external callers. A projection is not a
place an invariant can be violated, so routing generated reads through an
accessor would buy nothing.

`Fin`'s predicate is the one case where a lowerable `Prop` references something
other than a field: the bound comes from the type's literal argument. That is
in scope precisely because the argument is a literal and therefore known at
codegen time.

`Fin n` with a non-literal `n` is rejected as `NonLiteralTypeArgument` — its own
variant rather than `PolymorphicType`, because "needs monomorphisation" and
"needs a literal here" are different problems with different fixes.

### Blast radius

All compiler-caught. `UorAtlas.Instance` qualifies (`valid : q ≥ 1 ∧ T ≥ 1 ∧ O ≥ 1`)
and so does `Conformance.MidProp` (`first ≥ 0` is trivially true but still
lowerable). `spectral.rs` is unaffected — it is in-crate, so `pub(crate)` still
reads. External construction breaks: `prod-core`'s two test files and the
compile-tests crate's `smoke.rs`.

## Error variants

New in `prod_core::ComputeError` (runtime):

| Variant | Cause |
|---|---|
| `SubOverflow` | `Int` subtraction overflowed `i64` |
| `DivOverflow` | `Int` division overflowed `i64` (`MIN / -1`) |
| `NegOverflow` | `Int` negation overflowed `i64` |
| `InvariantViolated(&'static str)` | a checked constructor's predicate failed |

The `&'static str` payload names the type. It keeps the enum `Copy` and
heapless while making the failure debuggable, which a bare variant would not.

It is the first `ComputeError` variant with a payload, which affects the
existing `as_str()`/`Display` split: `as_str()` stays payload-free and returns
the constant `"invariant violated"`, while `Display` writes the type name
alongside it. That keeps `as_str()` usable in `const` contexts, which is why it
exists.

New in `prod_codegen::Error` (compile time):

| Variant | Cause |
|---|---|
| `NonLiteralTypeArgument` | `Fin n` where `n` is not a literal |

A structure whose `Prop` is merely not lowerable is **not** an error — it keeps
today's behaviour.

## Contract changes

`specs/lean-for-production.md` is generated, so these follow from the code, but
two need calling out:

- The Types and Operators sections gain the kinds, the three arithmetic
  policies (a table, not a sentence), the conversions, and `Fin` with literal
  bounds. The `Int` qualifier added in S1 is removed.
- **The "Erased invariants" section becomes false and must be rewritten, not
  appended to.** It stated the generated struct does *not* enforce the
  invariant and that callers must re-check, illustrated with a struct literal
  that no longer compiles from outside the crate. After Phase B that is
  backwards for every lowerable case. DONE in B1: the section is now
  "Erased invariants, and where they are re-checked", covers both published
  shapes, and tells a reader how to identify which one a type got.

## Testing

**The negative-operand cases matter more than the rest.** A suite with only
non-negative operands passes identically under truncating and Euclidean
division. The conformance corpus must include Lean-computed goldens for
`(-12) / 7 = -2` and `(-12) % 7 = 2`. That single pair is the guard against the
defect this design exists to prevent.

Similarly, sized integers need a case that actually wraps at the boundary
rather than one that stays in range, and `Int` needs cases at `i64::MIN` for
`sub`, `neg`, and `MIN / -1`.

Everything else rides existing machinery: conformance goldens pin lowering, the
compile-tests crate compiles them so a mis-render cannot hide in a string
comparison, `no_alloc` still applies (every kind here is a `Copy` scalar), and
`subset-check` fails the build on a stale contract.

## Migration order

Green tree at every step.

1. **Bool-connective probe.** Empirical; decides whether any node is needed.
2. **Kind tags and the kind-aware `as` pin.** Mechanical, wide churn, no new
   semantics. Everything else builds on it, so it lands first.
3. **`Int`:** Euclidean div/mod, checked add/sub/mul/pow, unary negation, `Int`
   deciders.
4. **Sized integers:** wrapping arithmetic, their deciders.
5. **Conversions.**
6. **The invariant rule.** `Instance` and `MidProp` migrate; external call sites
   break here.
7. **`Fin`,** on top of step 6.
8. **Contract regeneration,** including the rewritten erased-invariants section.

## Risks

- **Step 2 is the churn risk.** Every arithmetic node in every committed golden
  and every test fixture changes. Mitigated by the golden diffs and by the
  compile-tests crate, which now compiles what the goldens generate.
- **Step 6 is the blast-radius risk.** Making fields `pub(crate)` breaks every
  external construction site. Entirely compiler-caught.
- **Silent wrongness is concentrated in `Int`.** Euclidean-versus-truncating is
  invisible to any test that avoids negative operands, which is why the
  negative-operand goldens are called out as a requirement rather than a nicety.

---

## Phase A follow-ups (from the whole-branch review, 2026-08-09)

Recorded here rather than in scratch, because the first two shape Phase B.

**Do before Phase B, in this order:**

1. **Generate the golden assertions from the same table that generates the
   values.** Oracle coverage of the conformance corpus is 5 of 40 definitions:
   16 are asserted only against hand-written literals, and 19 — including
   `c_nat_shl`, `c_nat_pow`, `c_int_add`, `c_int_mul`, `c_u8_sub` — are compiled
   but never executed. `tests/goldens_consumed.rs` now makes an *unconsumed*
   golden a build failure, which is the guard that would have caught this
   milestone's one shipped defect, but it cannot create coverage that was never
   written. The systematic fix is to restructure `goldenEntries` into per-signature
   sample-input tables and map each table twice in one pass — into `goldens.ir`
   and into a generated `tests/conformance_goldens.rs` — so the two sides cannot
   drift. `prod-export` already writes seven files; an eighth costs nothing.
2. **De-duplicate the builtin-type knowledge.** It lives in three places:
   `lowerType`, `collectTypeDecls`'s exclusion list, and `subsetJson`'s
   hand-written `types` prose. Flagged three times across two milestones. Phase B
   adds `Fin`, a new builtin type, and will have to touch all three — this is the
   last cheap moment.
3. **Add a `U64` conformance case.** `U16`/`U32`/`U64` have no end-to-end coverage
   at all, and `U64` is the one width whose `rust_type()` is `"u64"`, identical to
   `Nat`'s — so a mis-tagged kind there compiles cleanly and silently turns a
   wrapping operation into a checked one. Every other width's mis-tag is a rustc
   error the compile-tests crate catches.

**Known and accepted, not scheduled:**

- The dictionary path (`natDictOp`/`natHDictOp`/`knownOpOf`) is a second
  operator-acceptance route accepting thirteen constants, all hard-mapped to kind
  `"Nat"`, six of which are polymorphic in `α` in Lean. It does not misfire today
  and is documented in `AGENTS.md`; item 3 above covers the one case where a
  misfire would not be caught by the compiler. Also: `instDiv`/`instMod` in
  `natDictOp` are dead rows (Lean 4.30 names them `Nat.instDiv`/`Nat.instMod`),
  and unlike `deciderNames` these are single-backticked so the build does not
  check them.
- `Nat` `shl`/`pow` report an error for inputs Lean answers totally — `0 <<< 64`
  is `0` in Lean but `Err(ShiftOverflow)` here, because Rust's `checked_shl` is
  `None` for any amount ≥ width regardless of value. Pre-existing since S0/S1,
  and an `Err` is not a panic, but it is a faithfulness gap.
- `Int` add/mul/pow reuse `AddOverflow`/`MulOverflow`/`PowOverflow`, whose
  messages still say "Nat … u64". Fix the strings; do not split the variants —
  the failure is identical and the enum is deliberately `Copy` and payload-free.
- `op_is_fallible`'s agreement with every rendering arm holds across all 54
  (operation, kind) cells, but by construction and review rather than by test.
  A table test over all pairs would make it permanent.
- `tests/goldens_consumed.rs` is a name-mention check, not a semantic one: a
  golden bound to a variable and never compared would pass. Adequate for the
  failure it targets (a golden nobody reads), and honestly documented as such.
