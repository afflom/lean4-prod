# Multi-backend split (Plan 1 of 2) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Split `prod-codegen` into a language-neutral lowering plus a Rust printer, with Rust at behavioural parity — no new backend ships.

**Architecture:** A new `prod-lower` crate owns a `TargetProfile`, a profile-driven fallibility fixpoint, an imperative Target IR, and name injectivity. A new `prod-emit-rust` prints Target IR. `prod-codegen` becomes a thin facade preserving its current public API. The migration uses a strangler pattern: the existing renderer keeps working while the new path is built beside it, with a differential harness comparing the two, and the old renderer is deleted only at cutover.

**Tech Stack:** Rust 1.95, `#![no_std]` + `alloc`, `nom` 7 (parser, unchanged), Lean 4.30.0 (unchanged), `just` + nix dev shell.

**Spec:** `specs/designs/2026-08-11-multi-backend-codegen.md`. This plan is **Plan 1 of 2** — the spec's "Implementation sequencing" section. Plan 2 is the Python backend, the prelude, generated assertions, the divergence registry and per-backend contracts. **Nothing in this plan is Python-specific**, but the profile must be able to express Python or the split has failed; several tasks assert that with `TargetProfile::PYTHON` even though no Python is emitted here.

## Global Constraints

- NO mathlib. Pure Lean 4 core/Init. NO `sorry`, NO `axiom`. **This plan changes nothing in `lean/`.**
- `prod-ir`, `prod-lower`, `prod-emit-rust` and `prod-codegen` stay `#![no_std]` (with `alloc`) and wasm32-clean. No `std`.
- `unsafe_code = "forbid"` workspace-wide except `prod-wasm` and `prod-alloc-counter`.
- `prod-core` denies `clippy::{unwrap_used, expect_used, panic}` — **including in its test targets**, so tests there propagate with `?`.
- Generated code must not panic on caller-controlled input and must not allocate.
- Generated artifacts are never hand-edited. `rust/prod-core/kernel.ir`, `goldens.ir`, `roots.json`, `coverage.md`, `subset.json` are gitignored — never add them by name; `git add -A` is fine. `lean/Conformance/golden.ir`, `golden-rejected.ir` and `specs/lean-for-production.md` are committed but regenerated only by the tooling.
- **`just conformance-bless` now requires a commit, not just a stage** — the gates diff against `HEAD`, not the index.
- lean/lake are NOT on PATH: `cd /Users/auser/work/rust/mine/lean4-prod/lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command <cmd>`. Lean builds take MINUTES — use 600000ms timeouts.
- Gates before every commit: `nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just prod` from the repo root, plus from `rust/`: `cargo clippy --all-targets -- -D warnings`, `cargo fmt --all -- --check`, and `RUSTC=$(rustup which --toolchain stable rustc) rustup run stable cargo build -p prod-ir -p prod-codegen -p prod-wasm --target wasm32-unknown-unknown`.
- Commit at the end of every task. Do NOT push.
- **`prod-codegen`'s public API must not change.** Consumers: `prod-cli`, `prod-macros`, `prod-wasm`, `prod-codegen-compile-tests`. The surface is `Error`, `REJECTIONS`, `Shape`, `generate_module`, `generate_def`.

## File structure

| File | Responsibility |
|---|---|
| `rust/prod-lower/src/profile.rs` | `TargetProfile` and its constants; the only place a language's semantics are declared |
| `rust/prod-lower/src/shape.rs` | `Shape`, the profile-driven fallibility fixpoint |
| `rust/prod-lower/src/names.rs` | `NamePolicy`, mangling, injectivity checking |
| `rust/prod-lower/src/target.rs` | Target IR data types only — no logic |
| `rust/prod-lower/src/lower.rs` | IR → Target IR |
| `rust/prod-lower/src/error.rs` | `LowerError`, folded into `prod-codegen::Error` |
| `rust/prod-emit-rust/src/lib.rs` | Target IR → Rust source |
| `rust/prod-codegen/src/lib.rs` | Facade: re-exports plus the existing renderer until cutover |

---

### Task 1: `prod-lower` with a profile-driven fallibility fixpoint

The most surgical possible first move: `op_is_fallible` currently hard-codes `matches!(k, Nat | Int)`. That single function is where a language's semantics enter the system.

**Files:**
- Create: `rust/prod-lower/Cargo.toml`, `rust/prod-lower/src/lib.rs`, `src/profile.rs`, `src/shape.rs`
- Modify: `rust/Cargo.toml` (workspace members), `rust/prod-codegen/Cargo.toml`, `rust/prod-codegen/src/lib.rs`

**Interfaces:**
- Produces:
  - `prod_lower::profile::{TargetProfile, NatRepr, ListStrategy, DivisionSemantics}`
  - `TargetProfile::RUST`, `TargetProfile::PYTHON` (associated consts)
  - `TargetProfile::op_is_fallible(&self, expr: &Expr) -> bool`
  - `prod_lower::shape::{Shape, Signatures, signatures}` with `signatures<'m>(defs: &'m [Definition], profile: &TargetProfile) -> Signatures<'m>`
- `prod-codegen` re-exports `Shape` so its public API is unchanged.

- [ ] **Step 1: Create the crate**

`rust/prod-lower/Cargo.toml` — copy `rust/prod-ir/Cargo.toml`'s `[package]` metadata style (edition, version, license) exactly, then:

```toml
[dependencies]
prod-ir = { path = "../prod-ir" }
```

`rust/prod-lower/src/lib.rs`:

```rust
//! Language-neutral lowering: IR → Target IR.
//!
//! Everything in this crate is shared by every backend. A backend's own
//! opinions live in a [`profile::TargetProfile`] it hands in, never in
//! branches here on which language is being generated.
#![no_std]

extern crate alloc;

pub mod profile;
pub mod shape;
```

Add `prod-lower` to `rust/Cargo.toml`'s `members`.

- [ ] **Step 2: Write the failing tests**

Create `rust/prod-lower/src/profile.rs` containing ONLY this test module for now:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use alloc::boxed::Box;
    use alloc::string::String;
    use alloc::vec;
    use prod_ir::{Definition, Expr, NumKind, Type};

    fn nat_add_def() -> Definition {
        Definition {
            name: String::from("f"),
            params: vec![
                (String::from("a"), Type::Nat),
                (String::from("b"), Type::Nat),
            ],
            ret: Type::Nat,
            body: Expr::Add(
                NumKind::Nat,
                Box::new(Expr::Var(String::from("a"))),
                Box::new(Expr::Var(String::from("b"))),
            ),
        }
    }

    #[test]
    fn rust_profile_makes_nat_add_fallible() {
        // u64 is finite, so Lean's total Nat.add becomes a checked add.
        assert!(TargetProfile::RUST.op_is_fallible(&nat_add_def().body));
    }

    #[test]
    fn python_profile_makes_nat_add_total() {
        // Python's int is arbitrary precision, exactly like Lean's Nat, so
        // there is nothing to check. This is the whole point of the profile:
        // if this test ever passes vacuously the split has bought nothing.
        assert!(!TargetProfile::PYTHON.op_is_fallible(&nat_add_def().body));
    }

    #[test]
    fn sized_arithmetic_is_total_under_every_profile() {
        // UInt8 add is BitVec addition in Lean -- wrapping IS the semantics,
        // not an overflow, so no profile may mark it fallible.
        let e = Expr::Add(
            NumKind::U8,
            Box::new(Expr::Var(String::from("a"))),
            Box::new(Expr::Var(String::from("b"))),
        );
        assert!(!TargetProfile::RUST.op_is_fallible(&e));
        assert!(!TargetProfile::PYTHON.op_is_fallible(&e));
    }

    #[test]
    fn nat_shift_left_stays_fallible_even_under_exact_nat() {
        // The spec's deliberate divergence: an exact-Nat backend caps the
        // shift and raises rather than attempting 1 << 10**9 and exhausting
        // memory. A hang is a worse failure than an error.
        let e = Expr::Shl(
            NumKind::Nat,
            Box::new(Expr::Var(String::from("a"))),
            Box::new(Expr::Var(String::from("b"))),
        );
        assert!(TargetProfile::RUST.op_is_fallible(&e));
        assert!(TargetProfile::PYTHON.op_is_fallible(&e));
    }
}
```

- [ ] **Step 3: Run to verify they fail**

Run: `cd rust && cargo test -p prod-lower`
Expected: FAIL — `TargetProfile` does not exist.

- [ ] **Step 4: Implement the profile**

Prepend to `rust/prod-lower/src/profile.rs`:

```rust
//! What a target language's semantics are, declared rather than branched on.

use prod_ir::{Expr, NumKind};

/// How a backend represents Lean's `Nat`.
///
/// Lean's `Nat` is arbitrary precision, so `Nat.add` is total. A backend that
/// maps it to a fixed-width integer introduces a failure mode Lean does not
/// have; a backend with native bignums does not. Every fallibility decision
/// for `Nat` follows from this one field.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NatRepr {
    /// 64-bit. Checked arithmetic; overflow is reported.
    Bounded64,
    /// Arbitrary precision, as in Lean. Arithmetic is total.
    Exact,
}

/// How a backend represents Lean's `List`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ListStrategy {
    /// Caller supplies storage; the lowering emits an explicit bounds check.
    CallerBuffer,
    /// The host has a growable sequence; elements are pushed.
    NativeSequence,
}

/// The host language's own integer division, which the lowering corrects
/// toward Lean's Euclidean semantics when they differ.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DivisionSemantics {
    Euclidean,
    /// Rounds toward negative infinity. Agrees with Euclidean **only when the
    /// divisor is positive** -- `12 / -7` is `-2 rem -2` floor, `-1 rem 5`
    /// Euclidean.
    Floor,
    /// Rounds toward zero.
    Truncate,
}

/// One target language's semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TargetProfile {
    pub nat_repr: NatRepr,
    pub list_strategy: ListStrategy,
    /// The host has no fixed-width integers, so every sized operation needs an
    /// explicit mask.
    pub sized_mask_required: bool,
    pub host_division: DivisionSemantics,
}

impl TargetProfile {
    pub const RUST: TargetProfile = TargetProfile {
        nat_repr: NatRepr::Bounded64,
        list_strategy: ListStrategy::CallerBuffer,
        sized_mask_required: false,
        host_division: DivisionSemantics::Truncate,
    };

    /// Declared here, in Plan 1, deliberately: a seam with one implementation
    /// encodes that implementation's assumptions. Plan 2 builds the emitter;
    /// this constant is what keeps Plan 1's tests honest.
    pub const PYTHON: TargetProfile = TargetProfile {
        nat_repr: NatRepr::Exact,
        list_strategy: ListStrategy::NativeSequence,
        sized_mask_required: true,
        host_division: DivisionSemantics::Floor,
    };

    /// Does this operation report failure under this profile?
    ///
    /// Sized integers wrap in Lean (`UInt8.add` is BitVec addition), so they
    /// are total under every profile. `Nat` subtraction saturates in Lean and
    /// never fails. `Nat` shift-left is fallible everywhere -- an exact-`Nat`
    /// backend caps it rather than attempting an allocation that would hang.
    /// What remains is governed by `nat_repr`.
    pub fn op_is_fallible(&self, expr: &Expr) -> bool {
        let nat_checked = self.nat_repr == NatRepr::Bounded64;
        match expr {
            Expr::Add(k, ..) | Expr::Mul(k, ..) | Expr::Pow(k, ..) => match k {
                NumKind::Nat => nat_checked,
                NumKind::Int => true,
                _ => false,
            },
            Expr::Sub(k, ..) | Expr::Div(k, ..) | Expr::Mod(k, ..) => *k == NumKind::Int,
            Expr::Neg(k, _) => *k == NumKind::Int,
            Expr::Shl(k, ..) => *k == NumKind::Nat,
            _ => false,
        }
    }
}
```

`Int` stays unconditionally fallible: `nat_repr` governs `Nat` only, and the two are separate knobs. If a later backend wants exact `Int`, that is a new field, not a reinterpretation of this one.

- [ ] **Step 5: Move the fixpoint**

Create `rust/prod-lower/src/shape.rs` by moving `Shape`, `Signatures`, `signatures` and `is_fallible` verbatim from `rust/prod-codegen/src/lib.rs`, with two changes: `signatures` takes `profile: &TargetProfile` as a second parameter, and `is_fallible` takes and threads it, calling `profile.op_is_fallible(expr)` instead of the free function. Delete the free `op_is_fallible` from `prod-codegen`. Keep every doc comment.

- [ ] **Step 6: Make `prod-codegen` a consumer**

Add `prod-lower = { path = "../prod-lower" }` to `rust/prod-codegen/Cargo.toml`. In `rust/prod-codegen/src/lib.rs`, delete the moved items and add:

```rust
pub use prod_lower::shape::Shape;
use prod_lower::profile::TargetProfile;
use prod_lower::shape::{signatures, Signatures};
```

Every existing `signatures(defs)` call site becomes `signatures(defs, &TargetProfile::RUST)`.

- [ ] **Step 7: Run the full suite**

Run: `cd rust && cargo test --workspace`
Expected: PASS, including every pre-existing `prod-codegen` test. If any generated output changed, something moved that should not have — this task is a pure move plus one parameter.

- [ ] **Step 8: Gates and commit**

Run `just prod` from the repo root, then clippy, fmt and the wasm32 build from `rust/`.

Commit message:

```
Fallibility becomes a property of the backend, not the IR

op_is_fallible hard-coded matches!(k, Nat | Int). That is not a fact
about Lean -- Lean's Nat is arbitrary precision and Nat.add is total.
The check exists because u64 is finite, so it belongs to the backend.

TargetProfile::PYTHON is declared now, in the plan that emits no Python,
because a seam with one implementation encodes that implementation's
assumptions. It is what makes the fixpoint tests non-vacuous.

Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>
```

---

### Task 2: Name policy and injectivity in core

`type_table` already rejects two types whose last components collide (`DuplicateTypeName`). That check is real, ad-hoc, and covers only types. C flattens every name into one global namespace, and Python cannot escape keywords the way Rust's `r#` does — it must *rename*, which is irreversible. Generalise the existing check before three backends each grow their own.

**Files:**
- Create: `rust/prod-lower/src/names.rs`
- Modify: `rust/prod-lower/src/lib.rs`, `rust/prod-codegen/src/lib.rs`

**Interfaces:**
- Consumes: nothing from Task 1.
- Produces:
  - `prod_lower::names::{NamePolicy, EscapeStrategy, NameTable, NameError}`
  - `NamePolicy::RUST`
  - `NameTable::build(module: &Module, policy: &NamePolicy) -> Result<NameTable, NameError>`
  - `NameTable::target_name(&self, lean_name: &str) -> Option<&str>`

- [ ] **Step 1: Write the failing tests**

Create `rust/prod-lower/src/names.rs` with only this test module. **Read the real field names of `TypeDecl` and `CtorDecl` out of `rust/prod-ir/src/lib.rs` first** — construct them exactly as declared rather than as written here, and fix the literals if they have drifted.

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use alloc::format;
    use alloc::string::String;
    use alloc::vec;
    use prod_ir::{CtorDecl, Module, TypeDecl};

    fn module_with_types(names: &[&str]) -> Module {
        Module {
            name: String::from("M"),
            types: names
                .iter()
                .map(|n| TypeDecl {
                    name: String::from(*n),
                    ctors: vec![CtorDecl {
                        name: format!("{}.mk", n),
                        fields: vec![],
                    }],
                    unsupported: None,
                    invariant: None,
                })
                .collect(),
            definitions: vec![],
        }
    }

    #[test]
    fn distinct_lean_names_that_flatten_to_one_target_name_are_rejected() {
        // The failure this component exists to prevent. Both flatten to
        // `Instance`; `crate::Instance` can only mean one of them, and
        // whichever loses is silently miscompiled.
        let m = module_with_types(&["A.Instance", "B.Instance"]);
        let err = NameTable::build(&m, &NamePolicy::RUST).unwrap_err();
        assert!(
            matches!(&err, NameError::Collision { target, .. } if target == "Instance"),
            "expected a collision on `Instance`, got {:?}",
            err
        );
    }

    #[test]
    fn distinct_names_that_stay_distinct_are_accepted() {
        let m = module_with_types(&["A.Instance", "A.Window"]);
        let table = NameTable::build(&m, &NamePolicy::RUST).expect("no collision");
        assert_eq!(table.target_name("A.Instance"), Some("Instance"));
        assert_eq!(table.target_name("A.Window"), Some("Window"));
    }

    #[test]
    fn a_keyword_name_is_escaped_not_renamed_under_the_rust_policy() {
        let m = module_with_types(&["A.type"]);
        let table = NameTable::build(&m, &NamePolicy::RUST).expect("no collision");
        assert_eq!(table.target_name("A.type"), Some("r#type"));
    }

    #[test]
    fn a_rename_policy_still_produces_injective_names() {
        // Python cannot escape, so it renames -- and renaming is exactly where
        // two distinct inputs silently become one. `type` renames to `type_`,
        // so a sibling literally named `type_` must collide rather than be
        // silently merged.
        let policy = NamePolicy {
            keywords: &["type"],
            escape: EscapeStrategy::SuffixUnderscore,
            flatten_namespaces: false,
        };
        let m = module_with_types(&["A.type", "A.type_"]);
        let err = NameTable::build(&m, &policy).unwrap_err();
        assert!(matches!(&err, NameError::Collision { target, .. } if target == "type_"));
    }
}
```

- [ ] **Step 2: Run to verify they fail**

Run: `cd rust && cargo test -p prod-lower names`
Expected: FAIL — `NamePolicy` does not exist.

- [ ] **Step 3: Implement**

Prepend to `names.rs`:

```rust
//! One place that guarantees distinct Lean names stay distinct.

use alloc::collections::BTreeMap;
use alloc::string::String;
use prod_ir::Module;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EscapeStrategy {
    /// Rust: `r#type`. Reversible.
    RawIdentifier,
    /// Python, C: `type_`. NOT reversible, which is why injectivity is checked.
    SuffixUnderscore,
}

pub struct NamePolicy {
    pub keywords: &'static [&'static str],
    pub escape: EscapeStrategy,
    /// C has no namespaces: `A.B.c` must become one globally unique symbol.
    pub flatten_namespaces: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NameError {
    Collision {
        target: String,
        first: String,
        second: String,
    },
}

pub struct NameTable {
    forward: BTreeMap<String, String>,
}

impl NameTable {
    pub fn target_name(&self, lean_name: &str) -> Option<&str> {
        self.forward.get(lean_name).map(|s| s.as_str())
    }
}
```

`NameTable::build` walks every type, constructor, field and definition name; applies the policy (last component unless `flatten_namespaces`, then the keyword escape); inserts into `forward`; and inserts into a **reverse** `BTreeMap<String, String>` used solely to detect collisions. On a duplicate target name, return `NameError::Collision { target, first, second }` naming both Lean sources. The reverse map is the component — without it this is just a mangler.

`NamePolicy::RUST` uses the `RUST_KEYWORDS` list currently in `prod-codegen`; move that constant here and have `prod-codegen` use `prod_lower::names`'s copy.

- [ ] **Step 4: Run tests**

Run: `cd rust && cargo test -p prod-lower`
Expected: PASS, all four.

- [ ] **Step 5: Retire the ad-hoc check**

`type_table`'s `short_seen` collision check is now a special case of `NameTable`. Leave `Error::DuplicateTypeName` and its `REJECTIONS` entry **exactly as they are** — the published contract names that rejection and a test pins its wording — but have `type_table` obtain its answer from `NameTable` so there is one implementation. If that changes which error a given input produces, stop and report rather than adjusting the contract to match.

- [ ] **Step 6: Full suite, gates, commit**

Run: `cd rust && cargo test --workspace`, then `just prod`, clippy, fmt, wasm32.

Commit message:

```
Name injectivity becomes a checked guarantee in one place

type_table already rejected two types whose last components collide.
That check was real but ad-hoc and covered only types, while C flattens
every name into one namespace and Python must rename keywords rather
than escape them -- and renaming is where two distinct inputs silently
become one.

The reverse map is the component: distinct Lean names must map to
distinct target names, verified, naming both sources when they do not.

Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>
```

---

### Task 3: Target IR types, and a tracer bullet through arithmetic

The first end-to-end slice. Deliberately narrow — literals, params, arithmetic, `let`, calls — but it goes all the way from `Expr` to Rust source, so the seam is proven before the hard cases arrive.

**Files:**
- Create: `rust/prod-lower/src/target.rs`, `rust/prod-lower/src/lower.rs`, `rust/prod-lower/src/error.rs`
- Create: `rust/prod-emit-rust/Cargo.toml`, `rust/prod-emit-rust/src/lib.rs`
- Modify: `rust/prod-lower/src/lib.rs`, `rust/Cargo.toml`, `rust/prod-ir/src/lib.rs` (remove `rust_type`)

**Interfaces:**
- Consumes: `TargetProfile`, `signatures`, `Shape` (Task 1); `NameTable` (Task 2).
- Produces:
  - `prod_lower::target::{Stmt, TExpr, Lit, BinOp, FallibleOp, Arm, ErrorCode, Body}`
  - `prod_lower::lower::lower_def(def: &Definition, shapes: &Signatures, profile: &TargetProfile) -> Result<Body, LowerError>`
  - `prod_lower::error::LowerError`
  - `prod_emit_rust::emit_body(body: &Body) -> String`
  - `prod_emit_rust::rust_type(kind: NumKind) -> &'static str` (moved from `prod-ir`)

- [ ] **Step 1: Define the Target IR**

`rust/prod-lower/src/target.rs`. Data only — no logic, no `impl` beyond derives.

```rust
//! The imperative IR every backend prints.
//!
//! # The invariant that makes this worth having
//!
//! **`TExpr` is total by construction.** Anything that can fail is a [`Stmt`].
//!
//! Rust and Python propagate errors inside an expression (`?`, exceptions); C
//! cannot -- it needs statements before the expression they feed. A renderer
//! returning a String per expression node can serve the first two and never
//! the third. Hoisting every failure to statement position serves all three,
//! and means the fallibility decision is made once, here, rather than
//! re-derived by each printer.

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use prod_ir::{NumKind, Type};

#[derive(Debug, Clone, PartialEq)]
pub enum Lit {
    Nat(u64),
    Int(i64),
    Bool(bool),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add, Sub, Mul, Div, Mod, Shl, Shr, Pow,
    Eq, Lt, Le, Gt,
    /// Bitwise AND. Emitted only by sized-integer masking under a profile with
    /// `sized_mask_required`; Lean has no such operator in the whitelist.
    BitAnd,
}

/// An operation that can fail, and therefore may appear only in [`Stmt::TryLet`].
#[derive(Debug, Clone, PartialEq)]
pub enum FallibleOp {
    Arith(NumKind, BinOp, TExpr, TExpr),
    Neg(NumKind, TExpr),
    /// A call to a definition whose [`crate::shape::Shape`] is `Fallible`.
    Call(String, Vec<TExpr>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum TExpr {
    Lit(Lit),
    Var(String),
    /// Infallible operations ONLY. Anything the profile marks fallible is a
    /// `TryLet`, never this.
    BinOp(NumKind, BinOp, Box<TExpr>, Box<TExpr>),
    Ctor(String, String, Vec<TExpr>),
    Proj(String, String, Box<TExpr>),
    /// Total callees ONLY.
    Call(String, Vec<TExpr>),
    Not(Box<TExpr>),
    And(Box<TExpr>, Box<TExpr>),
    Or(Box<TExpr>, Box<TExpr>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Arm {
    pub ctor: String,
    pub binders: Vec<String>,
    pub body: Vec<Stmt>,
}

/// Which failure a [`Stmt::Fail`] reports. Mirrors `prod_core::ComputeError`'s
/// variants by name; each printer maps it to its own error type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorCode {
    OutputTooSmall,
    Unreachable,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Let { name: String, ty: Type, value: TExpr },
    /// The only failure point in the language.
    TryLet { name: String, ty: Type, op: FallibleOp },
    If { cond: TExpr, then: Vec<Stmt>, else_: Vec<Stmt> },
    Switch { scrut: TExpr, arms: Vec<Arm>, default: Option<Vec<Stmt>> },
    Return(TExpr),
    Fail(ErrorCode),
    /// List construction, abstract over `ListStrategy`. Under `CallerBuffer`
    /// the lowering emits the index arithmetic and an explicit bounds check
    /// beside this; under `NativeSequence` it stands alone.
    Push { seq: String, value: TExpr },
}

/// One lowered definition.
#[derive(Debug, Clone, PartialEq)]
pub struct Body {
    pub name: String,
    pub params: Vec<(String, Type)>,
    pub ret: Type,
    pub shape: crate::shape::Shape,
    pub stmts: Vec<Stmt>,
}
```

- [ ] **Step 2: Write the failing lowering tests**

`rust/prod-lower/src/lower.rs`, test module only:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::profile::TargetProfile;
    use crate::shape::signatures;
    use crate::target::*;
    use alloc::boxed::Box;
    use alloc::string::String;
    use alloc::vec;
    use prod_ir::{Definition, Expr, NumKind, Type};

    fn def_add() -> Definition {
        Definition {
            name: String::from("f"),
            params: vec![
                (String::from("a"), Type::Nat),
                (String::from("b"), Type::Nat),
            ],
            ret: Type::Nat,
            body: Expr::Add(
                NumKind::Nat,
                Box::new(Expr::Var(String::from("a"))),
                Box::new(Expr::Var(String::from("b"))),
            ),
        }
    }

    #[test]
    fn a_fallible_op_becomes_a_trylet_and_a_return() {
        let defs = vec![def_add()];
        let shapes = signatures(&defs, &TargetProfile::RUST);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");

        assert_eq!(
            body.stmts.len(),
            2,
            "expected TryLet + Return, got {:?}",
            body.stmts
        );
        assert!(matches!(
            &body.stmts[0],
            Stmt::TryLet {
                op: FallibleOp::Arith(NumKind::Nat, BinOp::Add, ..),
                ..
            }
        ));
        match (&body.stmts[0], &body.stmts[1]) {
            (Stmt::TryLet { name, .. }, Stmt::Return(TExpr::Var(v))) => {
                assert_eq!(v, name, "the Return must name the temporary the TryLet bound");
            }
            other => panic!("expected TryLet then Return of its temporary, got {:?}", other),
        }
    }

    #[test]
    fn the_same_op_is_a_plain_binop_under_an_exact_nat_profile() {
        // Not a formatting difference: under Exact there is no failure to
        // hoist, so the statement list has a different SHAPE. This is the
        // fallibility decision being made once, in the lowering.
        let defs = vec![def_add()];
        let shapes = signatures(&defs, &TargetProfile::PYTHON);
        let body = lower_def(&defs[0], &shapes, &TargetProfile::PYTHON).expect("lowers");

        assert_eq!(body.stmts.len(), 1, "expected a bare Return, got {:?}", body.stmts);
        assert!(matches!(
            &body.stmts[0],
            Stmt::Return(TExpr::BinOp(NumKind::Nat, BinOp::Add, ..))
        ));
    }
}
```

- [ ] **Step 3: Run to verify they fail**

Run: `cd rust && cargo test -p prod-lower lower`
Expected: FAIL — `lower_def` does not exist.

- [ ] **Step 4: Implement the arithmetic slice**

Create `rust/prod-lower/src/error.rs`:

```rust
use alloc::string::String;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LowerError {
    ParamOutOfBounds(usize),
    /// Scaffolding. Task 7 proves no corpus definition can produce this, then
    /// deletes the variant so the compiler finds any node without a lowering.
    NotYetLowered(String),
    Name(crate::names::NameError),
}
```

`lower_def` walks `def.body` with a statement accumulator:

1. Maintain `stmts: Vec<Stmt>` and a counter yielding fresh temporaries `t0`, `t1`, …
2. `lower_expr(e, stmts) -> Result<TExpr, LowerError>` returns a **total** expression, pushing statements as needed.
3. Arithmetic node: lower both operands, then — if `profile.op_is_fallible(e)` — push `TryLet { name: fresh(), ty, op: FallibleOp::Arith(..) }` and return `TExpr::Var(name)`; otherwise return `TExpr::BinOp(..)` directly.
4. `Expr::Let(name, value, body)`: lower `value`, push `Stmt::Let`, lower `body`.
5. `Expr::Nat`/`Int`/`Bool` → `TExpr::Lit`. `Expr::Var` → `TExpr::Var`. `Expr::Param(i)` → `TExpr::Var(params[i].0.clone())`, or `LowerError::ParamOutOfBounds(i)`.
6. `Expr::Call(name, args)`: lower the args, then consult `shapes` — `Shape::Fallible` becomes a `TryLet` with `FallibleOp::Call`, `Shape::Value` becomes `TExpr::Call`. `Buffer` and `StaticList` are Task 6.
7. Every other node → `LowerError::NotYetLowered(<node name>)`. Later tasks replace those arms.
8. Finish with `stmts.push(Stmt::Return(result))`.

- [ ] **Step 5: Run the lowering tests**

Run: `cd rust && cargo test -p prod-lower`
Expected: PASS.

- [ ] **Step 6: The Rust printer for this slice**

Create `rust/prod-emit-rust` (dependencies: `prod-ir`, `prod-lower`; `#![no_std]` with `alloc`). `emit_body(&Body) -> String` renders the signature from `body.shape` (`Value` → `-> T`, `Fallible` → `-> Result<T, crate::ComputeError>`) and prints the statement list, re-inlining a `TryLet` whose temporary is used exactly once into `expr?` so Rust output stays idiomatic.

Move `NumKind::rust_type` here from `prod-ir` as a free function `rust_type(NumKind) -> &'static str`, keeping its doc comment about pinning an arithmetic receiver's type (E0689). Update `prod-codegen`'s uses. This is the one genuinely Rust-specific thing in the IR crate.

Test end to end, in `prod-emit-rust`:

```rust
#[test]
fn a_fallible_nat_add_prints_as_checked_rust() {
    let defs = alloc::vec![def_add()];
    let shapes = signatures(&defs, &TargetProfile::RUST);
    let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");
    let out = emit_body(&body);
    assert!(out.contains("-> Result<u64, crate::ComputeError>"), "got: {}", out);
    assert!(out.contains("checked_add"), "got: {}", out);
    assert!(out.contains('?'), "got: {}", out);
}
```

Duplicate `def_add()` into this crate's test module rather than exporting it — a fixture crossing a crate boundary for one assertion is not worth a `pub` item.

- [ ] **Step 7: Preserve the arithmetic renderings, which are load-bearing semantics**

"Arithmetic" in Step 4 hides five specific renderings in the current `Renderer`. Each encodes a Lean fact that took two milestones and one shipped defect to establish, and each must survive the port **unchanged**. Port them into `prod-emit-rust` and write one test per bullet asserting the rendered text:

- **`div_or_mod` — division by zero is total, and the two operators give DIFFERENT answers.** `x / 0 = 0` but `x % 0 = x`, matching `Nat.div_zero : n / 0 = 0` and `Nat.mod_zero : n % 0 = n`; `Init/Prelude.lean:2183` states the modulo half — *"When the divisor is `0`, the result is the dividend rather than an error"*, doctest `5 % 0 = 5` — and `Int.emod_zero : a % 0 = a` agrees. The code carries a `zero_is_dividend` flag that is `false` for `Div` and `true` for `Mod`. **Preserve both arms.** Rendering an error for either was a real defect shipped since M3; rendering the dividend for *division* would be a new one.
- **`div_or_mod` — `Int` division is Euclidean**, via `Int.ediv`/`Int.emod`, not Rust's truncating `/`. Lean's doctest gives `(-12) % 7 = 2` where Rust's `%` gives `-5`.
- **`total_shift` (`lib.rs:1613`) — `Nat.shiftRight` truncates to `0`** for large amounts: `checked_shr(..).unwrap_or(0)`, total and infallible.
- **`wrapping_shift` (`lib.rs:1652`) — `UIntN.shiftLeft` MASKS the amount mod width**, so `wrapping_shl` is correct. `Init/Data/UInt/Basic.lean:126`: `UInt8.shiftLeft a b = ⟨a.toBitVec <<< (UInt8.mod b 8).toBitVec⟩`, so `(1 : UInt8) <<< 8 = 1`, **not** `0`. This one shipped backwards once, green in CI, because nothing compared Lean's own golden to Rust's answer.
- **`wrapping_binop` (`lib.rs:1587`) and `checked_exponent_op` (`lib.rs:1518`)** — sized arithmetic wraps and cannot fail; `pow` on a sized kind is rejected because narrowing a `u64` exponent to `wrapping_pow`'s `u32` would silently change the answer.

These are printer concerns — *which Rust method* — except the zero-divisor and Euclidean rules, which are **semantics** and therefore belong in the lowering. Route them through the `host_division` profile field rather than hard-coding them in `prod-emit-rust`, so the field has a consumer in this plan instead of waiting unused for Plan 2. An unused profile field is an untested one.

- [ ] **Step 8: Gates and commit**

Run: `cd rust && cargo test --workspace`, then `just prod`, clippy, fmt, wasm32.

Commit message:

```
Target IR, and a tracer bullet from Expr to Rust source

Narrow on purpose -- literals, params, arithmetic, let, calls -- but end
to end, so the seam is proven before the hard cases arrive.

The two lowering tests are the point. The same Nat add lowers to a
TryLet plus a Return under the Rust profile and to a bare Return under
an exact-Nat one: not a formatting difference but a different statement
list, which is the fallibility decision being made once in the lowering
rather than re-derived by each printer.

NumKind::rust_type moves out of prod-ir, which had no business knowing
Rust's type names.

Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>
```

---

### Task 4: Control flow, and the no-hoist invariant

**Files:**
- Modify: `rust/prod-lower/src/lower.rs`, `rust/prod-emit-rust/src/lib.rs`

**Interfaces:**
- Consumes: `lower_def`, `Stmt`, `TExpr` (Task 3).
- Produces: lowering for `Expr::If`, `Expr::Match`, `Expr::Jp`/`Jmp`, `Expr::Unreachable`; printing for `Stmt::If`, `Stmt::Switch`, `Stmt::Fail`.

- [ ] **Step 1: Write the invariant test first**

This is the test the task exists for. Straight-line examples cannot catch the bug.

```rust
#[test]
fn a_fallible_op_in_one_arm_stays_in_that_arm() {
    // `if c then (a + b) else 0`, Nat, Rust profile.
    //
    // Hoisting the TryLet for `a + b` to the top would evaluate it even when
    // `c` is false -- turning a short-circuit into eager evaluation and
    // producing an overflow error where Lean has none.
    let def = Definition {
        name: String::from("f"),
        params: vec![
            (String::from("c"), Type::Bool),
            (String::from("a"), Type::Nat),
            (String::from("b"), Type::Nat),
        ],
        ret: Type::Nat,
        body: Expr::If(
            Box::new(Expr::Var(String::from("c"))),
            Box::new(Expr::Add(
                NumKind::Nat,
                Box::new(Expr::Var(String::from("a"))),
                Box::new(Expr::Var(String::from("b"))),
            )),
            Box::new(Expr::Nat(0)),
        ),
    };
    let defs = vec![def];
    let shapes = signatures(&defs, &TargetProfile::RUST);
    let body = lower_def(&defs[0], &shapes, &TargetProfile::RUST).expect("lowers");

    // Nothing fallible before the branch.
    for s in &body.stmts {
        if matches!(s, Stmt::If { .. }) {
            break;
        }
        assert!(
            !matches!(s, Stmt::TryLet { .. }),
            "a TryLet was hoisted above the If: {:?}",
            body.stmts
        );
    }
    // And the TryLet is inside the then-branch, not the else.
    let Some(Stmt::If { then, else_, .. }) =
        body.stmts.iter().find(|s| matches!(s, Stmt::If { .. }))
    else {
        panic!("expected an If, got {:?}", body.stmts)
    };
    assert!(
        then.iter().any(|s| matches!(s, Stmt::TryLet { .. })),
        "then: {:?}",
        then
    );
    assert!(
        !else_.iter().any(|s| matches!(s, Stmt::TryLet { .. })),
        "else: {:?}",
        else_
    );
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cd rust && cargo test -p prod-lower stays_in_that_arm`
Expected: FAIL — `Expr::If` reaches the `NotYetLowered` arm.

- [ ] **Step 3: Implement branch lowering**

`If` and `Match` lower each branch into its **own** statement accumulator, so `lower_expr` never lifts a branch's statements into the parent's list. Each branch ends with its own `Stmt::Return`. `Expr::Unreachable` → `Stmt::Fail(ErrorCode::Unreachable)`.

Join points: `prod-codegen` today supports only the single-caller, non-cyclic form and rejects the rest as `UnsupportedJoinPoint`. Preserve that exactly — inline the single-caller form at its jump site, return the same error otherwise. Widening join-point support is not in this plan; `JpContext`'s `jmp_count` and `is_cyclic` logic ports across unchanged.

- [ ] **Step 4: Run the tests**

Run: `cd rust && cargo test -p prod-lower`
Expected: PASS, including the no-hoist test.

- [ ] **Step 5: Print control flow, gates, commit**

Extend `emit_body` for `Stmt::If`, `Stmt::Switch` and `Stmt::Fail`. `Switch` prints as a Rust `match` with arm binders destructured.

Commit message:

```
Control flow, and the invariant that temporaries stay in their branch

A TryLet hoisted out of a branch turns a short-circuit into eager
evaluation -- producing an overflow error where Lean has none. Straight
-line lowering tests cannot see this, so the test with a fallible op in
one arm of a conditional is written first and is the point of the task.

Join-point support is unchanged: the single-caller non-cyclic form
inlines, everything else stays UnsupportedJoinPoint.

Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>
```

---

### Task 5: Types, constructors, projections, and the invariant machinery

**Files:**
- Modify: `rust/prod-lower/src/lower.rs`, `rust/prod-lower/src/target.rs`, `rust/prod-emit-rust/src/lib.rs`

**Interfaces:**
- Consumes: `NameTable` (Task 2), `TExpr` (Task 3).
- Produces:
  - `prod_lower::target::TypeDef` — the declaration plus its optional lowered invariant (`Option<TExpr>`) and `fields_private: bool`
  - `prod_lower::lower::lower_types(module: &Module, policy: &NamePolicy) -> Result<Vec<TypeDef>, LowerError>`
  - `prod_emit_rust::emit_types(types: &[TypeDef]) -> String`

- [ ] **Step 1: Write the failing tests**

The invariant machinery from PR #4 is the delicate part, and its behaviour must be preserved exactly.

```rust
#[test]
fn an_invariant_carrying_type_still_gets_private_fields_and_a_checked_new() {
    let ir = r#"
(module M
  (type "UorAtlas.Instance"
    (ctor "UorAtlas.Instance.mk" (q Nat) (T Nat) (O Nat))
    (invariant (and (le 1 q) (and (le 1 T) (le 1 O)))))
)
"#;
    let module = prod_ir::parser::parse_module(ir).expect("parses").1;
    let types = lower_types(&module, &NamePolicy::RUST).expect("lowers");
    let out = emit_types(&types);
    assert!(out.contains("pub(crate) q: u64"), "got: {}", out);
    assert!(!out.contains("pub q: u64"));
    assert!(
        out.contains("pub fn new(q: u64, T: u64, O: u64) -> Result<Self, crate::ComputeError>"),
        "got: {}",
        out
    );
    assert!(out.contains("if ((1 <= q) && ((1 <= T) && (1 <= O)))"), "got: {}", out);
    assert!(out.contains("pub fn q(&self) -> u64 { self.q }"), "got: {}", out);
}

#[test]
fn a_type_with_no_lowerable_invariant_keeps_public_fields() {
    let ir = r#"(module M (type "M.Pair" (ctor "M.Pair.mk" (a Nat) (b Nat))))"#;
    let module = prod_ir::parser::parse_module(ir).expect("parses").1;
    let out = emit_types(&lower_types(&module, &NamePolicy::RUST).expect("lowers"));
    assert!(out.contains("pub a: u64"), "got: {}", out);
    assert!(!out.contains("pub(crate)"));
    assert!(!out.contains("fn new("));
}

#[test]
fn the_invariant_is_not_lowered_inverted() {
    // `q >= 1` must render `1 <= q`, never `q <= 1`. A reversed comparison
    // compiles, returns a bool, and rejects exactly the inputs it should
    // accept -- a defect of this exact shape has shipped here before. The two
    // conjuncts point opposite ways on purpose, so a blanket swap is visible.
    let ir = r#"
(module M
  (type "M.Bound" (ctor "M.Bound.mk" (lo Nat) (hi Nat))
    (invariant (and (le 2 lo) (le hi 7))))
)
"#;
    let module = prod_ir::parser::parse_module(ir).expect("parses").1;
    let out = emit_types(&lower_types(&module, &NamePolicy::RUST).expect("lowers"));
    assert!(out.contains("(2 <= lo)"), "got: {}", out);
    assert!(out.contains("(hi <= 7)"), "got: {}", out);
}
```

- [ ] **Step 2: Run to verify they fail**

Run: `cd rust && cargo test -p prod-lower lower_types`
Expected: FAIL — `lower_types` does not exist.

- [ ] **Step 3: Implement**

Port `generate_type_decl` from `prod-codegen`, splitting it along the seam: the **decisions** (is there an invariant, are fields private, is a field named `new`, does a field type check) move to `lower_types`; the **syntax** moves to `emit_types`. Whether a field is private is semantic; how private is spelled is not.

Keep every existing rejection with identical wording — `ReservedFieldName`, `PolymorphicType`, `RecursiveType`, `OpaqueType`, `UnsupportedFieldType`, `UnknownField`, `DuplicateTypeName`. `REJECTIONS` and the published contract pin them, and this is a refactor.

**Restore the constructor-arity rejection, which Task 4 had to drop.** `prod-codegen`'s `generate_type_decl` region rejects a match alternative whose binder count differs from the constructor's declared field count, with `Error::UnsupportedFieldType`. Task 4's `arm_pattern` has no type table, so it falls through to the positional pattern and would emit `M.Shape.circle(r, extra)` for a mismatched arity — which does not compile. Task 4 could not keep the check because the type table arrives here, in Task 5.

So: once `lower_types` exists, thread the arity check back in and test it with an alt whose binder count is wrong. A generator that emits non-compiling code for a malformed input is strictly worse than one that names the reason, and this is the task that can tell the difference.

`Expr::Ctor` → `TExpr::Ctor` and `Expr::Proj` → `TExpr::Proj` in `lower_expr`; both are total.

- [ ] **Step 4: Run tests**

Run: `cd rust && cargo test -p prod-lower && cargo test -p prod-codegen`
Expected: PASS.

- [ ] **Step 5: Gates and commit**

Commit message:

```
Types, constructors, projections, and the checked constructors

The invariant machinery moves across the seam with its decisions on the
lowering side and its syntax on the printer side: whether a field is
private is a semantic question, how private is spelled is not.

Every rejection keeps its exact wording -- REJECTIONS and the published
contract pin them, and this is a refactor, not a redesign.

Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>
```

---

### Task 6: Lists, with the bounds check as an explicit statement

**Files:**
- Modify: `rust/prod-lower/src/lower.rs`, `rust/prod-emit-rust/src/lib.rs`

**Interfaces:**
- Consumes: `ListStrategy` (Task 1); `Stmt::Push`, `Stmt::Fail` (Task 3).
- Produces: lowering for `Shape::Buffer` and `Shape::StaticList` definitions.

- [ ] **Step 1: Read the corpus definition this test uses**

`lean/Conformance/golden.ir:158` declares `c_list_build`, which returns `(List Nat)` and is therefore `Shape::Buffer`. `golden.ir:61` declares `c_list_consume`, which *takes* one — the borrowed-slice parameter case. Read both before writing the test, and use `c_list_build`'s actual body rather than inventing a list-construction spelling.

```bash
sed -n '155,175p' lean/Conformance/golden.ir
```

- [ ] **Step 2: Write the failing test**

```rust
#[test]
fn the_buffer_bounds_check_is_an_explicit_statement_not_the_printers_job() {
    // Running out of caller-supplied buffer is a failure, so by this IR's
    // central invariant it must appear as a statement. Today that check lives
    // inside the Rust renderer -- with three printers that is three chances to
    // forget it.
    //
    // `c_list_build` from lean/Conformance/golden.ir:158 -- copy its `(def ...)`
    // form verbatim into this string, wrapped in `(module M ...)`.
    let ir = include_str!("../../../lean/Conformance/golden.ir");
    let module = prod_ir::parser::parse_module(ir).expect("parses").1;
    let def = module
        .definitions
        .iter()
        .find(|d| d.name.ends_with("c_list_build"))
        .expect("c_list_build is in the corpus");
    let shapes = signatures(&module.definitions, &TargetProfile::RUST);
    let body = lower_def(def, &shapes, &TargetProfile::RUST).expect("lowers");

    assert_eq!(
        body.shape,
        crate::shape::Shape::Buffer,
        "a (List Nat) return must be Buffer under the Rust profile"
    );

    fn mentions_output_too_small(stmts: &[Stmt]) -> bool {
        stmts.iter().any(|s| match s {
            Stmt::Fail(ErrorCode::OutputTooSmall) => true,
            Stmt::If { then, else_, .. } => {
                mentions_output_too_small(then) || mentions_output_too_small(else_)
            }
            Stmt::Switch { arms, default, .. } => {
                arms.iter().any(|a| mentions_output_too_small(&a.body))
                    || default.as_deref().is_some_and(mentions_output_too_small)
            }
            _ => false,
        })
    }
    assert!(
        mentions_output_too_small(&body.stmts),
        "no explicit OutputTooSmall guard in {:?}",
        body.stmts
    );
    assert!(body.stmts.iter().any(|s| matches!(s, Stmt::Push { .. })));
}
```

- [ ] **Step 3: Run to verify it fails**

Run: `cd rust && cargo test -p prod-lower bounds_check`
Expected: FAIL.

- [ ] **Step 4: Also lower comparisons and boolean connectives in definition BODIES**

Found during Task 5 and assigned to no task until now. `Lowering::expr` has no arm for `Expr::{Eq,Lt,Le,Gt,And,Or,Not}`, so a comparison in a *definition body* is still `NotYetLowered`. Task 5 added `lower_invariant` for the boolean fragment, but that is a separate, profile-free path for a structure's invariant predicate — it does not serve bodies.

This blocks Task 7, which proves `NotYetLowered` unreachable across the whole corpus. Corpus bodies do contain comparisons, so without this the proof fails.

Add the arms to `Lowering::expr`. All seven are **total** — none can fail under any profile — so each yields a `TExpr` directly and never a `TryLet`. Render them in `prod-emit-rust` as `==`, `<`, `<=`, `>`, `&&`, `||`, `!`, matching the current `Renderer` exactly. Test at least one comparison and one connective end to end, and check the operand order is preserved: `Lt(a, b)` must render `a < b`, not `b < a`.

**Also add `Expr::Convert`, which has no Target IR node at all.** Found during Task 5. `TExpr` has no conversion form, so `(convert Nat Int x)` cannot lower in a body *or* an invariant. `lean/Conformance/golden.ir` contains three of them, so Task 7's proof that `NotYetLowered` is unreachable across the corpus **will fail** without this.

This means adding a node to `rust/prod-lower/src/target.rs`, which Task 3 created — the one place this task reaches outside its own files. Conversions are total (the whitelist is the lossless set: `Nat<->Int`, `UIntN->Nat`, `Nat->UIntN`), so it is a `TExpr`, not a `FallibleOp`. Port `prod-codegen`'s existing rendering unchanged, including its rejection of the pairs that have none — every sized-to-sized pair and every `Int`-to-sized pair are deliberate non-goals and must stay `UnsupportedKind`, not silently render a cast.

- [ ] **Step 5: Implement the list lowering**

Under `ListStrategy::CallerBuffer`, each element lowers to an `If` comparing the running index against the buffer length, whose else-branch is `Stmt::Fail(ErrorCode::OutputTooSmall)`, followed by `Stmt::Push`. Under `NativeSequence`, just `Stmt::Push` — write that arm now even though no backend uses it yet: it is three lines, and an abstraction with one implementation is not one.

`Shape::StaticList` keeps its current `&'static [E]` rendering; that is a printer concern.

- [ ] **Step 6: Run tests, gates, commit**

Commit message:

```
Lists, with the bounds check hoisted into the IR

Running out of caller-supplied buffer is a failure, so by this IR's
central invariant it belongs in statement position. It lived inside the
Rust renderer, which with three printers is three chances to forget it.

The NativeSequence arm is written now despite having no consumer: it is
three lines, and an abstraction with one implementation is not one.

Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>
```

---

### Task 7: Cutover — `prod-codegen` becomes a facade

**Files:**
- Modify: `rust/prod-codegen/Cargo.toml` — **add `prod-emit-rust = { path = "../prod-emit-rust" }`**. No earlier task adds this dependency, and `generate_module` below cannot call `prod_emit_rust::*` without it.
- Modify: `rust/prod-codegen/src/lib.rs` (the large deletion), `rust/prod-codegen/src/tests.rs`
- Modify: `AGENTS.md`, `specs/designs/2026-08-11-multi-backend-codegen.md`

Note that `prod-wasm` depends on `prod-codegen`, so `prod-emit-rust` joins the wasm32 build transitively. It is `#![no_std]` with `alloc`, so this is fine — but the wasm32 gate is the thing that proves it, not this sentence.

**Interfaces:**
- Consumes: everything from Tasks 1-6.
- Produces: `prod_codegen::generate_module` / `generate_def` delegating to `lower_def` + `emit_body`, with the public API unchanged.

- [ ] **Step 1: Build the differential harness**

Before deleting anything, add a test running **both** paths over every module in the corpus — `lean/Conformance/golden.ir`, `rust/prod-core/kernel.ir`, `rust/prod-codegen-compile-tests/fixtures/representative.ir` — comparing output with whitespace normalised (collapse whitespace runs to one space, drop blank lines).

Normalised rather than exact because the spec traded byte-identity for behavioural equivalence; normalising catches semantic drift without demanding identical formatting.

Put a comment at the top saying this file is **scaffolding, deleted in Step 5**, so it is not mistaken for a permanent guarantee.

- [ ] **Step 2: Run it and report before changing anything**

Run: `cd rust && cargo test -p prod-codegen differential -- --nocapture`

Every difference is either a real lowering bug or an intended formatting change. **Report the list before fixing any of it.** A difference you cannot explain is the most valuable output of this entire plan, and normalising it away silently would waste it.

- [ ] **Step 3: Delete the old renderer**

Remove `Renderer`, `Mode`, `JpContext`, `generate_def_in`, `generate_type_decl`, `type_to_rust`, `param_type_to_rust`, `check_field_type`, `check_named_type`, `list_element`, `type_table` and their helpers from `prod-codegen`. `generate_module` becomes:

```rust
pub fn generate_module(module: &Module) -> Result<String, Error> {
    let profile = TargetProfile::RUST;
    NameTable::build(module, &NamePolicy::RUST)?;
    let types = lower_types(module, &NamePolicy::RUST)?;
    let shapes = signatures(&module.definitions, &profile);

    let mut out = prod_emit_rust::emit_types(&types);
    for def in &module.definitions {
        // `lower_def_in`, NOT `lower_def`: the type-table-aware form is what
        // makes the constructor-arity and `UnknownField` rejections fire. The
        // table-free `lower_def` cannot check either, so using it here would
        // silently drop two rejections that `REJECTIONS` still advertises.
        let body = lower_def_in(def, &shapes, &profile, &module.types)?;
        out.push_str(&prod_emit_rust::emit_body(&body));
        out.push('\n');
    }
    Ok(out)
}
```

`Error` gains `From<LowerError>` and `From<NameError>`. **`REJECTIONS` and every `Error` variant keep their exact current wording** — `test_every_error_variant_is_published_in_rejections` and the published contract both pin them.

`generate_def` keeps its current documented behaviour: a single definition, no module, so cross-definition fallibility and named types stay unresolvable.

- [ ] **Step 4: Prove `NotYetLowered` is unreachable, then delete it**

Add a test asserting that lowering every definition in all three corpus files yields no `LowerError::NotYetLowered`. Then delete the variant and let the compiler find any arm still producing it. A remaining arm is an IR node with no lowering, which would otherwise degrade silently to a runtime rejection.

- [ ] **Step 5: Delete the differential harness**

It compared the new path against an implementation that no longer exists. Leaving it is dead weight that reads like coverage.

- [ ] **Step 6: Full gates, docs, commit**

Run `just prod`, clippy, fmt, wasm32; confirm `git status` is clean.

Update `AGENTS.md` with the new crate topology and the rule that backend-specific knowledge belongs in a `TargetProfile`, never in a branch inside `prod-lower`. Mark Plan 1 done in the design doc.

Commit message:

```
Cutover: prod-codegen becomes a facade over lower + emit

generate_module now lowers to Target IR and prints it. The public API is
unchanged, which is what lets prod-cli, prod-macros, prod-wasm and the
compile-tests stay untouched.

A differential harness compared both paths over the whole corpus during
the migration and is deleted here along with the old renderer it was
comparing against -- a harness that outlives one of its two subjects
reads like coverage without being any.

NotYetLowered is proven unreachable on the corpus and then deleted, so
the compiler rather than a runtime rejection finds any node without a
lowering.

Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>
```

---

## Final verification

- [ ] **Every gate, from a clean tree**

```bash
cd lean && nix develop path:/Users/auser/work/rust/mine/lean4-prod --command lake build
cd /Users/auser/work/rust/mine/lean4-prod
nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just prod
nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just lint
nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just fmt-check
nix develop path:/Users/auser/work/rust/mine/lean4-prod --command just wasm-check
git status --short
```

- [ ] **Confirm behavioural parity, which is the whole claim of this plan**

`just prod` runs the compile-tests, which compile generated Rust and execute every Lean golden. That passing IS the parity claim. Confirm explicitly that `goldens_consumed`, `smoke`, `rejected` and `no_alloc` each ran, rather than assuming `just prod` covered them.

- [ ] **Confirm the seam is not Rust-shaped**

```bash
grep -rn "rust\|Rust" rust/prod-lower/src --include=*.rs
```

Should return only doc comments and `NamePolicy::RUST`. Any *logic* in `prod-lower` branching on Rust is the design failure this plan exists to prevent — report it rather than fixing it quietly.
