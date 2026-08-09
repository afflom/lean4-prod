import Lake
open Lake DSL

-- No external libraries: load-bearing identities are proved in pure Lean 4 by
-- `decide` / `omega` / `rfl` (same discipline as uor-addr-lean).
package «lean4-prod» where

lean_lib ProdLib where
  roots := #[`Prod]

@[default_target]
lean_lib Example where
  roots := #[`Example]

@[default_target]
lean_lib Conformance where
  roots := #[`Conformance]

-- Cases whose lowering is pinned but whose codegen is a deliberate rejection.
-- Kept out of `Conformance` so that corpus can carry the stronger promise that
-- everything in it also generates Rust that compiles.
@[default_target]
lean_lib ConformanceRejected where
  roots := #[`ConformanceRejected]

@[default_target]
lean_exe «prod-export» where
  root := `Prod.Emit
