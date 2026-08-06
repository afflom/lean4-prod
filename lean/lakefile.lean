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
lean_exe «prod-export» where
  root := `Prod.Emit
