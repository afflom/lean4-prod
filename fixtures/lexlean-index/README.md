# Imported byte indexing

Two LexLean modules exercise cross-module byte-index and slice wrappers. Generated Lean
is copied unchanged; the receipt binds compiler identity, source, lock, workspace
and the complete output tree. `just specialized-index` checks both wrappers' receipt,
retained typed LCNF, altered-body rejection, native std/no_std behavior and Wasm.
