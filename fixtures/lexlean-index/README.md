# Imported byte indexing

Two LexLean modules exercise a cross-module byte-index wrapper. Generated Lean
is copied unchanged; the receipt binds compiler identity, source, lock, workspace
and the complete output tree. `just specialized-index` checks the receipt,
retained typed LCNF, altered-body rejection, native std/no_std behavior and Wasm.
