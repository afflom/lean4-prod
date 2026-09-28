# Verification

Baseline `6e366b3c0e6872f4f75deb90ffc2f8e329b6cf5a` fails the ownership
regression. Its freshly generated Wasm traps on the exact 67,108,864-byte
fixture at 1,073,545,216 linear-memory bytes under the unchanged 1 GiB ceiling.

The six actual LexLean declarations passed kernel verification without axioms;
attestation `5906d942b475ae55d15daa15ac1a1a9f575828e450dbfb37e76c9017db72fe3e`.
Generated source and complete build outputs are bound by `fixture-manifest.json`.
Upstream CI checks this retained provenance and freshly compiles the generated
Lean; it does not rerun the external LexLean compiler.

`just owned-accumulator` passes native std/no_std in debug/release and 22 actual
Wasm cases per debug/release build, including exact 64 MiB input/output and
one-over refusal. Observed Wasm linear-memory peak: 536,739,840 bytes. Two fresh
exports, generated packages and Wasm binaries are byte-identical.

Compiler API tests additionally execute aliasing, exclusive branches, eager
arithmetic-error order, public-slice independence and 65,536 iterations on a
64 KiB stack. Eight conservative scope/ownership refusal shapes are checked.
Affected regression runs pass 135 tests. Three existing SDK-wrapper tests cannot
execute in this SDK container because `kotlinc`, `tsc` and `wasm-pack` are absent;
the complete upstream devcontainer CI remains required. Scoped Clippy, formatting,
wasm32 codegen builds and unchanged conformance-golden checks pass.

This is bounded compiler evidence, not complete SDK, OC-10 or Foundry acceptance.
The retained OC-10 parser improves, but its combined and 64 MiB encoder cases
still fail the Wasm memory bound; source writer fusion is a separate correction.
