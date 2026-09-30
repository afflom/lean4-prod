# Shared conditional fixture

`src/Main.lex.tex` defines repeated Boolean conditions in a three-field record.
LexLean generates `lean/Conformance/LexLeanSharedDecidable.lean`; do not edit the
generated module or build files. The fixture receipt records its compiler image,
binary, source and complete generated-output closure.

`just shared-decidable` exports the actual source-generated module twice, checks
proof-erasure refusal cases, compiles and executes native/no_std and bounded
import-free Wasm, and compares deterministic output. This compiler regression
does not establish application or SDK-release acceptance.
