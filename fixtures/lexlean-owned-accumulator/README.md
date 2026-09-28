# Owned accumulator compiler fixture

Actual LexLean source; generated Lean and runtime artifacts must not be edited.
The byte entry reverses complete 256 KiB chunks, up to an exact 64 MiB input
and output. Other lengths return `ff`. Public list slices retain their ABI.
This fixture is a compiler regression, not Foundry or SDK acceptance.
