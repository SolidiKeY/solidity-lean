# H55 proof guards: preliminary inventory

Status: partial. The coordinator's lease correction makes the listed source files inputs only until current owners transfer exact paths. No source migration is included. The three queue items and scope-complete acceptance remain outstanding.

`scripts/h55/proof-guards/census.py` emits a preliminary, single-line lexical inventory of tracked Lean files, with line text, file SHA-256, HEAD, and tracked working-tree status. At base 4d3790eadb8a5212233bc7d5e345817476b2f590 it found 637 matching lines in 197 files. This is not a count of no-op guards: it misses multiline guards, counts lines rather than occurrences, and can include comments, strings, nonterminal skips and effective closers. Do not use it to justify deletion. Full census, semantic classification, ownership routing, mechanical patches and real Lean checks are pending.

Evidence stored off Git in `/workspace/h55-proof-guards-evidence/` per bulk policy:

- `census.json` SHA-256 `75e6808b0e00f576476aaa35cd21ce33c2af6109d3d63549067f093d629d12b8`.
- `keysort.log` SHA-256 `81b5374a30d80c662ee32d4fccc441cad7c0007ece79b355153828ffdc4e7f3a`: `LEAN_NUM_THREADS=1 lean -j1 Solidity/KeySort.lean` passed, 1.881 seconds wall. Lean 4.24.0 (797c613eb9b6d4ec95db23e3e00af9ac6657f24b); Lake 5.0.0-src+797c613. This is a prerequisite only, not an affected-module proof or runtime gate.

Independent finder and skeptic reviews were read-only and used no Lean server. Both found the lexical coverage limits above and noted that HEAD alone does not describe dirty source files; the script now records tracked status as well as per-file hashes. No candidate was proven safe to remove. Python syntax compilation passed. Speed history inspected includes fcd5ba31b and 2ff6a0f3e; no before/after migration measurement has been made.

The first creation of the standalone census script occurred before acquiring the required writer lock; subsequent modification, checking and commit use the lock. No existing source was edited. Future writes and Lean checks must acquire the lock first.
