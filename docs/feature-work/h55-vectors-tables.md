# H55 vectors and tables: inventory preparation

Base: `4d3790eadb8a5212233bc7d5e345817476b2f590`. The 2026-11-02
coordination correction makes existing producer and consumer files read-only
migration inputs until an explicit owner handoff transfers the exact files.
This preparation changes no such input.

`python3 scripts/h55/vectors-tables/vector_census.py` checks the complete bytes,
count and sequential declaration names of nine frozen vector modules against
`tests/h55/vectors-tables/vector-manifest.json`. It reports 6,903 declarations.
The nine SHA-256 values were independently compared with the corresponding Git
blobs at the stated base. The manifest contains hashes and metadata, not bulk
vector data. `python3 -m unittest discover -s tests/h55/vectors-tables -p
"test_*.py" -v` passes missing, extra, order, schema and altered-output negative
controls as well as the full inventory check.

This is an integrity census, not the requested generator, an independent EVM
oracle, or a Lean proof. Source equality alone proves no opcode semantics.
The full generator, deterministic reproduction, lossless generation, compile,
Raw family case accounting and validation, table migration patches, timings,
KeySort and full affected-module gates remain outstanding. A filename census
finds 102 tracked `Solidity/Yul/Raw*.lean` files; that is not case accounting.
The independent finder and skeptic reviews remain outstanding. No runtime
pass is claimed. Lean 4.24.0 (797c613), Lake 5.0.0-src+797c613 were observed.
No cache pack or full export has yet been created. The H58 hold remains in force.
