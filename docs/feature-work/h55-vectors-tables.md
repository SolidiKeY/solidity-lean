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

## Additive codec preparation

`vector_codec.py extract /workspace/scratch/h55-vectors-tables/vectors.json`
extracts structured rows from the authenticated frozen files, and `check` renders
all rows and compares each complete output file byte-for-byte with its input.
A second independent invocation produced identical data bytes. The off-Git bulk
file is `/workspace/scratch/h55-vectors-tables/vectors.json`; its SHA-256 is
committed in `tests/h55/vectors-tables/bulk.sha256`. The four Python tests pass,
including per-file missing, extra, reordered, malformed schema and changed-output
controls. The extracted expected results are transcribed from the originals;
this neither validates the arithmetic oracle nor substitutes for kernel checks.
The codec is preparation, not acceptance of the full requested generator.

A KeySort prerequisite check ran with `LEAN_NUM_THREADS=1`, Lean `-j1`,
`--tstack=131072`, the repository writer lock and a preflight 4 GiB available
memory guard. It exited 0 in 1.634 seconds with no diagnostic output; log:
`/workspace/scratch/h55-vectors-tables/keysort.log`. An initial attempt did not
run Lean because `/usr/bin/time` was absent; the successful retry used the shell
timer. No whole-task runtime gate, compile, speed comparison or review is claimed.
