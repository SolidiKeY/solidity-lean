# Published 9584 adoption and producer API validation

Published master `9584f9e7df09f638d9e0cb8930501d1660aa4b2f` was fetched and
remote ancestry verified, then merged without discarding work as
`845abab89073eb11fe2b154b89686940d4f8706a`. The original assigned branch/base
are preserved. This is partial producer delivery, not whole-lane completion.

## Actual local checks

`api-gate.json`: PASS, 267 build jobs, 23.983 s, sampled process RSS
1,356,324,864 B, minimum raw outer headroom 7,252,631,552 B. Targets:
Solidity.Frontend.ExecutableAst.Shared.Scope and
Solidity.Frontend.ExecutableAst.ControlTuple.IntrinsicControls. Actual signatures
and #print axioms for all 17 adopted producer theorems are saved in
producer-signatures-axioms.log.gz. The audit found only existing standard
propext/Classical.choice/Quot.sound axioms, with no new axiom or sorryAx.
D changed no Lean declaration or theorem. The temporary audit input is a build
artifact, not a registered source module or an ordinary request input.

`mcp-gate.json`: PASS, two per-file repository MCP diagnostics, zero errors,
22.195 s, sampled RSS 2,175,803,392 B, minimum headroom 5,322,981,376 B.
All heavy work was serial with LEAN_NUM_THREADS=1 and Lean -j1, in exact
12 GiB/zero-swap Docker scopes with the unchanged 4 GiB outer reserve.

`C-controls-gate.json`: inventory PASS, fresh compiler source/AST/request hashes,
14 native and 14 real Chromium requests. The independent additionSimple guard
proves on both; all 13 exact C fixture functions remain unsupported on both.
No cached verdicts are used. semanticAcceptanceComplete and
identityNonVacuityComplete remain false. Native syscall traces and browser worker
boot/asset observations show no ordinary environment loads or kernel worker.
This is external execution evidence, not a universal no-load theorem.

The f77 binaries were deliberately reused, not rebuilt or claimed as fresh 9584
builds. runtime-revalidation.json checks all 336 current source pins and every
selected build input in each manifest, bridge/closure and actual executable/WASM
hashes. WASM SDK paths are resolved through the exact original bind-mount aliases;
an initial host probe lacked /emsdk, so no build-input PASS was claimed until
those aliases were checked. No pin was skipped. New producer modules are not
runtime dependencies; DirectRuntime, actual Calculus.ReadBounds/QueryReadBounds,
the native/WASM bridge and C source fixture are byte-identical to f77.

`validation-gate.json`: PASS, owned Python/Bash/Node syntax and closure/provenance
checks. Actual Lean 4.24.0 commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b;
Lake 5.0.0-src+797c613. Frozen KeySort PASS: parsed 377 taclets,
131 read-bearing, table covers 131, annotations match the pinned rule file.
RUNTIME_GATE_PASS remains pending; these checks alone do not establish it.

## Proof and runtime boundaries

Scope supplies seed/name-validation helpers. Three bounds theorems do not prove
validator correctness, lexical/source preservation or shared translator adequacy.
The 14 intrinsic controls prove or refute hand-built model programs, including
Box/Diamond controls. They do not certify the exact compiler AST or native/WASM
runtime requests. The runtime still uses its private obligation builder; the
shared callback-relative API remains unwired, and plain return/reference input
refusals remain unchanged.

No lane A traversal repair or exact B allocation Identity source is delivered.
The previous fresh f77 browser failure (13/14 verdicts, invariantCountsToBound
stack overflow) remains evidence for the identical binary. It was not rerun or
relabeled as a fresh 9584 stack test. Existing benchmark and failure receipts
remain immutable; no new 83-function results or post-A comparison are claimed.
Mandatory positive DIAMOND allocation Identity plus false/default-init/alias/
zero-length/OOB controls remain unaccepted on both backends. A scalar guard and
C model Diamond proofs are not substitutes. No callback implementation, premise,
exclusion, refusal, proof budget, protected Source or frozen ExtCall was changed.

## Cache and queue

The two gated API modules' 14 build artifacts were packed and independently
stream-verified at
`/workspace/solidity-lean/.lake/native-browser-9584-api-cache/build-cache.tar.zst`.
SHA256: `7de5d786716f556b829af405d8d2a6b7b2b48becf0b2927ae061f9f76f5ff2d6`.
This is a scoped relative build-cache snapshot, not a Lake artifact-cache catalog
or a full dependency pack. Its manifest identifies exact source/artifact hashes;
retrieval/adoption remains coordinator-pending. H41: no VM ship-cache.sh call.
The earlier H35 pack is coordinator-received; the f77 snapshot remains pending.
Incoming coordinator cache shipment is not inferred fresh from publication.

Original queue remains open: before-control failure/cold-build measurement gap;
A integration/stack repair; B Identity and C semantic acceptance; matched post-A
83-function rounds and final exact-head full/corpus gates. Prior h40 resource
failures are preserved and are not current-head passes. No whole-lane completion
or RUNTIME_GATE_PASS is claimed. Finder/skeptic reviews are read-only and use no
Lean server; final review details are recorded in reviews.json.
