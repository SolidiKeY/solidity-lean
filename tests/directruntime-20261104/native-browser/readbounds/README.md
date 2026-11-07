# Exact ReadBounds6513 consumer qualification

Fresh source build: `bd93d05fbb0b3c0eaa72f9129b27c4131f1ed650`, rebased onto the
master recorded in results-manifest.json. The exact reviewed producer repair is
6513fcbde2f10ded8b428e3ede8e87b5bbf7c68b. The native and WASM build manifests bind
344 source modules; the selected executable closure has 207 modules,9969 functions
and5003closed values. All207 compiled C bodies are retained off Git with hashes.

The earlier aggregate 300 second DirectRuntime rebuild remains a failed gate.
The reviewed dependency-first helper subsequently completed 344 target invocations
in 226.16 seconds, with each target capped at300 seconds (largest 19.58 seconds).
This corrects a timer boundary; it neither raises proof budgets nor replays an
unchanged performance STOP. It is not a cold-build comparison or H127 acceptance.

Fresh native build: 31.42 seconds; fresh WASM build: 273.54 seconds. Provenance-checked
object candidates were allowed, so these are not matched cold measurements.
The actual pinned SDK config remains mandatory. No benchmark STOP is cleared.
The initial browser launcher configuration failure is retained alongside the
successful launch using the installed Chromium binary.

Both backends completed all 83 functions in one functional-only round. The exact
original 84 request memory journal yields 64 proved,16 refuted,4 pending on each.
Required positive diamond Identity and its paired controls pass; four storage
alias/copy diamond cases remain pending. Environment/address/fixed-byte and
primitive-return suites retain their expected refusals. Native negatives pass 14/14.

**Browser negatives FAIL 13/14.** invariantCountsToBound still raises a stack
error. Its fresh trace repeats index 2388. A diagnostic-only symbol-map relink
produces a byte-identical WASM binary and identifies
`l_Solidity_Decide_BEnv_set___redArg` (DecideScoped). No failed request was replayed
for that diagnosis. This identifies a routine, not sole causality. No continuation
classifier masks this failure, and RUNTIME_GATE_PASS remains pending.

Post-rebase repair builds, four MCP diagnostics, exact-fuel/deep occurrence
controls, four old/new equality axiom signatures and KeySort pass. The signatures
use only propext and Quot.sound. These kernel equalities do not prove source,
compiler, ABI or native correctness. Finite native/browser observations, selected
C/object closure auditing and request-specific no-frontend-load traces remain
external evidence. Optional certificates remain separate.

The wrapper index binds exact executed private wrappers to reviewable repository
copies in scripts/. Bulk evidence, actual runtimes, selected C and cache packs
remain on this VM; manifest paths/hashes support coordinator pull. No ship-cache,
model push, PR or deployment is performed. H127's authenticated slow runner,
sealed inputs/cache A/B, lifecycle cleanup, complete measurement provenance,
five-module A/B and pin-relocation quiet window remain unfinished.

The subsequent ordinary editor smoke also passes stale-result clearing, false
assertions, direct counterexample certificate separation, branch controls and
disconnected fresh edits. Builder provenance and closure regressions pass. These
are functional observations, not startup or throughput STOP clearance.

The latest master rebase changes only unrelated CheckedMul controls; all 344
runtime source hashes still match the tested build. The exact tested Git source
is retained in source-build.bundle with its actual prerequisites recorded.
The existing WASM toolchain source has 15 tracked changes; its patch is retained
as a post-qualification observation. Git HEAD alone is not pristine-source or
source-to-library attestation. Runtime library hashes match the earlier build.

VX1 retains sole ownership of both OpenLoops proof modules. Current bytes equal
its observed published head, and the separate registration-only patch excludes
both files. Master currently lacks RowsNine.lean. Owner acknowledgement and
owner-first integration are needed before rebasing removes the copied dependency;
no next push is authorized by this handoff.
