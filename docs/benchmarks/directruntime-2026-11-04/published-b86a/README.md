# Published b86a adoption and composed-reader admission inventory

Fetched exact master `b86ae4568cef6d6226f4d170360bbb089debe3fb`, verified remote
and original-base ancestry, then merged as
`10a2291320c930f644587f828ff45be9a082f675` without discarding lane work.
Published integration receipt `sched-20261105T1200Z` is coordinator-attested;
its full/Bridge gates are not claimed as new VM consumer gates.

## Local gates and observations

- Composition build PASS: 21 jobs, 2.016 s, sampled RSS 634,511,360 B,
  minimum raw outer headroom 8,482,160,640 B. The exact committed
  Shared.Compose module is used; no producer or DirectRuntime source is edited.
- Actual #check/#print axioms cover executableExpression, executableStatements
  and executableReader. The expression/statement definitions depend on no axioms;
  reader reports existing propext only. No new theorem, axiom or sorry is added.
- A build-time test calls published Shared.function/executableReader on the
  freshly compiled exact C fixture: 13 public functions, 9 translated, 4 refused.
  Refusals: aliased (String expected), sideEffect (unary operator), inlineArray
  (unsupported uint8), callTuple (expected explicit tuple). These are recorded
  observations, not an enforced complete expected-admission regression oracle.
- Root storage validation succeeds separately. Shared.contract returns validated
  roots and does not populate translated function bodies. Neither result certifies
  compiler/source adequacy, intrinsic proof or runtime support. The test artifact
  adds only IO/error handling around the committed reader, not a translator.
- Fresh real native/Chromium C requests: 14/backend, independent additionSimple
  guard proved, all 13 C controls unsupported. Current source/AST/compiler/wire
  hashes and actual backend identities are retained; no cached verdicts are used.
  Native traces/browser assets show no ordinary environment loads/kernel worker.
- Per-file repository MCP check of Compose: zero errors, 3.778 s, sampled RSS
  998,830,080 B, minimum headroom 8,033,566,720 B.
- Metadata gate asserts the exact three qualified definition targets and current
  fixture names/hashes, and checks all 336 source AND generated C hashes in both
  runtime manifests plus 60 native/308 WASM build-input pins and binary hashes.
  Original WASM bind-mount aliases are explicit. The f77 fresh-built binaries are
  reused, not new b86a builds. DirectRuntime, Calculus.ReadBounds/QueryReadBounds,
  bridge and C Solidity fixture remain byte-identical to f77.
- Final Python/Bash/Node syntax, closure/provenance checks and frozen KeySort PASS.
  Actual Lean 4.24.0 commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b;
  Lake 5.0.0-src+797c613. KeySort: parsed 377 taclets, 131 read-bearing,
  table covers 131, annotations match the pinned rules.

Every bounded command receipt records exact command, exit, wall time, sampled
RSS and headroom. Heavy work is serial with LEAN_NUM_THREADS=1/Lean -j1 in exact
12 GiB/zero-swap scopes, preserving the unchanged 4 GiB outer reserve.
Build-time #eval/Lean dependency inspection is separate from ordinary compiled
native/WASM requests; it is not a kernel-backed runtime fallback or certificate.

## Harness lineage and review

Finder and skeptic found no confirmed defect. A minor target-check robustness
suggestion was applied: the final wrapper asserts the exact qualified definition
set rather than only count. The originally executed wrapper is archived in
api-executed-wrapper-v1.sh.gz with its SHA; no execution is silently attributed
to changed source. The stronger check passed independently in metadata-gate.json
against the original log. The original build/admission results remain immutable.
The generated build-time test source is archived as admission-test-input.lean.gz;
its SHA matches producer-inventory.json. No new registered Lean source module or
worker theorem is introduced. Final review details are in reviews.json.

## Cache and unfinished queue

One gated Compose module's seven build artifacts were packed and independently
stream-verified at
`/workspace/solidity-lean/.lake/native-browser-b86a-api-cache/build-cache.tar.zst`,
SHA256 `a9b660360b0ea1dff1c806e6f48822adac16fd343ade4802796747320c36006e`.
This is a relative build-cache snapshot, not a Lake artifact catalog or full
dependency pack; coordinator retrieval/adoption is pending under H41. No VM
ship-cache.sh invocation occurred. Earlier received/pending packs keep their
previous receipt statuses; incoming master cache freshness is not inferred.

The committed composition is still unconsumed by private DirectRuntime. H40 lane
A stack repair and runtime consumer migration remain pending. The identical f77
binary's earlier browser stack failure (13/14 verdicts) remains artifact-specific
historical evidence, not a new b86a stack retest. No new 83-function benchmark,
binary build or post-A comparison is claimed this turn.

Exact B allocation/write/read/assert Identity DIAMOND twin and false/default-init/
alias/zero-length/OOB controls remain unaccepted on both backends. Reader admission,
C model Diamond proofs and the scalar harness guard are not substitutes. C semantic
support, original cold-before measurement gap, matched post-A three-round metrics,
final exact-head full/corpus gates and RUNTIME_GATE_PASS remain incomplete. Prior
resource/browser failures are preserved. No whole-lane completion, statement,
premise, exclusion, refusal, budget or trust-policy change is claimed.
