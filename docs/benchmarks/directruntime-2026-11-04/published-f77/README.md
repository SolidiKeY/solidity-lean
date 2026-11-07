# Published f77 adoption and fresh backend inventory

Adopted exact published master `f77cf60d3cea8f7f1db8db29cc027532b0cd3fce`
with merge `506cf233088472d61bd380d846ad469d39fe67c5`, preserving the owned
branch and original base `b419c3cf4f642ae519b66bebc26cdf2f7cf93574`.
Both ancestry checks pass. Repository: `/workspace/solidity-lean`.

Publication changed the PrintStmt dependency among the 336 source records in
each old runtime manifest. Old artifacts could not establish current freshness.
Both outputs were freshly rebuilt into previously absent f77 output directories.
The resulting native executable and WASM are byte-identical to the hardened
artifacts, with new manifests pinning current source. This proves neither shared
translator integration nor source adequacy.

The new Shared.Intrinsic API supplies a relative obligation builder with explicit
BodyLoopLowerer and PlainEntryPre callbacks, refusing plain returns and reference
parameters. DirectRuntime still uses its existing private builder. Neither it nor
ReadBounds changed in this publication. H40 assigns the stack repair to lane A;
D changed no Lean source, source premise, budget or unsupported observation.

## Actual VM checks

Every `*-gate.json` records its exact command, exit, wall time, sampled process
RSS, scope and minimum outer headroom. Docker scopes were exactly 12 GiB with
zero swap, one CPU, LEAN_NUM_THREADS=1 and serial Lean -j1. The 4 GiB reserve
remained enforced. No systemd scope or swap exception was used.

- Native build PASS: 403.901 s, sampled RSS 1,801,474,048 B, min headroom
  6,681,100,288 B. Includes invalidated Lean dependencies, new shared Intrinsic
  target and 200 fresh C/object builds plus link.
- WASM build PASS: 263.320 s, sampled RSS 1,430,298,624 B, min headroom
  8,309,321,728 B. All 200 C modules freshly compiled with pinned SDK/runtime.
- Native AST, source LSP and real Chromium benchmarks each PASS 249/249:
  83 functions, three rounds, fresh compiler requests and complete denominators.
  Source/AST/compiler/request identities are retained in inputs and control files.
- Native existing controls PASS 14/14; closure/provenance unit checks PASS.
- Native fresh audit PASS 249 replies, no observed .olean/.ilean or Lean/Lake
  subprocess loads; allocated sections and load layout exactly match the
  independently classified baseline. This is artifact-specific external evidence,
  not a universal purity or semantic-equivalence theorem.
- Browser existing controls FAIL: 13/14 verdicts, seven request groups;
  invariantCountsToBound raises `Maximum call stack size exceeded`. Its exact
  source, AST, serialized request SHA and error stack remain recorded. No
  exception-to-success conversion, stack flag or fuel/budget change was made.
- C fixture: freshly compiled exact 13-control source, all unsupported on both
  fresh backends. Separate additionSimple guard proves on both; 14 actual requests
  per backend, fresh worker boot and source/request/binary pins. This is an
  inventory pass only; semanticAcceptanceComplete and identityNonVacuityComplete
  remain false. The guard is not the required allocation Identity twin.
- Offline/spec/stale/edit/unsupported browser controls PASS. Ordinary requests
  use compiled native/WASM backends; no serialized environment/kernel worker
  assets are observed. Optional certification stays separate.
- Per-file repository Lean MCP diagnostics: KeySort, DirectRuntime and
  Shared.Intrinsic all zero errors. No reviewer used the Lean server.
- Actual versions: Lean 4.24.0 commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b;
  Lake 5.0.0-src+797c613. Frozen KeySort PASS: parsed 377 taclets,
  131 read-bearing, table covers 131; annotations match the pinned rules.
- Worker axiom inventory: zero new/changed Lean declarations or theorem targets;
  therefore no new #print axioms commands. Producer changes remain separate.

performance-summary.json uses median and nearest-rank p95 of 83 per-function
medians. Native AST median/p95 0.793/3.803 ms; source LSP 59.032/74.594 ms;
browser 188.265/238.798 ms. All recorded latency/startup comparisons stay below
the unchanged 10% slowdown stop threshold. Startup is one fresh process/page
observation, not machine-cold. The native whole build includes invalidated Lean
work, unlike the earlier warm-Lean cold-C experiment; they are not matched build
measurements. The original failed cold-native before attempt is not repaired
retroactively. No post-translator integration comparison is claimed.

browser-binary-binding.json checks the recorded benchmark runtime.build, actual
embedded WASM bytes, package manifest and companion worker boot against the new
WASM digest. This closes the unchanged benchmark harness's lack of a direct
expected-digest assertion without editing that harness. Source/binary manifests
are copied here; absolute live binaries remain under .lake/native-browser-f77.

## Cache and handoff boundary

H41's old H35 artifact-cache pack remains coordinator-confirmed received and
unchanged (sha 3f2fb9f6a585b6a64f386b6e127b972a84fd7149ca914a29a191afac97d95dbb).
No ship-cache.sh was invoked. A new scoped relative **build-cache snapshot** is
prepared at `/workspace/solidity-lean/.lake/native-browser-f77-cache/build-cache.tar.zst`,
sha d1a73712eb4ce60a151a58418d3df1bd3e9d230a3a01ce40c2b4f1f83943d31d.
All 2,359 files for 337 gated source modules were streamed and independently
verified, with source/module/artifact manifest beside the archive. This is not
a Lake artifact-cache catalog/delta; coordinator retrieval/adoption is pending.
It is never an ordinary runtime request input. Publication does not establish
incoming H21 cache freshness or adoption.

## Outstanding queue

1. Original fresh before benchmark exists, but browser control completion remains
   failed and initial full cold-native wall/RSS was not captured successfully.
2. Shared consumer integration, source/input adequacy and H40 traversal repair
   remain lane A dependencies. No parallel translator or unowned bridge edit.
3. Exact B allocation Identity DIAMOND twin and false/default-init/alias/zero/OOB
   controls in both modalities remain unaccepted; no scalar Identity substitute.
   C controls remain unsupported, not proved merely by admission success.
4. Fresh matched post-A integration measurements, complete mandatory controls,
   final exact-head full/corpus gates and final owner-integrated acceptance remain
   pending. Prior h40 full/corpus resource failures are preserved, not rerun as
   fake passes or attributed to this exact source head. RUNTIME_GATE_PASS pending.

Independent finder/skeptic review results are in reviews.json. Gate commands and
failures are indexed in gates.json. No whole-lane completion is claimed.
