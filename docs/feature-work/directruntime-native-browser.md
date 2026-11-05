# Native/browser lane — blocked integration, reviewed builder hardening

Batch `solidity-directruntime-20261104`, branch
`codex/solidity-directruntime-20261104/native-browser`, repository
`/workspace/solidity-lean`. Original base:
`b419c3cf4f642ae519b66bebc26cdf2f7cf93574`.
The generated absolute VM handoff records the final full committed head.
**Incomplete; no RUNTIME_GATE_PASS.** No push, PR or default-branch merge.

## Published delivery and ownership

Fetched and verified origin/master at
`89373e34cdfd6bb5db7054b1c204d01edffc5fa7`; the original base is its ancestor.
Merged that explicitly delivered coordinator commit into the owned branch without
resetting either history. The shared Boundary/Translate APIs are present. Their
published receipt names producer `fcdddfcc446b5004860875f772ff6033e60c745f` and
explicitly leaves producer migration/parity incomplete. DirectRuntime is unchanged.
No duplicate translator, producer migration or unowned loader edit was introduced.

Worker changes relative to that delivery contain no Lean source edits: theorem and
axiom signatures, proof budgets, premises and exclusions are unchanged by D.
Published producer changes and their coordinator gate receipt are separate from
this worker's evidence. No new worker Lean module or registration row is needed.
The earlier setup/checkpoint-validation.json is a historical pre-delivery receipt,
not a claim that the subsequent coordinator merge contains no Lean changes.

## Queue accounting

| Item | State |
|---|---|
| 1. Fresh before83-function baseline | All three matrices recorded; original before cold-build timing remains incomplete; separate empty-output build now recorded. |
| 2. Closure/bridge and A integration | Owned hardening implemented and freshly built; shared APIs delivered, runtime migration and unowned loader handoff pending. |
| 3. Fresh producer and existing controls | Existing native14/14; browser13/14 plus one backend error. B/C and exact Identity diamond twin still missing. |
| 4. Matched after/final gates | Hardening AST/browser comparison recorded; post-A native LSP/producer matrices and final gates pending. |

## Measurements and exact artifacts

Evidence root: `docs/benchmarks/directruntime-2026-11-04/`.
Before evidence is immutable. Hardening candidates are a separate comparison,
not a completed post-translator result. Medians are medians of83 per-function
medians over3 rounds; p95 uses nearest rank. No cached verdict counts.

| Boundary | Before median / p95 ms | Hardening median / p95 ms | Requests each |
|---|---|---|---|
| Native precompiled AST | 0.838905 / 4.069482 | 0.839166 / 4.016354 | 249/249 |
| Real Chromium source-to-result | 185.922378 / 224.386924 | 184.344599 / 228.494508 | 249/249 |

Native AST excludes Solidity compilation; all83 hardening sources/ASTs were newly
compiled and pinned. Browser submissions are live source edits with fresh compiler
requests. Native LSP before was249/249 (median62.251926 ms, p9575.866278 ms,
initialization127.573555 ms); its post-integration counterpart remains pending.

Native AST median changed+0.0311%; browser median−0.85%, p95+1.83%.
Single native process-ready startup rose7.561709→9.873351 ms (+30.57%). Work paused
for investigation:20 alternating fresh-process pairs gave2.381416→2.477630 ms
median (+4.04%), p954.305062→3.217978 ms. These are warm-filesystem process-startup
measurements, not machine-cold results. The original >10% observation is retained;
there is no blanket cold-start PASS. Browser startup3428.200938→3350.047615 ms.

Native candidate:20,738,864 bytes, SHA-256
`e2db9f182d5194aa71a17c7cd2806839bb5fe23dd39abd0064b86d8bc750799d`.
WASM candidate:16,378,154 bytes, SHA-256
`4a5a55fef0cebd89fb85eb7ada60d4479bd6674656678b334fd28ea250328bef`.
Paths: `.lake/native-browser-hardening/native/direct-check` and
`.lake/native-browser-hardening/direct/direct.wasm`.
The complete WASM and all200 module records equal the before artifact exactly.
Manifests, JavaScript/package identities and equivalence receipts are in hardening/.
The old HTML is preserved under `.lake/native-browser-before-package/`.

## Implemented owned hardening

- Missing generated `l_`/`_init_l_` archive callback roots fail closed; iterator inputs
  are materialized once. Other ABI roots still require linker validation.
- Native cache keys pin the selected compiler/header/static-runtime inputs. Builders
  reject inherited compiler/root/include/library overrides that bypass that identity.
- Both builders execute captured closure/bridge bytes, pin initial selected file sets,
  and reject final source/provenance changes. WASM link outputs stay private until
  checks pass; the manifest is published last.
- Effective Emscripten LLVM/Binaryen/node tools, explicit canonical EM_CONFIG, Python
  interpreter and driver sources are pinned. The pinned Python entry is emcc.py,
  invoked with-E, matching the SDK shell wrapper. The config probe also uses-E.
- `DIRECT_RUNTIME_FULL=1` is rejected by the ordinary builder. Optional certification
  remains separate; unowned ordinary loaders still need their coordinated safeguards.
- WASM extraction now runs in a serial child using captured helper bytes and JSON
  roots/pruned C. The child exits before compilation. This is build data, not a Lean
  serialized environment shipped or loaded on ordinary requests.

Selected-tool provenance is not a universal hermetic-compiler proof. Native leanc
still names broad archives; exact emitted code and runtime behavior are audited
separately. No bridge/runtime semantics or generated C bytes changed in this checkpoint.

## Gates, resources and retained failures

All commands/exits/wall/RSS/headroom receipts are indexed by setup/gate-ledger.json.
Raw logs/text/traces are byte-preserving `.gz` captures, with original/archive SHA-256
in raw-captures.json. Restore/verify with
`python3 tests/directruntime-20261104/native-browser/restore-raw-evidence.py`.
No prior failure or completed verdict was overwritten.

Each bounded gate verifies12 GiB memory.max, zero memory.swap.max, LEAN_NUM_THREADS=1,
serial Lean-j1 config, and the unchanged4 GiB outer raw headroom reserve.
The outer16 GiB/max-swap scope alone is insufficient; host swap reports zero.
Cache preparation uses read-only descriptors and clean-page advice on private/public
SDK/source/build files, without deletion, global cache dropping or threshold changes.

Actual toolchain output in hardening/validation.log:
`Lean (version 4.24.0, x86_64-unknown-linux-gnu, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release)`;
`Lake version 5.0.0-src+797c613 (Lean version 4.24.0)`.
Node24.19.0, Chromium154.0.8037.57, Emscripten4.0.15.

- Native build first stopped at the reserve after158.411697 s. Successful retry:
  225.842830 s, sampled process RSS1,751,130,112 bytes, minimum headroom4,385,718,272.
  It reused completed objects and is not a complete successful cold-build timing.
  A subsequent enforced-empty-output native build passed288.991666 s, RSS1,735,020,544,
  minimum headroom4,707,598,336; all200 native objects and link were fresh. Lean
  dependencies were warm (337-job target replay), not a fully cold Lean rebuild.
  cold-native/command-context.json records the exact output/empty-check environment
  selectors. Its binary exactly matches the audited candidate;249 fresh requests,14 controls
  and18 tests passed again (median0.819917 ms, p953.760364 ms, startup6.557948 ms).
- WASM setup errors (missing explicit config and mistaken shell-entry invocation)
  and subsequent reserve stops remain recorded. GC alone did not resolve pressure.
  Final isolated-extraction build passed259.666026 s, sampled process RSS1,469,034,496,
  minimum headroom5,074,190,336. All200 extracted module records match before.
- Fresh native249 matrix and14 controls passed. Eight provenance mutation/boundary
  tests plus ten closure tests passed in hardening/validation-gate.json.
- Fresh browser249 matrix, offline fresh-worker/spec smoke, edit/staleness and
  unsupported-calldata controls passed. Cached retrieval checks are behavior controls,
  never counted as fresh throughput or Identity non-vacuity evidence.
- Actual frozen sort checker passed again: `parsed 377 taclets, 131 read-bearing,
  table covers 131`; `OK — annotations match` the pinned solidityProgramRules.key.
- Earlier DirectRuntime MCP checks stopped at the reserve twice; no successful
  DirectRuntime MCP or final run-lean/TestSuite/full-policy gate is claimed here.

## Ordinary runtime boundary and required failure

The fresh native audit completed249/249 actual replies, with no observed .olean/.ilean
loads or Lean/Lake subprocesses. Its29 allocated sections, entry and program-header
layout equal the independently classified before binary. Original coarse audit failure
(three frontend-named pure helper/init stubs) remains immutable. The separately named
native-audit-bound receipt explicitly binds successful structural classification to the
baseline binary and coarse-receipt hashes. This is artifact-specific external evidence,
not a general purity or semantic-equivalence theorem or namespace exemption.

Browser wire evidence pins fresh source/compiler/AST, serialized request bytes, actual
WASM imports/exports and embedded assets. No forbidden environment/kernel assets were
requested; compiledOnly is true and kernelBuild is null. Wrapper-assigned sourceHash or
zero-import metadata alone is not proof; the binary does not attest source hashes.

The fresh complete browser control diagnostic attempted7 groups/14 expected rows.
Thirteen rows returned expected verdicts; invariantCountsToBound threw
`RangeError: Maximum call stack size exceeded`. Its source and serialized request
hash match the earlier failed control and the fresh native pending result. The actual
worker error is not pending, unsupported, refuted or a passed negative control.
The initial compiler-path setup failure is separate and preserved.

The byte-identical diagnostic symbol map identifies LTm.fitsM/LFml.fitsM traversal
activations in ReadBounds; hardening/browser-stack-handoff.json records exact frames.
This does not prove a sole initiating phase or a repair. No Chrome stack override,
fuel/budget change, catch-to-pass, control exclusion or kernel fallback was used.
ReadBounds/DirectRuntime/translator are outside D's write ownership.

## Reviews, questions and remaining work

Independent read-only finder and skeptic, neither using Lean server, reviewed the
closure, provenance, config/tool selection, process isolation and observed metrics.
Confirmed findings were fixed, including iterator exhaustion and explicit classification
receipt linkage. setup/reviews.json records their results. Full acceptance is withheld.

Self-contained Q-PRODUCERS and Q-BROWSER-STACK, with mutually exclusive options, are in
setup/producer-handoff.json. Shared APIs are now delivered, but A's committed runtime
migration, B/C controls and the owner repair for the required stack failure remain
pending. The unowned build launcher needs explicit EM_CONFIG; loader/package/desktop
freshness/full-mode defenses require coordinated handoff, not silent D edits.

Still required: the exact positive Identity diamond twin and false/default/alias/zero/OOB
controls on both fresh backends; C controls; producer migration/parity; remaining cold-start/build comparison limits; matched post-integration native LSP/browser performance; successful
per-file/final policy gates; final independent reviews and owner-integrated merge handoff.
These blocked gates do not imply all future independent work is exhausted.

## H35 VM validation and cache transport

H35 was applied on this same VM at source head
`65e23115fe6c3c5c78aa632f319091b63301fb6f`.
The actual runtime target built successfully with the serial configuration's
`-j1`; all 249 fresh native requests, 14 controls and 18 tests passed again.
The worker has no Lean changes relative to the delivered coordinator commit,
including no uncommitted or untracked Lean files. Therefore there are zero new
or changed worker theorems and no applicable `#print axioms` targets; this is
an explicit inventory, not a claim about producer proof closure. The initial
inventory setup assertion failed before checking any modules and is preserved;
the corrected full gate and strengthened working-tree inventory passed.

The actual `ship-cache.sh` call used its supported non-master-head override and
the VM's real Lake cache. It prepared 1,673 artifacts / 559 mappings (three
uncached traces skipped), then exited 1 because coordinator routing state
`/home/ubuntu/.local/state/cloudvm-coord/poll-state.json` is absent. No receiver
was contacted and no successful shipment receipt or shipped marker exists.
The script is documented as coordinator-to-lanes and its VMEXEC/catalog/state
configuration is not available here. No empty lane list or invented receiver
was supplied to obtain a vacuous success.

The 539,036,429-byte pack remains at
`.lake/native-browser-h35-cache-ship/20261104T222539Z-65e23115/pack-afaaecf77f0a6f11.tar.zst`,
SHA-256 `3f2fb9f6a585b6a64f386b6e127b972a84fd7149ca914a29a191afac97d95dbb`.
A separate bounded streaming check verified every archive member against the
manifest and all mapping references, without loading Lean environments.
`h35/cache-shipment-receipt.json` records the failed transport and local
verification separately; it is not a remote cache success receipt.

Under H35, unshipped checkpoints remain **partial**, despite passing VM gates;
earlier completed implementation/build labels do not establish merge readiness.
Q-H35-CACHE asks for either worker-accessible routing to rerun the script, or
coordinator retrieval/verification and a real cache receipt. All previous
producer, Identity, browser-stack and final-gate obligations remain unchanged.

## H40: assigned repair and coordinator-pending cache

The user's 2026-11-05 H40 decision assigns the browser traversal repair to
runtime owner lane A. Budgets remain unchanged. This lane waits for the
committed repair, then rebuilds and retests both backends; no bridge workaround,
stack-size override, exclusion or catch-to-pass is authorized. Q-BROWSER-STACK
is resolved as an ownership decision, not as a repaired backend.

H35 delivery is now **coordinator-pending**. The verified prepared pack and its
historical failed worker transport receipt remain intact. No remote cache
receipt has arrived and delivery is not marked successful. Q-H35-CACHE is closed
by that assignment; no additional routing decision is requested from the user.

An independent per-file Lean MCP retry now passed: KeySort and DirectRuntime
both reported zero errors. The same12GiB/no-swap scope and4GiB reserve remained
active. The full policy attempt subsequently stopped at the unchanged reserve
before run-lean completed (872.77s, sampled process RSS4.94GB). This is a failed
resource gate, not a source theorem failure or a full PASS. Earlier failures
remain preserved. Separate independent policy controls are recorded when run.

First fresh origin/master was `1d14f57a3a048bb1c1969c4c2c958d010ab84cb5`;
a final recheck reached `1e367905c938186aac1680f25d1059721ddce333`.
ReadBounds, DirectRuntime and Shared have no changes from the delivered89373e34.
No runtime repair was present there to retest. Unrelated remote changes were not
merged. Evidence: h40/decision.json, remote-audit.json and cache-delivery.json.
All original Identity/producer/backend and final acceptance obligations persist.

H40 follow-through: independent trust/orphan/layer/root/doc-path/axiom-pin,
strict-automatic and frozen sort checks passed. TestSuite parity passed using
the existing tracked `tests/migration/solkey.pin.json` snapshot after the external
setup path lacked its adjacent pin. No pin or source observation was changed.
The corpus probe completed with the existing supported/unsupported mix, but its
build hit the unchanged resource guard on both bounded attempts. Releasing only
measured clean pages of the prepared private pack and public Node toolchain
increased headroom; it did not establish a full/corpus PASS. All setup/resource
failures remain in h40/ receipts and logs. No further retry or budget waiver is
claimed. Worker Lean/theorem changes remain empty; this is validation/backfill.

H40 resolves the two ownership/routing questions. The remaining producer-delivery
question is retained as deferred history while waiting; there is no new scope
question this turn. The required browser control, exact Identity twin and B/C
controls remain unaccepted, and all post-repair gates must be rerun as applicable.

## H41 cache receipt and amended transport policy

The coordinator confirms receipt of the preserved H35 pack and verification
against SHA-256 `3f2fb9f6a585b6a64f386b6e127b972a84fd7149ca914a29a191afac97d95dbb`.
The supplied receiver receipt is
`/home/guilherme/.local/state/cloudvm-coord/receipts/native-browser-cache-received-20261105T025529Z.json`.
This is coordinator-attested receipt evidence; the remote file was not read
on this VM. A fresh local hash matches and the 539,036,429-byte archive remains
intact at its recorded path. Evidence: h41/cache-receipt.json.

H41 amends H35: leave verified packs on the VM and record path/SHA; the
coordinator pulls them. **Never run ship-cache.sh on a VM.** Future prepared
packs are coordinator-pending until receipt. This specific pack is now
coordinator-confirmed received; the historical failed worker attempt remains
an immutable pre-H41 event and is not retried.

Receipt closes this pack's transport obligation only. It does not repair the
browser traversal, supply Identity/B/C controls, or turn the resource-stopped
full/corpus checks into passes. H40 still assigns the repair to lane A with
unchanged budgets. Fresh master remains1e367905 with no changes in the compared
runtime/read-bounds/shared paths; this lane continues to await that repair.
