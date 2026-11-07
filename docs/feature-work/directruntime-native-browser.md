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
`$XDG_STATE_HOME/cloudvm-coord/receipts/native-browser-cache-received-20261105T025529Z.json`.
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

## Adopted published 8495 checkpoint

Adopted `8495f1deb0a95dd6b9301822d8649ab76b217681` with an ordinary merge
into this owned branch, preserving original base/history/work. Its packet is
`docs/feature-work/integration-20261105-checkpoints.md`. Imported producer edits
are separate from worker edits: D adds no Lean declaration or axiom. Withheld
packets/protected Source repairs were not taken; no scanner or trust rule changed.

The packet delivers Memory.Reader and ControlTuple.Adapter/AdmissionControls
plus C's source/AST fixture. Their explicit-j1 VM build passed21jobs and13fixture
admission checks. Those checks explicitly imply no intrinsic proof/runtime verdict.
DirectRuntime, ReadBounds and runtime wiring remain unchanged; H40's lane A repair
is still awaited. H21 cache freshness is not inferred from publication.

Fixture backfill freshly compiled C's exact13public-function source with the
pinned compiler and submitted actual serialized requests to both real backends.
All13 controls remain unsupported. A separately freshly compiled existing
additionSimple guard proves on both, demonstrating the client is not always
unknown; it is not the required allocation Identity twin. Semantic/Identity
acceptance remains false. The exact B Identity allocation fixture is not in
this packet; the scalar web Identity example is not substituted.

These inventory requests deliberately reuse the previously compiled native/WASM
artifacts after checking all336current source hashes, bridge/closure and binary
identities. They are not claimed as fresh post-integration binary builds or a
completed post-A regression/performance gate. No environment/kernel assets or
serialized environments were observed on the recorded ordinary requests.

An evidence mistake in the first supplement reused two raw native paths,
overwriting the initial trace/reply stream. The first JSON/log survives; missing
raw evidence is not reconstructed. Versioned source and exact browser journal
lineage are retained in published-8495/evidence-lineage.json. A corrected harness
with output guards ran in a new verified-controls directory; its14-request
native trace/browser evidence is intact. Both reviewers accepted the scoped
inventory and disclosure. All original full/corpus, Identity/B-C, A-repair and
matched post-integration gates remain required.

## Follow-on f77 adoption and fresh binaries

Adopted exact published f77cf60d by merge 506cf233, preserving this lane. The
PrintStmt dependency changed, so old manifest freshness was rejected and both
backends rebuilt into fresh output directories. Native and WASM build gates
pass; all three 83-function benchmark modalities pass 249/249, with no recorded
latency/startup comparison over the unchanged 10% threshold. Whole native build
timing is not matched to the warm-Lean earlier build. Current package bytes,
benchmark runtime.build and worker boots are pinned to the freshly built WASM.

Fresh existing browser controls still fail on the same traversal stack overflow;
13/14 verdicts complete. H40 repair remains lane A's responsibility. All13 C
controls remain unsupported on both fresh backends; the independent positive
harness guard is not Identity non-vacuity. Shared.Intrinsic's relative callbacks
are not wired into DirectRuntime and establish no source adequacy. Exact B
Identity/control delivery, semantic integration and final full/corpus gates remain
pending. D adds no Lean declaration, axiom, budget or premise change.

The current versions/KeySort and three per-file MCP checks pass. A new verified
337-module relative build-cache snapshot remains coordinator-pending under H41;
it is explicitly not a Lake artifact catalog. The previous H35 pack remains
coordinator-received. No VM ship-cache.sh invocation occurred. Full evidence and
queue limits: [published f77 inventory](../benchmarks/directruntime-2026-11-04/published-f77/README.md).

## Published 9584 producer adoption

Merged exact published 9584f9e7 as 845abab8 while preserving this lane's work.
Locally built Shared.Scope and C IntrinsicControls; all17 producer theorem
signatures/axiom inventories pass with only existing standard axioms. Per-file
MCP checks report zero errors. Scope bounds and hand-built intrinsic controls
do not prove compiler/source adequacy or runtime support. D changes no Lean
declaration, premise, refusal, budget or trust rule.

All336 runtime source pins and all build-input/binary identities remain current;
the f77 native/WASM binaries are explicitly reused, not fresh9584 builds. Fresh
C requests still give13unsupported controls plus a separately proved harness
guard on each backend. No allocation Identity substitute or cached verdict is
counted. The identical binary's earlier stack failure remains retained evidence;
no repair was delivered or new benchmark claimed. H40/A, B Identity, C semantic
acceptance and final full/corpus/post-integration gates remain pending.

The two API modules' verified relative build-cache snapshot remains
coordinator-pending under H41, not a Lake artifact catalog/full dependency pack.
No VM shipping was attempted. Evidence, actual commands/resources and boundaries:
[published9584 adoption](../benchmarks/directruntime-2026-11-04/published-9584/README.md).

## Published b86a composition adoption

Merged exact published b86ae456 as 10a22913, preserving this lane. The committed
Shared.Compose reader combines the existing memory and control callbacks; local
build, exact definition-axiom inventory and per-file MCP checks pass. Fresh C
AST admission records9translated/4refused functions and separate root storage
validation, not function population, source adequacy or proof/runtime support.
The test artifact adds only IO/error handling around the published API. D adds
no registered Lean module, theorem, translator or producer edit.

All336 runtime source/generated-C pins and selected build inputs remain current;
f77 binaries are explicitly reused. Fresh native/browser C requests still give
13unsupported controls plus a proved scalar harness guard. The private runtime
consumer and H40 stack repair remain unchanged; exact allocation Identity and
paired controls, semantic integration, matched post-A benchmark and final full/
corpus gates remain pending. No new stack test or83benchmark is claimed.

The original executed wrapper is archived; review's exact-target guard suggestion
was applied and validated independently without rewriting prior evidence. The
one-module verified build-cache snapshot remains coordinator-pending under H41,
not a Lake catalog/full dependency pack. Evidence and queue boundaries:
[publishedb86a inventory](../benchmarks/directruntime-2026-11-04/published-b86a/README.md).

## H44 reviewable split

Bulk generated fixtures, evidence dumps, logs and historical executed-script copies
are removed from the merge diff and retained on this VM. The committed
[H44 manifest](../benchmarks/directruntime-2026-11-04/H44-bulk-manifest.json) records
the absolute archive path, byte size, SHA256 and coverage. All1530 archived files
were verified against preserved originals;1404 tracked bulk paths were untracked.
The review diff contains80 scripts/docs/manifest files,2816 added lines before
this handoff paragraph, versus533911 before splitting. No code, theorem, gate or
budget changed in the split. Existing reproduction scripts require the archived
evidence at its original relative paths; extract the archive at repository root
when reproducing elsewhere. Earlier artifact receipts retain their original heads.
Required runtime/Identity/semantic/full-gate obligations remain open.

## H81 fresh native/browser checkpoint (partial)

[Compact manifest](../../tests/directruntime-20261104/native-browser/h81-progress-manifest.json)
records the externally retained, individually hash-verified evidence and cache.
Fresh builds at source head0140eb13 use206 matching extracted C modules.
All343 runtime Lean source hashes also match B head64796174; all9 source pins
in the delivered A packet match. Exact B external journal delivery is still
pending; independently regenerated requests do not constitute its receipt.

The exact published Identity diamond twin, both compiler modes, proves through
fresh native and real Chromium WASM workers. The84-case matrix has exact result
object parity:64 proved,16 refuted,4 pending per backend; all64 required-positive
cases and72 concrete halt expectations pass. The four storage diamond pending
cases remain undecided. All13 C construct functions remain unsupported with
`plain return obligation`; the addition guard passes. Admission is not proof.

Both83-function benchmarks complete249/249 requests over3 rounds. Native median
1.017780ms versus0.838905ms is a21.32% STOP. Browser median191.497978ms and
p95235.344016ms rise3.00% and4.88%, while fresh-page startup4531.930874ms
versus3428.200938ms is a32.20% STOP. Startup is not machine-cold. No unchanged
stopped candidate was rerun; H68 metadata/runtime/UI differences confound cause.
Existing browser negative controls complete13/14 verdicts: invariantCountsToBound
still throws a traversal stack overflow. Offline/edit/staleness/spec controls
pass. No budgets, metadata requirements or refusals changed.

The selected206-module C/object/import/export inventory agrees across builds.
Three coarse frontend-origin flags remain visible; exact-body and machine-call
classification matches previously reviewed generic helpers. The original audit
source/execution is archived; review strengthened exact-label/direct-jump checks
against its retained disassembly without overwriting the original run. This
inventory and request-specific no-environment traces are not a universal purity
or compiler/source-preservation proof. Twelve existing intrinsic model controls
and their axiom inventory pass read-only; no worker Lean theorem was changed.

Actual Lean4.24.0 (797c613), Lake5.0.0-src+797c613; KeySort377/131/131
annotations match. Gates used serial12GiB/no-swap scopes with4GiB outer reserve.
Native/WASM builds took289.45s/278.82s, sampled RSS1.81GB/1.47GB. MCP checks
have zero errors; builder/closure regressions pass. The343-module verified cache
pack stays on this VM for coordinator pull under H41; no ship-cache was run.
H44 bulk stays out of Git. Full acceptance, semantic/source transport, owner
repairs, timing resolution and final combined gates remain open.

Final independent read-only finder and skeptic reviews pass with the stated
limits. Their archive denominator clarification was fixed:453 payload files plus
the index,454 archive members. Neither reviewer used Lean or reran benchmarks.

## Exact B journal receipt and reconciliation

[Reconciliation manifest](../../tests/directruntime-20261104/native-browser/b-original-reconciliation-manifest.json)
records verified delivery of the original537822-byte journal and handoff. The
84 cases match saved source/compiler identities; explicit selectors identify
the intended function. Common-field values match, but zero complete request
objects are identical: delivered raw AST/sourceId fields differ from normalized
line metadata. All field-presence differences are retained; the checker permits
missing fields generally and does not establish metadata-only equivalence.
The exact delivered bytes have not been replayed through either backend.

Both saved backend denominators and wire hashes reconcile. Selector and shared
value drift controls reject their mutations. Four primary input files have
before/after metadata/hash checks; referenced sources are hashed once. Finder
and skeptic pass with these limits; finder provenance advice was applied.
The initial /usr/bin/time setup failed before comparison (exit127), retained
externally; Python resource accounting and final comparison pass. No Lean,
browser, build or stopped benchmark rerun was needed for this tooling change.

This clears only the exact B delivery wait. Prior four pending diamond cases,
13 unsupported C constructs, browser stack failure and both timing STOPs remain.
The A H44 archive is still pending. Under H88 no new cache shipment or semantic
gate is inferred from the old343-module pack. Original full acceptance remains
open. All bulk stays outside Git with the committed checksum manifest.

## Exact B journal functional replay

[Replay manifest](../../tests/directruntime-20261104/native-browser/b-original-replay-manifest.json)
advances the preceding receipt-only checkpoint. The exact delivered original
84-request journal now runs through native and real Chromium WASM. All84
complete request objects and reconstructed compact wire lines match delivery.
Results match across backends:64 proved,16 refuted,4 pending, with all64 required
positives and72 concrete halt expectations satisfied. Positive Identity diamond
passes both compiler modes in both backends; paired controls reject vacuity.
Statuses also match the earlier normalized-request run. These are trusted
compiled-checker observations, not source/compiler preservation or proof terms.

The run revalidates prior fresh H81 binaries and343 source hashes; no new
runtime build occurred. Freshly compiled companion fixtures bind source/compiler
provenance; submitted ASTs come from the exact original journal. The141.65s
functional run used12GiB/no swap/CPU1, sampled RSS1.376GB and minimum outer
headroom10.587GB. Native trace and browser asset observations found no forbidden
environment/kernel loads. No performance benchmark was rerun.

Finder and skeptic requested this mode-specific wording. The executed harness
is archived; the subsequent edit changes only report boundary text. The final
checker and syntax gates pass. Four pending storage diamond cases,13 unsupported
C constructs, the existing browser stack failure and both timing STOPs remain.
External A data and reviewed producer repairs remain required; no final runtime
gate or whole-assignment completion is claimed.

## OT-PAGES-IDE: explicit pinned SDK config

The Pages IDE job in run42295102972 (job128158368938) builds GMP and leanrt,
then fails the strict explicit `EM_CONFIG` guard. The existing compact builder
already invokes `build-direct.sh` inside the digest-pinned Emscripten4.0.15
image. That entrypoint now exports `/emsdk/.emscripten` after SDK activation
and refuses a missing file before invoking Python. The Python builder retains
its explicit-config requirement and all compiler/config provenance checks.

The regression control executes the real entrypoint in bounded Docker with a
fixture SDK and capture-only builder: unset and inherited unrelated configs
select the pinned path; a missing SDK config fails before Python. All three
controls and the eight existing builder/provenance tests pass. These tests
check plumbing, not actual SDK compilation or Pages success. Read-only finder
and skeptic reviews find no blocking defect. No Lean source, proof budget or
trust boundary changed; no runtime build or stopped benchmark was repeated.

A `pages.yml` workflow_dispatch on the published lane branch and a green IDE
job remain required. The VM CLI token is invalid and the available connector
has no dispatch action; host-owned branch publication/dispatch is pending.
The non-default-branch workflow does not deploy Pages. H100 remains open until
the actual IDE result is retrieved. Exact evidence is retained outside Git at
`/workspace/solidity-lean/.lake/native-browser-pages-sdk-config/receipt.json`.

H100 IDE verification completed on the exact reviewed fix head
`39d914b72eb31f116fe628282026437346a70deb`: [Pages run42300556762](https://github.com/SolidiKeY/solidity-lean/actions/runs/42300556762),
IDE job128176919315, succeeded. All16 reported steps passed, including the
native build/audit guards, generated-C/leanrt/GMP WASM build, offline HTML and
fresh offline launch/proof/reopening tests. Independent finder and skeptic
confirmed the head and result through live GitHub reads. The
[CI manifest](../../tests/directruntime-20261104/native-browser/pages-sdk-config-ci-manifest.json)
pins externally retained logs and metadata. This clears the IDE-fix validation
wait; the overall workflow was still running its Solidity job at inspection.
No default-branch deployment, original timing STOP resolution or whole-goal
completion is inferred. This documentation increment changes no tested code.

## Reviewed primitive-return intake and fresh regressions

[Results manifest](../../tests/directruntime-20261104/native-browser/primitive-return/results-manifest.json)
records source build `1e8b4cee884df7f90bf711abfddce5a6f8957d10`. After adopting
published master33eb46304, this consumes exactly the listed production file
`Shared/Intrinsic.lean` from reviewed producer957e5def, SHA74c01bac…4577.
It does not consume the unpublished H90 Translate/Compose changes or qualify
the whole producer branch. No producer definition was manually rewritten.

Fresh native and WASM builds pass in294.26s/268.69s, sampled RSS1.74GB/1.47GB.
All heavy checks use serial12GiB/no-swap scopes, thread1/-j1 and the4GiB reserve.
The206-module selected C/object inventory matches across backends:9963functions
and4988closed values. Request-specific traces show no forbidden environment
loads; this inventory is not a universal purity or machine-correctness theorem.

| Functional corpus | Per-backend observations | Boundary |
|---|---|---|
| C construct fixture,13functions |9proved,4unsupported |Exact reviewed refusal strings retained |
| A primitive-return fixture,8functions |6proved,2refuted |Defaults,tuple,earlyexit,shadow,falseassert,division |
| B exact delivered journal,84requests |64proved,16refuted,4pending |All64required positives and Identitydiamond both compiler modes pass |
| Existing83functions |83proved in each backend |One functional pass;no timing comparison |

C and A each also execute a separate positive addition guard, so raw reports
have14 and9 rows respectively. All four corpora have exact native/browser
result-object parity. The B corpus removed by published H44 cleanup was recovered
from exact Git0140 bytes: its manifest SHAe492ab28…ddd35 matches the prior
receipt and all84case fields match the authenticated original handoff. Its
original537822-byte journal is unchanged; no regenerated substitution was used.

The18finite modal cases, return side-effect check and2refusal guards pass.
`#check` preserves explicit callback signatures; both obligation definitions
print only `propext` and `Quot.sound`. The existing12intrinsic memory controls
also pass read-only. These model controls do not prove compiler/source transport.
Five per-file MCP diagnostics report zero errors. The supplied H44 verifier runs
unmodified in an isolated layout and verifies all50files/3229786data bytes.

Fresh native negatives/specs pass14verdicts. Fresh browser negatives retain
13/14: invariantCountsToBound still raises a stack error. Edited-source,
counterexample and offline UI controls pass. The original native median and
browser startup STOPs remain; no stopped83-function timing benchmark was rerun.

Setup failures are retained individually: missing output parent; B live manifest
removal and a subsequent non-overwrite guard;109-byte MCP socket path; the
retired check-solkey helper; symbol postprocessing filename. Recovery does not
relabel those failed receipts. Eighteen unit checks and syntax pass before the
retired-helper failure; on-demand KeySort separately passes377/131/131 matching
annotations on actual Lean4.24.0/Lake5.0.0-src+797c613.

| Local registration proposal | Role | Central action |
|---|---|---|
| `tests/directruntime-20261104/native-browser/primitive-return/FiniteControls.lean` |Standalone per-file model driver |No generated library root addition |

## OT-STACK-SYMBOLS exact historical mapping

A diagnostic relink of retained H81objects with `--emit-symbol-map` reproduces
the historical WASM byte-for-byte, SHA6ae1d6db…b563. Its3939-entry symbol map
binds indices2203/2205 to `Solidity.Decide.LTm.fitsM` and its boxed lambda,
2208/2210 to `Solidity.Decide.LFml.fitsM` and its boxed lambda,3126 to
`lean_apply_1`, and3207 to `emscripten_builtin_malloc`. The historical source
anchor is Calculus/ReadBounds.lean. This identifies active routines, not a
complete causal explanation or algorithm repair. No source algorithm was edited.

The relink itself succeeded; postprocessing first looked for direct.symbols
instead of the emitted direct.js.symbols. A post-only recovery verifies whole
binary equality and reads the existing map, without another relink or request
run. Exact trace/map/source bytes are packaged for A. The map qualifies only
the historical6ae binary, not the fresh19e or whole H90 reader.

Final read-only finder and skeptic reviews pass with these limits. They
independently checked both archive hashes/counts, gate exits and the exact
historical binary equality; neither ran Lean, builds or timing reruns.


## Fixed-byte producer intake and exact prerequisite recovery

[Results manifest](../../tests/directruntime-20261104/native-browser/fixed-byte/results-manifest.json)
pins amended source build1b2bdb490054293c86cddb5e4b7fa15736bae25b and exact
producer2738af9966 Translate,Compose and ControlTuple.Adapter bytes. The first
intake matched Shared/DirectRuntime but omitted the adapter's local scalar
callback. Both backends refused tupleSwap/repeated; those failed reports and a
separate missing-activation setup failure remain archived. The exact committed
adapter prerequisite fixes the omissions with unchanged expectations.

Fresh native and real Chromium runs match all20fixed-byte fixtures:12proved,
4refuted,4unsupported per backend,plus2positive harness guards. The source-level
box twin erases to the exact producer diamond source after removing10annotations.
Tags and specific parameter/positive-length refusal strings are asserted.
C13,A8,B84 and83existing functions all pass their unchanged observation checks
on both amended binaries. B retains64proved/16refuted/4pending; exact positive
Identitydiamond passes in both compiler modes. Native negatives pass14/14,
browser negatives remain13/14 with invariantCountsToBound stack overflow.
Edited-source,counterexample and disconnected fresh-edit UI controls pass.

The206-module inventory has9966functions/4989closed values with selected C
parity. Seven per-file diagnostics report0errors;32marker guards,18finite modal
cases/effect/refusal controls and12intrinsic memory controls pass. Both decoder
lemmas print only propext,Classical.choice,Quot.sound. These are decoder/model
facts and trusted compiled-checker observations,not source/compiler/ABI/native
preservation or exhaustive source/H90 migration proofs. Ordinary-request traces
and browser assets load no forbidden serialized environment/frontend resources;
reviewed frontend-origin generic bodies remain explicitly classified.

Actual Lean4.24.0/Lake5.0.0-src+797c613,18unit checks and on-demand KeySort
377/131/131 with matching annotations pass. Every heavy gate uses serial12GiB,
swap0,CPU1,threads1/-j1 and4GiB outer reserve. Amended native30.52s reuses
content-addressed objects and performs a new link; WASM285.05s recompiles selected
C. The first371.15s native build was26.13% above prior294.26s; this conservatively
retains a build-cost STOP. Empty native output is not a fully cold machine or
matched invalidation workload. Unchanged SliceCopy source/C does not establish
a cause. The incremental rebuild cannot clear that STOP. Original native median
+21.32% and browser startup+32.20% STOPs remain; no stopped timing benchmark
was rerun. Full performance/final runtime acceptance remains pending repairs.

| Local registration proposal | Role | Central action |
|---|---|---|
| fixed-byte/MarkerControls.lean |Standalone32-spelling/signature/axiom driver |No generated production root addition |

Bulk fixtures,logs andruntime binaries remain off Git under the manifest's
absolute paths with per-file SHA256 indexes. Independent read-only finder and
skeptic inspect the exact intake,denominators,failures andarchive receipts;
no proof budgets,statements,exclusions,trust pins or optional-certificate boundary
are weakened. This checkpoint does not complete the original queue.

The locally verified24-artifact incremental cache pack is retained for coordinator
pull with path/size/SHA in the manifest. Delivery is coordinator-pending; no
ship-cache.sh or H88 cross-cache coherence claim is made.


## H71 address-local qualification and owner conflict versions

[Address results manifest](../../tests/directruntime-20261104/native-browser/address/results-manifest.json)
pins source build4234b74778787f681ebb50f2890355d99f37731a,exact producer0834bc67
Translate/Compose hashes and verified packet c19c588e…ec5dfb. The delivered
0a96c06e producer archive was inspected without execution. H71authorizes scoped
consumption while the coordinator publication/merge wait remains separate.
Both conflict files now equal the reviewed owner versions;no manual producer
rewrite or unpublished master adoption occurred.

All343runtime source files match reviewed owner09bb5b5e. Compared with the full
0834tree,only the published LinearCountermodel dependency differs. This dependency
context is explicit;the packet is a two-file increment,not wholebranch,census or
source/ABI qualification.

Both freshly built native and real Chromium backends match all16source-backed
address fixtures:10proved,2refuted,4unsupported,plus2positive harness guards per
backend. Eight source-level box annotations erase to the exact diamond source.
Parameter/payable refusals retain the exact unsupported-address diagnostic.
A separate compiler-produced AddressStateRefusal contract fails closed on both
backends;that gap request is neither a positive proof nor part of the16fixtures.

The new kernel decoder equation and prior narrow/fixed-byte equations print
only propext,Classical.choice,Quot.sound. Marker/identity/malformed/payable guards,
3builtinidentity negatives,base-first error priority,32fixed-byte spellings,
18finite modal cases,one return-effect check,two refusal guards and12intrinsic memory controls pass.
Eight per-file diagnostics report0errors. These prove decoder/model facts and
record trusted checker observations;source/compiler/ABI/native preservation,
full importer parity and original semantic/world obligations remain open.

Retained fresh fixed-byte20,C13,A8,B84 and83function controls match their unchanged
expectations on both backends. B retains64proved/16refuted/4pending,including the
positive exact Identitydiamond in both compiler modes. Native negatives pass14/14;
browser negatives remain13/14 with invariantCountsToBound stack overflow. Edited
source,counterexample and disconnected fresh-edit UI controls pass.

The206-module selected-C/object inventory has9985functions/5006closed values,
with native/WASM parity and current request-specific no-forbidden-load traces.
Its exact-body classification is not a universal purity or machine-correctness
proof. Actual Lean4.24.0/Lake5.0.0-src+797c613,18unit checks and on-demand KeySort
377/131/131 with matching annotations pass. Every heavy gate uses serial12GiB,
swap0,CPU1,threads1/-j1 and4GiB outer reserve. Native28.80s is incremental;WASM
269.95s recompiles selected C. The191.48s marker gate includes transitive rebuilds.
These are not matched-cold measurements and do not clear the prior native median
+21.32%,browser startup+32.20% or native build+26.13% STOPs. No unchanged stopped
benchmark was rerun;RUNTIME_GATE_PASS remains pending.

Finder and skeptic caught a supplementary-harness provenance gap before use:
fixture/source/compiler were initially only self-consistent. The tested version
binds them to the exact pinned suite and completed parent report,checks its
single public function,current binaries/bridge/closure/sourcepins,and fails
closed on RPC timeout. Both reviewers confirmed the correction. The executed
private script and committed script are byte-identical.

| Local registration proposal | Role | Central action |
|---|---|---|
| address/MarkerIdentityControls.lean |Standalone marker/identity/signature/axiom driver |No generated productionroot addition |

Bulk ASTs,logs,binaries and24incremental cache artifacts remain off Git with
absolute paths,per-file indexes and SHA256 in the manifest. Cache delivery is
coordinator-pending;no ship-cache or H88cross-cache coherence is inferred.
Independent final finder/skeptic review remains scoped to these receipts and
limits;this increment does not complete the original assigned queue.


### Published owner merge and refreshed current evidence

Published master4f0a2d6abe3a920d8c5a20c8c06d373a1014824d contains reviewed
owner09bb5b5e. After saving the qualification checkpoint,the clean ort merge
0eb39db1dba7f81e4d8d0b4756ab50b87d4dcd6d retained both exact owner files and
the H100explicit EM_CONFIG fix. The coordinator merge wait is fulfilled.
[Post-merge manifest](../../tests/directruntime-20261104/native-browser/address/post-merge-manifest.json)
records refreshed builds and all controls;prior4234receipts remain frozen.

All343currentruntime sourcefiles match published4f0. Compared with09bb,the only
delta is the published additive SourceCounterexample companion. A complete
206-module/object/current-binary inventory binds native and WASM parity and
excludes the four new optional kernel-candidate helper families from selected
functions/native symbols. This limited exclusion is not universal purity or
source/ABI preservation. Reviewers required and confirmed nonempty complete
module coverage,current object hashes,companion-summary/binary/source bindings,
actual HEAD/provenance hashes and non-overwriting receipts before execution.

Fresh postmerge native25.49s and WASM272.51s builds pass under the same bounded
policy. Nine per-file diagnostics report0errors;actual toolchain,KeySort,axioms
and model controls pass. Address16plus2guards and the extra state gap,retained
fixed-byte20,C13,A8,B84 and83functions pass unchanged native/browser observation
checks. Identitydiamond succeeds in both compiler modes. Native negatives and
edited-source/offline UI pass;browser negatives remain13/14 with invariant stack
overflow. Four storage-diamond cases and all timing/build-cost STOPs remain.
No stopped timing benchmark was rerun;RUNTIME_GATE_PASS remains pending.

The new exclusion script is committed byte-identical to its tested private
copy. Current archives and32incremental cache artifacts stay off Git with
per-file indexes and SHA256;cache delivery remains coordinator-pending.


## Environment frontier delivery and source-ID preparation

The H71environment packet pins producer44d89439 and an eight-module frontier.
Seven current file hashes match;Translate90479 is missing. The advertised branch
fetch succeeds,but exact-SHA fetch returns128/notourref,and packet/evidence paths
are absent. The [exact delivery request](../../tests/directruntime-20261104/native-browser/environment-source-request.json)
records hashes and required bytes;no decoder/source fixture is reconstructed.
The requested16environment cases and15metadata negatives remain unqualified.

Independent [source-ID preparation](../../tests/directruntime-20261104/native-browser/request-identity/preparation-manifest.json)
now binds actual positive unique compiler function IDs into fixture and guard
requests,then checks returned IDs on native and real Chromium. Sixteen retained
address fixtures plus2guards perbackend pass unchanged verdict/tag expectations,
with18identity checks. Four intentionally mismatched/malformed selectors per
backend fail closed with exact gaps. Positive guards prevent counting an
always-gap implementation as success. Four fresh external compiler runs occur;
the existing0eb native/WASM/site are retained,with343runtime sourcepins each still
matching current04c6context. These are selector API regressions,not freshbinary,
newenvironment,source/ABI orperformance qualification. No cachedverdict is used.

Allthree bounded gates pass12GiB/swap0/CPU1,threads1 and4GiB reserve;Node syntax
passes. No Lean/productionruntime source or proof budget changed,so no new
Lean/axiom/cache gate is claimed. Existing stack,cost,startup andfour storage
holds remain;no stopped timing benchmark was rerun. Independent finder/skeptic
review covers these limits. Bulk ASTs/logs remain off Git with per-file hashes.


## Authenticated environment source and published guard theorem

The delivered source archive and ticket match their recorded hashes. All eight
frontier snapshots and all twelve source/control/manifest entries were verified.
Seven published frontier files match the snapshots byte for byte. Translate
contains the delivered definitions plus a 37-line standalone guard theorem;
removing only that theorem and its docstring reproduces the delivered hash.
The published proof remains in place. This does not establish full file or
binary equivalence, source preservation, or ABI adequacy.

Fresh native and real Chromium runs use source build
4d7285b80e89741e9da8cb49ce7ab8b62a828a72. The sixteen environment requests match:
eight proved, four refuted and four unsupported per backend, plus two positive
guards. Compiler function IDs select each request and match each reply.
Unsupported block.number and tx.origin retain their exact diagnostics; wrong
value/time assertions refute. Eight box annotations erase to the exact producer
source. Fifteen metadata foils, three supported keys, two unsupported siblings
and base-first error priority pass. The helper has no axioms; its published
guard theorem uses propext and Quot.sound. These are decoder/model observations,
not compiler identity or world adequacy proofs.

Thirteen per-file diagnostics and the retained decoder/model controls pass.
Address, fixed-byte, C, A, B and all 83 functional observations match their
recorded expectations on native and browser. Identity diamond succeeds in both
compiler modes; four storage-diamond cases remain pending. Native negatives
and browser UI checks pass. Browser negatives remain 13/14, failing on the known
invariant stack overflow. The candidate-exclusion check initially rejected a
stale private output path; correcting that path passed. Both receipts remain.
Executable inventories and observed absence of forbidden loads have their
recorded finite scope. Every existing timing/build-cost STOP remains open;
no stopped benchmark was rerun and RUNTIME_GATE_PASS remains pending.

After validation, the branch fast-forwarded to published master
3a5b9de412b84a13777b6fbf8c8f310e10b3448e. All 343 compiled runtime sources and
checked repository build inputs are unchanged. The original source-build and
binary identities remain explicit in the
[results manifest](../../tests/directruntime-20261104/native-browser/environment/results-manifest.json).

The original producer AST and evidence archive remain undelivered. A fresh
independent compilation of the authenticated source with the producer arguments
reproduces the expected AST hash exactly; this is content reproduction, not a
producer transport receipt. Bulk evidence, binaries and the verified 32-artifact
incremental cache stay off Git with hashes and indexes. Cache delivery remains
coordinator-pending; no ship-cache or release-cache coherence claim is made.
The local registration proposal covers the standalone MetadataControls driver;
no generated root was edited.


## Reviewable environment validation wrappers

The P2 review note identified that private `.lake` wrapper locations were not
reviewable from Git. The [wrapper index](../../tests/directruntime-20261104/native-browser/environment/wrapper-index.json)
now maps twenty preserved source/configuration snapshots to repository paths,
sealed archive members, sizes and SHA256 hashes. The
[scripts README](../../tests/directruntime-20261104/native-browser/environment/scripts/README.md)
explains the original preparation, failed/recovered continuation and bounds.
A read-only verifier checks the tracked snapshots and optionally their sealed
archive members; it executes no historical wrapper.

The index records the original VM handoff locator and exact evidence/runtime/
cache archive hashes for the existing coordinator retrieval channel. H71
relayed the handoff metadata; bulk retrieval and recipient inspection remain
coordinator-pending under H41. No public download or completed delivery is
claimed. Generated fixtures, logs, binaries and caches remain outside Git.
These snapshots retain historical paths and private prerequisites; they are
review artifacts, not a turnkey or newly accepted runtime replay. All original
stack, performance, storage-semantic and final-gate holds remain open.

This increment adopts published master d7a1cbdf597826add5af3533fdaf6b8d91e28f66
and changes no production Lean source, theorem, budget, trusted boundary or
historical verdict. Syntax/identity controls and independent read-only reviews
are recorded in the portable preservation receipt. No Lean build or unchanged
stopped benchmark was rerun for these documentation/tooling changes.


## Narrow browser-negative continuation

The maintained environment checks.sh and remaining-checks.sh no longer use a
blanket browser-negative failure bypass. A read-only
[continuation guard](../../tests/directruntime-20261104/native-browser/environment/known-stack-continuation.py)
permits independent checks to continue only when the sole failed control is the
known invariantCountsToBound source with the documented WASM stack-overflow
error. It requires the failed gate exit, bounded resources, complete requests,
matching worker/binary and request identities, and healthy sibling verdicts.
Other errors, missing results, timeouts, resource stops, changed source or
unexpected sibling outcomes stop the wrapper. The original browser gate stays
failed; no STOP or acceptance requirement is released.

Both original scripts remain byte-identical in scripts/historical and are
indexed against their sealed archive members. The maintained copies are
explicitly distinct from those historical snapshots. The guard reconstructs request hashes from retained AST bytes, checks sources
against the six retained baseline controls and tracked ClosedSpecs, and pins
the runner plus reviewed failing fixture
and wire. Offline tests use the
retained receipt and twenty-six mutations; they run no browser/runtime or stopped
workload. The first test harness attempt mistook pop()'s return value for an
exit status; explicit status handling fixed the test setup. This was not a
browser/runtime rerun or a guard-acceptance defect. Existing seals remain
unchanged; no Lean source, theorem, budget or trust boundary changed.


## H127 slow-example runner intake and pre-use design

H127 assigns this lane the H109 slow-example runner after two rejected Terra
drafts. It does not transfer the rest of H55–H58 or clear runtime STOPs. The
existing fourteen-module non-default slow library is retained. The
[pre-use contract](../../tests/directruntime-20261104/native-browser/h109/RUNNER-DESIGN.md)
requires sealed source/Git/package/toolchain/cache inputs, actual kernel cgroup
checks, serial execution, whole-container cleanup and precise timing/memory
provenance. The exact H116 intake supersedes the provisional600 plan: only cumulative
original Derived17 replay gets CI600/local300; H109 module measurements stay300.
No proof heartbeat, statement, exclusion or other budget changes.

The source-plan preparer validates all committed regular-file bytes against
Git and records SHA256, source modes and all fourteen targets. Descriptor-based
reads reject symlink ancestors, special files and size drift. It only prepares
a plan: live observations are not a sealed executable snapshot or resource
attestation. Synthetic metadata controls and the existing slow-root partition
checks run without Lean. Full source inventory stays outside Git with a hash.
Independent read-only finder/skeptic reviews found and resolved regular-file,
isolated-Git/package and cleanup-contract gaps. No production runner, real
slow-module checks, matched measurements, CI qualification or pin relocation
is claimed. The latest module-times result and both rejected drafts are now delivered in
the authenticated b3fb intake; the older H82 report is historical. A coordinator quiet window will be requested only
when an exact reviewed axiom-pin migration is ready.


### H127 exact draft intake and full-tree identity primitive

The coordinator delivered the exact b3fb module-times result/waits and both
rejected drafts. This lane read their source without importing or executing
either; [draft-review.json](../../tests/directruntime-20261104/native-browser/h109/draft-review.json)
records eight concrete input, serialism, timing/RSS, CPU, cleanup, evidence and
A/B obligations. The supplemental archive contains a duplicate self-hardlink;
strict production membership validation rejects that form. Only selected
regular text/JSON payloads were inspected; both draft hashes also verify in
the separate twelve-regular-member sealed delivery. No historical gates were
rerun or reclassified as current proof/measurement results.

The input-inventory primitive observes every source/cache/toolchain/package
entry, including content, xattrs, modes, ownership and mtime; it separates inode
identity from cross-copy content comparison. Special files and escaping or
dangling links reject. Its verification CLI requires the exact inventory pin,
and observations stay explicitly non-atomic. This is implementation progress
on complete input binding, not a sealed snapshot or an authenticated runner.
The exact H116 scope is cumulative original Derived17 CI600/local300 only;
H109 module measurements retain300 in both contexts. No default checkpoint,
static-classification owner, shared pin/root or theorem/budget was changed.
The real serial controller, kernel resource/measurement/cleanup implementation,
matched A/B, CI/lane-end gates and pin quiet window remain pending.
