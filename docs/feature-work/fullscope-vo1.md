# VO1 optimizer — O01 / O02 / O03

Base: e70b959bf6dd81d09bfaf6eda8025b1cc98bc4c3.
Branch: codex/solidity-fullscope-20261104/vo1-optimizer.
Checkout: /workspace/solidity-lean.

## O01 interface checkpoint (source only; not ready)

`Solidity/Optimizer/Pass.lean` imports existing intrinsic Solidity and Yul syntax.
`Pass Prog = Prog → Prog`; `Preserves Related pass = ∀ p, Related p (pass p)`.
`Validator Related` contains executable `validate` and proof `sound`.
`validate_sound` requires acceptance; `validated_preserves` additionally requires
reflexivity for rejection. `Preserves.comp` requires transitivity.
Lowering.Pass fixes C/Γ/Δ; Yul.Pass fixes F/X/c/n. There is no erased IR.

The relation is deliberately a parameter pending the X01 D6 producer contract.
This is no claim that an arbitrary relation satisfies D6. No public correctness
adapter or concrete optimizer pass has been proved by this checkpoint.
Consumers: VO2 and VT validator consumers; V09 and VY3 compilation adapters.
No owner files, generated roots, maps or trust pins were modified.

Runtime: verified Docker memory.max=12884901888, memory.swap.max=0;
Lean 4.24.0 (797c613), Lake 5.0.0-src+797c613; serial LEAN_NUM_THREADS=1,
-j1 alternate TOML, 180s prerequisite timeout. KeySort: 377 parsed, 131
read-bearing/table coverage; OK. Peak cgroup bytes 775319552.
Evidence: tests/fullscope-20261104/vo1/evidence/runtime-keysort.log.
Old setup validation is historical and is not evidence for this checkpoint.

## Open queue and dependencies

O01: kernel checking, finder/skeptic review, registration proposal, composition
into Compilation.correct/G49, artifact-bound D6 relation, baseline gas/code-size
benchmarks, controls, axiom inventory, full gates, sealed cache export/receipt.
O02: all value passes, checked Panic preservation, solc rule reference and controls.
O03: all structural passes; X06 aliasing needed for memory/storage and LICM.
Final: integrated prerequisites/V16 revalidation, full gates, sealed handoff.
Backfill: composition laws, negative validator controls, nontrivial witnesses,
baseline/gas/code-size benchmarks remain open. No checkpoint is ready.

Interface source kernel-check: `lake -f tests/fullscope-20261104/vo1/runtime.toml
build Solidity.Optimizer.Pass`, bounded Docker, timeout 300s, exit 0; 18 jobs
completed, interface 437ms, cgroup memory.peak=536776704 bytes. Full group wall
and sampled aggregate RSS were not captured: UNVERIFIABLE, do not infer them.
This is not final H35 validation or checkpoint readiness.

Separate read-only finder and skeptic reviews (no Lean/server) found no
confirmed defect. Finder checked indices, validator acceptance and rejection,
and transitivity premises. Skeptic noted that arbitrary Related can be True and
that an always-reject validator is possible: only generic infrastructure is
proved. Final D6 binding must establish transitivity with compatible actual
artifact/gas-oracle parameters; the generic law does not supply that proof.


## O01 composition/control backfill checkpoint (partial)

Source IDs: existing `Solidity.Prog C Γ Δ` and `Solidity.Yul.Stmt F X c n`.
New owned modules: `Optimizer/Laws`, `Optimizer/RoadmapComposition`,
`Optimizer/Controls`. No existing theorem, observation, exclusion, expected
verdict, producer file, heartbeat limit or trust pin changed.

Exact additional boundaries (see declarations for implicit type parameters):

- `Validator.equality P [DecidableEq P] : Validator (fun p q : P => p = q)`;
  accepts by executable decidable equality, never Classical.decEq.
- `Validator.rejects_unsound validator (changed : ¬ Related p q) :
  validator.validate p q = false`.
- `asRoadmapPass L pass : Roadmap.Pass L L`, with Dom=True and identity envAbs.
- `beforeCompilation pass optimizer compiler correct coverage :
  Roadmap.Cert ((asRoadmapPass L pass).comp compiler (fun p _ => coverage p))`;
  optimizer is `Roadmap.Cert (asRoadmapPass L pass)`, correct is the unchanged
  compiler certificate, coverage is `∀ p, compiler.Dom (pass p)`.
  This adapter preserves the imported full resource/hash/environment obligations;
  it does not derive an optimizer certificate from generic Preserves.

Kernel checks: laws/adapter build exit0 (2.053s, sampled peak aggregate RSS
599687168 bytes); controls build exit0 (2.050s, RSS599191552). Later final
controls/axiom build exit0 (1.756s, RSS492474368, cgroup peak151019520).
Controls exercise accepting equality, unequal mutation rejection, rejection
fallback, universally quantified rejection by any sound equality validator,
composition of guarded proposals, and intrinsic syntax inhabitants.
These are framework controls; the skip-only Yul and assumeFalse lowering
inhabitants do NOT meet the nontrivial semantic-witness requirement.

Axiom output: validate_sound, validated_preserves, Preserves.comp,
no_sound_checker_accepts, combination and asRoadmapPass use no axioms;
beforeCompilation inherits only propext from Roadmap.Cert.comp. No new axioms.
The imported standard axiom's global pin remains COORD-owned.
Static trust gate exit0: 3839 sources, 285 inventoried sites, 0 findings.
Per-file MCP: Pass, Laws, Controls, RoadmapComposition each report zero errors.
Final source-bound MCP Controls check: exit0, 3.425s, sampled aggregate RSS
934653952, cgroup peak434679808 bytes, four samples, source unchanged and owned
container cleanup verified. Exact commands and source hashes are in receipts.

The first full-gate attempt failed because Node was absent from the inner PATH;
fixed using the already installed Node. Retry exits1 at generated registration:
four missing optimizer imports. Layer check passes for the 603 currently
registered core modules, but optimizer CORE registration is still a proposal.
No downstream full build or final global axiom inventory has passed.
A very short cached source-final build returned child0 but runner1 for zero RSS
samples; retain that failure. The final MCP re-elaboration above resolves the
owned-source observation gap, not the blocked full gate.

Resource policy: Docker digest pinned in the runner; memory.max=12GiB,
memory.swap.max=0, LEAN_NUM_THREADS=1 and explicit -j1; 4GiB admission/runtime
reserve; inner command timeout290s with kill-after2; outer watchdog300s.
Historical exact walls for the first two runs remain UNVERIFIABLE; budget
accounting conservatively charges their full 180+300s caps. Orphan logs and
reservations are charged300s; this includes conservative overcharging of static
logs. No budget was lifted and no resource/time stop was declared PASS.

### Separate read-only reviews and repairs

Finder and skeptic independently reviewed source and runner without Lean/server.
No proof-logic defect found. They identified exception/signal cleanup, missing
working-tree/root/vendor/script fingerprints, orphan-run budget reservations,
timeout overshoot, absent RSS samples and ambiguous child-vs-runner exits.
All were fixed: bounded owned-container cleanup with uncertainty retained,
before/after full-input hashes, reservation-before-launch, strict inner timeout,
measured-memory requirements, and separate runner_exit/child_exit. Both final
narrow reviews confirm prior findings fixed, no further finding. External
fixtures/toolchain identities are to be bound in the cache manifest.

### Dependency requests, readiness and queue accounting

Stub relay: `Solidity/Optimizer/Pass.lean@4447817d703775814e82a07fa14238f5e08dc119`.
Intended consumers VO2/VT. Relay receipt is PENDING; retain this request.

1. X01: exact committed D6 relation and D1 artifact/gas-oracle parameter API,
   including composition with compatible actual optimized artifact parameters.
2. V09/VY3: producer-owned Compilation.correct adapters/coverage and current
   compiler-to-physical-artifact/Osaka target oracle APIs for genuine baselines.
   Current Evm/Machine explicitly has no gas and symbolic/structured instructions;
   counting those as byte size or assigning Osaka gas would fabricate evidence.
3. Published integration 8495f1de resolves generated-root and module-map entries.
   COORD still owns the outstanding Optimizer CORE enumeration in
   scripts/check-layers.mjs. The original proposal remains historical; see the
   post-integration section for current full-gate timeout and cache request.
4. X06: physical aliasing facts for redundant sload/mload/store and LICM.
5. H41 cache delivery RECEIVED, per coordinator receipt below. Preserve the
   verified pack. H41 supersedes the prior VM ship-cache request: never run
   ship-cache.sh on this VM; future verified exports are coordinator-pending
   until the coordinator supplies a pull receipt. The historical dry-run
   failure remains evidence, not a current blocker.

O01 interface and independent laws/negative controls are implemented and checked;
O01 overall remains BLOCKED on concrete D6, compiler/public correctness adapters,
real code-size/gas benchmarks, semantic witnesses, registration/full gates,
and V16/integrated-prerequisite revalidation. Cache receipt is now satisfied under H41.
O02 has not begun under the required sequential ordering: constant folding and
propagation with Panic, copy propagation, solc-rule expression simplification,
dead-code and unused-variable elimination all remain OPEN after O01.
O03 has not begun: inlining, CSE, load/store elimination, LICM and unused-function
pruning all remain OPEN after O01/O02; alias-dependent parts additionally await
X06. No same-lane producer stub was invented.
Backfill accounting: composition laws and framework negative/combination controls
are checked; nontrivial semantic examples and baseline/gas/code-size benchmarks
remain pending the same D6/artifact/target producer APIs. No additional assigned
independent backfill is available without inventing or changing those interfaces.
The entire assignment is unfinished. No checkpoint readiness or publication.


## H41 cache receipt update — 2026-11-05

Coordinator-reported receipt:
`/home/guilherme/.local/state/cloudvm-coord/receipts/vo1-optimizer-cache-received-20261105T020426Z.json`.
The coordinator reports pulling and verifying the pack against SHA256
`f84ba52f64e1d260ff0e6c7711acf9089330bc9bca8e604123332bfe48679b29`.
Local SHA256 was rechecked and matches. Preserve the existing 89,252,357-byte
pack at `/workspace/solidity-lean/tests/fullscope-20261104/vo1/delivery/cache-packet.tar.zst`.
The host receipt file was not independently opened on this VM; the coordinator message
supplied in the user turn is the receipt source. Machine-readable record:
`tests/fullscope-20261104/vo1/evidence/h41-cache-receipt.json`.

H41 amends H35: leave verified packs on the VM; the coordinator pulls them;
**never run ship-cache.sh on a VM**. New packs remain coordinator-pending until
receipt. This pack is coordinator-received. Earlier sealed handoffs retain
historical pending status; this update supersedes that status without rewriting
the old seals or claiming any additional proof/build gate passed.

Safely fetched origin/master at 1d14f57a3a048bb1c1969c4c2c958d010ab84cb5;
no reset, checkout replacement, merge or publication. No X01 D6 contract,
compiler adapter or VO1 registration was published there. New VS4
Semantics/Nondeterminism modules are present remotely, but Source.lean explicitly
has readsD1=false and leaves D1 integration to X01/X03/X07. They do not discharge
the pending full-scope D6 binding. The branch and all prior owned source remain
unchanged apart from this documentation/receipt update. All O01/O02/O03 proof,
benchmark, witness and integrated validation obligations listed above remain open;
cache delivery alone does not establish readiness.


H41 documentation checks: JSON parse/path validation and git diff --check pass.
Separate read-only finder/skeptic reviews found no confirmed defect. Both
confirmed receipt attribution, unchanged pack hash/size, retained historical
seals and explicit unfinished queue; skeptic also verified the original checksum
manifest unchanged. No Lean/server/build was run for this documentation-only
update and no historical proof result was promoted to a new gate PASS.


## Published integration adoption — 2026-11-05

Published master: 8495f1deb0a95dd6b9301822d8649ab76b217681.
Prior owned head: edb08f9bc3b64b3ac749b390b1dd7763211d03bb.
Adopted by non-destructive merge: 240c8daf31b03cad8adebff7b491db734f429c64.
Original base/branch are unchanged; all evidence and H41-received packs retained.
No reset, replacement goal/VM, push or default-branch merge. Packet scope:
docs/feature-work/integration-20261105-checkpoints.md and its vo1/v09/vy3 notes.
The four optimizer module blobs exactly match da915469; publication is a bounded
framework increment, not whole-lane completion or D6 certification.

### Resolved and retained boundaries

Generated Solidity.lean imports and compiler-transport module-map rows are now
published. Local registration/map/orphan checks pass; orphan checker reports
3907 reachable, zero orphaned. CORE enumeration is still absent for optimizer
modules in scripts/check-layers.mjs (COORD-owned). A stricter supplementary
read-only run adds those four names to CORE only in memory, retaining every
original forbidden pattern: 632 core modules, zero elaborator/parser paths.
The ordinary checker covers 628 registered modules. Neither its success nor the
supplementary control edits or discharges the outstanding central registration.
Exact command and static results: evidence/integrated-static.json.

V09 ReturnedStorageCapture.readback retains symbolic PathSlot and guarded
successful compilation; it does not yield actual numeric slots, bytes or gas.
VY3 FramedWordLowering gives real successful selected closed-numeric-run reflection,
explicitly not Source/G24/native/gas/capacity/physical-view adequacy. Neither is the
requested optimizer adapter. Roadmap.Contracts and Evm.Compiler interfaces used
by VO1 remain unchanged. The coordinator explicitly reports VX1 H38 awaiting
Source and EVM/resource reviews before freeze. No owner stub or D6 relation was
invented; original owner requests and full-scope premises remain in force.

### Local integrated checks and resource stop

Runtime/KeySort revalidation passes: Lean 4.24.0 at 797c613, Lake 5.0.0-src+797c613;
377 parsed taclets and 131 read-bearing annotations, table matches. This was
measured in the verified 12GiB/no-swap container, explicit serial arguments,
4GiB reserve, unchanged command/group/aggregate budgets. Runtime receipt wall
1.910791s, sampled aggregate RSS 55148544, cgroup peak 30121984 bytes.

Owned import-closure build and per-file MCP pass on the merged tree; wall
3.473579s, sampled aggregate RSS 922025984, cgroup peak 460918784 bytes, five samples,
source fingerprints unchanged, owned-container cleanup verified. Axiom inventory
remains unchanged: framework/control theorems axiom-free, beforeCompilation only
propext from the existing Roadmap composition. Static trust passes for 3923 sources,
287 inventoried sites, zero findings. No inference of global kernel audit PASS.

Required ./run-lean.sh now passes layer/registration prechecks and enters the
build. It rebuilds a roughly 2600-target closure locally rather than completing
warm. The unchanged inner timeout stops it: child/runner exit124, wall 291.480437s,
sampled aggregate RSS 1718996992, cgroup memory peak 1875193856 bytes, 561 samples,
cleanup verified, no source mutation. No compiler .olean was present before the
attempt; H21 shipping notice alone is not cache freshness. Preserve every partial
artifact, trace, old seal and uncertain receipt. This is a TIMEOUT, not PASS;
remaining full build/axiom/native/semantic/final gates remain OPEN. Do not restart
an unbounded whole build or lift guard. Request actual VO1 target outcome/cache
receipt for sched-20261105T0200Z; split serial validation if caches remain missing.
Actual commands/exit/wall/RSS/hashes are in integrated-runtime.json,
integrated-owned.json and integrated-full.json. Initial historical missing-wall
and cache-provenance limitations remain UNVERIFIABLE, not reconstructed.

The owned alternate runtime TOML now gives every library/executable explicit-j1,
including executable targets previously reached only by final gates. Tracked
lakefile and producer sources were not changed. No heartbeat or proof limit rose.

### Export preservation repair and reviews

The existing exporter checked archive existence after writing mapping/manifest,
which could corrupt a historical seal on rerun. It now rejects nonempty outputs
before writes, permits only a fresh direct owned-delivery subdirectory, rejects
escaping/symlink destinations, records incomplete state for failures, checks all
required trace output artifacts and input mappings, and labels new exports
coordinator-pending. Old H41-received pack/metadata/checksums are unchanged.
Fresh invocation: python3 tests/fullscope-20261104/vo1/export-cache.py
  tests/fullscope-20261104/vo1/delivery/<fresh-name>.

Separate read-only finder/skeptic reviews confirmed integration boundaries and
found the exporter defects; both source repairs were reviewed. First negative
control harness held the writer lock around the self-locking exporter, so it
exercised only lock contention; retained evidence is NOT a guard test PASS.
Corrected controls release that parent lock, assert exact nonempty/escape refusal
messages, and verify historical hashes unchanged. Both reviewers confirm intended
guards exercised and no residual control finding. Review evidence:
integrated-reviews.md and export-preservation-controls-guards.json.

### Current queue and handoff

O01 framework publication, composition-law backfill and generic controls remain
checked, with local post-integration focused revalidation. Full O01 remains
BLOCKED on frozen D6/actual-artifact API, real compiler/public adapters,
nontrivial semantic witnesses, current compiler gas/code-size benchmarks, CORE
registration and timeout/cache-dependent full/integrated/V16 gates. O02's six
value-pass obligations and O03's inlining/CSE/load-store/LICM/pruning obligations
remain OPEN under the required sequential ordering. X06 aliasing remains needed.
No independent semantic backfill was invented around an unavailable contract.
H41 receipt for the old pack remains satisfied; any fresh integrated own-closure
pack is a separate coordinator-pending export, with exact path/hash in its
manifest and versioned handoff. It is not a full-master cache or build PASS.
Stub source is published at 8495f1de and byte-identical to original 4447817d; no
explicit VO2/VT relay receipt has been supplied, so retain relay request.


Final normalized-config focused check also passes (integrated-final-config.json):
child/runner0, wall5.603526s, sampled aggregate RSS896647168, cgroup432697344
bytes, nine samples, unchanged fingerprints and verified cleanup. The removed
TOML trailing blank line is parsed-config identical (runtime-config-format.json).
Final separate read-only finder/skeptic ledger reviews found no overclaim and
confirmed timeout/full-scope boundaries. Finder noted compound bash command
lists should use bash -euc or && in future so an early failure cannot be masked;
current logs explicitly show both build success and zero diagnostics, so no
existing failure is promoted. Full/integrated validation remains OPEN.


## Follow-on publication adoption — 2026-11-05

Authorized publication f77cf60d3cea8f7f1db8db29cc027532b0cd3fce includes
8495f1deb0a95dd6b9301822d8649ab76b217681 (ancestry checked). Adopted on the
same owned branch by merge 62d8b0de368b515fab391757abb65dc817b65a0e, preserving
prior head cea4fb438ee52ec994c14c32f3d699b56932b0fe and every old seal/pack.
Exact packet scope: integration-20261105-deferred.md and
integration-20261105-checkpoints.md.
No reset, goal creation, push, owner source edit or default-branch merge.

All four optimizer modules, their 20-module local import closure, current compiler
and Roadmap contract interfaces, central CORE list and owned runtime config are
unchanged. Type grammar adds bounded parser results; Shared.Intrinsic constructs
relative obligations with producer callbacks/refusals retained; uniqueness adds
only Statement target, not its proof; StorageOnlyHavoc derives typed formulas,
not ExtCall execution, physical aliasing or Source/native adequacy. No O01 blocker
is discharged. No H16 Source or frozen Core ExtCall edit by this lane.

New contextual-equivalence modules are useful generic infrastructure, but
CtxEquiv.Unify explicitly labels its Preserves stub restricted/noncompositional
and omits D1 actual artifact/oracle binding pending X01. Current observations
omit logs/required physical observations. It cannot replace approved frozen D6.
Both independent read-only reviewers confirm this boundary. The producer prose
claiming Optimizer/** is not on master is stale after 8495 publication; request
producer/coordinator documentation reconciliation, without editing that file or
using the stale comment as an availability verdict.

Fail-fast bounded followon-focused check passes: Lean 4.24.0 at 797c613,
Lake 5.0.0-src+797c613; owned closure build successful; KeySort 377 taclets/131
annotations matched; MCP 0 errors. Wall 3.960751s, sampled aggregate RSS 964988928,
cgroup peak 490659840 bytes, 5 samples, unchanged source fingerprints and verified
cleanup. Runtime is still 12GiB/no-swap, LEAN_NUM_THREADS=1/-j1, 4GiB reserve and
unchanged time budgets. Axiom output remains unchanged. Receipt contains exact
commands and source hashes; no global audit inferred.

Local register/map checks pass; ordinary layer checker 636 modules/0 forbidden
paths (still excludes Optimizer); orphan check 3922 reachable/0 orphans;
static trust 3938 sources, 287 inventoried sites, 0 findings. Results are in
followon-static.json. Source/config applicability of the existing verified
2275ba9b... packet: all 27 exported source/config rows match; its source head
remains cea4fb43, not relabelled to the new merge. No new owned proof artifact
requires another duplicate export. Packet remains coordinator-pending under H41;
the earlier f84ba52f... packet stays coordinator-received and unchanged.
Neither source applicability nor publication notice proves H21 full-cache freshness.

The earlier full gate timeout 124 on the 8495 adoption tree remains retained
evidence: its actual checked HEAD was 240c8daf31b03cad8adebff7b491db734f429c64,
not the publication commit itself. Current full
validation remains OPEN. No further identical cold whole-build attempt was made
without a confirmed VO1 H21 cache outcome or ready dependency. The coordinator
reports 49 cache successes, 1 capacity skip and 5 failures under H30; VO1's exact
target receipt is not inferred from aggregate counts. Request actual per-target
receipt, retain partial artifacts and use bounded split validation where needed.
No resource stop is marked PASS and no cap/heartbeat/statement was changed.

Queue unchanged: O01 concrete D6/certificates/adapters/baselines/nontrivial
semantic witnesses/CORE and final gates open; O02 all value passes and O03 all
structural passes open in original order; X06 alias-dependent work still awaits
owner facts. Independent composition/negative/framework backfill remains checked.
No new interface or semantic backfill is invented around withheld VX1 H38.
Separate finder/skeptic reviews were read-only, no Lean/server, and found no
new VO1 unblocking API; exact review record: evidence/followon-reviews.md.

Final read-only ledger reviews confirm metric/scope/cache claims. Skeptic requested
clarifying historical timeout provenance: actual checked HEAD 240c8daf adopted
published 8495, rather than a run directly on 8495. Wording corrected above;
receipts remain unchanged. No final gate or readiness claim added.


## 0840Z publication adoption and interpreter fixture backfill — 2026-11-05

Published 9584f9e7df09f638d9e0cb8930501d1660aa4b2f includes prior f77cf60;
ancestry verified. Prior owned head 93abcb01754a13d01abeae6498eb21a338f68231
preserved by merge ddbf9b7752b9a9bc4aadf0dfb198ae192b0f58b2. Same branch/VM,
no reset, new goal, protected owner edit, default-branch merge or push. Scope:
integration-20261105T0840Z.md and exact per-lane packets. Optimizer modules,
Compiler/Roadmap interfaces and CORE enumeration are unchanged.

Separate read-only finder/skeptic reviews confirm no semantic dependency unblock:
V09 ValueReflection reflects an actual successful selected value run under its
full state representation; BitwiseValueContext retains its guards. VY3
FramedControl composes existing successful numeric-stack certificates, not
failure/divergence/physical/native adequacy. V16 source-size and intrinsic revert
consumers do not give target panic bytes or Source/Osaka completeness. VT Dialect
is arity-indexed syntax/compiler metadata, not authenticated execution/layout/gas.
H38 owner-review hold remains. No producer stub or partial relation replaces D6.

### Actual integrated gates and cache progress

adoption0840-focused passes: Lean 4.24.0/Lake 5.0.0-src+797c613, owned build/MCP 0
errors, KeySort 377/131 match; wall 3.433050s, sampled aggregate RSS 955523072,
cgroup 492208128 bytes, 5 samples, source unchanged, cleanup verified.
Local root/map checks pass; orphan check 3994 reachable/0 orphans. Static trust
4010 sources/287 sites/0 findings. Axiom pin inventory 7925 theorems, 0 errors and
0 unrecorded changes; no global trust pin was edited by VO1.

Unlike the earlier cache state, measured local cache before retry was 7.3GiB and
4533 mapping lines. This justified one fresh bounded full attempt, not a cache-
freshness claim from publication. It really fetched artifacts. Full attempt at
actual HEAD ddbf9b77 ends 124 after 291.718066s, sampled aggregate RSS 1442230272,
cgroup 1299464192, 561 samples; 612 fetched log lines/143 built log lines. Required
library-only prerequisite was then split off with inner 180s: ends 124 after
181.519842s, sampled aggregate RSS 1864445952, cgroup 1384099840, 348 samples;
849 fetched/130 built log lines. Counts are log lines, not unique proof modules.
Both verify unchanged sources and owned-container cleanup; every restored/built
artifact is retained. No guard, swap, heartbeat or aggregate budget was raised.
Neither timeout is PASS. The one extra 180s prerequisite is consumed; further
validation needs finer groups/cache outcomes, not a longer retry. Exact receipts
and progress counts: adoption0840-full/library JSON and validation-progress.json.
Planned unexecuted split targets: tests/fullscope-20261104/vo1/remaining-validation-plan.md.
Full/global transitive audits/examples/native/final V16 validation remain OPEN.

### New assigned interpreter-backed fixture controls

Owned tests/fullscope-20261104/vo1/ValueValidatorControls.lean reuses existing
intrinsic Val/Prog/State and actual interpreter definitions, not a new IR.
Its exact test relation is SameResultAt state a b := a.evalT state=b.evalT state.
validatorAt state : Validator (SameResultAt state) constructively decides that
one supplied state's complete typed result, including halt tags. It is NOT a
whole-program/environment/D6 validator. No state domain or observation clause of
a public theorem was restricted. No O02 pass implementation is claimed.

Universal-state actual arithmetic result: addition.evalT state=.ok(uintOfNat 5).
Accepting control compares typed 2+3 with 5; negative control rejects 4; guarded
proposal fallback returns the exact original expression. An inhabited witness
uses State.init StandardExample in the empty local context. Actual lowering
program .cons (.assert false) .nil runs to .error.panic and cannot equal skip.
Separate result-token equality rejects Panic vs a successful zero. This does
not establish checked-overflow Panic preservation, panic-code/byte correspondence,
whole-session observations, physical-layout correctness, gas or a cost claim.
All those relevant O01/O02 obligations remain open.

Initial MCP failed because the existing Except result had no suitable automatic
DecidableEq instance; no verdict was changed. Added a private constructive instance in the owned fixture
with parameter-only Except cases (G0 permitted), no Classical.decEq or new axiom.
Retain the original failure. Fixed and final MCP checks pass. Final kernel
per-file command is repository-approved lake env lean --tstack=131072 -j1;
wall 2.392422s, sampled aggregate RSS 632557568, cgroup 137981952, 2 samples,
source stable/cleanup verified. Final MCP wall 4.456803s, RSS 1110409216,
cgroup 615727104, 6 samples. Exact logs/receipts retain commands and hashes.

Transitive axiom output covers twelve declarations/instance. Constructive result
comparison uses no axioms; eleven evaluator-backed declarations inherit only
propext/Classical.choice/Quot.sound from the existing interpreter. No new axioms,
sorry, unallowed native_decide or heartbeat increase. Original pure framework
axiom sets remain unchanged. Inventory: value-controls-axioms.json.
Both independent read-only fixture reviews find no defect and confirm the
per-state/actual-assert boundaries. These are real nontrivial existing-IR fixture
witnesses; they do NOT close the final D6 pass-preservation witness requirement.

### Fresh cache scope, reviews and current queue

Exporter now includes this per-file fixture source, actual passing kernel receipt
and exact log, and its imported dependency closure. It explicitly claims no
fixture .olean. It requires fixture/runtime/TOML/toolchain identities in the
receipt, verifies current Lean/config inputs and retained log digest, then keeps
existing full artifact/mapping completeness checks. Both read-only reviewers
identified missing-key/log-identity enforcement; fixed and re-reviewed. No old
pack/manifest/seal is overwritten. A new packet must use a fresh directory and remain
coordinator-pending under H41, never VM ship-cache. Actual hash/path/status will be
in the versioned manifest/handoff after successful export and verification; full-cache and build PASS are not implied.

Current queue accounting: published conditional interface and composition laws
remain checked; scalar and now actual interpreter-backed positive/negative/
inhabited/Panic fixture backfill are checked. O01 concrete frozen D6, real
compiler/public adapters, code-size/Osaka gas baselines, full D6 semantic
witnesses, CORE enumeration and final/integrated gates remain OPEN. O02 folding/
propagation preserving Panic, copy propagation, solc-rule simplification,
dead-code/unused-variable elimination all remain OPEN in original order.
O03 internal inlining/CSE/redundant load-store/LICM/function pruning all remain
OPEN; X06 aliasing facts still required. New producer increments were reused by
import/inspection, never reimplemented or assumed complete. H38/VY5 owner holds
remain unchanged; no exclusion, premise, observation or expected verdict weakened.

Backfill-accounting correction: earlier statements that no independent semantic
fixture work was available are superseded by this checkpoint. Interpreter-backed
controls did not require inventing D6 and are now implemented/checked. They still
do not discharge full D6 optimization witnesses. Composition/negative/inhabited
fixture backfill is accounted for; physical artifact/gas baseline work and final
pass certificates remain producer-dependent. No whole assignment completion.

The fixture also instantiates Preserves for any guarded typed expression proposal
at the explicit state (checked_proposal_preserves_at), and composes two such
proposals using real evaluator-result equality (sequential_preserves_at). These
are state-indexed framework backfill laws, not frozen D6 or implemented O02 passes.
Fresh fixture-cache export is planned after the reviewed source checkpoint; its
actual path/hash will be recorded only after export and archive verification.

Final relation-law evidence is value-controls-relations-mcp/kernel (both pass).
Initial implicit relation inference selected syntax equality instead of the
specified SameResultAt and failed; explicit Related arguments fix inference
without changing either theorem statement. All failed diagnostics/kernel logs
remain failures, never used as passing axiom inventory. Current twelve reports
are taken only from the final passing kernel log; final reviews confirm scope.


## 1200Z publication adoption and Yul fixture backfill — 2026-11-05

Published b86ae4568cef6d6226f4d170360bbb089debe3fb includes 9584f9e7;
ancestry verified. Prior owned head 18bd7e045c1ebbbcdab6eca4036f8c060a486409
is preserved by adoption merge 787b6430362ed37ea4e06a0edd5c29cfa1fe261c.
Same original VM/branch; no reset/new goal/push/default-branch merge or protected
H16 Source/frozen ExtCall edit. Exact packet scope is
integration-20261105T1200Z.md and its per-lane documents.

Read-only finder/skeptic reviews confirm the four optimizer modules and 20-module
local import closure, current Compiler/Roadmap contracts and CORE enumeration
are unchanged. New MemoryScopeBoundary/Allocation preserve existing emitted
code, scope/drop representation and allocation count. Allocation 1 is NOT Osaka
gas. FramedBranch transports guarded numeric branch tails under existing arm
certificates; condition compilation/Source-G24/native/resource adequacy remain
open. VT DataRef/DataTable resolves supplied byte intervals/labels, not compiler
assembly authentication or actual output-layout provenance. V16 keeps intrinsic
and physical frames separate. No D6/physical gas/adapter/X06 unblock is inferred.

Current bounded focused check passes (adoption1200-focused): runtime versions,
original framework, KeySort 377/131 and Value fixture MCP 0; wall 4.508755s,
sampled RSS 1105289216,cgroup 611176448, 6 samples; source stable/cleanup verified.
Static root/map checks pass; 4045 reachable/0 orphans; trust 4061 sources/287 sites/
0 findings; 7990 axiom pins/0 errors/0 drift. These are not global kernel-audit PASS.
Current library split gate reuses restored artifacts but times out 124 after
290.747725s, RSS 2266918912,cgroup 1987284992, 560 samples, source unchanged and
cleanup verified. Source progress is retained; no cap or budget raised. Earlier
full/library timeouts and all failures remain OPEN. Publication's combined gate
receipt is coordinator evidence, not completion of VO1's local whole-lane gates.

### Real typed Yul branch/continuation controls

Owned YulValidatorControls.lean imports the owner's ClosedRun interpreter and
existing original intrinsic syntax; no evaluator or producer interface copied.
branchProgram condition : Yul.Stmt [] [] ⟨true,false⟩ 1 is an if/leave followed by
an assignment to its sole initialized local. Existing erased effect-profile
proofs justify this chosen concrete example only, not admission or a new compiler
filter. Word 0 guard executes assignment 7/normal; Word 1 leaves with local 0 and
nonnormal flow. Fuel 0 gives unfinished horizon None, not divergence or gas.
An inhabited Word 0 witness reaches a real result. Actual erasedProgram retains
guard 1 but changes leave to skip; its run writes 7, and actual_erase_rejected
checks that real bad AST candidate's result against the original. Positive and
negative result-level equality checks also distinguish changed guards and dropped
results. Observation projects the sole local and isNormal; no full-world/D6
program validator, optimizer pass, cost claim or source-admission proof follows.

MCP checks pass. Lake supplied with Lean 4.24 requires the file command
lake lean FILE -- --tstack=131072 -j1; the older flag-first documented form fails
with unknown --tstack and is retained as failed CLI evidence. lake help lean
supplied the actual usage. Fetched .olean artifacts may stay in the content-
addressed cache, with importArts in setup JSON; absence of a projected local
.olean is NOT a cache-freshness verdict. Cache-aware file checking is used.
The ClosedRun prerequisite child completed/fetched, but its wrapper recorded
zero RSS samples and therefore FAILED its metric guard. Retain that result;
subsequent MCP/kernel checks provide measured evidence, not a rewritten PASS.

Final Yul kernel check yul-controls-1200-kernel passes: wall 2.394102s,
RSS 634990592,cgroup 148324352, 2 samples. MCP erasure check passes: wall 3.952326s,
RSS 1024688128,cgroup 538656768, 5 samples. Twelve actual axiom reports: profiles
use propext; resultValidator uses none; interpreter-backed observations use only
propext/Quot.sound. No new axiom/sorry/native_decide or heartbeat change.
Current Value controls rechecked with cache-aware file command: wall 2.390629s,
RSS 648380416,cgroup 151207936, 2 samples; same 12 reports as before (private Eq
none, other 11 only inherited standard evaluator axioms). Both source-stable and
cleanup verified. Exact commands/outputs/source identities are retained.

### Cache extension, reviews and remaining queue

Fresh exporter scope now explicitly covers BOTH fixtures, each with its own
current kernel receipt, required fixture/runtime/TOML/toolchain identities,
matched log SHA and imported dependency traversal. Existing nonempty/escape and
artifact/mapping completeness guards remain. No fixture olean, full-build or
delivery claim. Separate read-only reviews find no defect in either the Yul
controls or the multi-fixture provenance extension. Actual fresh packet path/hash
will be recorded only after export and archive verification; H41 coordinator-
pending until pulled/receipted. All old packs/seals/receipts remain unchanged.

O01 conditional framework and independent composition/negative/inhabited controls
are checked; current actual interpreter-backed witnesses now cover both lowering
and Yul. These are fixture backfill, NOT final D6 pass witnesses. Frozen H38/D6,
state-independent optimizer certificates, producer connection adapters, actual
code-size/Osaka gas benchmarks, CORE and final/global/V16 gates remain OPEN.
O02 all six value passes and O03 inlining/CSE/redundant load-store/LICM/pruning
remain OPEN in original order; X06 aliasing still required. No profile/exclusion,
observation, premise or expected verdict was weakened. No whole-lane completion.


## 1422Z adoption and finite pipeline backfill — 2026-11-05

Adopted remote-verified master 8bf8321873befa3f35ca31e97e5339a1baee93e6
through owned merge d99f88acf3007c5d0cef795c70383616d13bcbe9. Original base
and f9fee952 owned checkpoint remain ancestors; checkout was clean before fetch.
No resets, pushes, protected producer edits, generated registry edits or budget
changes. Read-only finder and skeptic inspected the new relevant producer APIs:
RawAddress supplies actual Source calldata/allocator evidence, not compiler/EVM
adequacy. TupleReturnConsumer consumes checked mixed-tuple emission and its real
returned map; automatic whole-call selection is still refused. FramedConditional
now derives successful condition and selected-arm execution under the owner's
three strong numeric certificates; Source/native/resources remain open.
CreationLibrarySpec's exact constructor-return postconditions do not supply
Source construction, installation or gas. No H38/D6, physical benchmark or X06
unblock follows. Compiler/Roadmap.Contracts and CORE enumeration are unchanged.

### Finite composition implementation and exact premises

Existing Laws.lean now defines Pass.pipeline : List (Pass P) → Pass P and
proves Pass.pipeline_append: pipeline (a ++ b) = (pipeline a).comp (pipeline b).
Preserves.pipeline requires explicit reflexivity, transitivity and
∀ pass ∈ passes, Preserves Related pass; each stage therefore covers every
intermediate input, not only the original input. guardedPipeline validates each
untrusted proposal against its current input. guardedPipeline_preserves retains
explicit reflexivity/transitivity and a Validator Related with its proved
soundness field. It adds no input-domain restriction, D6 instance or compiler
certificate. Existing binary interfaces remain unchanged. List recursion is on
a parameter-only family, with no indexed match or representation refactor.

PipelineControls.lean uses parity only as a test observation. Proposed stages
[+2,+1,×3] run 37→39→39→117: first/final accepted, middle rejected. Reversal
would give113, whole-pipeline rollback37, and admitting the mutation120.
Empty pipeline returns37. These kernel-checked executable controls test ordering
and per-stage fallback, not source/physical/D6 observations or optimization cost.
Finder initially observed commuting accepted additions could not detect reversal;
replaced final +4 with ×3, and both reviewers confirmed the correction. No other
source/helper finding. Initial implicit-relation and decidable-predicate inference
failures remain retained; explicit Related/proposition fixed them without theorem
weakening. Final changed-file MCP diagnostics report zero errors.

### Actual bounded checks and remaining gates

All Lean checks used the owned bounded.py runner, explicit -j1,
LEAN_NUM_THREADS=1, verified cgroup12884901888/no swap, 4GiB admission reserve,
source stability, sampled aggregate RSS and verified own-container cleanup.
Final focused build/MCP receipt adoption1422-focused-final: exit0,
14.877093s, peak RSS2767011840, cgroup2338680832,26 samples. Actual versions:
Lean4.24.0 (797c613), Lake5.0.0-src+797c613. Optimizer.Controls build succeeds;
KeySort parses377 taclets/131 read-bearing, table covers131, annotations match.
Sequential MCP checks of all three fixtures return zero diagnostics.

Pipeline kernel receipt adoption1422-pipeline-kernel: exit0,1.875337s,
RSS447062016,cgroup142802944,1 sample. Ten actual axiom reports:
pipeline_append uses propext; Preserves.pipeline uses none;
guardedPipeline_preserves/stages_preserve use propext/Quot.sound; validator and
five executable result controls use none. Value refreshed kernel receipt
adoption1422-value-kernel: exit0,2.391498s,RSS647901184,cgroup151257088,2 samples;
twelve original reports remain standard-only. Yul refreshed receipt
adoption1422-yul-kernel: exit0,2.416733s,RSS439656448,cgroup147730432,1 sample;
twelve original reports remain standard-only. Exact commands, source identities,
logs and inventories are committed under tests/fullscope-20261104/vo1/evidence.
Inherited AST linter replay is not a new pipeline warning.

The planned separate Evm.Compiler prerequisite USED its one180s allowance:
exit124,181.462758s,RSS1709150208,cgroup1513582592,348 samples. Actual dependency
rebuild progressed but timed out; artifacts retained, source stable, cleanup
verified. No PASS, longer retry or further prerequisite allowance is inferred.
Earlier full/library timeouts remain unresolved. Static root/map checks pass;
4090 reachable/0 orphans; trust4106 sources/287 sites/0 findings;8059 axiom pins/
0 errors/0 drift. These static checks are not global kernel-audit completion.

Exporter now covers three fixtures with their current passing kernel receipts,
matched proof/config inputs and logs. Both read-only reviews confirmed existing
non-overwrite/source/cache completeness guards remain. New packet is not a
fixture-olean, full-build or delivery claim; actual export/hash/seal will be in
the versioned delivery/adoption-1422-pipeline-20261105 handoff. H41 coordinator
pull only. Previous1200Z packet is verified at delivery/cache-1200-yul-20261105/
cache-packet.tar.zst, SHA882e73f896ad0cf02a073ab0782c8cf3d3351ab67365206abca3e7e870f121af,
coordinator-pending. All old packs/checksums/seals retained unchanged.

O01 remains PARTIAL: frozen H38/D6, state-independent actual optimizer
certificates, producer connection adapters, code-size/Osaka benchmarks, CORE
registration and full/global/final V16 checks remain OPEN. O02 all value passes
and O03 inlining/CSE/load-store elimination/LICM/pruning remain OPEN in original
order, with X06 prerequisites retained. This milestone completes independent
finite composition/negative-control backfill only; it is not checkpoint readiness
or whole-lane completion. No premises, observations, exclusions or verdicts changed.

Final ledger review correction: finder caught wrapped Value axiom output truncated in the derived JSON summary. Regenerated all34 reports with complete multiline parsing, explicit axiom arrays, full raw reports and log SHA. Complete retained kernel logs were always unchanged; no proof defect. Skeptic confirmed scope/metrics and open obligations.


## 1608Z adoption and two-state validator negative control — 2026-11-05

Remote-verified master3ad22f66d8fc6431378c22e71823436c79dede7f adopted through
owned merge ec7a937f0bdf4a0e5f48f9ee54b36c774fa5b1bd; original base and owned
91ec204e checkpoint preserved. Clean checkout before fetch; no resets or pushes.
Finder/skeptic independently reviewed relevant new producer APIs without Lean:
MemoryCallScopeBoundary retains actual code/cost/maps and explicit existing
premises. NormalFramedTransport derives numeric frame certificates from actual
normal-control derivations/emission/selection; it is not Source/failure/resource
adequacy. IRLoopPackets supplies finite successful loop traces, not termination.
MemoryLoopHorizonCostGrowth is allocation-cost monotonicity, not Osaka gas,
capacity or aliasing. No frozen H38/D6/artifact/gas/X06/optimizer-adapter unblock.
Optimizer source, Compiler/Roadmap contracts and CORE unchanged by publication.

### Actual state-dependent counterexample

ValueValidatorControls.lean adds localState(value) : State StandardExample
[.val .uint], localRead/localZero : Val StandardExample [.val .uint] .uint and
replaceLocal, a constant-zero proposal. Both state0 and state1 inhabit exactly
the same intrinsic context, using existing State.init/push and actual evalT.
Seven new kernel-checked controls prove acceptance/output0 at state0,
rejection/fallback at state1, actual result inequality at state1, then
frozen_zero_not_one and frozen_zero_not_universal. The latter is exactly:
¬ Preserves (fun a b : Val StandardExample [.val .uint] .uint =>
  ∀ state : State StandardExample [.val .uint], SameResultAt state a b)
  (validated (validatorAt (localState 0)) replaceLocal).
No extra premises. A single artifact produced using state0 fails preservation
at state1. This does not contradict the unchanged supplied-state theorem;
it rules out generalizing that limited checker to all environments. It is
negative-validator backfill, not an O02 pass or a D6/full-world counterexample.
No existing theorem, expected verdict, observation or admission profile changed.
Both reviewers found no source defect; no indexed match or evaluator copied.

### Current local evidence and committed checkpoint boundary

All heavy work serial under bounded.py: actual inner12GiB/no swap, threads1,
explicit-j1,4GiB admission reserve; source stable and own-container cleanup
verified for every pass. Environment resource probe saved separately.
adoption1608-focused passes:15.386331s,RSS2537811968,cgroup2132717568,26 samples;
Lean4.24.0 commit797c613, Lake5.0.0-src+797c613; framework build successful,
KeySort377 taclets/131 read-bearing/table131 OK; all three fixture MCP checks0.
Changed Value file first MCP:5.090063s,RSS1209962496,cgroup745512960,8 samples.
Current kernel receipts (commands/logs/source SHA in evidence/adoption1608-*):
Value2.405854s,RSS657682432,cgroup155480064,2 samples;
Yul2.400456s,RSS455778304,cgroup147988480,1 sample;
Pipeline1.873622s,RSS434311168,cgroup142778368,1 sample; all exit0.
Complete multiline inventory41 reports:19 Value,12 Yul,10 Pipeline;
seven new Value controls use inherited propext/Classical.choice/Quot.sound only.
No axiom/sorry/native_decide/heartbeat increase. Inherited AST linter replay
is not a new warning in the changed fixture.

Static registry/maps pass;4127 reachable/0 orphans;trust4143 sources/287 sites/
0 findings;8115 axiom pins/0 errors/0 drift. Static inventory is not global
kernel-audit completion. No repeated compiler prerequisite or whole-target
build attempted: the earlier180s Compiler attempt and full/library timeouts
remain open pending actual producer cache coverage/finer bounded validation.
This fixture-only change does not turn coordinator combined gates into local
whole-lane completion. Exporter only refreshes three receipt filenames; existing
source/config/log/non-overwrite/cache completeness guards retained. New packet
path/hash and seal will be in delivery/adoption-1608-two-state-20261105; H41
coordinator-pending until pulled/receipted, never VM ship-cache.sh. Previous
1422Z pack SHA c8407bbed74a1e9da661cd489342502806323264819e4f3db459d350b1e21b14
remains at delivery/cache-1422-pipeline-20261105/cache-packet.tar.zst,pending.

O01 remains PARTIAL: frozen H38/D6, actual state-independent optimizer
certificates, producer connection adapters, actual physical code-size/Osaka
benchmarks, CORE registration and full/global/final V16 gates OPEN. O02 all
value passes and O03 all structural passes OPEN in original order, retaining
X06 aliasing dependency. Ready negative-control backfill completed here; no
checkpoint readiness or whole-lane completion claimed. Proofs versus compiler/
EVM evidence remain distinct, with original premises/exclusions unchanged.


## Requested e6849d3b rebase — 2026-11-05

Fetched/verified e6849d3bdf516099d20c33d3581d523449764018 from origin/master.
Before the next checkpoint commit, rebased the nine lane commits with
`git rebase --onto e6849d3bdf516099d20c33d3581d523449764018
3ad22f66d8fc6431378c22e71823436c79dede7f` on the original branch. Clean input;
no conflicts or resets. Old full head73ccbb333f91be9f4ac75d73a8d9b26d011e89b2
is preserved at codex/solidity-fullscope-20261104/vo1-pre-rebase-e6849d3b,
and all old bundles/seals/cache packets remain unchanged. Rebased head before
this handoff is03fd071df1e24b5a74c9bf3f530619a04dc260f7. Original basee70b959b
remains an ancestor. Full nine-entry old/new commit mapping and range-diff are
in evidence/rebasee684-preservation.json. First two patches omit definitions
already on master; all four optimizer source files and all204 old lane-owned
changed paths have identical blobs at old73ccbb33 and rebased03fd071d. No
coordinator-pruned producer evidence restored. Subsequent checkpoint changes
are handoff/receipt-filename updates and fresh evidence, not proof changes.

Separate read-only finder/skeptic confirmed preservation and inspected V08/V16
producer updates. RelationalGuardSpec is populated scalar fixture transport,
not fetched EVM/gas/rollback/full admission. Creation/library relative interfaces
retain explicit producer duties and currently uninhabited admission inputs.
WorldImageAccess is supplied-image lookup, not artifact authentication or
optimizer preservation. No D6, physical gas, optimizer adapter or X06 unblock.
No protected Source/ExtCall or other producer file edited by VO1.

Focused check rebasee684-focused exit0:14.385066s,RSS2446954496,
cgroup2005364736,25 samples; actual Lean4.24.0/Lake5.0.0-src+797c613,
framework build successful, KeySort377 taclets/131 read-bearing/table131 OK,
all three fixture MCP diagnostics0. Kernel receipts all exit0:
Value2.451684s,RSS657682432,cgroup155766784,3 samples;
Yul1.889072s,RSS520343552,cgroup147763200,1 sample;
Pipeline1.881424s,RSS527364096,cgroup143003648,1 sample.
Complete41-report axiom inventory remains standard-only (19/12/10).
Heavy checks serial under verified12GiB/no swap, threads1/-j1,4GiB admission
reserve and unchanged proof/build budgets; source stable and cleanup verified.
Historical head-bound evidence is not relabelled as current evidence.

Current central static gates: root registry passes;4162 reachable/0 orphans;
trust4178 sources/287 sites/0 findings. Module-map check FAILS exit1 with27
missing rows; axiom-pin check FAILS exit1 with8599 pinned theorems,0 errors,
479 unrecorded changes. Initial tool output was truncated, so retained it as
partial initial evidence and reran only these failed read-only checks to save
complete logs in rebasee684-maps.log and rebasee684-axiom-pins.log. No inventory
`--write`, module-map or policy edit; central repairs requested from COORD.
No Optimizer/vo1 pin changes appear in the failed inventory output. These FAILS
remain blockers, not passing gates or permission to expand trust.

Cache exporter only refreshes current three receipt filenames; guards unchanged.
New source/toolchain-bound packet will be recorded in the versioned
 delivery/rebase-e684-20261105 handoff after export/verification; coordinator-
pending under H41. Never VM ship-cache.sh. Existing packs remain preserved.
O01 PARTIAL; O02/O03 OPEN/blocked in original order. Frozen H38/D6, actual
optimizer certificates/adapters, physical gas/code-size benchmarks, X06, CORE,
central map/pins repairs and full/global/final V16 validation remain OPEN.
Prior compiler/full/library timeout124 receipts remain failures; no extra
prerequisite or longer retry here. Rebase completion is not whole-lane readiness.


## H44 reviewable source/evidence split — 2026-11-05

H44 authorizes splitting the held head 94b422337839a6d1a5f725b04d5af491bdc39829 into a small source
increment and external bulk. The complete held history is preserved at
codex/solidity-fullscope-20261104/vo1-pre-h44-94b42233. The new increment is consolidated directly on already-
merged master 260441fd82852fc1c294e62f6818e15de6375ceb; original assignment base remains e70b959b.
Only Git history/index are reorganized; raw working files are not discarded,
and no goal/VM is reset. All Lean sources, typed fixture proofs, validation
scripts, runtime configuration, theorem statements, gates and budgets are
identical to the held head. No new implementation or scope is added.

All210 bulk evidence files are removed from the new Git index and ignored,
while retained at /workspace/solidity-lean/tests/fullscope-20261104/vo1/evidence.
Raw payload size: 34013785 bytes. Verified archive:
/workspace/solidity-lean/tests/fullscope-20261104/vo1/delivery/h44-split-20261105/bulk-evidence.tar.zst
Archive size: 11993397 bytes.
SHA256: d8da415a511bb278c770641e4c24b7b0b91dce475292a4f947c19363f2de9d95
External per-file manifest: /workspace/solidity-lean/tests/fullscope-20261104/vo1/delivery/h44-split-20261105/bulk-files.json.
The committed tests/fullscope-20261104/vo1/bulk-evidence.sha256 records absolute
archive/manifest paths and SHA256 values. The archive also contains MANIFEST.json
with every raw file's absolute path, byte size and SHA256, plus all210 original
files. Streaming archive verification checked211 entries; raw hashes remained
unchanged. Original reservations, failed receipts, cache packs and seals remain
preserved on this VM; historical evidence has not been reconstructed.

A fresh checkout alone lacks the bulk receipts. Verify the committed manifest
with sha256sum --check before using the archive. Restore its evidence/* members
under tests/fullscope-20261104/vo1/ before running bounded.py, mcp-check.sh,
export-cache.py or historical evidence checks. This restores the original
receipts/time reservations and prevents treating a missing archive as a fresh
proof budget. On this VM the raw paths are already present. Archive members
use evidence/<filename>; MANIFEST.json is the archive's independent file list.
Do not commit extracted data. H41 cache delivery remains a separate process.

Separate read-only finder and skeptic confirmed the classification: all bulk
changes are in evidence/; the other13 changed paths are source, docs, scripts
and necessary config. Base master has no VO1 evidence files, so exclusion adds
no upstream deletion. The final source-only increment additionally contains the
small SHA256 manifest. Source/tree/archive/index integrity checks verify the
packaging split; Lean is not rerun for this source-identical operation.
Coordinator reports the held head passed pre-gate; no new command receipt or
whole-lane gate PASS is invented from that report. Previous proofs, failures,
reviews and limitations retain their original revision bindings. O01 remains
partial and O02/O03 remain open; this packaging fix establishes no additional
D6/compiler/EVM/gas theorem and changes no premise or expected verdict.

Final read-only finder and skeptic independently verified the14-file split, unchanged source/scripts/config, both committed hashes, all210 raw files and211 archive entries. No findings; no Lean/server/builds or writes by reviewers.

## Moved lane (Claude VM) — O02 value passes checkpoint — 2026-11-05

Status lines in the sections above that say O02 is "OPEN", "not begun" or that "No
O02 pass implementation is claimed" are historical (Codex VM) and superseded by this
section and the ones after it.

Batch moved4-20261105, branch `cloud/moved4-20261105/vo1-optimizer`, started from
`origin/cloud/vo1-optimizer-move` (cdfa3601) merged with origin/master (aec9adf1,
already contained). The Codex-VM receipts, `bounded.py`/`bin/lake`/`runtime.toml`
tooling and the "restore evidence before bounded.py" instruction above apply only to
that VM and are not used or cited here; every gate below is fresh. No published
signature of `Optimizer/Pass.lean` changed; O02 only adds modules.

### Delivered passes (all over the existing intrinsic `Val C Γ p` / `Prog C Γ Δ`)

| Pass | Module | Headline theorem (exact) |
|---|---|---|
| constant folding | `Optimizer/ConstFold.lean` | `Val.cfold_evalT σ v : v.cfold.evalT σ = v.evalT σ` |
| fold + dead branches | `Optimizer/StmtFold.lean` | `Prog.cfold_runC P : Prog.runC (Prog.cfold P) = Prog.runC P` |
| any proved expression pass, lifted | `Optimizer/StmtFold.lean` | `Prog.vopt_runC V P : Prog.runC (Prog.vopt V P) = Prog.runC P` |
| constant + copy propagation | `Optimizer/Propagate.lean` | `Prog.cprop_runC F P σ (hF : F.Holds σ) : Prog.runC (Prog.cprop F P) σ = Prog.runC P σ`; `Prog.cprop_empty_runC P` (no premise) |
| expression simplification | `Optimizer/Simplify.lean` | `Val.simp_evalT σ v`; `Prog.simplify_runC P` |
| unused-variable elimination | `Optimizer/UnusedVar.lean` | `blockDecl_runC … (hi : initSafe init = true) … (hw : P'.wk (.drop .refl) = ⟨Γ₁, h', P⟩)`; `Prog.uve_runC P` (no premise) |

O01 instances (`Preserves SameRun _`): `cfold_preserves`, `vopt_preserves`,
`cprop_preserves`, `uve_preserves`, where `SameRun P Q := Prog.runC P = Prog.runC Q`
(equality of the typed run as a function of the typed state: value or halt kind,
final storage, heap, ledger, locals and heap growth). The pipeline
`[cprop, simplify, cfold, uve]` is certified in `O02Controls.o02_pipeline_preserves`
through the unchanged `Preserves.pipeline` (O01 laws). Only the D6 binding remains
X01's: `SameRun` is stronger than "every observation except gas values" because the
lowering IR has no gas observation (D1 artifact/gas oracle not yet frozen), so no
gas value is equated or fabricated.

### Exact behaviour and boundaries

- Failures are kept, never folded: `ofOpt none` (checked overflow outside
  `checked { }`, zero divisor, out-of-range conversion; a revert in this model, see
  solc-alignment "Checked arithmetic") leaves the node as written; `assert(false)`
  (Panic) and `require(false)` are never dropped; inside `checked { }` the elaborator's
  range `assert`s (`Stmt.guard`) are ordinary `assert`s and keep their Panic. Controls:
  `overflow_kept`, `overflow_reverts`, `assert_folded`, `assert_panics`.
- Short circuit: a literal left operand that decides `&&`/`||` drops the right operand
  exactly when `BinOp.shortT` does.
- Dead code: `if (lit)` becomes the block of the branch taken; `require(true);`,
  `assert(true);`, `while (false) …` are dropped from the sequence (with the loop's
  `LoopAnn`, which the run does not read; a verification layer reading annotations of
  an optimized program would see none for that loop). No pass recurses into `call`,
  `callRec`, `callReceiver`, `tryCall` or `catchData` bodies.
- Positions rewritten: local assignments, local declarations, `require`, `assert`,
  `transfer`/`send` operands, `if`/`while` conditions, recursively in branches,
  blocks and loop bodies. Not rewritten (left exactly as written, so trivially
  preserved): storage/memory path index expressions, `opAssign`/`incDec`, storage
  writes, calls and their bodies, `try`/`catch`, receiver calls, revert data.
- Propagation records a fact only from `x = e;` / `T x = e;` whose propagated and
  folded right side is a literal or a local (never an environment read); assigning a
  local kills the fact for it and every fact reading it; facts survive local
  assignments (except killed ones), declarations, `require` and `assert`; other
  statements reset to no facts; `transfer`/`send` operands are folded but not
  propagated into; branches,
  blocks and loop exits reset to no facts; loop bodies and conditions start with no
  facts. Controls: `prop_constant`, `prop_copy`, `prop_killed`.
- Simplifier (solc `RuleList.h` reference): `X+0`, `0+X`, `X-0`, `X*1`, `1*X`, `X/1`
  at `uint`/`int`; `X&&true`, `true&&X`, `X||false`, `false||X`; `s-s → 0`,
  `s==s → true`, `s!=s → false` only for a simple `s`. Not implemented: `X*0 → 0`
  (for any `X`; for a compound `X` it would hide a halt), `X-X → 0` for a compound `X`
  (same reason), bitwise and shift identities, and the wrapping-arithmetic rules
  stated modulo `2^256`. Negative controls:
  `simp_sub_overflow_kept`, `unrestricted_sub_wrong`, `simp_mul_zero_kept`,
  `unrestricted_mul_wrong`.
- Unused variables: a declaration that is the block's *first statement*, whose
  initialiser is absent or simple and whose remaining body strengthens (`Prog.str?`, fragment: local
  assignment/declaration, `require`, `assert`, `revert`, `assume(false)`, `transfer`,
  `if`, blocks, over path-free values) is removed. Iterating the pass removes a run of leading unused declarations
  only; a declaration after another kept statement, a declaration at a body's top
  level outside a block (its removal would change the context type), an unused but
  assigned local (`x = …` does not strengthen), and any block whose rest uses storage
  or memory paths, `send`, a loop or a call are left as written. Only an explicit `{ … }` block is a candidate: `if` branches, loop
  bodies, function bodies and the top-level program are not (an `if (lit)` becomes a
  block under `Prog.cfold` first). Names: `ConstFold.Prog.str?_wk`,
  `ConstFold.Prog.uve_runC`, `ConstFold.Prog.cprop_runC` live in namespace
  `Solidity.Optimizer.ConstFold`. A failing initialiser is kept (`failing_init_kept`,
  `failing_init_drop_wrong`). Semantics reuse the existing `Prog.run_wk` and
  `TWkRel.drop` unchanged.

Controls: `tests/fullscope-20261104/vo1/O02Controls.lean` (not imported by the
generated roots; checked by per-file Lean diagnostics). Axioms of every headline
theorem and control: `propext`, `Classical.choice`, `Quot.sound` only (the classical
ones come through the interpreter's `TLoop.run`); no `sorry`, no `native_decide`, no
heartbeat option.

Registration: the five modules are in the generated `Solidity.lean`
(`register.sh`), with rows in `docs/module-map/compiler-transport.d/vo1-optimizer.md`
(`fragments.sh`). `scripts/check-layers.mjs`: 857 core modules, 0 reach the
elaborator (the Optimizer CORE enumeration stays COORD's, unchanged).

### Composition with `Compilation.correct` (caveat)

`SameRun` is equality of `Prog.runC`; `Compilation.correct` (`Evm/Compiler.lean`) is
stated over `P.run` (the recursor form; rewrite with `Prog.runR_eq`) and its
agreement premise reads syntactic properties of the program (`Prog.asserts`,
`Evm.Prog.pays`, the `Evm.Prog.pushes` frame). A pass can change those
(`if (false) { push }` changes `pushes`; dropping `assert(true)` changes `asserts`),
and compilation is partial (`Option`), with no proof here that optimizer output stays
in the compiled fragment. So composing an O02 pass before the compiler gives the
compiler theorem about the optimized program, not literally the original's
statement; the bridge (coverage plus the agreement premises over `SameRun`) is part
of the open O01 composition item and needs the V09/VY3 adapters. `SameRun` also fixes
heap typing/contents and final locals, which is exact for O02 but stronger than D6
for future memory passes (dead allocation, memory dead stores) in O03.

### Remaining O02 obligations

- D6 binding (X01) and D1 artifact/gas oracle: open, waiting on X01.
- Optimizing inside storage/memory index expressions, compound assignments and call
  arguments, and recursing into call/try/catch bodies: not done (left as written);
  these need path-level congruences.
- Dead-code elimination beyond literal conditions: code after `revert`/`assert(false)`,
  dead stores and unused pure assignments are not removed.
- solc rules not implemented (valid under checked semantics): bitwise/shift
  identities, `X%1`, `X**0`, `X^X`, `X&X`, `!!X` (see the Simplify update below for
  the ones added later).
- Unused-variable elimination outside the strengthening fragment and of non-first
  declarations within one pass: not done.

### O02 checkpoint gates (fresh, this VM) — 2026-11-06

Lean 4.24.0 (elan toolchain `leanprover--lean4---v4.24.0`), 4 cores, 15 GB.

- `gate.sh per-file` over all lane files at 23f40bc5: PASS for `Optimizer/{Pass,Laws,
  ConstFold,StmtFold,Propagate,Simplify,UnusedVar,CSE,RoadmapComposition,Controls}.lean`
  and `tests/fullscope-20261104/vo1/{O02Controls,O03Controls,PipelineControls,
  ValueValidatorControls,YulValidatorControls}.lean` (each `lake env lean FILE`,
  0 errors; 1–16 s each).
- Lean MCP diagnostics: no errors or warnings on every touched file.
- `#print axioms` (in the control files): every headline theorem uses only `propext`,
  `Classical.choice`, `Quot.sound` (`Val.pbeq_eq`: `propext`, `Quot.sound`).
- `register.sh --check`, `fragments.sh --check`: PASS. `check-layers.mjs`: 857 core
  modules, 0 reach the elaborator or the checked parser adapters.
- `gate.sh checkpoint` (`lake build Solidity`, cold): NOT COMPLETED. The cold library
  build is 5412 jobs on a mostly sequential chain (single modules up to 410 s, e.g.
  `Backend/Scalar/PowerBounds`); after ~65 min it had built ~280 modules, so it was
  stopped. No master Lake artifacts were present in this VM's cache. `gate.sh touched`
  expands to the same full build because the generated root changed. This is a
  resource stop, recorded as open: the integrated build needs the coordinator's warm
  cache.

Reviews (separate read-only finder and skeptic, no Lean server):
- Finder: no high-severity defect; confirmed `SameRun` non-vacuous and the dead-code
  rewrites against `Run.lean`. Medium: Simplify doc implied a `s*0` rule (now
  implemented); `Stmt.uve` doc said "every block" (now "explicit blocks"). Low:
  Propagate doc ("only across require/assert") corrected; duplicate/dead tactic
  alternatives removed; unused `ofInt?_val` removed; long lines wrapped; namespace
  names now cited as `ConstFold.*`. All fixed.
- Skeptic: proofs hold; O02 not complete in the D6/compiler sense (D6 binding and
  `Compilation.correct` composition are open, waiting on X01/V09 — disclosed above);
  disclosure fixes applied for unused-variable coverage, omitted solc rules, thin
  dead-code elimination, the composition caveat (`asserts`/`pays`/`pushes`, partial
  compilation, `runR_eq`), stale status lines. Added rules `s*0`, `X**1`, `X>>0`,
  `s<s`/`s>s`/`s<=s`/`s>=s` and controls for loop propagation, `while(false)` removal,
  short circuit, a storage write left as written.

## O03 checkpoint: common-subexpression elimination — 2026-11-06

`Optimizer/CSE.lean`. After `x = e;` or `T x = e;` completes, later occurrences of `e`
are replaced by `x` while `x` and the locals `e` reads are unassigned (solc's
`CommonSubexpressionEliminator`). Theorems: `Val.pbeq_eq` (typed syntactic equality on
the pure fragment is equality, no classical decision), `Val.cse_evalT (hA : Avail.Holds A σ)`,
`ConstFold.Prog.cse_runC A P σ hA`, `ConstFold.Prog.cse_empty_runC P` (no premise),
`cse_preserves`. Entries survive local assignments only when pure and independent of
the assigned local (`Val.indep`), and survive declarations, `require`, `assert`; any
other statement or scope exit clears them; loop bodies start empty. Controls
(`O03Controls.lean`): `cse_replaced`, `cse_killed`, and the run-level negative control
`wrong_kill_differs` (the unkilled rewrite yields `1` where the program yields `8`).

O03 remaining: internal-function inlining, unused-function pruning (open, below),
redundant `sload`/`mload`/store elimination and LICM (wait for X06 aliasing facts; no
assumed facts). CSE does not look inside storage/memory reads or across calls.

CSE review (separate read-only finder+skeptic, no Lean server): no soundness defect.
Finder: the docstring did not distinguish entry creation by `x = e` (pure, independent
of `x`) from `T x = e` (any `e`; impure entries can never match since `Val.pbeq` is
`false` outside the pure fragment) — docstring fixed; `get_set_ne'`/`get_set'` copy
`RunFrame`'s lemmas to avoid importing it (kept). Skeptic: `Prog.cse_empty_runC` is
premise-free run equality; storage-read entries cannot be reused after a storage write
(storage-writing statements clear entries, and impure entries never match); coverage
gaps recorded above (no storage/memory read CSE, nothing across joins or into loops,
syntactic matching only).

## O03 checkpoint: inlining of internal calls — 2026-11-06

`Optimizer/Inline.lean`. A void internal call with value arguments,
`.call f args .none body` with `args.allVal = true`, becomes
`{ T₁ x₁ = e₁; …; Tₙ xₙ = eₙ; body' }` (`inlineBlock`), each argument read past the
parameters before it (`Val.wk (thinUnder _)`) and `body' := (body.wk (thinTop Γ ps)).2.2`.
Theorems (exact): `bindArgs_runC` (the declarations evaluate the arguments in
`Args.evalT`'s order with its halts); `inlineBlock_runC f args h body :
Stmt.runC (inlineBlock args h body) = Stmt.runC (.call f args .none body)`;
`ConstFold.Prog.inl_runC P` (no premise); `inl_preserves`. The proof reuses the
existing `Prog.run_wk`, `TWkRel.drop`, `Prog.wk_over`, `TEnv.off_wk` unchanged; the new
environment lemmas are `put_top`, `put_under`, `drop_put_top`, `off_top`,
`off_bot_inj` (an environment is determined by the list of its values).
Controls (`O03Controls.lean`): `call_inlined` (exact inlined syntax), `inlined_ok`/
`call_ok` and `inlined_reverts`/`call_reverts` on concrete states, `ret_call_kept`.

Not covered (left as written): calls with return values (`CallRet.val/rets/mem/storage`),
(storage or memory parameters: inlined since the X06 follow-up) `callRec`, receiver calls, `try` self-calls; calls
inside an inlined body are not inlined in the same pass (run it again).

### Unused-function pruning: open

In the lowering IR an internal callee has no table entry: every `Stmt.call` carries its
callee's body, so an unused internal function has no representation to prune there.
In Yul (`Stmt.functions ss bodies rest`) pruning a group that `rest` never calls needs a
strengthening of Yul syntax over `Member` indices and a fuel-shifted simulation of
`Yul.Closed.evalStmtNode` (the `functions` node consumes one fuel step), which is not
done. Open, no claim.

### Remaining O03

- Redundant `sload`/`mload`/store elimination and LICM of memory/storage reads: wait for
  X06 aliasing facts (VX4, wave B); no assumed aliasing facts.
- (Superseded by the X06 follow-up below: guarded LICM, `Prog.licm`.) LICM of pure expressions: a hoisted expression may fail when the loop runs zero
  times, so only failure-free expressions could move; not done.
- Unused-function pruning (above), inlining with return values/reference parameters.

Inlining review (separate read-only finder+skeptic, no Lean server): no defect in the
theorem; `inlineBlock_runC` is function equality with the single premise
`args.allVal = true`, halts and their order match `Args.evalT`, the caller's locals
match `leaveT`, and nothing else in `TRun.call` changes. Fixed: the module doc named
`inlineCall_runC` for the main lemma (now `inlineBlock_runC`); coverage text now says
calls inside `try`/receiver/non-inlined call bodies are not rewritten, and that only
`Stmt.runC` is preserved (the call name, and gas/code-size/stack-depth effects that
solc's inliner trades, are not modelled — the latter is a D1/D6 benchmark item).
Added controls: a two-argument call whose second argument reads the caller's local
(`two_args_inlined`, `two_args_ok`, `two_args_call_ok`) and the negative control
`wrong_inline_reverts` (an inliner without re-indexing reverts where the call succeeds).

### Inlining with one value return — 2026-11-06

`inlineBlockVal_runC f args h p r res body : Stmt.runC (inlineBlockVal args h p r res body) =
Stmt.runC (.call f args (.val p r res) body)` (premise `args.allVal = true` only). The call
`x = g(args)` (or `g(args);` with the value discarded, `res = none`) becomes
`{ params; T r; { body' } x = r; }`. It rests on the new `frame_runC`: the weakened body,
its scope ended, leaves exactly its frame's final locals on top of the caller's locals
weakened along the heap (`TEnv.append qs (drop body.ext …) (TEnv.wk … σ.env)`), proved from
`Prog.run_wk`/`TWkRel.drop` with `put_top_gen` and `off_bot_inj`. `inlineCall` now inlines
`CallRet.none` and `CallRet.val`; `Prog.inl_runC` is unchanged in statement. Controls:
`ret_call_inlined` (exact syntax), `ret_call_seven`/`ret_inlined_seven` (both leave
`a = 7` from `a = 5`), `mem_call_kept` (a memory return is left as written). Still not
inlined: several returns (`rets`), memory/storage returns, reference parameters,
`callRec`, receiver calls.

Value-return inlining review (read-only finder+skeptic): no blocking issue; statement is
`Stmt.runC` function equality with premise `args.allVal = true`; order (arguments, `T r`
default, body in an inner block, `x = r`) matches `enterT`/`take`/`leaveT`; an argument
reading the assigned caller local sees the old value in both forms. Applied: controls for
the discarded-return branch and a body reading the return default (`g2_assigned`,
`g2_call_assigned`, `g2_discarded`, `g2_call_discarded`), the negative control
`wrong_target_differs` (a wrong target index leaves `a = 5` where the call gives `7`), and
`storage_arg_kept`; `put_top_gen` documented. Not applied (optional): restating
`inlineBlock_runC` through `frame_runC`.

### O02 coverage extension — 2026-11-06

`Prog.vopt` (hence `Prog.cfold`, `Prog.simplify`) now also rewrites the value of a storage
write (`assign l (.val v)`, `push b (some (.val v))`, through `Src.vopt` and
`Src.vopt_valueT`) and the right side of `opAssign`/`pushOpAssign` (locations: see the location item below). Control: `store_folded`
(`total = 2 + 3; total += 0 + 1;` → `total = 5; total += 1;`), `store_same`.

Propagation across storage statements: facts now survive `assign`, `delete` and `pop`
(`KeepsLocals`, `keeps_assign`, `keeps_delete`, `keeps_pop`: every value local and
environment value unchanged), and the value an `assign` stores is propagated into
(`Src.opt`, `Src.opt_valueT`). `transfer`/`send` still reset facts (`selfBalance`, an
environment value, changes). Control `prop_across_store`
(`uint a = 5; total = a; uint b = a + 1;` → `total = 5; uint b = 6;`).

CSE across storage statements: pure entries (`Val.isPure`) survive `assign`, `delete`,
`pop` (`Avail.keep`, `Avail.holds_keep` via `Val.evalT_keep` and `KeepsLocals`); impure
entries (storage/memory reads) are dropped there, so a storage write never leaves a stale
storage-read entry. Control `cse_across_store`.

## Certified pipeline — 2026-11-06

`Optimizer/Pipeline.lean`: `round Γ Γ' = Pass.pipeline [Prog.inl, Prog.cprop Facts.empty,
Prog.simplify, Prog.cfold, Prog.cse [], Prog.uve]`, `Prog.optimize n` (n rounds),
`round_preserves`, `optimize_preserves`, `Prog.optimize_runC n P : Prog.runC
(Prog.optimize n P) = Prog.runC P` (no premise), all through the unchanged O01
`Preserves.pipeline`. End-to-end control `e2e_optimized`: `uint a = 2; f(a + 3);` with
`f(x) { require(x > 3); }` becomes `uint a = 2; { }` in one round (inline, propagate
`x = 5`, fold `require(5 > 3)` to `true` and drop it, remove the unused `x`).
For consumers (VO2/VT): `Prog.optimize`/`Prog.optimize_runC` are the stable entry points;
no published `Pass.lean` signature changed.

Constant folding now also folds index expressions inside storage and memory paths
(mutual `SPath/Loc/MPath/MLoc/Val.cfold` with `SPath.cfold_resolveT`,
`Loc.cfold_resolveT`, `MPath.cfold_mvalT`, `MLoc.cfold_addrT`, `Val.cfold_evalT`); the
statement of `Val.cfold_evalT` is unchanged. Control `index_folded`
(`balances[2 + 3]` → `balances[5]`). This supersedes the "storage/memory path index
expressions left as written" item for folding. Propagation and simplification fold read
paths too (`Val.opt` and `simpFoldPass` end in `Val.cfold`) but do not substitute or
simplify inside them; CSE leaves them as written.
`Prog.vopt` also rewrites the storage location of `assign`, `delete`, `push` and `pop`
(`SPath.vmap`/`Loc.vmap` with `SPath.vmap_resolveT`, `Loc.vmap_resolveT`), so folding
and simplification reach `x[e] = v`, `delete x[e]`, `x[e].push(v)` indices. Control
`delete_index_folded`. Compound-assignment receivers (`opAssign`, `pushOpAssign`),
`pushIncDec` and memory locations are still left as written.

## O02 dead code after a halting statement — 2026-11-06

`Optimizer/DeadCode.lean`. In every scope (block, `if` branch, loop body), the statements
after one that always halts (`revert`, `assume(false)`, `require(lit false)`,
`assert(lit false)`; `alwaysHalts_runC`) are removed (`Prog.cut`). Theorems: `cut_scope P σ
: scopeRun (Prog.cut P).2 σ = scopeRun P σ` (the run with the scope ended is unchanged,
the halt kept), `ConstFold.Prog.dce_runC P` (no premise), `dce_preserves`. The top-level
sequence is not cut (its output context is the program's type). `Prog.dce` is a stage of
`round` (after `Prog.cfold`). Controls: `after_halt_cut`, `after_halt_reverts`,
`halt_kept_wrong` (dropping the halting `require` itself would change the run).

Review of the storage-surviving facts/CSE entries, path folding, location rewriting and
the pipeline (read-only finder+skeptic): no soundness issue (`KeepsLocals` holds for
`assign/delete/pop` since they only replace `storage`; impure CSE entries are dropped
there; no evaluation reordering; pipeline premise-free). Doc drift fixed: StmtFold
header (locations of `assign/delete/push/pop`, receivers of compound assignments and
`pushIncDec` left as written), stale location sentences in this document, `KeepsLocals`
wording.

Dead local stores (`DeadCode.lean`): `x = e₁; x = e₂;` → `x = e₂;` when `e₁` is simple
(cannot fail) and `e₂` does not read `x`; `dseCons_runC`, `ConstFold.Prog.dse_runC` (no
premise), `dse_preserves`; a stage of `round` after `Prog.dce`. Controls:
`dead_store_removed`, `self_read_kept`, `failing_store_kept`. Storage/memory dead stores
stay with X06.

## Moved-lane handoff and queue accounting — 2026-11-06

Branch `cloud/moved4-20261105/vo1-optimizer` (Claude VM), from `cloud/vo1-optimizer-move`
cdfa3601 + origin/master aec9adf1. All work is source + kernel proofs; no compiler/EVM
evidence, no gas or code-size claims. `Optimizer/Pass.lean` signatures unchanged.

| Item | Status | Evidence |
|---|---|---|
| O01 interface, laws, controls | done (inherited) | `Pass`, `Laws`, `Controls`, test controls |
| O01 composition into `Compilation.correct`/G49 | open, waits on V09/VY3 adapters and X01 D6 | caveat section above |
| O01 code-size/gas baselines | open, waits on D1 artifact/gas oracle (machine has no gas) | — |
| O02 constant folding (Panic/revert kept) | done | `Val.cfold_evalT`, `Prog.cfold_runC` |
| O02 constant + copy propagation | done | `Prog.cprop_empty_runC` |
| O02 expression simplification (solc rules, checked-safe subset) | done (subset listed) | `Val.simp_evalT`, `Prog.simplify_runC` |
| O02 dead code (literal branches, satisfied checks, dead loops, code after halts, dead local stores) | done | `Prog.cfold_runC`, `Prog.dce_runC`, `Prog.dse_runC` |
| O02 unused-variable elimination | done (fragment: leading block declarations) | `blockDecl_runC`, `Prog.uve_runC` |
| O02 D6 binding | open, X01 | — |
| O03 inlining of internal functions | done for void and single-value returns with value arguments | `inlineBlock_runC`, `inlineBlockVal_runC`, `Prog.inl_runC` |
| O03 CSE | done (pure expressions, syntactic) | `Val.pbeq_eq`, `Prog.cse_empty_runC` |
| O03 unused-function pruning | open (no lowering-IR function table; Yul needs a fuel-shift simulation) | — |
| O03 redundant sload/mload/store elimination, LICM | done in the X06 follow-up (fragments listed there) | `Prog.rle_empty_runC`, `Prog.dstore_runC`, `Prog.licm_runC` |
| Certified pipeline | done | `Prog.optimize_runC`, `e2e_optimized` |
| Final revalidation after integrated prerequisites/V16 | open | — |

Consumers (VO2/VT): `Prog.optimize n` with `Prog.optimize_runC`, the per-pass
`*_preserves` instances of `Preserves SameRun`, and `ValPass`/`Prog.vopt_runC` for new
expression passes.

Owner requests (unchanged from the Codex handoff, still open): X01 — frozen D6 relation
and D1 artifact/gas-oracle API; V09/VY3 — `Compilation.correct` adapters covering
optimizer output (the agreement premises read `asserts`/`pays`/`pushes`); X06 — aliasing
facts; COORD — Optimizer entries in `scripts/check-layers.mjs` CORE (not edited here).

Dead-code review (read-only finder+skeptic): no soundness issue (halts are kept and carry
no state; `ite`/`loop`/`block` drop with the branch's own `Ext`, which `scopeRun` takes;
`assignLocal` targets only value locals, distinct `TEnv` slots, so no aliasing). Fixed:
coverage wording (only blocks, `if` branches and loop bodies; `revertData` not treated as
halting at first (now fixed: `revert` with data halts, `alwaysHalts_runC` covers it); `Val.indep` also rejects storage/memory reads in `e₂`); `o02_pipeline_preserves`
now includes `Prog.dce` and `Prog.dse`. Added controls `guarded_kept` (non-literal
`require` not cut), `branch_cut` (cut inside an `if` branch), `different_targets_kept`.

## Checkpoint gate at e272602b — 2026-11-06

`gate.sh checkpoint`, warm-cache resumption across three 2 h task windows (the first was
lost to a container restart; Lake kept the built modules). Final run (02:48–03:49 UTC):

- `build-touched` and `library` (`lake build Solidity`): PASS, `✔ [5414/5415] Built
  Solidity`, no build errors in any of the three logs.
- `check-trust.sh`, `check-orphans.mjs`, `check-layers.mjs`, `register.sh --check`,
  `fragments.sh --check`: PASS.
- `check-doc-paths.sh`: FAIL, not this lane. The only missing reference is in
  `docs/feature-work/after-roadmap-va1.md` (cites a Mathlib test under `Bridge/.lake`),
  a file this lane does not own or change; the other lines are `ambiguous` warnings.
- `check-axiom-pins.mjs`: FAIL on its "unrecorded changes" rule only: 0 errors,
  3735 unrecorded new pins from other lanes' merged modules, none from
  `Solidity/Optimizer/**` (no optimizer theorem appears in the output). Recording pins
  edits the shared trust pins, which this lane may not edit; left to the coordinator.

## Lane-end gate `./run-lean.sh` at 6ccdac52 — 2026-11-06

03:49–04:25 UTC, warm cache. Lake built every target, including Bridge and the solc
TestSuite (`✔ [5832/5833] Built SolkeyTestSuite`), with no Lean errors. `check-layers`,
`register.sh --check` and `fragments.sh --check` passed. The script exits 1 at its
`solkeycheck` step: "167 mismatch(es) … parsed 392 taclets, 135 read-bearing, table
covers 131". These are storage-taclet annotation rows and `save<[Struct<[..]>` tokens
in the SolKey rule table. This lane changes no `Calculus/`, `scripts/` or SolKey pin
file, so this is open for the rule-table/SolKey lanes, not for vo1.

## Follow-up 2 (H66): X06 memory optimizations — 2026-11-06

Scope approved by the user (2026-11-06). Three new modules, all over the existing
intrinsic lowering IR and the existing O01 interface (`Pass`, `Preserves SameRun`); no
signature of `Optimizer/Pass.lean` changed. "Waits for X06 aliasing facts" in the
sections above is superseded: the alias analysis below is this lane's own, proved
against the typed run, with no assumed aliasing facts.

| Pass | Module | Headline theorem (exact) | Kind |
|---|---|---|---|
| redundant load elimination | `Optimizer/Loads.lean` | `Prog.rle_empty_runC P : Prog.runC (Prog.rle [] P) = Prog.runC P`; `Prog.rle_runC E P σ (hE : LEnt.Holds E σ)` | run equality |
| dead store elimination | `Optimizer/DeadStore.lean` | `Prog.dstore_runC P : Prog.runC (Prog.dstore P) = Prog.runC P`; `sstore_dead_runC`, `mstore_dead_runC` | run equality |
| loop-invariant code motion | `Optimizer/LICM.lean` | `licm_runC a c x e rest (h : LicmOk c x e rest)`; `Prog.licm_runC P : Prog.runC (Prog.licm P) = Prog.runC P` | run equality |

All three are equalities of the typed run (value or halt kind, final storage, heap and its
typing, ledger, locals), not refinements: no pass removes a behaviour, including errors.
O01 instances: `rle_preserves`, `dstore_preserves`, `licm_preserves`.

### Redundant load elimination (`Prog.rle`)

Static loads (`Load`): a primitive state variable `v` (`.read (.root v _)`), a primitive
member `m.f` of a memory local (`.readMem (.field (.var m _) f _)`), a primitive element
`m[k]` of a memory local at a simple index. Entries `LEnt` record "load `ld` evaluates to
the simple value `s`" (invariant `LEnt.Holds`); they are created by `x = ld;`/`T x = ld;`
(holder `x`) and by `v = s;`, `m.f = s;`, `m[k] = s;` with `s` simple (store-to-load
forwarding), and a later occurrence of a recorded load in any expression position of
`x = …`, `T x = …`, `require`, `assert`, `if` conditions, storage and memory store values
is replaced by the holder.

Alias analysis (each rule proved): a local assignment kills entries whose holder or
location reads the local (`LEnt.reads`); a storage write `l = …` kills only storage
entries of the state variable `l` starts at (`Loc.root?`, `Loc.resolveT_rootName`,
`Storage.find_write_other`; a write through a storage alias kills every storage entry)
and no memory entry; a memory write kills only the memory entries it may alias
(`MLoc.apartB`, sound by `MLoc.addrT_apart` and `Heap.readAddr_writeAddr_apart`):
distinct member names of *any* two objects (two memory locals may name the same
struct), a member and an element, and two elements at distinct literal indices are
apart; a memory write keeps every storage entry. `require`, `assert` and declarations
keep entries; every other statement, and the exit of a branch, block or loop, clears
them; a loop body starts empty. Not covered: loads through storage paths with fields or
indices (`s.f`, `balances[k]`), loads through memory paths deeper than one step, entries
across calls, joins or loop back-edges.

### Dead store elimination (`Prog.dstore`)

`v = s; v = e;` → `v = e;` at a primitive state variable when `s` is simple and `e` is
pure (`Val.isPure`: it reads no storage); `m.f = s₁; m.f = s₂;` / `m[k] = s₁; m[k] = s₂;`
→ the second store at one static memory location (`mSameB`) when both values are simple;
applied in every sequence (blocks, branches, loop bodies). Side conditions: the first
value cannot fail (else its halt is the program's); a state-variable store never fails
(`write_root`) and the last of two wins (`SFields.set_set`); a memory store fails exactly
when its address is unset or out of bounds, independently of the value
(`Heap.writeAddr_none`), so the first store fails exactly when the second would, and the
heap after both is the heap after the second (`Heap.writeAddr_writeAddr`, from new
`Objs.set_set`, `MFields.set_set`, `MObj.setElem_setElem`). Only adjacent stores are
merged; stores through storage paths, aliases or non-simple memory values are kept.

Memory expansion, size and gas: the typed state (`State`: storage, heap typing `H`, heap,
locals, ledger, balance, transaction) and its step result (`Out`: state and heap-typing
extension) carry no memory-size or gas field, and the lowering IR has no `msize` or gas
read. A store at an existing slot leaves the heap typing unchanged (`TRun.assignMem`
returns `List.prefix_refl`), so there is no expansion effect in this semantics to drop;
the theorem is equality of the whole typed run, heap typing included. The cost side
(solc's memory-expansion gas) belongs to the D1 gas oracle (X01), still open.

### Loop-invariant code motion (`Prog.licm`)

`while (c) { x = e; rest }` → `if (c) { x = e; while (c) { rest } }` (`hoist`), applied to
every loop, innermost first; one hoist per loop per round (`Prog.optimize n` repeats).
The guard `if (c)` is the zero-iteration side condition, proved: without it a hoisted
`e` that reverts (e.g. an underflow) would halt a loop that never runs; under it `e` is
evaluated exactly when the first iteration evaluates it, in the same state, with the same
halt (`licm_runC`, first iteration matched in `TLoop.hoist_run`). Side conditions
(`licmB`, packaged as `LicmOk`): `e` and `c` invariant expressions (`Val.invB`: literals,
locals, environment values, operators, reads of primitive state variables — the
invariant `sload`s); neither reads `x`; `rest` within `nonpayable` (no memory statement,
no allocation), writing no local `e` reads and not `x` (`Prog.writesAt`), and only state
variables `e` does not read (`Prog.storeAt = some L`); invariance across iterations from
the existing `Prog.run_frame`/`Prog.run_keeps` (`runC_inv`, `runC_local`) and
`TLoop.run_congr_inv`. Divergence is preserved (`TLoop.run` is the same limit on both
sides). Not covered: hoisting from the middle of a body, declarations (`T t = e;`
introduces a local the loop's type does not have), memory loads, loops whose rest reads
or writes memory, `do`/`for` forms other than the lowered `while`.

### Pipeline and controls

`stages` now runs `[inl, cprop, simplify, cfold, dce, dse, cse, rle, dstore, licm, uve]`;
`round_preserves`, `optimize_preserves` and `Prog.optimize_runC` (statement unchanged)
cover them. Controls `tests/fullscope-20261104/vo1/X06Controls.lean` (not imported by the
generated roots; per-file diagnostics): RLE `rle_forwarded`, `rle_load_load`,
`rle_other_root`, `rle_mem_apart` (positive), `rle_killed`, `rle_mem_alias` (kept as
written), negatives `wrong_kill_differs` (kernel) and the aliasing negative
(`wrongAlias`, `#guard`), witness `entry0_holds`/`rle_entry0` (nonempty entries hold);
DSE `dstore_removed`, `dstore_mem_removed`, kept `dstore_live_kept`,
`dstore_failing_kept`, `dstore_mem_other_kept`, negatives `live_runs_two` vs
`live_dropped_runs_one` and `failing_first_reverts` vs `failing_dropped_returns`
(kernel), witness `sstore_witness`; LICM `licm_hoisted`, `licm_guarded`, rejected
`licm_root_rejected`, `licm_local_rejected`, negatives `unguarded` (reverts where the
loop returns) and `wrongRoot` (`x = 0` vs `2`), witness `licm_witness` (`LicmOk` by
`decide`); pipeline `e2e_optimized`, `e2e_licm`. Memory and loop runs are pinned with
`#guard` (the compiled interpreter, as the repository pins initial-store runs) because
the kernel does not unfold allocation and `TLoop.run` (classical) there; every syntactic
result and every storage-only run is a kernel `rfl`.

Axioms (`#print axioms` in the controls): `Prog.rle_empty_runC`, `Prog.rle_runC`,
`Prog.dstore_runC`, `sstore_dead_runC`, `mstore_dead_runC`, `licm_runC`,
`Prog.licm_runC`, the three `*_preserves`, `Prog.optimize_runC`: `propext`,
`Classical.choice`, `Quot.sound` only (the classical ones through `TLoop.run`); no
`sorry`, no `native_decide`, no heartbeat option.

### Backfill: inlining with reference parameters

`bindArgs` now binds every argument kind, so `inlineBlock`/`inlineBlockVal` and their
theorems lost the premise `args.allVal = true` (a strengthening; `Args.allVal` is
removed, no other module used it): a storage parameter is declared as the storage alias
`R storage x = e;` (`declStorage … (some (.path e))`, the identity the call shares) and a
memory parameter as the memory alias `R memory x = e;` (`declMem … (some (.alias e))`,
the object by identity, no copy), each read past the parameters before it
(`SPath.resolveT_wk`, `MPath.mvalT_wk`); `bindArgs_runC` covers the three arms. So
`Prog.inl` inlines void and single-value calls with any parameters
(`inlineBlock_runC f args body`, `inlineBlockVal_runC f args p r res body`, no premise).
Controls: `ref_call_inlined`, `ref_call_same` and the `#guard`ed `balances[1] = 7` runs in
`X06Controls.lean`; `O03Controls.storage_arg_kept` became `storage_arg_inlined`/
`storage_arg_same`.

Still open: inlining calls with several returns (`CallRet.rets`), memory or storage
returns, `callRec`, receiver calls. Design note for `rets`: the call leaves its return
variables in the caller (`rs ++ Γ`), which no single statement but the call does, so the
rewrite is at `Prog` level — declare the caller's return locals at their defaults, then a
block that declares the frame `rs ++ ps` above them (recursing on the binders so that
`(rs ++ ps) ++ (rs ++ Γ)` is definitional; `List.append_assoc` is not), runs the body
weakened by `thinTop (rs ++ Γ) (rs ++ ps)` (`frame_runC`), and copies each inner return
variable to its caller local; the remaining proof is the copy-back sequence against
`CallRet.leaveT`'s `TEnv.append`, and memory binders (`snocMem`) allocate on entry, after
the arguments, which the order of declarations must keep.

### Reviews (read-only finder + skeptic, no Lean server) and repairs

No soundness defect found; both confirmed `SameRun` is `Prog.runC` equality, the three
`*_preserves` instantiate it directly (the `Validator`/`validate_sound` path is not used:
direct preservation is stronger), the memory rule `MLoc.apartB` is exactly what
`MAddr.Apart` justifies (index/index only for distinct literals, stronger than needed),
the LICM zero-iteration, condition-error and `e`-revert cases are matched exactly, and
`State`/`Out` carry no memory-size or gas field. Applied:
- LICM copied a written loop invariant (`LoopAnn.inv`/`.invLex`) onto the shortened loop,
  whose entry state is after `x = e` (invisible to `runC`, wrong for the calculus):
  `hoist` now requires `LoopAnn.plainB` (unwind bound or automatic); control
  `licm_annotated_kept`.
- Doc precision: RLE keeps entries across local value declarations only (storage/memory
  declarations clear them) and rewrites a store's value, not its location; DSE's `e₂` is
  `Val.isPure` (no storage and no memory read); LICM's `c` is re-evaluated each iteration
  and need not be loop-invariant; stale O03 rows above superseded; `rle_killed` doc and
  the controls header (which now states which controls are `#guard`).
- Docstrings for every headline lemma; unused binder removed.
- Controls added: member apartness on aliased memory locals (`rle_member_apart`, kill
  `rle_member_alias_kept`, runs `4`/`6`), member vs element (`rle_member_index`), memory
  dead-store negative (`dstore_live_mem_kept`, `#guard` `1` vs `0`), `mstore_witness`/
  `mstore_witness_run`, kernel zero-iteration controls (`fail_loop_returns`,
  `unguarded_reverts`, `guarded_returns`), `e` reverting in the first iteration
  (`licm_rev_hoisted`, `rev_loop_reverts`, `rev_hoisted_reverts`), `rest` writing `x`
  (`licm_x_rejected`).
Not applied, recorded: the passes use `match` on `Stmt`/`Prog` like every earlier
optimizer pass (Gate G0 condition 1 asks for `casesOn` in kernel-evaluated code; the
controls reduce them by `rfl` in seconds, and the pass family would move together); all
passes share namespace `Solidity.Optimizer.ConstFold` (the lane's existing convention);
private copies of `TEnv.get_set(_ne)` and `ArrTy.eq` in `Loads.lean` (avoid importing
`RunFrame`/`Calculus.TermEq` there).

### RLE extension: keyed storage loads

After the reviews, `Load.sindex` adds primitive entries of a state-variable mapping or
array at a simple key (`balances[msg.sender]`, `values[i]`) as static loads: load-load
reuse for both, store-to-load forwarding for mapping entries (`balances[k] = s;`; an array
element is not forwarded, its bounds check reading the array), killed by any write to
the same state variable (root granularity: `balances[2] = 7` kills `balances[1]`) and by an
assignment to a local the key reads; a write to another state variable keeps them
(`Load.evalT_storage_write`, both the root reference and the entry reference keep their
root). Controls `rle_keyed`, `rle_keyed_forwarded`, `rle_keyed_kill`,
`rle_keyed_local_kill`, `rle_keyed_local_store_kept` and the `#guard`ed negative
(forwarding past the key's assignment reads `5` where the program reads `0`). Still not
covered: struct members of storage (`s.f`), nested paths, key-sensitive apartness of two
entries of one mapping (different literal keys).

### X06 gates at c0cc5e178 — 2026-11-06

- MCP diagnostics on every touched file: no errors. `#print axioms` on the headline
  theorems (`Prog.rle_empty_runC`, `rle_preserves`, `Prog.dstore_runC`,
  `dstore_preserves`, `licm_runC`, `Prog.licm_runC`, `licm_preserves`,
  `Prog.optimize_runC`, the witnesses) in `tests/fullscope-20261104/vo1/X06Controls.lean`:
  `[propext, Classical.choice, Quot.sound]` (`licm_witness`: `[propext, Quot.sound]`);
  no `sorryAx`, no new axiom.
- `gate.sh checkpoint` (warm-cache resumption over three task windows): `build-touched`
  and `library` PASS with no build errors; `trust`, `orphans`, `layers`, `roots` PASS.
  Module times: `Loads` 12 s, `DeadStore` 9.5 s, `LICM` 6.9 s, `Pipeline` 0.7 s.
  FAIL, none from this lane: `fragments` (master's `docs/README.md` carries a
  decisions-20261106 row no fragment produces; identical on `origin/master`),
  `doc-paths` (the only missing reference is in `after-roadmap-va1.md`), `axiom-pins`
  (0 errors; 4379 unrecorded pins, none under `Solidity/Optimizer/`).
- `./run-lean.sh`: stops at `fragments.sh --check` for the same master README row.
  With that file regenerated locally (`fragments.sh --force`, restored afterwards and
  not committed): `Build completed successfully (6413 jobs)` (a first attempt lost
  `Examples/Tactics/{RevertData,OpenLoops}` to the OOM killer, exit 137; the rerun built
  them). `check-solkey.sh` against the unpinned sibling `../solkey` (`b8d5f88`, not the
  pin `473da8944c`): 167 mismatches (storage-taclet annotation rows,
  `save<[Struct<[..]>`), as recorded above. Rerun against the pinned snapshot
  (`SOLKEY_RULES=tests/migration/solkey/.../solidityProgramRules.key`): OK,
  "annotations match", 377 taclets, 131 read-bearing, table covers 131.


## Constant observers: first G0 repair — 2026-11-07

Re-baselined the existing branch by fast-forward to published
5da4771e63a4278ed53932ac39a032e3d7aea6ed; old H44 archive hashes still match.
Current master already contains O02 lowering passes, O03 inlining/CSE/RLE/
dead stores/LICM and the eleven-stage SameRun pipeline. Earlier rows saying
those implementations or intrinsic X06 apartness facts are missing are obsolete.
This is still fragment coverage, not full D6 closure. Unused-function pruning,
remaining pass coverage, public compiler adapters, D1/D6/artifact binding and
physical gas/code-size benchmarks remain open. CtxEquiv/Unify explicitly calls
its D6 relation a stub; no substitute is introduced here.

The existing ledger records indexed matches in optimizer code as an unresolved
Gate G0 obligation. This small repair replaces only Simple.const? and Val.const?
in ConstFold.lean with casesOn whose motives generalize the primitive-type
index (Val's mutual-family motive is motive_5). Exact signatures, constructor
results, literal proof arguments and transparency are retained. All theorem
statements and bodies are unchanged; no premise, expected verdict, exclusion,
axiom or heartbeat changes. These nonrecursive observers need no recursive twin.
This removes exactly two indexed matches. Recursive folding and the rest of the
optimizer family remain G0 work; timings do not waive that requirement.

Warned before refactoring and inspected source commits64f81751c/a383b213a;
no speed-motivated reversal found. Repository per-file gate on the unchanged
file: PASS,8.358962s total,RSS669380608,cgroup274010112,10 samples; after repair:
PASS,3.815002s,RSS678596608,cgroup193605632,4 samples (gate rows5s/2s).
Cache warming confounds this one pair: no speedup claim or gas/code-size
benchmark follows. Both commands used the same historical runtime config and
explicit-j1 wrapper. Actual Lean4.24.0 commit797c613, Lake5.0.0-src+797c613.
The intermediate Val motive-name elaboration failure is retained; corrected
motive_5 gives MCP0 (6.961470s,RSS1327255552,cgroup888700928,10 samples).

Existing O02Controls and direct observer axiom audit PASS through gate.sh
per-file:51.563411s,RSS895635456,cgroup592531456,95 samples. Twenty reports
use only propext/Classical.choice/Quot.sound. Existing overflow/revert, assert
Panic, short-circuit and invalid-simplification controls are unchanged; this
proves only the existing lowering-IR results, not source Panic-byte/D6 adequacy.
Reviewers found ignored audit/config files lacked execution-time fingerprints.
A focused fresh audit recheck fixes that gap: matching SHA256 before/after,
PASS2.326856s,RSS523194368,cgroup150966272,2 samples, same five axiom reports.
Those hashes match the cache snapshots. Earlier ignored-file executions are
not retrospectively labelled source-stable; the failed broad checkpoint's
external runtime snapshot is retained without a historical before/after claim.

Required checkpoint attempt: build-touched PASS29s, then library phase times
out124 at292.166640s,RSS1816416256,cgroup2586542080,561 samples; last sampled
Lean target Backend.Scalar.PowerBounds. Artifacts retained, no timeout lifted.
All heavy checks serial under verified12GiB/no swap,threads1,-j1,4GiB admission
reserve and original aggregate budget. Source stability/cleanup receipts retained.
External current-runtime.toml mirrors the current lakefile with serial args;
original tracked historical runtime is unchanged. Full examples/global audits/
remaining final gates did not complete and remain open. No checkpoint readiness.

Static roots/fragments/trust PASS (6562 sources,289 sites,0 findings). Layers
FAIL:12 core→non-core closure edges (901 core,0 elaborator/adaptor reach,95 pinned
allowances). Pin inventory FAIL:11 unrecorded changes,0 errors,99 baselined
changes. Failures name producer areas, not optimizer changes; COORD owns repairs
and Optimizer CORE registration. No central allowance, pin or registry edited.
Separate read-only finder/skeptic reviews confirmed constructor semantics and
scope; their ignored-input finding was addressed by the fresh bound audit.

H44: all new raw data remains VM-only. Committed const-g0.sha256 has two entries:
- delivery/const-g0-20261107/evidence.tar.zst:3686986 bytes,
  SHA7becced85a9e85ec83df9f4df394c257d430ffe32ff35527ee8e1cbccd7eb2b6;
  56 payload files/11011907 bytes, plus per-file MANIFEST.json.
- delivery/cache-const-g0-20261107/cache-packet.tar.zst:100769388 bytes,
  SHA791e86d883e119c24384a819f8245c550118605e8e0694de39611031dff7c3db;
  checked66-module closure, not full-master cache, coordinator-pending under H41.
Cache metadata explicitly records a precommit dirty-source snapshot at5da4771e6;
source SHA256 values are authoritative, with final committed-source binding in
the handoff. Audit/config snapshots bind to the fresh recheck, not the initial
ignored-input execution. Never VM ship-cache.sh. Old evidence/packs unchanged.
O01 remains partial; O02/O03 remain partial/full-scope obligations open. This
small G0 repair is kernel checked; broad checkpoint/central-policy blockers
must be resolved before advancing its required validation or claiming closure.

Final finder and skeptic independently confirmed the fresh execution-hash binding, archive hashes/sizes, scope and failure accounting; no remaining finding in this two-observer change. Neither used Lean/server/builds or writes.


## H82 compatibility correction — 2026-11-07

The coordinator held284a998737e01be7ebc4e41e0d77f5f07e18c032 because the earlier
const? rewrite changed existing definition bodies and dropped generated equation
lemmas. That was not proof-only under H82. This correction explicitly supersedes
the previous section's claim that existing runtime observers were G0-repaired.
Old measurements/archives remain immutable records of the rejected proposal;
they do not describe this corrected implementation or an accepted runtime change.
Held history is preserved at codex/solidity-fullscope-20261104/vo1-pre-h82-284a9987.

Simple.const? and Val.const? are restored verbatim from published reference
95d1e9cb29dc5a34d1db68af3ca47e47b75e293f, including the original matcher equations.
All existing downstream declarations, theorem statements/bodies and callers are
unchanged versus that reference. The net source delta is32 added lines only:
Simple.constView?, Val.constView? and their constView?_eq lemmas. New views use
index-generalizing casesOn, and Val's new view delegates to the new Simple view.
Each equality states value.constView? = value.const? for every typed input,
with no additional premise. No global simp attribute or caller redirection.
Only the NEW views satisfy this G0 observation pattern. Existing runtime callers
still use the frozen matchers; their G0 obligation remains open. No speedup,
pass-coverage or D6/compiler/EVM/gas claim is added by the unused helper views.

Validation: ConstFold MCP0,8.002832s,RSS1392562176,cgroup934486016,12 samples.
Repository per-file gates on ConstFold, CompatibilityAudit and unchanged
O02Controls all PASS:54.749236s,RSS936792064,cgroup534700032,102 samples.
Metadata audit confirms precisely Simple.const?.eq_1..eq_4 and
Val.const?.eq_1..eq_10 (14 equations), and prints their types. New views and both
agreement lemmas depend only on propext; old evaluation proofs and all15 O02
axiom reports remain standard-only. Audit file SHA is recorded before/after its
execution and matches the cache snapshot. Existing positive/negative control
verdicts, including overflow IR revert and assert Panic, are unchanged; this
establishes no source Panic-byte/D6 adequacy beyond the existing IR boundary.

gate.sh touched PASS (build-touched29s),30.308200s total,RSS1030500352,
cgroup573001728,54 samples. Its current-runtime config SHA matches before/after
and the packet. All heavy work serial under verified12GiB/no swap,threads1,-j1,
4GiB reserve and unchanged proof/build budgets. Actual Lean4.24.0 commit797c613,
Lake5.0.0-src+797c613. No maxHeartbeats increase, sorry, new axiom or native_decide.
Broader original checkpoint/full gates were not rerun here; historical timeout
and central-policy failures retain their original revision bindings and no full
assignment readiness is claimed. H82 correction is additive proof/helper work,
not permission to migrate frozen callers or change other definition bodies.

Separate read-only finder/skeptic confirmed the additive32-line delta, exact
restoration and proof semantics; final ledger/hash review recorded in handoff.
H44 new raw evidence remains VM-only; const-h82.sha256 commits two pointers:
- delivery/const-h82-20261107/evidence.tar.zst,1859523 bytes,
  SHAedd4427b7a74606f67b211dfd50725dbca1373f29609289c643e665c795390d8,
  29 payload files plus per-file MANIFEST.json.
- delivery/cache-const-h82-20261107/cache-packet.tar.zst,100864700 bytes,
  SHA108e48f0aa911c1203cc8a49ebc8def5ea32ce27727437bc1fa99070aaa545be,
  scoped66-module corrected cache, coordinator-pending under H41.
Cache HEAD metadata is precommit held base284a; source hashes and final committed
binding are authoritative. Old packet791e86... is not the corrected-source pack.
Never VM ship-cache.sh. Coordinator explicitly requested pushing the correction;
only the assigned codex branch is authorized, with no default-branch push/PR.
O01/O02/O03 full obligations remain open under their original semantics/budgets.

Final finder and skeptic approved source, restored equations, ledger and artifact hashes; no remaining correction finding. Both were read-only and used no Lean/server/builds.
