# H44 split of held checkpoint 001b1de0a

The coordinator's H44 instruction narrows this increment to reviewable code,
documentation and one compact external-artifact manifest. The held increment's
raw datasets and generated Lean fixtures were already off Git. Its generated
current queue and expanded evidence index are now external as well. The queue is
preserved byte-for-byte; the expanded index changes only storage references and
current documentation identity. No theorem, proof gate, budget, source module,
script, test or accepted inventory payload changes in this split.

The prior head and its archive remain preserved. The replacement increment is
forward-only on the same branch; its net change from integrated master contains
scripts/tests, documentation and the compact manifest, with no added dataset,
corpus, log or generated fixture. All four original migration checkpoints remain
partial. This split is not migration acceptance or goal completion.

# Continuation after master ac9d8db2a

The latest coordinator instruction explicitly authorized fetching master and
continuing from its reviewed merge. This branch fast-forwarded cleanly to
`ac9d8db2ad2b29d4f04ed2391d78b5f19b4c97a6`; original base remains
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. No push, default-branch write,
new/reset goal or completion transition occurred. The current queue is
`CURRENT-QUEUE.json` in the external archive indexed by the
[compact manifest](../../tests/h62/item6/migrate-examples/evidence/resume-ac9d8db2a.json).
It supersedes historical retirement and prior incremental-wait state below.

## Accepted old inventory checkpoint

The saved incremental retry log ended “Build completed successfully (1080 jobs)”,
but the VM restart left no monitor seal. It is not accepted timing evidence.
A fresh bounded incremental confirmation passes exit0,1080 jobs,1.01795s,
58986496-byte sampled peak. This is a cached build, not the clean baseline.
All354 assigned source files and1075 explicit-import closure files remain
byte-identical to the pinned base, including721 external local modules.

A complete old ModuleData inventory now records15858 kernel occurrences,
15818 unique kernel names,107634 compiler-extra occurrences/names,40 kernel
reemissions across modules and55 kernel/compiler name overlaps. All123492
occurrences are retained;123397 distinct structural names; no exclusions.
Repeated kernel names have zero signature variants. Occurrence identity is
(module,category,structural name): exact duplicates within a table still fail.
ModuleData provenance is not exclusive source ownership; lazy generated
realizations can appear under multiple modules. This does not transfer ownership.

The full source stream contains604931 structural expression nodes. Kernel
signatures retain declaration kind/safety, universes, binder names/order/flags,
private/protected-name flags and canonical metadata. Fingerprint:
`4787a9ecf205001781a58bab547ab4f91f491aeb02cf332f986b2c51d1a78e16`.
Native IO memoization uses existing ExprPtr keys solely to traverse shared
expressions; addresses and node IDs never enter structural fingerprints.
Strong Expr references prevent live pointer reuse. No model statements,
definition bodies, proof budgets, axiom declarations or trust shortcuts changed.

The accepted direct-file export passes exit0 in23.21997s at1816281088 bytes RSS;
bounded stream validation passes exit0 in13.13199s at516358144 bytes. These are
instrumentation measurements, not assigned-module timing comparisons. The
validator authenticates all354 frozen paths/hashes, actual4.24.0 compiler/full
commit, capture source commit, exact regenerated fixture, read-only repository
codec inputs, module counts/completion and a matching compiler/file stream seal.
Compiler-extra signatures and actual export accessibility remain unresolved;
new signatures/shims are null. No full H78, new parity, semantic or axiom-equality
acceptance follows. Type fingerprints do not establish definition-value semantics.

The encoder and codec are read-only tooling dependencies from
scripts/h62/item6/migrate-testsuite/expr_dag.py and dag_codec.py, already present
in the authorized integration. Their repository paths/hashes are in the manifest.
The scoped patch does not take ownership of or duplicate those files; the bundle
retains the integrated upstream ancestry needed by this tooling.

The tree export failed the unchanged RSS cap after150.0478s (12942381056 bytes);
its1.7GB partial stream lacks completion and remains unaccepted on the original
VM. Two later buffered audit trials were explicitly interrupted, recorded and
preserved. Lean's run_elab captures stdout; direct file transport avoids retaining
or formatting the large stream as one diagnostic. Neither interrupted trial is
accepted timing/proof evidence. No known STOP was repeated unchanged.

## Gates, reviews and portable evidence

25 Python controls pass: process/interface8, dependency/fixture5, DAG10,
portable evidence2. Native controls pass on both actual official toolchains,
exercise distinct runtime nodes, and preserve shared-content/binder/let hashes.
Their checker authenticates successful bounded compiler results, actual runtime
version/full commit, file/node seals and exact regenerated fixtures. Reusing the
old stream or old result as new is refused. Current bounded per-file KeySort
checks exit0 on both versions. Lean MCP diagnostics are not exposed here.

Actual old: Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b,
Lake5.0.0-src+797c613. Actual new: Lean4.35.0
commiteb6cafb7290e8bd5f2937522d8d804f58f02bafc, Lake5.0.0-src+eb6cafb.
Official4.35 archive SHA256 remains
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
The authoritative preserved pin/provenance artifact is required; archive hash
verification is an external-artifact check, not something inferred from this prose.

Finder and skeptic reviewed read-only without Lean/server/writes. Fixed findings:
streaming memory, frozen-census/compiler provenance, bytecode-cache-free dependency
loading, genuine native-node controls, cross-version control provenance and
legitimate ModuleData occurrence accounting. Full final migration review remains
pending its gates. Complete review evidence is included in the artifact archive.

[The compact committed H44 manifest](../../tests/h62/item6/migrate-examples/evidence/resume-ac9d8db2a.json)
records the external archive's absolute VM path, exact byte size and SHA256,
plus its per-file checksum manifest. Generated queue state, the expanded evidence
index, fixtures, inventories, dumps and logs are external archive members.
The index is `evidence-manifest.json`; the queue is `CURRENT-QUEUE.json`.
No VM artifact is claimed to be available from Git alone.

The existing repository-only command still works with the compact manifest;
it checks the same code/document inputs and reports the archive pending. With
--artifact-root set to the archive's directory it verifies the whole archive.
After verifying and unpacking it, run the unchanged expanded per-file verifier:

```sh
python3 scripts/h62/item6/migrate-examples/verify_evidence.py \
  --manifest "$EXAMPLES_ARTIFACT_ROOT/evidence-manifest.json" \
  --artifact-root "$EXAMPLES_ARTIFACT_ROOT"
```

Using --repository-only instead reports external artifacts pending. The archive
contains old-inventory.jsonl,old-summary.json,raw InterfaceDagOldDirect.jsonl,
fixture/manifest, compiler/result/log, sealed controls and actual version records.
Original assignment/queue/scope files remain in the cumulative patch/bundle and
in the archive. The generated current queue is moved byte-for-byte, not changed.

## Remaining queue and typed dependency

The committed testsuite owner report records five official4.35.0 failures in
Solidity/Syntax/Raw.lean at597,650,665,682,684. That unchanged dependency is in
this directory's closure; accepted String/Slice/dependent-pattern compatibility
work belongs to migrate-syntax via root/gate. This lane did not repeat the known
failure or change an existing parser definition. See CURRENT-QUEUE.json for the
repository-relative report and source hash. SortCheck.Parser remains a separate
nonblocking CLI issue outside this examples closure.

All four original checkpoints remain partial: clean old baseline, complete new
build, new generated-public/signature/visibility inventory and producer shims,
matched clean timing/RSS with >10percent STOP, definition/meaning/axiom checks,
final ./run-lean.sh and complete root-gate handoff. The current DAG collector is
explicitly old-only; new-stage collection/comparison still needs validation.
Before reusing measure.sh, establish a pinned-base owned fixture worktree or
exact original354-target/configuration: the current generated master root also
contains unassigned DecisionResidue. Recording a fresh cache does not fix target
scope drift. This measurement setup remains unfinished.
No valid assigned old/new timing delta exists. No RUNTIME_GATE_PASS.
Fresh-thread continuation retains the original VM/branch/goal; no competing
continuation was created. The sections below are historical checkpoints.

---

# Reactivated after the coordinator merge (2026-11-06)

The coordinator explicitly instructed: “Merged migrate-examples e511ddcb6e into
master 20e492ee9 (gate touched PASS, Bridge build PASS, finder+skeptic review:
no blockers). Merge origin/master into your branch and continue.” This supersedes
the historical retirement for this worker. No goal was created or reset. The
exposed goal tool still has only complete/blocked outcomes, with no get/resume
operation; the earlier blocked response remains historical evidence.

The assigned branch fast-forwarded cleanly from
`e511ddcb6e0b66e6e77d34542b57d61a3675e0c3` to fetched `origin/master`
`d96f2406d352de7e0b72ba6ac4ab29dc457582c6`. The frozen base, retired lane head,
and reported master merge `20e492ee99a3fa8679aa526de0b6e731d85e4134` are all
ancestors. No push or default-branch write occurred.

## Current checkpoint and limits

A deterministic committed-blob dependency scanner now reproduces both base and
integrated trees: original354 examples,1075 local explicit-import modules,721
external local modules including8 LeanTeX vendor modules, no unresolved imports.
All original354 source blobs and all1075 closure blobs are unchanged. Master
additionally contains `Solidity/Examples/DecisionResidue.lean`, outside this
original assignment and outside the original roots' dependency closure. The
scanner reports that addition separately. Header inventory assumes valid source;
stdlib artifact presence is not compiler/API validation.

The audit-fixture generator verifies all354 census paths/hashes against frozen
Git blobs and replaces only `import SolidityExamples` with the exact assigned
imports in an off-Git fixture. It rejects any missing original or additional
transitive example module, rather than filtering declarations. The serializer
adds private-name encoding and protected-name metadata. Both flags participate
in interface fingerprints and comparisons; a visibility-only negative control
must fail. Those flags alone do not establish complete module-export visibility.
All public generated declarations remain required by H78; no shims implemented.

Five dependency/fixture controls and seven process/interface controls pass.
Both pinned toolchains compile the updated stdlib-only serializer probe; both
empty outputs are rejected by full-scope validation. These are tooling checks,
not successful model inventories or general Solidity semantic theorems.

The resumed old `lake build SolidityExamples` failed after1256.334362676s,
shell247/child-9, `RESOURCE_STOP`, sampled group peak7264968704 bytes, while
checking OpenLoops. Decisive guard: estimated cgroup headroom4290437120 bytes,
below the unchanged4294967296-byte reserve; current13620232192 bytes,
clean-inactive estimate730800128 bytes, swap0. Host available10348617728 bytes.
This incremental failure is excluded from baseline/timing comparison. Do not
rerun it unchanged. Advisory preparation now includes the already-allowlisted
owned `.lake` directory and reduced charge6027747328 ->611373056 bytes;
42767 regular files advised, no errors. No source bytes, reserve, cap or proof
budget changed. Any retry must repeat that preparation and retain the same guard.

The prior SortCheck Parser String.trim failure remains an external CLI issue,
but Parser is NOT in the assigned examples' dependency closure (only Annotations
and Faithfulness are). Current upstream policy removes solkeycheck from gates.
It is not a reason to block this directory build. KeySort itself still has
passing bounded checks on both pinned versions in the preserved evidence.

All four original checkpoints remain partial: completed clean old baseline,
full old/new generated-public API export and compatibility, new directory build,
matched clean timings, meaning/axiom assessment and final `./run-lean.sh` are
still required. No valid timing delta or RUNTIME_GATE_PASS exists. No original
model source, frozen statement, definition body or budget was edited. No axiom
declarations or trust shortcuts were edited; compiled old/new axiom comparison
remains pending.
Cumulative exported review patches are now restricted to original assigned paths;
bundles also retain the authorized upstream integration ancestry. Earlier e511
artifacts and all full original assignment/scope files are preserved.

The following is the historical e511 handoff record. Its retirement/next-work
instructions and external-blocker interpretation are superseded above.

---

# H82 RETIRED — no implementation continuation authorized

Successor: `solidity-h62-6-20261106/migrate-root-gate`.
The accepted H82 stop-and-handoff supersedes this document's earlier next-work
instructions. Full stopped handoff, original assignment/queues/scope, policies
and every open wait are committed under
`tests/h62/item6/migrate-examples/handoff/`. Both full old builds are incomplete;
replacement2 was intentionally interrupted for retirement at7103.8784s.
No PAUSED setter is exposed; only complete/blocked stop outcomes exist. Actual
non-completion stop response is preserved off Git; no completion claim.
No H71 push permission text was delivered, so no push is attempted.

# H62 item 6: examples migration overlay

Full assignment remains unfinished. This is a reviewed tooling/backfill handoff,
not a migration acceptance or runtime gate pass.

Batch/owner: `solidity-h62-6-20261106/migrate-examples`.
Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Branch: `codex/solidity-h62-6-20261106/migrate-examples`.
Repository: `/workspace/solidity-lean-migrate-examples`.
Original checkout `/workspace/solidity-lean`, branch `work`, is preserved.
Exact base was fetched; strict ancestry checks against `origin/master` and HEAD
returned0. Assigned remote branch was absent; assigned local branch began at BASE.
Full exported head is recorded by `committed-state.json` in the evidence directory.

Original VM: `ccarenv_b64_Y2NhcmVudl8zNmNkNjExMGZjMTQ4MTkxODJjMDA1NDQ2NDY3MjNkMg`.
Original persistent objective SHA256:
`4f63c0cac2f8cb9d098a419dabd250ba85c65c79e5a3df78dd26034550417470`.
get_goal is not exposed; coordinator explicitly permits continuing supplied goal
context. No replacement goal or competing automation was created. Fresh-thread
continuation belongs to coordinator/original goal on this VM and branch.

## Four checkpoints

1. Census complete at source level; clean old measurement FAILED and must be
   replaced. All 354 assigned files match the ownership snapshot exactly;
   1,067 direct imports, 885 external edges to 233 modules, 7,518 lexical entries.
   Lexical entries are not a Lean parser or all generated declarations.
2. Official pinned 4.35.0 provisioned and basic API/KeySort probes pass. Whole
   directory adaptation/build is not accepted; external migration is pending.
3. All-module new build and valid matched clean comparison pending. No timing
   delta exists. Any valid regression escalates; greater than 10 percent stops.
4. Initial patch/bundle/evidence exported. Full elaborated interface inventory,
   old/new equality and final cross-directory root-gate handoff remain pending.

No original Lean file, theorem statement, premise, observation, proof budget,
root, central module map, axiom pin or tracked toolchain file has changed.
No source-model axioms, sorry or trust shortcuts added. No push, merge, pre-gate,
publish, freeze announcement or producer ownership transfer.

## Toolchain provenance

Coordinator inputs `/workspace/h62-coordinator-inputs/` all SHA256 verified.
Pinned official Linux archive:
`/workspace/h62-toolchains/lean-4.35.0-linux.tar.zst`, SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Installed Lean/Lake binary hashes were checked against archive members.
Extraction command and binary hashes: `toolchain-provenance.json`.
Old archive SHA256:
`b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec`.

Actual old: Lean 4.24.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b;
Lake 5.0.0-src+797c613. Actual new: Lean 4.35.0,
commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc; Lake 5.0.0-src+eb6cafb.
`runtime-versions-v2.json` records actual `lake env lean -j1 --version` output.
Private serial wrappers call unchanged official binaries with `-j1`; no final
lean-toolchain edit. No shared/per-master v4.24 cache.

## Resources and revised comparison method

VM hard memory cap 16 GiB; CPU quota 4 CPUs,5 online processors; swap total/current 0.
One heavy Lean process at a time, explicit `-j1`, `LEAN_NUM_THREADS=1`.
Writer lock `/tmp/solidity-lean-feature-groups-20261025/writer.lock` is held for
writes/checks. No systemd-run. Guard samples every 0.5 s, caps aggregate group RSS
at 12 GiB, requires host MemAvailable4 GiB, and estimated cgroup headroom 4 GiB:

`limit - current + max(0, inactive_file - file_dirty - file_writeback)`

Reclaimable bytes are clamped to current charge; estimate clamped to [0, limit].
Active cache/slab are excluded. This is an estimated available reserve, not a
hard guarantee of 4 GiB uncharged memory. Existing VM cap is the hard bound.
Resource violations and the stop-time snapshot are now saved; all stops fail.
Cleanup kills only owned process groups and rejects unfinished orphaned work.

Both replacement comparison runs require the SAME explicit advisory cache
preparation manifest `cache-roots.json`. It lists both official installations,
both release archives and this lane's private cache/evidence directory.
`cold-cache.py` uses read-only DONTNEED on regular files only, skips symlinks,
restricts resolved roots and records before/after charge. It does not modify
source bytes or promise fully cold physical cache. No global drop_caches.
Probe advised 32,194 files; cgroup charge 9,348,055,040 ->2,885,308,416 bytes,
no errors. Preparation occurs before the timed build. Each run starts with
clean Lake outputs and a new private cache, hashes the entire tracked tree
before/after and refuses cache/result reuse. CPU/memory settings are recorded.

## Actual gates and decisive output

All evidence is under `/workspace/h62-migrate-examples-evidence` (bulk off Git).

- Census repeated byte-identically, SHA256
  `ab85ba2f770ef45b85ca111896303466e3caef78a0b57ca1325b9ad4a803cf6f`.
- Six Python controls pass (`acceptance-resource-v2.log`): scanner boundaries,
  successful command, orphan rejection/cleanup, conservative cache accounting,
  exact scope/structural identity and missing/changed interfaces.
- Old bounded `bash scripts/check-solkey.sh`: exit 0,22.6803 s, sampled RSS
  808,235,008 bytes.377 taclets,131 read-bearing, table covers131; annotations
  match explicitly supplied SolKey rules file (`old-keysort.*`).
- `lake env lean -j1 --tstack=131072 Solidity/KeySort.lean`: exit 0 on BOTH
  toolchains (`keysort-module-4.24.0.*`, `keysort-module-4.35.0.*`).
- API fixture: exit 0 on BOTH toolchains; generated 7=7 has no axioms. Parser,
  elaborator, evaluator and addDecl/consumer exercised, false equality type
  refused. No Solidity program property is established (`api-fixture-*.log`).
- Serializer syntax/runtime-name controls: exit 0 on BOTH toolchains
  (`interface-syntax-*-v2.*`). Probe intentionally imports no model and reports
  0 modules/0 declarations. Full-scope validator rejects BOTH probe outputs
  (`empty-inventory-refusal-*`). These are NOT frozen-interface passes.
- Early fixture layout and serializer command-namespace/type-inference errors
  were corrected; failed logs retained. Full `InterfaceDump.lean` still awaits
  successful all-module compilation; imported private visibility must be checked.
- Initial old `run-lean.sh` attempts stopped before checking for absent GNU time
  or hidden Node PATH. Third passed layer checks and built KeySort, then was
  deliberately interrupted after 148.8484 s; not a passing final gate.
- Focused CLEAN old `lake build SolidityExamples`, `old-examples-clean-1`:
  FAILED, shell 247/child -9, `RESOURCE_STOP`,5861.847718698 s, sampled aggregate
  RSS5,336,875,008 bytes. No completed old baseline. Last completed log entry is
  CallResultRestore. Source and whole tracked-tree hashes match before/after.
  Original guard treated all cgroup charge as unavailable; it did not save the
  violating counter. Cache pressure is inferred, not a stop-time observation.
  This failed result is excluded from future timing comparisons.
- `./run-lean.sh` final new confirmation remains pending. No RUNTIME_GATE_PASS.

Fixture timer data is diagnostic, not a controlled old/new performance comparison.
The source census/hash and Python controls are external instrumentation. Lean
proof terms are kernel checked; runtime `#guard`/`#eval` checks are regression
checks, not general semantic theorems. Type hashes do not prove definition-value
semantics. All original source bytes currently remain unchanged.

## Dependency blocker DEP-SORTCHECK-435

New `bash scripts/check-solkey.sh`: exit 1,18.1622 s, sampled RSS1,798,197,248 bytes.
Its script hides Lake output; `lake build solkeycheck` reproduced exit 1 in 4.0337 s.
Primary error: `Solidity/SortCheck/Parser.lean:76:13`, removed `String.trim`.
Follow-on evaluation errors are compiler recovery, not source sorry additions.
Owner: `solidity-h62-6-20261106/migrate-sortcheck`; integration owner:
`solidity-h62-6-20261106/migrate-root-gate`.
Exact-file request: `owner-requests.json`, saved for coordinator relay; no owner
patch received or applied. relay.sh is absent here. No absence of reply is
permission to edit owned originals. Transitive examples closure has 721 external
local modules (713 Solidity plus 8 vendored LeanTeX); source/API changes there remain owner migration work.

## Interface and case accounting

`InterfaceDump.lean` enumerates loaded named constants by source module, including
generated/private constants when available. Names are structurally encoded;
levels, binder information and logical expression constructors are retained;
nonsemantic mdata is normalized. Source module header sorted.
`interfaces.py` requires all 354 census modules, rejects duplicate/open/empty
inventories and requires known generated declaration sentinels. Counts include
legitimate zero-constant files. A completion footer/count rejects truncated exports. Old/new structural name sets and type hashes
must match; additions/removals/type changes fail, never silently excluded.
Private import visibility changes require diagnosis. Anonymous command cases
remain accounted by source census/hash plus successful full builds. Definition
semantics require source/proof/regression review, not type fingerprints alone.
`prepare-probe.py` deterministically produces the rejected stdlib-only probe.

## Reviews and exact continuation

Independent read-only finder and skeptic used no Lean/server or writes. Initial
scanner, cleanup and provenance issues fixed. Resource/collector follow-ups fixed;
see `review-initial.md` and `review-resource-v2.md`. Final checks are recorded
above; full milestone acceptance/review waits for successful required gates.

Historical replacement clean command (not authorization to resume this retired worker):

```sh
bash scripts/h62/item6/migrate-examples/measure.sh \
  /workspace/.setup/tools/lean-4.24.0-linux \
  /workspace/h62-migrate-examples-evidence/bounded-4.24.0 \
  /workspace/h62-migrate-examples-evidence/cache-old-examples-clean-2 \
  /workspace/h62-migrate-examples-evidence old-examples-clean-2 \
  /workspace/h62-migrate-examples-evidence/cache-roots.json
```

The run was stopped for H82 retirement. Inspect its `.log`, `.json`, settings,
cache-preparation and source/tree hashes; do not resume this worker.
On success, collect complete old interfaces, then resume new-toolchain directory
builds/owner requests, matched comparison, final policy and full handoff.
No unfinished obligation is complete merely because a checkpoint was committed.
Export a committed snapshot only after releasing the build lock:

`python3 scripts/h62/item6/migrate-examples/export.py --evidence /workspace/h62-migrate-examples-evidence`

Exporter rejects busy lock, dirty/wrong branch or missing base ancestry. It emits
patch, thin bundle, deterministic evidence archive, full head/base and SHA256
manifest. Initial snapshots never prove pending/later gates. Do not push or merge.
