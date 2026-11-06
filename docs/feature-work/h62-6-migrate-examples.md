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
