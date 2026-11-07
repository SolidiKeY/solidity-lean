# H82 final stopped-lane handoff — authoritative current state

**RETIRED / STOP after preservation; assignment incomplete.**
`handoff_to: solidity-h62-6-20261106/migrate-root-gate`.
The explicit consolidation resolution confirms that generic Continue broadcasts
do not revoke retirement. No new proof implementation or known timing STOP rerun
occurred. No scope takeover is effective until final stopped/head acknowledgement;
successor integrates final head. Preserve VM/branch/evidence; delete nothing.

Complete visible original assignment/objective, verbatim work/backfill queue,
exact24-entry/21-module scope and provenance are committed in
`tests/h62/item6/migrate-storage/h82-handoff/`, alongside current open queue,
schema-v1 waits, H82 instructions/resolution and retirement status. Its
`SHA256SUMS` binds all files; exporter copies them into the evidence archive
under `h82-handoff-scope/`. Original renderer/framing bytes are not exposed;
the supplied rendered fingerprint remains unverified while full visible task
text and its separate saved-byte hashes are preserved.

H82 WITHDRAWS historical O-STORAGE-001 proof-only exact-file agreement requests.
No agreement is needed for a statement-preserving proof tactic repair. The
technical HashedLayout:376/417/420 failure remains, with zero assigned new-module
passes; new type hashes, complete matched resources,1576 affected modules and
final gates remain pending. Current `open-queue.json` and `waits-v1.json` contain
all obligations. Historical permission language below is superseded.

Only goal `stop_goal(complete|blocked)` is exposed; no PAUSED operation exists.
Neither outcome substitutes for PAUSED. No goal is created/reset/marked complete.
Coordinator explicitly will pause the existing goal after final head/idle turn.
No automatic implementation continuation is authorized. No H71 push authority
was supplied/found in available inputs, so original no-push restrictions remain.
The cumulative patch, bundle, archive, full scope files and SHA256SUMS are
exported with exact final head/base/branch and clean status. Historical validation
below is retained without new proof work or timing reruns in this checkpoint.

## Historical H70 checkpoint — superseded permission protocol

# H62 Storage migration — H70 partial owner-overlay handoff

Status: **blocked, assignment incomplete**. Checkpoints: 1 done (assigned
component census/old baseline), 2 partial, 3 blocked, 4 partial handoff exported.
Repository `/workspace/solidity-lean`; branch
`codex/solidity-h62-6-20261106/migrate-storage`; exact base
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. The base was fetched and verified
as an ancestor of published master. Original clean branch `work` remains
preserved; no reset, push, merge, default-branch edit, freeze or ownership
transfer. No original Hash/Storage source, toolchain file, generated root/map
or axiom pin has been edited. All implementation writes are assigned scripts,
tests and this document.

## Current blocker and concrete review request

**O-STORAGE-001 / OWNER_COORDINATION**, exact file
`Solidity/Storage/HashedLayout.lean:376`, theorem `STy.locate_bounded`.
With the exact relayed Hash overlay, Lean4.35 fails dependent elimination in
the word/nonempty-path proof arm. The following guards at417/420 detect
`sorryAx` from rejected error recovery; no failing artifact or pin is accepted.
All21 assigned modules depend on this module; none has passed the new build.

Live producer: `solidity-v07-v11-20261030/v10-storage-operations` (V10), via
coordinator. Migration overlay lane: this branch. Exact-file request and
source/proposal hashes: `/workspace/migrate-storage-evidence/dependency-report.json`
and `h70-dependency-report.json`. Original source remains untouched pending
coordination. The concrete **UNAPPLIED** proposal is
`tests/h62/item6/migrate-storage/hashed-layout-proposal.patch`, SHA256
`c7e83d702c94f9c4baee4f6fa497bc6f37826763ca34f3d4a3d18810c1eec537`.
It changes only the proof arm:

```lean
| .word, _, s :: _, _, _, _, _, h => by cases s <;> cases h
```

This proposal has isolated rejection-case evidence below. It has NOT been
applied to the original or claimed to validate the full module. Obtain live
owner exact-file coordination or an equivalent owner-supplied migration first.
H70 routing explicitly supplies no original-file permission.

**G-ROOT-001 / FINAL_INTEGRATED_GATE_AND_RESOURCE_DISPOSITION**, owner
`solidity-h62-6-20261106/migrate-root-gate`: complete matched comparison,
resource disposition, full affected1576-module validation and `./run-lean.sh`
remain pending. Root alone owns the final tracked `lean-toolchain` edit.
Whole-build timing/RSS delta remains **null**. No `RUNTIME_GATE_PASS`, full
build/comparison pass, or assignment completion is claimed.

## H70 Hash-owner relay: exact private fixture, component passes

Owner `solidity-h62-6-20261106/migrate-hash`, reported head
`a3f49ee0ec1829e63022c90194048d5a1ffe0d22`, source `2a18afcd`.
The inline patch exactly matches relay SHA256
`3aebc61f1a1979d4e36d669e3c33f5ae8c848d38a3ca0574c62329bdc154bbff`.
It is saved at `tests/h62/item6/migrate-storage/collision-bound-owner.patch`.
The host-only receipt path was unavailable on this VM; it was not treated as
retrieved. Inline bytes were verified independently. `relay.sh` is host-only;
no VM installation or external publication was attempted.

`prepare_owner_overlay.py` copies the57-module pinned closure plus the two
existing API/export fixtures to `/workspace/migrate-storage-evidence/h70-source/`.
It applies only the exact Hash patch to that private copy. Manifest:
`h70-source-manifest.json`; original blob
`b54c93a5b24340a19160c1fb378d057ccee60f84`; patched blob
`092971eda8c7d6997276a92ba19b25b7ce05844e`. Only the Hash copy changes;
all statements/imports/budgets are preserved.59 source files are hashed and
read-only. Actual compiled hashes and pinned original hashes are separate.
Before/after source, manifest and control checks all passed; runtime stopped.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item6/migrate-storage/prepare_owner_overlay.py /workspace/migrate-storage-evidence/h70-source /workspace/migrate-storage-evidence/h70-source-manifest.json
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item6/migrate-storage/measure.py /workspace/migrate-storage-evidence/toolchains/lean-4.35.0-linux /workspace/migrate-storage-evidence/h70-new-clean-1 --image sha256:d9b8c34d61a9b9a3c44cab883d7d2f2619d674966ab520186f799cf32e3e0377 --owner-fixture /workspace/migrate-storage-evidence/h70-source-manifest.json
```

Actual result: KeySort PASS, Keccak PASS, owner-patched CollisionBound PASS
(including its original axiom guards), then unchanged HashedLayout FAIL.
Four modules attempted, three passed, zero assigned modules passed. Decisive
logs: `h70-new-clean-1.console.log`; module logs and full commands/exits are in
`h70-new-clean-1/logs/` and `result.json`. D-HASH-001 is component-cleared
**only in this private owner fixture**; the owner's full affected gates remain
pending, and original Hash source remains unchanged.

Both independent reviewers confirmed the Hash patch changes proofs only and
the actual fixture matches the exact postimage. Their consumer-hardening
suggestion was implemented after this diagnostic run: future `measure.py`
consumption independently checks the full expected postimage, not just the
manifest and patch digest. The exact run-time measure/census bytes are retained
at `h70-run-controls/`, verified against the run's recorded control hashes.
The actual run's owner postimage is independently verified by current controls.
No claim is made that the subsequent hardening executed in that earlier run.

## Bounded resources, versions and timing boundary

Official `leanprover/lean4:v4.35.0`, archive
`lean-4.35.0-linux.tar.zst`, SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Actual Lean4.35.0 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`,
Lake `5.0.0-src+eb6cafb`. Actual old Lean4.24.0 commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, Lake
`5.0.0-src+797c613`. Archive/extraction and coordinator input verification are
under `/workspace/migrate-storage-evidence/`. No alternative build or
v4.24 per-master cache is used.

Same runtime image and limits throughout: one CPU; hard Docker12GiB cap;
memory+swap total12GiB (zero swap);4GiB available reserve; one heavy Lean
process; `LEAN_NUM_THREADS=1`; `-j1 --tstack=131072 -M10240`; offline network;
read-only source/toolchain mounts. No systemd-run. Component measurements use
empty private output/cache directories. RSS is sampled; OS page cache is not
normalized. Component elaboration does not replace repository final gates.
The stopped idle container sentinel's137 exit is separate from each Lean exit.

Authoritative old baseline `old-clean-3`:57/57 modules and21/21 assigned
originals PASS;160.346414358 seconds; peak sampled RSS848093184 bytes.
Original commands/results remain in the prior handoff and `old-clean-3/result.json`.

ESCALATE partial KeySort observations to root gate: old wall1.665646s,
new wall2.09012s (25.4841% increase); old sampled RSS261459968,
new522829824 bytes. This failed partial run supplies no matched whole-build
regression figure. Heavy migration stopped at the failed prerequisite; only
bounded isolated backfill followed. Retain the binding rule: escalate any
regression and STOP >10% slowdown; complete matched comparison and resource
disposition remain G-ROOT-001 obligations.

## Completed in-scope backfill and proof boundaries

All21 original modules remain byte-identical to base:360 named source
declarations and all original cases, semantics, premises and budgets preserved.
No new production helpers, `sorry`, `axiom`, `native_decide`, or raised budgets.
Census/import closure, whole-source hashes, eight direct cross-directory edges,
36 external source dependencies and1576 affected downstream modules are in
`census-base.json`. Declaration rows are lexical navigation aids.

Old kernel-type export:1065 constants across all21 modules, including generated
constants; `frozen-interface-old.json` and raw `frozen-api-old-bound.log` remain
off git. The deterministic generator validates uniqueness/module coverage,
sorts module/name and hashes canonical metadata-stripped type/level repr.
Definition semantics additionally rely on source hashes; generated/binder
names can cause conservative structural-hash differences. Candidate type
export/comparison remains blocked.

Earlier `ApiControls.lean` passes both official versions for the Hash migration
boundary; old hash-bound results are retained. Its isolated proofs did not
repair production. New `LocateRejectControls.lean` is test-only: faithful
parameter-only copies of Loc/STy/Step/locate, a classifier covering all11
invalid constructor/head combinations, three named proofs, four rejection or
valid-path examples. The word/nonempty contradiction proves the exact local
elimination boundary without new premises. Empty paths and valid mapping
access ensure the fixture is not reject-all.

Both final bound runs PASS; all control/original/compiled-source checks true,
runtimes stopped. The three old proofs have no axioms; the new proofs use
standard `propext`. These facts do not prove production `locate_bounded` or
full affected validation. The initial old empty-path `rfl` attempt failed and
is retained; the final portable proof explicitly splits the type. No failed
error-recovery proof is accepted.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item6/migrate-storage/fixture.py /workspace/migrate-storage-evidence/old-clean-3 tests/h62/item6/migrate-storage/LocateRejectControls.lean /workspace/migrate-storage-evidence/h70-locate-old-bound.log
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item6/migrate-storage/fixture.py /workspace/migrate-storage-evidence/new-clean-2 tests/h62/item6/migrate-storage/LocateRejectControls.lean /workspace/migrate-storage-evidence/h70-locate-new-bound.log
PYTHONDONTWRITEBYTECODE=1 python3 tests/h62/item6/migrate-storage/overlay-acceptance.py
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item6/migrate-storage/report.py /workspace/migrate-storage-evidence
```

Locate fixtures run on the stopped original-root runtimes above; the already
bound H70 source tree is not silently extended or modified. Owner-overlay
negative controls verify exact digest/path/postimage, original/fixture hashes,
and rejection of unpatched/tampered postimages. Earlier scanner negative
controls cover comments, strings, imports/cycles, positions and file drift.
These are tooling and isolated Lean checks, not solc/EVM differential tests.

Independent read-only finder and skeptic used neither Lean execution nor its
server and made no edits. They confirmed exact Hash postimage/proof-only changes,
all11 rejection cases and valid controls, unweakened vocabulary, unapplied
proposal scope, actual4attempt/3pass outcome and unknown complete timing.
Their postimage hardening finding is fixed; source/run hashes and axiom limits
are explicit. Reviews are retained in `reviews.md`; final gates remain blocked.

## Exported checkpoint and coordinator continuation

Commit only this isolated branch. No new production registration is needed;
all Lean additions are test fixtures. Registration note:
`tests/h62/item6/migrate-storage/registration-fragment.md`.
`export.py` emits `original.patch`, prerequisite `migration.bundle`, `handoff.md`,
`committed-state.json`, deterministic `evidence.tar.gz`, and `checksums.sha256`
under `/workspace/migrate-storage-evidence/`. Bulk remains off git with
committed generators and checksum manifests. Prior exported a81b06e checkpoint
is retained in `history/a81b06e570570d6695564f20627b6cab0d00b0ef/`.
A relocated `local-checksums.sha256` verifies the preserved historical copies;
the retained old manifest itself still uses its original absolute paths.
All absolute paths and final committed HEAD are in exported metadata.

Fresh-thread handoff goes to the coordinator, not a self-launched replacement.
Continue this same VM/environment
`ccarenv_b64_Y2NhcmVudl9kODgyZDA2ODc5ZjA4MTkxYmI4OGZhZjhlOWEwOTczYg`,
branch and existing blocked goal. Goal ID/get_goal is not exposed; the supplied
frozen objective SHA is
`4b3d109b4fbd5c345a4db540473024c3c38e98353533491a0561043b347ae938` is not a substitute
for a goal ID. No goal was created/reset. The coordinator-confirmed supplied
objective remains binding.

Next: obtain O-STORAGE-001 exact-file coordination, apply only an approved
statement/budget-preserving migration on the assigned lane, build the full
candidate, compare frozen types and clean matched resources, obtain G-ROOT-001
resource disposition and all required affected/final gates, repeat reviews,
and export a complete handoff. No checkpoint or elapsed time completes this
unfinished queue.
