# H62 item 4: generic Yul Views controls

Status: blocked partial implementation, not a completed checkpoint or assignment.
Branch: `codex/solidity-h62-4-20261106/generic-yul-views`.
Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Repository: `/workspace/solidity-lean`.
Export/handoff/evidence: `/workspace/h62-generic-yul-views/`.
The final committed head and artifact hashes are recorded in that directory's
`handoff.json` and `SHA256SUMS`; this document cannot contain its own commit hash.

## Scope and preserved originals

Writes are confined to this document and
`tests/h62/item4/generic-yul-views/` and
`scripts/h62/item4/generic-yul-views/`.
Every one of the 868 original `Solidity/Yul/Views/*.lean` files matches its base
Git blob byte for byte. No frozen statement, premise, exclusion, observation,
representation, generated root, central module map or axiom pin was changed.
No merge, pre-gate, push, publication or deployment was performed.
The clean older `work` branch remains preserved. The assigned branch was created
at the exact base after fetching it and verifying it is an ancestor of fetched
`origin/master`. No prior lane branch existed locally or remotely.

## Checkpoint 1: census (partial)

The deterministic lexical inventory covers all 868 Views modules, including
286 Controls modules. It records 9,929 declarations/guards: 6,271 theorems,
3,423 definitions, 29 abbreviations, 79 structures, 39 inductives, 2 named local
instances, 2 examples, 1 constant, 4 `#guard` and 79 `#guard_msgs` commands.
The Controls subset contains 3,026 theorems, 2,058 definitions, 5 abbreviations,
2 local instances, 4 guards and 79 message guards.

Every record retains the exact source statement prefix and SHA256, the command
body hash, separate expected-message comment/hash when present, source location
and a preserved/read-only/pending-owner disposition. Every file has a SHA256.
These are lexical source identities, not elaborated Lean statement hashes or
an enumeration of every conjunct/semantic branch. No observation was deleted:
whole-source blob equality provides the preservation boundary. A detailed
semantic classification and owner migration disposition remain open.

The supplied audit is `refactor-audit-20261106.md` (SHA256
`31ab16906906a9b22fd28700aacc72d2ee0ffe81cea723ae209eb28e5299286a`).
Items 9/11 describe analogous twin-file/helper/fixture techniques; their named
Backend/Evm targets are outside this lane. Item 16's table-plus-lemma technique
applies here; its Raw/vector generator work stays H55. No Raw/vector generator
was duplicated. All five coordinator input hashes passed their supplied manifest.

## Checkpoint 2: semantic packet and typed fixtures (partial)

`tests/h62/item4/generic-yul-views/GenericByteObjects.lean` introduces `ByteObjectFixture D`, `ByteObjectFacts f`,
and `byteObjectFacts f`. The latter is parameterized over arbitrary byte lists,
physical base addresses and residual memory, with the original length premise.
Its fields retain exact header, intrinsically typed bytes/string decoders,
all live payload positions, all outside bytes, the actual `ObjectByte` source
relation and idempotence. Its proof composes existing universal semantic laws;
it does not decide the table or introduce a new source language/state.

`tests/h62/item4/generic-yul-views/Fixtures.lean` contains seven typed rows: lengths 0, 2, 1, 31, 32, 33 and 64;
aligned/unaligned/zero bases and nonzero residuals. These are backfill, not
additional original cases or a completed migration of 3,026 control theorems.
Two candidates retain exactly the types of `ReadControls.byte_component` and
`ReadControls.byte_component_decode`. All original declarations remain intact.
The files contain `#print axioms` commands, but those outputs are NOT available:
the candidates have not compiled against the pinned migrated dependencies.
Static scanning found no added sorry, axiom, native_decide, trust shortcut or
raised proof budget. This is not a kernel axiom-set claim.

## Checkpoint 3: correspondence and acceptance (partial)

The two exact-type candidate instances and original declarations appear together
in the fixture module. It also references the existing crossing-slot refusal,
dirty-bool rejection and endian negative theorem unchanged. The remaining
negative/refusal inventory is preserved at the source level, not fully rerun.

Reproduce static acceptance from the repository root:

```sh
python3 scripts/h62/item4/generic-yul-views/acceptance.py \
  --inputs /workspace/h62-coordinator-inputs \
  --evidence /workspace/h62-generic-yul-views/evidence
```

This verifies all 868 base blobs and the exact file universe, reproduces the
inventory byte for byte, checks coordinator input hashes, runs seven adversarial
scanner controls and a cleanup regression (child ignores TERM), and scans the
additive Lean source for prohibited shortcuts. Its explicit result is
`STATIC_ACCEPTANCE_PASS`, never `RUNTIME_GATE_PASS`.
The 7.3 MiB inventory and reproduction are off git, with checksums.

## Checkpoint 4: measurements and runtime gates (blocked)

Official pinned archive: `lean-4.35.0-linux.tar.zst`, SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Lean reports 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
Lake reports 5.0.0-src+eb6cafb (Lean 4.35.0).
`lean -j1 --tstack=131072 Solidity/KeySort.lean` passed with exit 0,
no diagnostics, 1.564 s wall and 506,564 KiB max child RSS.
The earlier `/usr/bin/time` setup attempt failed because that binary is absent;
it is separately retained, never counted as a passing KeySort attempt.

The full gate used an off-git base-source snapshot at
`/workspace/h62-generic-yul-views/validation`, a fresh v4.35 cache and the same
`./run-lean.sh`. Only snapshot toolchain/Lake execution configuration changed:
cache disabled and explicit `-j1 --tstack=131072`; original source files remained
unchanged. A snapshot Git index was required by repository registration tools;
the initial missing-index setup failure is separately retained.

The actual run passed both layer checks (857 core modules, zero forbidden
paths), then compilation failed in unchanged `Hash/CollisionBound.lean:407`,
`:660`, `:680` and `Language/FixedPoint.lean:152`, `:170`, `:184`, etc.
Subsequent guard-message sorryAx output is fallout from failed base proofs,
not an introduced source axiom or a passing proof. The run was interrupted after
these failures: historical `full-gate.json` records exit -15, 75.839 s wall,
1,714,671,616 bytes peak sampled aggregate RSS. It is not a completed gate.
All members of its owned process group 1439 were verified quiescent.
Both the helper and original fixture depend on CollisionBound through
`Yul.Views.WordMemory -> Yul.Views.Bytes -> Roadmap.Contracts`.

The VM has a 16 GiB cgroup and no host swap. The bounded runner applies 12 GiB
per-process RLIMIT_AS, samples aggregate RSS against 12 GiB, and reserves 4 GiB
using the minimum of host availability and cgroup headroom. It enforces one
observed Lean process, 300 s per Lean process, and verifies owned-group cleanup.
No systemd-run was used. The old full-gate result predates runner cleanup fixes;
the later cleanup regression validates those fixes separately.

There is no valid before/after timing delta. After dependency relay, warm the
same dependency closure with the same pinned release, cache/resources and serial
flags; measure original ReadControls and the exact owner-overlay plus helper
under matched conditions, preserving logs for both. Include all affected
modules and table checking, not just the two small instances. Stop and report
if slowdown exceeds 10%. Then run the full affected gate and original negative
coverage. Do not count setup/failure timings as proof or performance results.

## Independent reviews and fixes

Independent finder `/root/finder` and skeptic `/root/skeptic` performed read-only
reviews without a Lean server, builds or fixes. Confirmed census findings were
fixed: guard expectations/attributes attached to wrong commands, quoted `where`
identifiers, fail-open empty roots, and two omitted named local instances.
Confirmed runner findings were fixed: surviving descendants after leader exit,
cgroup-aware headroom, and inaccurate hard-aggregate-cap labels. The cleanup
control kills a child ignoring TERM and verifies no live member remains.
Final handoff consistency reviews found no additional defect or overclaim.
Final reviews support an accurate partial/blocked handoff and grant no Lean,
full-gate, timing or completion approval. Review evidence is `evidence/reviews.json`.

## Typed blockers and exact resume actions

- `DEPENDENCY_MIGRATION_REQUIRED`: `Solidity/Language/FixedPoint.lean`
  (full-gate failure) still needs an owner relay. The initial Hash blocker is
  superseded by H70 below: its exact overlay was supplied and targeted checking
  passed in isolation; full affected validation remains pending. H70 also records
  the current Roadmap/Storage blockers. These originals remain outside our write
  scope; no local repairs were attempted.
- `OWNER_RELAY_REQUIRED`: VY2 exact-file agreement is still absent. No `relay.sh`
  exists in this checkout. The coordinator can retrieve this committed request:
  approve/apply a migration of `Solidity/Yul/Views/ReadControls.lean` and a new
  shared module Solidity/Yul/Views/H62ControlFacts.lean (proposed, not yet created), only after candidate
  Lean/axiom/timing checks pass. No absence of reply is treated as permission.
  The module-map registration row proposed for the owner is:
  `Solidity/Yul/Views/H62ControlFacts.lean | Typed byte-object control packet;
  arbitrary bytes, base and residual; exact header/payload/decoder/framing laws.`
  New generated roots/maps/pins must be registered by the owner/coordinator.

Resume on this original VM and branch with the existing persistent goal. Do not
create/reset a goal or launch a replacement thread. `get_goal` was not exposed;
the coordinator explicitly confirmed that optional inspection absence is not a
blocker. After dependency relay, compile/minimize both additive modules, inspect
real axiom outputs, complete semantic case dispositions/negative coverage,
prepare exact owner migration patches, measure matched before/after, and rerun
full gates. All four checkpoints remain unfinished. No human scope/exclusion
or premise decision is requested; the blockers require owner coordination.


## H70 Hash relay consumption (partial, still blocked)

The owner relay from `solidity-h62-6-20261106/migrate-hash`, head
`a3f49ee0ec1829e63022c90194048d5a1ffe0d22`, source `2a18afcd`, supplied the
CollisionBound overlay with SHA256
`3aebc61f1a1979d4e36d669e3c33f5ae8c848d38a3ca0574c62329bdc154bbff`.
That exact hash and patch applicability passed. The overlay was applied only to
the isolated validation snapshot; assigned-checkout originals remain unchanged.
Independent read-only finder/skeptic reviews found no statement/trust/budget
change; the finder compared all 91 lexical declaration signatures unchanged.

The bounded targeted `lean -j1 --tstack=131072 Solidity/Hash/CollisionBound.lean`
check passed, exit 0, 4.630 s wall, 610,770,944 bytes sampled peak RSS, one Lean
process and verified group cleanup. This resolves the earlier direct Hash
compile failure locally for this exact overlay, not its full affected gates.
The following bounded `lake --fail-fast build Solidity.Yul.Views.ReadControls`
failed, exit 1, 8.457 s wall, 724,402,176 bytes sampled peak RSS, one Lean process
and verified group cleanup. No retry, proof shortcut or budget increase followed.

New exact owner relay requests:

- `TRUST_GATE_STOP`: `solidity-h62-6-20261106/migrate-roadmap`,
  `Solidity/Roadmap/Contracts.lean:1104`, theorem
  `Solidity.Roadmap.PublicCorrectness.transfer`. The unchanged guard expects no
  axioms; v4.35 reports `propext`, `Classical.choice`, `Quot.sound`. Owner analysis
  and resolution under the existing trust policy are required. No permission to
  update a guard/pin, expand trust or bypass the stop is inferred.
- `DEPENDENCY_MIGRATION_REQUIRED`: `solidity-h62-6-20261106/migrate-storage`,
  `Solidity/Storage/HashedLayout.lean:376`, dependent elimination fails; downstream
  axiom guards at 417/420 also fail after the proof error. Relay a validated
  owner repair. This source remains outside this lane's write scope.

The Language relay for `Solidity/Language/FixedPoint.lean` and VY2 exact-file
agreement on `Solidity/Yul/Views/ReadControls.lean` and proposed
Solidity/Yul/Views/H62ControlFacts.lean are still pending. `relay.sh` is host-only;
its absence is not an installation task or an independent blocker.
The additive lemma and seven rows still lack real Lean/axiom/refusal validation;
no full gate, timing delta or checkpoint completion is claimed.
Saved evidence: `evidence/h70-hash-consumption.json`,
`evidence/h70-hash-overlay-check.{json,log}` and
`evidence/h70-views-dependencies.{json,log}` under the export directory.

## H82 user-authorized stopped handoff

Implementation stopped for accepted successor `solidity-inline-assembly5-20261031/vy2-physical`. No automatic continuation authorized. Exact-file agreement request withdrawn under H82; trust/definition/interface changes still need owner authorization. Current Roadmap/Storage/Language waits remain. New correspondence backfill has three passing external tests and two current literal-free matching types; both independent reviewers found that masking can hide literal/quoted-identifier changes, and preservation dispositions require the separate base-blob check. No general exact lexical or kernel claim is made. No repair was undertaken after retirement.

Handoff files are in `scripts/h62/item4/generic-yul-views/handoff/`: original assignment transcription, scope manifest, full work/backfill queue and retirement limitations. The transcription is incomplete in its long owner-key paragraph; the exact original frozen rendered prompt has NOT been reproduced or hash-verified. Full ownership snapshot is exported off git. Successor needs exact original-thread export before new work.

The exposed goal API cannot set PAUSED: its only outcomes are complete/blocked. No substitute completion or new goal was requested. No push was performed because H71 permission is not present in available inputs. Final cumulative patch, bundle, head and SHA256 manifest are recorded in the export handoff.

## H82b successor intake and literal correspondence repair

The successor verified all 557 H82b checksum entries and the exact final Git heads, then integrated the three stopped members on its existing branch. The authenticated assignment now includes the omitted owner-key paragraph and exclusive scope. The historical transcription gap above is resolved by the H82b metadata package; this does not validate retired proof or gate claims.

The external correspondence checker now uses masked text only for declaration/proof boundaries and retains ordinary string and quoted-identifier contents for equality. Whitespace inside literals is significant. Unsupported Lean character literals and raw strings fail closed (including conservative false refusals when their spelling occurs in comments). Nine regression controls pass, including changed literals, escaped whitespace and raw-string refusal. The two real ReadControls/Fixtures type pairs still match. Seven scanner tests and the process-cleanup control also pass. The initial sandbox-only scanner/cleanup attempts failed to create temporary directories; reruns with authorized filesystem access passed. No Lean statements, definitions, axioms or budgets changed; kernel correspondence, complete census/refusal coverage and matched production timings remain pending.

Read-only finder review caught an escaped-character regex defect in the first draft; it was corrected and the finder confirmed the repair. Skeptic review caught raw-string false acceptance; explicit refusal and a mutation regression address it. A further character-literal whitespace finding is likewise handled by explicit refusal and a regression. Neither reviewer ran tests, Lean or a server. Evidence: `/workspace/vy2-evidence/h82b-intake/correspondence-tests.log`.
## Explicit coordinator resume after integration

The later coordinator instruction explicitly resumed this lane and authorized
merging origin/master. The clean original branch fast-forwarded from
67e0398f217da988605a7323efeabbfd44b1a84b to
d96f2406d352de7e0b72ba6ac4ab29dc457582c6, which contains the reported
20e492ee99a3fa8679aa526de0b6e731d85e4134 integration. The earlier stopped
package is preserved as historical evidence; its pause text no longer describes
the current authorized work. No push or new goal was requested.

Independent backfill repaired the correspondence checker defect recorded by
both retirement reviewers: comparison now retains literal and quoted-identifier
contents and normalizes whitespace only outside them. Six external tests pass,
including changed string values, internal string whitespace and quoted type
identifiers. The current two selected type comparisons and all 3026 control
theorem dispositions reproduce. This still supports only selected unquoted
theorem names and is not a Lean parser or a semantic proof. Original-preservation
claims continue to require the separate base-blob acceptance evidence.

The integrated tree has no changes to the four previously failing dependency
files relative to the stopped head; those known failures were not rerun.
Roadmap axiom drift, Storage dependent elimination and Language migration remain
waits. Independent queue work remains available; status is partial, not blocked.
No original Lean source, axiom set, proof budget, interface or observation changed
in this resumed checkpoint. Kernel fixture/refusal validation and matched timing
remain open.

## Repository-verifiable input pins after ac9d8db2a integration

The coordinator reported the prior checkpoint integrated with passing gates and
requested continuing from master. The original clean branch fast-forwarded to
ac9d8db2ad2b29d4f04ed2391d78b5f19b4c97a6. No prior stopped package was overwritten.

Review minor addressed: the small committed source manifest is
`scripts/h62/item4/generic-yul-views/checkpoint-manifest.json`. It records 12
repository-relative source paths and SHA256 values, including both Lean
candidates and the original ReadControls input. From the repository root run
`python3 scripts/h62/item4/generic-yul-views/verify_manifest.py`; expected output
is `SOURCE_MANIFEST_PASS files=12; source identity only`. The manifest lists
reproduction commands. It is deliberately a source-input manifest, not a hash
of itself or of VM-only bulk evidence. Future source edits require reviewed
manifest regeneration; a changed file fails verification. Bulk H44 inventory
and logs remain off git in separately checksummed exports.

Three external controls pass for content mutation, escaping/absolute paths,
and empty/duplicate inventories; six correspondence controls also pass.
This establishes reproducibility of the selected source inputs, not semantic
preservation of every original case, Lean validity, axiom acceptance or timings.
The four known failing dependency files have not changed since the prior
checkpoint; no known failing Lean gate was rerun unchanged. Roadmap, Storage
and Language waits and all original proof/coverage/timing obligations remain.

## Timing acceptance backfill after 2a43bf4fc integration

The coordinator reported prior head46b06b522 integrated and instructed rebaseline.
Fetched origin/master was 2a43bf4fcdaf24750265afc8f8be5b420d1d22b0; task source
files matched, but prior changes had different integrated commit IDs. A
fast-forward attempt failed without changing files. A normal merge preserved
both histories and completed without conflict at8e5714f9293d1efa4ffdfee34238e8795cb076d2.
No reset or push occurred. The four known dependency source files remain unchanged.

Independent backfill adds `scripts/h62/item4/generic-yul-views/compare_timings.py`
and `scripts/h62/item4/generic-yul-views/test_timings.py`. This validates recorded
serial timing evidence, not actual performance. Inputs have schema_version1,
conditions (pinned toolchain archive hash, cache/resource/case/statement hashes,
lean_threads1, heavy_jobs1, lean_args including -j1), a module inventory and
at least three trials. Each trial records exit, resource_stop, wall_seconds and
module_seconds. Failed/resource-stopped, incomplete, nonfinite or nonpositive
records fail. Candidate inventory must retain every baseline module. Median
aggregate and each original module are checked; slowdown strictly above10%
returns TIMING_STOP and exit1. Added helper modules count toward aggregate cost.
Three trials is this tool's measurement protocol, not a raised Lean budget.

Usage: python3 scripts/h62/item4/generic-yul-views/compare_timings.py BEFORE.json AFTER.json
Bulk records stay off git. Six synthetic controls pass: aggregate/module-key collision, threshold/STOP, cache
mismatch, unsuccessful/incomplete evidence, helper cost and nonfinite time.
The caller must still prove the supplied inventories cover the full affected
closure, bind identities to actual source, and establish actual cache/resource
equivalence. Matching metadata alone does not establish these facts. No real
before/after delta or runtime gate is claimed. The committed repo-relative
source manifest now includes the two new tools (14 source pins).
All original proof, refusal-coverage and measurement obligations remain open.

Independent finder/skeptic both identified aggregate-row overwrite by a module
named aggregate. Fixed by namespace-prefixing module row keys; the added
regression retains TIMING_STOP for +20% wall slowdown with an unchanged module.
Reviews used no Lean server, builds or writes.

## Proof-only dependency repair after cc1ea1c9c integration

The clean lane fast-forwarded to coordinator-reported integration
cc1ea1c9c99522bff459dcc57e41339e1f347243. Under H82 standing permission, a
proof-only Storage repair was tested in the isolated pinned-v4.35 snapshot
before adoption. `Solidity/Storage/HashedLayout.lean:376` now explicitly reduces
`STy.locate` in the impossible word/nonempty-path hypothesis before `cases h`.
The exact theorem signatures, definitions, premises, exclusions, budgets and
axiom guards are unchanged. No source representation or interface changed.
History inspection found no speed-motivated change being undone.

Bounded command: lake --fail-fast build Solidity.Storage.HashedLayout, with
LEAN_NUM_THREADS=1 and explicit -j1 in snapshot Lake configuration. Exit0;
2.0246s wall,640237568 bytes peak sampled aggregateRSS, one Lean process,
no resource stop, process group quiescent. Existing no-sorry axiom guards for
STy.locate_bounded and located_word_inj pass unchanged. The adopted file matches
the validated snapshot SHA256:
9ac3cd0d246769c84330e724e5326446d57ce2fe408d5dcce652fdaf5f62e507.
This removes the prior targeted Storage compile blocker; full affected
validation remains pending behind Roadmap. No valid before/after performance
delta exists because the original v4.35 proof failed. No slowdown claim is made.

Roadmap experiments were not adopted. An explicit existential-elimination
rewrite and constructor-elimination rewrite both still fail the unchanged
no-axiom guard for PublicCorrectness.transfer. Print-only diagnostics establish
that RefinesUnder.safety, RefinesUnder.completes and Prefix.Le.final_eq have no
axioms, while the generated PublicCorrectness.refines projection reports
propext,Classical.choice,Quot.sound. This is a dependency localization, not
permission to change the axiom set or guard. Original Roadmap source is unchanged
in the assigned checkout and restored in the isolated snapshot after preserving
failed experiments off git. Relevant logs are transfer-explicit-check,
transfer-axiom-localization, transfer-constructor-check, storage-word-refusal-check
and storage-word-refusal-explicit-check under the existing evidence directory.
The initial Storage simplification attempt left none=some unresolved; adding
constructor discrimination produced the passing result. All failed checks remain
failed evidence, not proofs.

Independent finder/skeptic reviews are read-only, no Lean server/builds/writes.
The source manifest includes the adopted Storage file (15 source pins). Current
owner waits are Roadmap projection axiom drift and Language migration; the
former Storage owner-relay request is superseded by this passing proof-only
repair, with affected validation still pending. Generic fixture proofs, full
negative/refusal coverage, semantic inventory and actual matched timings remain
unfinished.

### Frozen-source provenance for correspondence labels

The lexical correspondence report now authenticates the existing frozen base from acceptance.py, compares complete current file Git blobs to that base and binds the result to census SHA256 hashes. Only matching files receive a preserved-original label. Modified and added files are explicitly unverified, baseline removals are listed separately, and source/content-universe changes after scanning fail closed. The scanner alone reports preservation as unchecked. Selected correspondence is tied to the exact ReadControls source path, so a same-basename file cannot inherit that evidence. No acceptance policy, frozen Lean declaration, proof budget or trust inventory is changed.

The external refusal suite covers matching-but-changed pairs, proof-only file changes, new and removed files, missing/empty baselines, missing provenance, stale source contents and stale file universes. All 25 correspondence controls, seven census controls and the bounded-process control pass. Real-corpus reproduction retains both selected pairs and all 2,990 current control rows: 832 files match frozen blobs, 36 are modified and ten are additions; no frozen files are removed. This current inventory does not replace the historical 3,026-case inventory, whose semantic/migration reconciliation remains unfinished. Modified sources still require separate exact-statement and meaning checks. Even matching source bytes do not establish transitive dependency identity or elaborated type/meaning preservation; lexical PASS is not kernel correspondence.

Independent read-only finder/skeptic found no confirmed defects. Evidence and matched external-CLI timings are retained at `/workspace/vy2-evidence/views-preservation/`. All four original checkpoints remain partial; generic Lean proof/refusal validation, complete case accounting, full-scope matched build timings and final/runtime acceptance remain open.

The final matched correspondence-entrypoint samples, sharing the current census helper, give median 2.195→2.215 seconds (+1.0%, below the 10% stop). These are external CLI measurements, not historical full-toolchain or Lean build acceptance.

### Reconcile the complete frozen Controls theorem inventory

`reconcile_frozen.py` reads all frozen Views blobs at the existing acceptance base through authenticated Git object hashes, rescans that immutable snapshot with the shared census parser, and retains one report row for each of its 3,026 Controls theorems. It searches every current Views theorem file, so moving a theorem to a file without Controls in its name does not drop the original case. All matches are lexical candidates, including same-file matches: namespace identity, transitive meaning, kernel correspondence and accepted migrations remain unproved.

Three real-corpus reports are byte-identical. The partition is 2,973 same-file command-text candidates, 38 other-file command-text candidates, 14 ambiguous command-text candidates and one unmatched case. Every original case is retained once; the current inventory still has 2,990 Controls-file theorems and 6,277 theorem declarations overall. The unmatched sb_not_stored_external statement adds Monetary.wordView under the documented H19 natural-balance migration in vy5-natural-account.md; that context is recorded without accepting it as frozen-statement equivalence or claiming a weakening/vacuity defect.

Ten new refusal/accounting controls cover frozen-versus-worktree bytes, moves to non-Controls files, deletions, proof changes, duplicate candidates, additions, duplicate/empty original inventories and corrupted frozen objects. They reuse the existing temporary-Git fixture rather than copying its implementation. The prior25 correspondence controls still pass, and the shared frozen-blob helper extraction leaves existing correspondence output byte-identical. Independent read-only finder/skeptic found no confirmed defects. Evidence is at `/workspace/vy2-evidence/views-frozen-cases/`. Standalone report timings are not comparable historical/full-build measurements. All four original checkpoints remain partial; semantic case reconciliation, generic proofs/refusals and final/runtime acceptance remain open.

### Source-name hints for ambiguous text matches

The frozen reconciliation report now reuses the existing audit-yul lexical census for source-name/visibility hints, rather than adding a second namespace parser. It reads hash-bound immutable copies for only the ambiguous cases and records that parser version and every consulted source hash. Missing or unsupported extraction stays explicit; stale source bytes fail closed. Private source names are not treated as elaborated mangled names, and generated/namespace/type/semantic resolution is not inferred.

Each of the fourteen real command-text ambiguities has one matching lexical source-name hint. The original ambiguous status and every candidate remain intact: this is review guidance, not fourteen accepted migrations. All 3,026 original rows, their prior classifications and the single unmatched H19 case remain unchanged. Seven additional controls cover distinct/changed source namespaces, private-name ambiguity, missing/partial/unsupported extraction and stale source bytes; seventeen reconciliation controls pass. Independent read-only finder/skeptic reviews and matched external-entrypoint measurements are retained with raw failures at `/workspace/vy2-evidence/views-namespace-hints/`. Full semantic case reconciliation, generic Lean correspondence and final/runtime acceptance remain open.

Three alternating matched report-entrypoint samples give median 4.500→4.468 seconds (−0.7%), below the performance stop. These targeted external measurements do not establish full-build or kernel timing acceptance.

### Refuse ambiguous identifiers and truncated compound types

The selected-pair lexical checker previously overwrote repeated theorem names, accepted qualified/primed identifier prefixes as the selected simple names, and cut a type-level let at its binding assignment. Concrete false-pass inputs are retained at `/workspace/vy2-evidence/views-type-refusals/prior-false-passes.json`. It now consumes the complete unquoted name token, refuses duplicates instead of selecting the last declaration, and explicitly refuses known compound term-type forms before delimiter-only extraction can truncate them. This remains a restricted lexical check, not a general Lean parser or semantic proof; unsupported syntax needs separate parser/kernel validation. Keyword text in string literals and quoted type names remains supported.

Twelve added controls cover duplicated/namespace-colliding names, qualified and primed prefixes, type-level let/have/letI/match/by forms and literal/quoted keyword handling. All37 correspondence controls pass. On the real corpus, both selected pairs and all2,990 current control rows are unchanged; all three recorded false passes are refused. Three alternating matched external CLI samples give median2.219→2.245 seconds (+1.2%, below the stop threshold), not full-build/kernel timing acceptance. Independent read-only finder/skeptic review and raw regression/reproduction evidence are retained with the same packet. No Lean production statement, shared interface, acceptance policy, budget, axiom or exclusion was changed; all original semantic/kernel/full-scope gates remain open.


### Live pinned byte-object proof validation

The inherited GenericByteObjects and Fixtures audit modules now pass serial kernel checking on Lean 4.24.0 (797c613), after refreshing their direct ByteObjects and ReadControls dependencies. The generic theorem proves all seven semantic fields for arbitrary layout, byte list, residual view and base; all seven existing fixture rows instantiate that theorem. No production statement or proof was changed. The two selected fixture theorem types were compared structurally with the original ReadControls declaration types in the Lean environment and both are exactly equal. All four audit declarations report only propext and Quot.sound.

The bounded checks used LEAN_NUM_THREADS=1 and -j1 with the existing stack and 300-second limits. GenericByteObjects checked in 0.27 seconds at 431,148 KiB VmHWM, Fixtures in 0.34 seconds at 429,736 KiB, and the corrected type/axiom audit in 0.93 seconds at 1,188,040 KiB. The first audit script used a reserved identifier and failed; its raw output is retained alongside the corrected passing run at /workspace/vy2-evidence/views-byte-proof-check/. KeySort passed before these checks. There is no implementation timing delta because these modules were not edited.

This closes the previously missing live 4.24 targeted checks only. It does not establish isolated 4.35 migration acceptance, kernel correspondence for the other frozen cases, complete refusal coverage, full affected-build timing or runtime acceptance. All four original checkpoints remain partial; the Source/Horizon and production-import performance STOPs remain in force.


### Generic byte-image injectivity and same-base refusal

The existing generic audit module now derives byte-list injectivity from its decoder law: fixtures with the same base and byte view have equal byte lists, regardless of residual view or alignment. The existing short and long unaligned table rows instantiate this law to prove their images differ. No fixture, production declaration, interface, representation, budget or exclusion was changed; no per-case module was added. The new control guards against collapsing distinct payloads into one image, not against a reject-all compiler or an invalid allocation strategy.

Both additions pass bounded serial Lean 4.24 checks and report only propext and Quot.sound. The four previous audit type/axiom exports remain byte-identical, and both selected original-instance types still compare structurally equal. Three matched samples give median GenericByteObjects 0.27→0.29 seconds (+7.4%) and Fixtures 0.36→0.39 seconds (+8.3%), below the existing 10% stop; these tiny targeted measurements are not full-build timing acceptance. Failed proof attempts are retained with the final checks at /workspace/vy2-evidence/views-byte-injectivity/. All original migration, semantic census, physical/compiler adequacy and final gates remain open.


### Refuse ambiguous serial timing metadata

The recorded-timing validator previously accepted conflicting -j1/-j8 arguments and Boolean thread counts as serial. It now requires integer counts of one and exactly one -j1 option, rejecting other -j and --threads forms so a later option cannot override the declared serial setting. Non-thread arguments remain supported. This validates recorded metadata only; it does not authenticate a process, cache or resource policy.

Eight timing controls pass, including conflicting/split/duplicate options, malformed argument containers and Boolean/float/string counts. All existing external correspondence, census, reconciliation, bounded-process and manifest suites also pass. Valid CLI output is byte-identical. Three matched batches of ten CLI invocations give median 0.03762→0.03939 seconds (+4.7%), below the timing stop. Raw samples are retained at /workspace/vy2-evidence/views-timing-serial/. No Lean statement, proof, budget, pin or acceptance boundary changed; full assignment gates remain open.


### Joint live-byte premise witness

The existing fixture module now constructs one closed witness for the entire bytesObject_payload telescope: a nonempty byte list, its word-length bound, residual view, base, index and in-range proof together. An off-Git Lean audit reconstructs the existential telescope from the imported theorem and checks definitional equality, including universe parameters. The source signature is text-identical to the frozen c6f550e281a7e5affa9a99bc2cdaed556dec00e4 version. This is one ordinary statement's joint inhabitance, not independent assumptions, per-input feasibility, compiler totality or complete corpus accounting.

The witness and telescope audit pass serial pinned Lean 4.24 checks; byte_payload_joint has no axioms. Three matched fixture-module samples give median 0.45→0.41 seconds (−8.9%), with raw timings and signature provenance at /workspace/vy2-evidence/views-payload-witness/. Existing statements, fixtures and production definitions remain unchanged. The full audit census, production reached-state/physical bridge, migration and final gates remain open.


### Coupled unchanged-view premise witness

The existing fixture module now jointly inhabits the complete bytesObject_unchanged telescope. One existing nonempty unaligned fixture supplies the byte list, length bound, residual byte view and base; the generic semantic packet proves both the header equality and every live payload equality for that same view. The off-Git kernel audit checks all parameters and both coupled hypotheses together, with exact universe/telescope fidelity. The source signature remains text-identical to frozen c6f550e281a7e5affa9a99bc2cdaed556dec00e4. No new fixture or per-case module was added.

Serial Lean 4.24 checks pass, with propext and Quot.sound as the witness axioms. Three matched fixture-module samples give median 0.44→0.46 seconds (+4.5%), below the stop. Evidence is at /workspace/vy2-evidence/views-unchanged-witness/. This is one statement's simultaneous premise inhabitance, not per-input feasibility, compiler success, physical execution adequacy or complete witness accounting. No corpus count is promoted while the authenticated bulk census is absent; all original final/migration/producer gates and prior STOPs remain open.


### Complete the nine explicit ByteObjects premise telescopes

Four additional reusable witnesses in the existing fixture module cover the seven remaining ByteObjects theorems. One proof serves header/payload-list/idempotence, another serves both decoders, and the residual and typed-source-read laws retain their coupled premises. The source-read witness uses ObjectByte.bytes at an actual live index with the corresponding offset and byte value. Together with the two previous proofs, six proof declarations witness all nine explicit theorem telescopes in this module. The small byte-witnesses.json records the exact source/proof map and frozen signature hashes; every signature matches the original c6f550e281a7e5affa9a99bc2cdaed556dec00e4 source.

The batch kernel audit checks all nine full existential telescopes, universe parameters and allowed axiom sets. New object/decoder/residual witnesses use no axioms; the typed source-read witness uses only propext. Three matched serial Lean 4.24 fixture samples give median 0.51→0.52 seconds (+2.0%), below the stop. Bulk proof logs, negative missing-premise check and exact generated audit source remain at /workspace/vy2-evidence/views-byte-family-witnesses/. This is a local nine-statement result, not authenticated global corpus accounting, per-input feasibility or compiler/physical adequacy. No original interface, fixture table, proof budget, acceptance criterion or exclusion changes; all wider obligations and prior STOPs remain open.


### Share raw calldata-copy laws with actual frame-copy proofs

Inputs now provides generic live-byte, outside-destination, empty-copy and zero-padding laws by instantiating the existing copyBytes and calldata-zero laws. Three existing FrameCalldata proofs consume these shared laws directly. Their headers, all definitions, mathematical source advancement and the deliberate absence of an MCOPY-style source-end premise remain unchanged; there is no new fixture family or state carrier.

All eleven existing FrameCalldata declarations have byte-identical elaborated type, universe and axiom exports before and after the proof refactor. Existing Controls and FrameCalldataControls pass, retaining maximal-source padding, no-source-end, whole-map, canonical writeback and reserved-area checks. New raw laws use propext, with Quot.sound additionally inherited by the empty-copy functional equality. Matched serial Lean4.24 medians are Inputs0.44→0.45 seconds (+2.3%) and FrameCalldata0.28→0.26 seconds (−7.1%), below the stop. The initial emitted Inputs run was slower and is retained; the reported medians use identical no-emission conditions. Evidence is at /workspace/vy2-evidence/calldata-shared-laws/.

These are mathematical byte-view and existing logical-frame proofs. Successful native destination-range/allocation, selected program/emission provenance, actual compiler dispatch and physical reached-state adequacy remain separate obligations. No frontend row, fork exclusion, source definition, proof budget, existing axiom set or acceptance criterion was changed. Global case accounting, full-scope timings/final gates and previous STOPs remain open.


### Copied calldata agrees with the actual ABI slice reader

The shared raw layer now proves equality of the entire copied byte window with the source's zero-extended window. FrameCalldata_readBytes is an exact instance, replacing its local list proof. AbiCalldataAgreement derives equality with the owner's actual Source.fitBytes and proves that loading a copied word agrees with abiInputWord on the explicitly selected input slice. The base parameter is retained: no selector or other prefix is silently discarded, and destination alignment remains unrestricted in the mathematical view.

All eleven original frame declaration type, universe and axiom exports remain byte-identical, and every original definition is unchanged. Existing frame and ABI boundary controls pass. The existing selector fixture verifies the copied argument at base4 and retains the wrong-base0 refusal through the new word law; no duplicate fixture table was added. All three new laws use propext and Quot.sound, inherited from the existing extensional list/read agreements. Matched serial Lean4.24 medians are Inputs0.43→0.44 seconds (+2.3%), FrameCalldata0.27→0.27 seconds and AbiCalldataAgreement0.34→0.34 seconds. Evidence is at /workspace/vy2-evidence/calldata-abi-copy/.

This connects mathematical copied bytes and the actual Source ABI reader, not decoder/program admission, native destination-range/allocation, selected emission, compiler dispatch or physical reached-state adequacy. No original statement, source definition, observation, budget, existing axiom set, fork exclusion or acceptance criterion changed. Full corpus, timing and final gates plus prior producer/STOP obligations remain open.


### Preserve actual typed ABI decoder results for copied words

One generic theorem lifts the copied slice-word equality through the existing Source.decodeWord for every layout and source type. It preserves the exact typed result, including success, revert and unsupported/stuck outcomes; no per-type decoder, canonical-memory cleanup or admission premise is introduced. The explicit input-slice base remains. Existing ABI fixtures verify uint success and the dirty-bool empty revert through the new agreement, reusing the original data rather than adding cases or state carriers.

The first word-level congruence attempt hit the unchanged default heartbeat limit; explicitly transporting numeric word equality avoids that unfolding and compiles normally. A two-law proposal including a redundant tuple-result wrapper hit the timing stop (median0.31→0.36 seconds, +16.1%); that wrapper was removed. More explicit intermediate/congruence variants and a candidate arithmetic proof optimization also exceeded the timing limit; the original arithmetic proof was restored exactly. The retained word-only proof infers the elementary numeric equality before applying the decoder, with an explicit maintenance comment explaining that elaboration choice. Its final matched median is0.31→0.33 seconds (+6.5%), below the stop. Failed attempts and exact code are retained at /workspace/vy2-evidence/calldata-decode-agreement/. No budget was raised; budget and timing failures were optimized before rechecking.

The axiom audit matches the existing Source.decodeWord and abi_decode_uint_word boundary exactly: propext, Classical.choice and Quot.sound. Existing ABI boundary controls pass; all original code outside the additive lemma is byte-identical. This is static word-result agreement, not dynamic argument/program admission, native range/allocation, selected emission, compiler dispatch or physical reached-state adequacy. Full corpus/pin/final gates and original producer/STOP obligations remain open.
