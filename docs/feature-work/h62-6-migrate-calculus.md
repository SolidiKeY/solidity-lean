# H82 retirement acknowledgement — implementation stopped

This section supersedes historical stop/continuation wording below. The human
explicitly requested stop-and-handoff after successor relay acceptance.
`handoff_to`: `solidity-h62-6-20261106/migrate-root-gate`. The final full commit
and cumulative export are recorded in the retirement artifact manifest; the prior
snapshot 201748fa51ec0386ac648e0aea31ed5e1843a264 is not asserted final.

No new Lean run, proof implementation, source adaptation, VM, goal, Claude-owned
source edit or message was performed for this retirement checkpoint. It adds only
required assignment/scope/queue/policy/provenance and stopped-state documentation.
The original VM, branch, evidence, H70 producer and prior sealed handoff are preserved.
The successor integrates the final head only after this worker's stopped acknowledgement.

The original assignment, entire work/backfill queue and exact 389-entry scope are
committed under `tests/h62/item6/migrate-calculus/retirement/`, with SHA256SUMS.
The assignment was transcribed from the visible original thread; the exact scope
substring comes from the verified original ownership snapshot. The unavailable
launcher-rendered wire bytes are not falsely claimed to match the supplied
0992f14182a95808d7e2bf1d1e1610b8677b2b85e79f2c8697c7fb782cd1eb59 identity.
The full visible assignment and original goal objective are both preserved.

Current H78 supersedes RSS-only stops within the 8 GiB per-module cap. Historical
+102.4262% diagnostic RSS growth remains cut-over evidence, not a standalone active
RSS stop. Separate slowdown/trust/acceptance holds remain. Historical runs enforced
12 GiB and are not retroactively claimed to be 8 GiB gates. Full H81 policy text,
H71 push permission, root-local H78 requirements and schema files were not delivered
here. Coordinator-local paths are provenance only. No push is made because H71
permission is unavailable and the original no-push constraint remains.

H82 removes exact-file owner agreements for the specified statement-preserving
proof/additive/import/module-split/doc edits. Existing statement/signature,
statement-dependent definition, budget, axiom-set or exclusion changes still require
the owner; frozen ones require H57 versioned pairs. No obsolete proof-only agreement
request is retained as a blocker. None of these standing permissions authorizes
implementation after this explicit retirement/pause.

Remaining waits and every original queue/backfill item are in retirement-state.json:
accepted Syntax.Raw prerequisite delivery/confirmation; root-gate matched full
comparison and public API/trust acceptance; delivery of existing H78 new exports
and authoritative requirements/policy artifacts as needed. H78 coverage includes
all original public generated noConfusion/recOn/casesOn/match_ and other declarations,
with per-shim old/new/shim signatures, visibility and provenance. No blanket generated
exclusion or consumer-rewrite compatibility is accepted. implemented_shims=[].
The old complete type inventory is preserved; complete new exports/visibility and
shim records remain unfinished. No full migration, semantic equivalence or runtime
acceptance is inferred. H44/H68/H69/H78/H80/H81 obligations carry to the survivor.

**Pause capability failure:** only codex_goals_stop_goal(outcome=complete|blocked)
is exposed; no pause/get/update-goal operation exists in the current tool catalog.
The requested PAUSED service transition therefore cannot be submitted or confirmed.
No unsupported enum, substitute completion, goal reset or replacement was attempted.
Last observed service state was blocked in the previous result; current readback is
unavailable. The worker stops under the explicit user retirement instruction and
will not automatically continue implementation. The coordinator must use a
pause-capable control if a service-level PAUSED transition is required.

---

# H62 migrate-calculus: blocked migration, reviewed H70 producer available

The clean old-toolchain directory build passes. The H70 proof-only producer is
committed and available for coordinator retrieval. Full new-toolchain migration
remains blocked by the syntax owner dependency and the recorded RSS STOP.
No full migration or RUNTIME_GATE_PASS is claimed.

## Identity and scope

- Batch/slug: solidity-h62-6-20261106 / migrate-calculus.
- Repository: `/workspace/migrate-calculus`, a separate worktree.
- Branch: `codex/solidity-h62-6-20261106/migrate-calculus`.
- Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`, fetched and verified as an
  ancestor of fetched origin/master before branch creation.
- Original `/workspace/solidity-lean` checkout remains on `work` unchanged.
- Clean baseline code head: `dd8163e4a7a1601c0ae02d70fa421572bedb4815`;
  all 490 measured Lean source files were byte-identical to the pinned base.
- H70 source-only producer head: `25fc247b3279902e1520de400a375754d0314d5f`.
- Final committed handoff head is recorded automatically in the export manifest.

The only production change is one proof line in
`Solidity/Calculus/LinearCountermodel.lean`. No statement, premise, exclusion,
computational definition, import, proof budget or trust pin changes. Root files,
central maps and lean-toolchain are unchanged. There were no pushes, merges,
PRs, pre-gate/deployment runs or freeze announcements. Live producer ownership
continues unchanged; H55 work was not taken.

## H70 partial producer

The coordinator requested publication of the exact reviewed partial producer for
migrate-corpus and audit-exact-verification. Commit 25fc247b changes only the
falseNode_spec proof at line 134:

```diff
-  simpa only [Bool.not_eq_true'] using hp
+  simpa only [falseNode, Bool.not_eq_true'] using hp
```

The actual canonical file is `Solidity/Calculus/LinearCountermodel.lean`.
The H70 summary's shorter Linear/Countermodel path is not a second file.
The committed file equals the previously reviewed full-module fixture with its
two diagnostic #print commands removed. The full-module fixture passed on both
actual toolchains before the RSS STOP; its falseNode_spec/searchCountermodel
axiom sets contain only propext, Classical.choice and Quot.sound.

The committed-path new build was not rerun after publication: the STOP remains
in force. This is a partial producer boundary, not a full directory gate.
The H70 exact-file publication does not transfer live ownership or authorize
additional new-toolchain work. The source statement header is unchanged.

| Artifact under `/workspace/migrate-calculus-evidence/h70-producer` | SHA256 |
|---|---|
| producer.patch | 1e9f4cbb4d16309faf398cb9b949aa7a9635772467122e91ad4cb36a2cbc555d |
| producer.diff | e6cb692412eb22013991d2b64037705c484e0dede6ef1c73628f555c699b3518 |
| LinearCountermodel.lean | 073590d8c660b2d776bf96e5d4da8e6b6dad76d7ab6f4b8d0471d11b0a1f023a |

Base file SHA256: b2a6ba4f212715ae9e4e329ae774914303d07687735d9973eb9cb6c6d2edfa79.
producer.json records full head/base/parent, consumer keys, the baseline type
hash and statement-header hash, patch paths and exact gate boundary.
SHA256SUMS covers that partial publication. No remote transport acknowledgement
is claimed; the coordinator retrieves the committed objects/artifacts from this VM.

## Census and frozen baseline interfaces

The pinned census accounts for all 385 assigned Lean modules, their 490-module
local closure, 105 external local dependencies, 83 direct boundary imports and
1213 reverse boundary imports across tracked Lean files, including roots and
Bridge. No reverse header was unparsed. All 105 external modules have unique
migration owners in backfill/cross-directory-owners.json. No import cycle was found.
The census was taken before the H70 proof-only source edit.

The old-only interface audit reuses only the owned, fully validated old build.
It emits exact Name trees, levels, binder names/info, declaration kinds, safety
flags and types; only nonsemantic Expr.mdata is removed. It never exports proof
bodies and is not a semantic-equivalence proof. Private/generated declarations
and zero-declaration umbrella modules are retained, not excluded.

| Baseline inventory | Count |
|---|---:|
| Assigned modules | 385 (376 with declarations, 9 with zero) |
| Declarations | 47965 |
| Private declarations | 7703 |
| Theorems | 24491 |
| Definitions | 19995 |
| Constructors / recursors / inductives / opaques | 2337 / 427 / 423 / 292 |
| Existing unsafe declarations | 34 |
| Owned axiom declarations | 0 |

The 34 unsafe flags belong to the pinned baseline, including existing elaborator
implementations; none was introduced by the producer patch. New custom axioms,
sorry, native_decide and raised maxHeartbeats in production: zero.

`old-interface-check-01/frozen-types.ndjson` is 267094042 bytes; SHA256
95e5af8a318e6ee07e228c7e358e48065b56dc9e977b8c36bacabd64de02f2fe.
The canonical declaration hashes are declaration-type-sha256.ndjson; module hashes
and counts are frozen-interface-manifest.json. Hashing requires a successful
matching audit record, exact Lean-reported completion count and unique names.
It binds result/log/raw-stream SHA256 values and rejects truncated streams.
The old-only audit passed in 100.691179657 s with 1547210752 bytes sampled RSS.
No new-toolchain interface-equivalence gate has passed.

## Toolchains and resource protocol

All five supplied coordinator input hashes were verified. Required new release:
leanprover/lean4:v4.35.0, official lean-4.35.0-linux.tar.zst, SHA256
7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d.

| Toolchain | Actual observed versions |
|---|---|
| Old | Lean 4.24.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake 5.0.0-src+797c613 |
| New | Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc; Lake 5.0.0-src+eb6cafb |

Full archive/install comparison checked 11574 old and 17938 new entries.
Deliberately pairing the new archive with the old install was rejected.
installation-verification.json preserves those results. No custom Lean build
or v4.24 per-master cache was used; testing uses private sysroot/config overlays.
The final lean-toolchain edit belongs to migrate-root-gate.

Heavy checks are serial: actual memory.max=12884901888, memory.swap.max=0,
cpu.max=100000 100000, LEAN_NUM_THREADS=1 and explicit -j1. A lock serializes
actual Lean execution; process observations reject multiple live Lean processes
and missing -j1, while ignoring zombies. No systemd-run was invoked.
The parent reserve is 4 GiB, measured conservatively as min(host MemAvailable,
parent memory.max minus current). Limits and reserve were never relaxed.

Fresh measurement outputs must not exist beforehand. Artifact caches are disabled.
The runtime image is sha256:d9b8c34d61a9b9a3c44cab883d7d2f2619d674966ab520186f799cf32e3e0377;
read-only host executable/library mounts are recorded in every result.

Before the accepted baseline, POSIX_FADV_DONTNEED advised only regular read-only
files under the owned evidence directory and verified old install/archive,
skipping symlinks. It preserved every file. This is advisory cache conditioning,
not guaranteed eviction. Initial idle usage fell 9468493824 to 3458945024 bytes.
The same policy/roots are required for a later authorized comparison. The runner
records roots, pre/post accounting, helper hash and executed helper source.
No global drop_caches or resource-limit write was used.

## Gates, outcomes and decisive evidence

All paths below are under `/workspace/migrate-calculus-evidence`. Successful
bounded result files contain the exact invocation, Docker command, leaf commands,
versions, source/config/harness hashes, actual limits, outputs and exit codes.
Fresh reproduction needs a new output directory and the exact frozen source tree;
the current branch includes the H70 proof edit and must not be reset for a baseline.

| Gate / command | Outcome and evidence |
|---|---|
| census.py ROOT OUTPUT | PASS: base-census-v3/census.json, source-sha256.txt, ordered-modules.txt |
| bounded.py old clean, complete closure | PASS 490/490: old-clean-04/result.json; 3150.846505021 s wall, 3488944128 bytes sampled peak RSS, 8872005632 bytes minimum available; no guard stop |
| bounded.py official new full probe | BLOCKED: new-clean-02/result.json; KeySort/AST/SpecSyntax pass, Syntax.Raw fails at 597/650/665/682/684 |
| bounded.py independent new subset | Nine unchanged assigned modules PASS; LinearCountermodel failed (subsequently H70 producer), PresburgerDecision not rebuilt; new-independent-03/result.json |
| bounded.py identical fixtures and proof candidate | PASS on old-candidate-09 and new-candidate-08; four dependency modules plus both fixtures; standard-only axiom reports |
| bounded.py old interface audit | PASS: old-interface-check-01/result.json and GeneratedFrozenTypes.lean.log; all 385 / 47965 |
| interfaces.py hash ROOT CENSUS AUDIT | PASS: complete audit binding and frozen-interface-manifest.json |
| PYTHONDONTWRITEBYTECODE=1 python3 tests/h62/item6/migrate-calculus/test_tooling.py | PASS 10 tests; tooling-final.log |
| node scripts/check-layers.mjs | PASS: 857 core modules, zero reach elaborator or checked adapters; static-layers.log |
| bash scripts/coord-tools/register.sh --check | PASS exit 0; static-roots.log |
| bash scripts/coord-tools/fragments.sh --check | PASS exit 0; static-fragments.log |
| git diff --check | PASS |
| Full new directory build/comparison and final run-lean.sh | PENDING/BLOCKED; not executed past STOP; no RUNTIME_GATE_PASS |

StringApiCases.lean has three test adapters, one bounded equation-unfolding tactic
and eight fixed kernel-checked theorem statements (ASCII/Unicode, zero/overrun,
negative identity, character lists, suffix success/refusal). All eight axiom reports
are present in the final matching old/new runs. Old slicing sets are empty, old
suffix sets use propext, and new sets use only the standard three. These are
isolated standard-library controls, not full Solidity preservation proofs.
Python scanners, hashes, structural checks and timing observations are external
tests/metadata; they do not prove interface equivalence or source/backend adequacy.

Earlier attempts remain off git: old-clean-01 was deliberately stopped during
review; old-clean-02 stopped after 176 passes on an unclassified process observation
whose snapshot was not retained; old-clean-03 stopped after 262 passes on reserve.
No partial timings were combined into the accepted baseline. The corrected observer
retains process and actual offending memory snapshots; the accepted old-clean-04
starts empty and passes every job. All historical files remain preserved.

## Typed blockers and remaining obligations

1. DEP-SYNTAX-RAW-V435: migrate-syntax owns Solidity/Syntax/Raw.lean. Its five
   String/Slice API failures block 374/385 assigned modules. backfill/syntax-raw-impacts.json
   records a concrete dependency route for each. relay.sh is unavailable; requests
   were saved for coordinator pickup, not treated as acknowledged.
2. RSS-STOP: matched diagnostic wall is 21.1943729 s old versus 16.4929547 s new
   (-22.1824 percent), but sampled aggregate RSS is 867917824 versus 1756893184
   bytes (+102.4262 percent). backfill/matched-diagnostic-comparison.json records
   identical sources/settings and the escalation. New-toolchain work remains stopped
   pending root/gate classification. This subset is not the full-directory comparison.
3. Remaining new migration/build, full clean before/after comparison, new frozen-type
   comparison, full affected acceptance and final repository gates remain unfinished.
   The H70 partial producer resolves only its exact reviewed proof change.

The exact-file producer/request metadata is committed at
`tests/h62/item6/migrate-calculus/owner-requests.json` and preserved off git.
No scope, statement, premise or case exclusion is proposed. questions=[];
no new human approval or relaxed gate is inferred.

## Independent reviews and handoff

Separate read-only finder and skeptic reviewed every preparation/backfill milestone,
resource fixes, H70 source/patch bytes, complete old baseline and all type hashes.
Neither ran Lean or a Lean server. Confirmed findings were fixed: reverse roots/Bridge
coverage, module headers, census/source provenance, observation timeouts, reserve
preflight, archive/install binding, zombie handling, cache-helper provenance and
truncated type-stream rejection. Both accepted the final focused fixes. The finder
recomputed all 47965 declaration/module hashes; both verified provenance hashes,
matching fixture sources, standard axioms, 105 owner mappings and the RSS STOP.
The root worker ran the writable temporary-file control; reviewers stayed read-only.

Bulk artifacts stay off git. Deterministic generators are census.py, bounded.py,
cache.py, backfill.py, interfaces.py and export.py under the assigned scripts path.
Generated full-module candidate/import audit copies are retained off git and removed
from the checkout. No new production module registration is needed for the one-line
existing-module producer; standalone test helpers do not alter generated roots.

Export targets: `/workspace/migrate-calculus-evidence/handoff/original.patch`,
HANDOFF.md, migrate-calculus.bundle, manifest.json and SHA256SUMS. The exporter
records the final full head/base/repository and verifies the bundle; final checksum
validation is recorded separately. H70's source-only patch remains in h70-producer/.

This is the original launcher goal for rendered prompt SHA256
0992f14182a95808d7e2bf1d1e1610b8677b2b85e79f2c8697c7fb782cd1eb59.
get_goal is not exposed; coordinator confirmed that optional absence is not a blocker.
No goal was recreated/reset and no competing continuation was scheduled.
Original VM: ccarenv_b64_Y2NhcmVudl9kODQ1MTc2ZjEzOTg4MTkxOGM0YzMyZmJjYzQ5Y2U4YQ.
The coordinator owns the fresh-thread handoff on this same VM/branch/goal. Resume only
within the original scope and authorizations, preserving the STOP and complete queue.
The goal is blocked, not complete.
