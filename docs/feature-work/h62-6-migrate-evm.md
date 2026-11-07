# H62 item 6: EVM toolchain migration

Status: **H82 retired/stopped by explicit user PAUSE; full assignment unfinished**.
The platform goal API has no PAUSED operation; this capability failure is
reported rather than substituting complete/blocked or scheduling continuation. The old census/build is complete.
The new compiler fails in an owner dependency and the observed prerequisite
slowdowns exceed the frozen STOP threshold. No production EVM file was changed.

## Original VM, goal and checkout

- Batch/owner: `solidity-h62-6-20261106/migrate-evm`.
- VM: `ccarenv_b64_Y2NhcmVudl9lZjMyYTI0MTM0ZjA4MTkxODY2NmEyMGVlYjM3YzFiMg`.
- Repository: `/workspace/migrate-evm`.
- Branch: `codex/solidity-h62-6-20261106/migrate-evm`.
- Exact base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
- Original goal rendered-prompt SHA256:
  `6ed54463661ca87ff6264a7b0ba8ed9af5c6f39762c2d1a970be04ffe57fd9cd`.
  The launcher-created goal remains unfinished. No goal ID/get_goal is exposed;
  coordinator explicitly confirmed that inspection absence is not a blocker.
  No goal was created, reset or replaced.
- Original clean checkout `/workspace/solidity-lean` was preserved at `6cf853aea`.
  `git fetch origin master` recovered the missing pin. The exact base passed
  `git merge-base --is-ancestor` against published origin/master
  `821e3e8f4c7a5ac3a51dc5cba8be813bb173e310`; a new owned worktree/branch was
  created at that base without resetting/discarding existing work.
- All five `/workspace/h62-coordinator-inputs` files match `sha256.json`.
  Official new release SHA matches `toolchain-pin.json` exactly.

This overlay does not take ownership from live producer lanes. Exact-file
coordination remains required before existing-source edits. No relay.sh or Lean
MCP diagnostics tool is exposed here. Owner requests are saved for the coordinator
through the authorized saved-task/handoff route; no absent reply was treated as
permission. No push, merge, PR, master change, cut-over, deployment or producer
freeze was performed. No H55 work was duplicated.

## Four-checkpoint state

| Checkpoint | State and evidence |
|---|---|
| 1. Pinned import/API census and clean old measurement | Done: 277 assigned files, 386-module closure; all old modules pass; all 14,079 elaborated declarations inventoried. |
| 2. Identical official new release and adaptations | Blocked: release verified; Syntax.Raw owner repair and performance STOP resolution required before EVM adaptations can proceed. |
| 3. New modules, clean timing acceptance and affected gates | Blocked: three prerequisites pass; Raw fails; zero new-toolchain EVM modules checked. Full new timing/API comparison and final Lake/run-lean gates remain pending. |
| 4. Migration patch and root-gate handoff | Partial: reviewed tooling, old frozen hashes, dependency report and patch/bundle handoff supplied; completed migration patch/new API hashes cannot yet be supplied. |

## Exact releases and fixed measurement settings

Official archives retained in `/workspace/migrate-evm-artifacts/toolchains/`:

| Release | Archive SHA256 | Actual compiler/Lake |
|---|---|---|
| v4.24.0 | `b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec` | Lean `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake `5.0.0-src+797c613` |
| v4.35.0 | `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d` | Lean `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake `5.0.0-src+eb6cafb` |

The latter is exactly `leanprover/lean4:v4.35.0` from the coordinator's official
Linux archive, not a self-build or independently selected release. Direct private
binaries were used for tests; tracked lean-toolchain remains v4.24.0. Its final
edit belongs exclusively to migrate-root-gate.

Both final measurements use committed instrumentation
`c9df585f9c78134adc2f14ff383925d207502679`, identical original source census,
empty independent private olean directories, no per-master artifacts, and the
same Docker image:
`python@sha256:935c3c5b12357a7e10caa9c1e6ca5692344d97cf229832ef584be2cec9fc03df`.
VM cgroup is 16 GiB/four CPUs, host swap zero. Each measurement enforces 12 GiB,
zero swap, one CPU, 128 PIDs, read-only source and no network; checks outer
4 GiB reserve before/during each file; sets LEAN_NUM_THREADS=1 and explicit
`--tstack=131072 -j1`; stops any module at 300 seconds. One Lean job runs at a
time, with the repository writer lock. No systemd-run was used.

Peak RSS is kernel wait4 per child; process-group sampled RSS and cgroup peak
memory are separately recorded, never conflated. These are clean private olean
checks, not a full Lake executable/library-root build. OS page cache was not
claimed cold. Final repository/affected acceptance remains blocked.

## Actual build gates and mandatory performance escalation

| Command | Actual result |
|---|---|
| `bash scripts/h62/item6/migrate-evm/run-bounded.sh 4.24.0 old-clean-final` | Exit 0: 386/386 closure modules, 277/277 EVM; 2102.710780899 s wall; kernel peak RSS 3,111,133,184 bytes. No OOM or resource stop. KeySort passed first. |
| `bash scripts/h62/item6/migrate-evm/run-bounded.sh 4.35.0 new-clean-final` | Exit 1: KeySort/AST/SpecSyntax passed; Syntax.Raw failed with five API errors. 78.519332428 s until failure, kernel RSS 1,540,100,096 bytes. EVM checked: 0/277. This is not a full new measurement. |

The successful prerequisite prefix regresses from 18.196041 s to 45.277680 s,
**+148.83 percent**. Individual measured wall changes: KeySort +55.00 percent,
AST +120.26 percent, SpecSyntax +301.11 percent. RSS comparisons are in
`evidence/performance-stop.json`. These are single observed prefix measurements,
not statistical estimates or a total EVM delta. The complete old/new EVM aggregate
is unknown. The frozen rule says any regression escalates and greater than ten
percent STOP: **B-PERF-PREFIX is STOP**, not a pass or merely an unmeasured gate.
No further new-toolchain Lean checks were run after this finding.

ESCALATE B-PERF-PREFIX to migrate-root-gate/coordinator. Safe owner actions are
(1) investigate and supply a scope-preserving performance remedy before any
reviewed rerun, or (2) retain the blocked handoff while owners resolve migration
inputs. Neither action permits weaker statements/budgets or authorizes this lane
to lift STOP. Live proving ownership continues unchanged.

## Typed dependency request

**B-SYNTAX-RAW: OUT_OF_SCOPE_OWNER_MIGRATION_DEPENDENCY**.
Owner: `solidity-h62-6-20261106/migrate-syntax`; relay/root reviewer:
`solidity-h62-6-20261106/migrate-root-gate`.

Read-only `Solidity/Syntax/Raw.lean` fails at lines 597, 650, 665, 682 and 684:
`hashMember?`, `fnParts?`, `canonFnTy`. String.drop now yields String.Slice;
Slice.toList and String.dropRight are unavailable in those forms, and the
partially applied endsWith predicate has changed shape. The exact diagnostics
are in `evidence/new-clean-final/Solidity.Syntax.Raw.log`.

All 277 EVM originals transitively depend on Raw; no independent original module
can bypass it. Owner must supply a reviewed v4.35.0 adaptation preserving exact
types/semantics/budgets and coordinate the authorized fixture/overlay route. Raw
was not edited. No permission to edit existing EVM originals was inferred.
The complete report records 39 direct external edges to 17 distinct modules,
and all 109 external closure modules with source hashes in the census.

## Frozen interfaces and substantive bounded backfill

Census freezes whole source bytes, imports and explicit proof budgets for every
assigned file and dependency. Lexical EVM counts are 4,319 declaration keywords,
zero sorry and zero axiom tokens; keyword counts are not elaborated APIs.

The old streaming reader [ReadApi.lean](../../tests/h62/item6/migrate-evm/ReadApi.lean)
loads the already-proved private cache at trust level 0 without elaborator
extensions. It emits selected module origins, kinds, universe parameters and
exact structural expression DAGs. ExprStructEq retains binder names/annotations;
all twelve expression constructors, metadata and let nonDep flags are retained.
Structural memoization avoids expanding enormous repeated type subtrees.

`bash scripts/h62/item6/migrate-evm/run-inventory.sh 4.24.0
/workspace/migrate-evm-artifacts/evidence/old-clean-final old-api-sealed` exited 0.
Its controls distinguish names, annotations, nonempty metadata payloads, universes
and let flags within the same graph; sharing/compaction controls also pass.
The export contains **14,079 unique declarations across all 277 modules**:
8,947 theorems, 4,113 definitions, 185 inductives, 646 constructors,
186 recursors and two opaques; zero axiom declarations. No free/metavariables.
The complete metadata has 1,352,130 DAG nodes, 44,886,070 bytes and SHA256
`3c1a4cbf0308c7e82700a52fe60a8c12ed84cb0a0af11ee6a07ac59d5f49c61d`.

The [sealer](../../scripts/h62/item6/migrate-evm/seal-api.py) validated schema,
field types, backward references, roots, reachability, node/name uniqueness,
name ordering and complete positive module coverage. It produces
`evidence/frozen-interface-hashes.json`, including exact source and old API
hashes for every assigned module; new API is explicitly null/blocked.
No module has a zero-declaration API; none was silently dropped.

Acceptance: scanner five tests and sealer eight tests passed. Negative controls
include changed theorem source, missing/cyclic imports, lexical masking,
malformed natural/edge fields, unreachable/duplicate nodes, duplicate names,
unsorted data and empty/missing module coverage. Synthetic schema fixtures are
external controls, not Lean proof evidence. Cache preflight rejects incomplete,
wrong-version, missing-artifact or source-drifted caches; candidate-census input
is available for later coordinated adaptations.

Several retained metadata prototypes hit the reserve guard, or were deliberately
stopped while replacing expensive command output/raw expanded expressions with
the streamed DAG reader. One raw type row exceeded 24 MiB. Those attempts are
not passes. Their logs/source prototypes stay off git. Cache advice released
only owned inactive release/source/static-library pages after measurements;
no files or bounds were removed/raised. Obsolete command-based drivers are
retired. The two initial build-instrumentation pilots were also deliberately
stopped and never counted as completed baselines. See setup/acceptance records.

## Reviews, proof boundary and final handoff

Independent read-only finder `/root/finder_census` and skeptic
`/root/skeptic_census` used no Lean server and made no edits. Findings fixed:
exact wait4 RSS/hard limits; resource preflight; exception-safe group cleanup;
interruptible owned-container cleanup; typed OOM events; lexical quote/multiline
imports; candidate census support; complete cache provenance; DAG collision
controls; schema/reachability/coverage checks; obsolete tooling retirement.
They confirmed all 277 originals depend on Raw and independently identified the
mandatory performance STOP. Review evidence is exported with the handoff.

Old Lean compilation checks the original declarations/proofs. IO metadata
fingerprints and Python controls do not replay proofs, establish definition-body
equivalence, or prove new-toolchain compatibility. Full new EVM proofs, API
comparison, all affected acceptance, final Lake/run-lean gate and accepted clean
aggregate wall/RSS comparison remain unfinished. Existing production declarations,
frozen statements, premises/exclusions/observations, intrinsic representations,
proof budgets and axiom pins were not modified; no new sorry/axiom/native trust
shortcut was introduced. No production module registration fragment is needed.

Artifacts are off git under `/workspace/migrate-evm-artifacts/`: final original
patch, incremental bundle, HANDOFF.md (full committed head/base), evidence archive
and SHA256SUMS. The coordinator owns the next fresh-thread handoff on this exact
VM/branch/goal after owner inputs resolve all blockers; do not self-launch a
replacement goal. Resume only within original scope and after the STOP/owner
conditions are satisfied. Goal must not be marked complete on this partial lane.

## Final static gate results and pre-existing documentation blocker

Layer check passed: 857 core modules, zero reach the elaborator or checked parser
adapters. Generated-root registration and fragment checks passed without editing
those files. Python/shell syntax, scanner/sealer tests, cache negative controls,
source-census equality and diff whitespace checks passed.

In the archived lane run, `bash scripts/check-doc-paths.sh` exited 1 because
an earlier version of the after-roadmap VA1 note cited an absent optional Mathlib
cache test. The stable provenance is the
[pinned upstream SplitIfs test](https://github.com/leanprover-community/mathlib4/blob/f897ebcf72cd16f89ab4577d0c826cd14afaafc7/MathlibTest/SplitIfs.lean),
also linked in the current after-roadmap VA1 note. This is an upstream source
reference, not a claim that a local cache file exists. The historical failed gate
remains part of the handoff alongside the syntax/performance blockers.

H70 documentation repair, 2026-11-07: the inherited **B-DOC-CITE** literal
cache-path citation is replaced by that pinned upstream reference. No cache file
is invented, no Mathlib dependency is added, and the documentation checker is
unchanged. This repairs the citation only; it does not turn the historical gate,
axiom inventory or v4.35 migration into an acceptance pass.

## Final H82 retirement checkpoint

Successor/handoff_to: solidity-h62-6-20261106/migrate-root-gate. The successor
queue relay was accepted before the user ordered retirement. This worker makes
no new proof implementation and stops after final head acknowledgement. All
production EVM files, statements, definitions, budgets, axiom sets and exclusions
remain unchanged. No new timing or Lean run is performed, and the explicit
performance STOP is retained.

The complete original assignment, original goal context, unabridged work/backfill
queue, exact280-entry scope, complete current H82 authority, checksum-matching
H78 root request and every pending item/wait are committed under
`tests/h62/item6/migrate-evm/handoff/`. Their SHA256SUMS is committed as well.
Identical copies and actual delivered coordinator inputs are in the evidence
archive, using portable archive-relative paths. The original rendered-prompt
byte file is unavailable; full first-user assignment is transcribed from the
original thread, with scope/120 owner keys checked against the verified registry.
Its actual file hash is reported separately; no false rendered-digest match is
asserted. The copied H78 ticket exactly matches the supplied749df2f...41f5 digest.

H82 removes pending exact-file permission waits for pure statement-preserving
proof/import/doc work; B-DOC-CITE is now successor work, not a permission wait.
Definition-body/API/budget/axiom/exclusion changes still require owner/frozen-pair
rules. H78 visibility and old/new generated public API/shim evidence remain
incomplete. Implemented shims: none; no public generated exclusion is authorized.
Full H68/H69/H71/H80/H81 policy texts and the H78 requirements/staged owner files
were not delivered here, so host paths are recorded only as provenance.

No H71 push authorization was verifiable from supplied inputs. Original no-push
permission therefore remains; no push (including coordination refs), master
change or external/Claude-owner message is sent. Final cumulative patch/bundle,
head-specific handoff, evidence archive and checksums are exported locally for
the survivor. Prior VM, branches, artifacts and proof caches are preserved.

PAUSE TOOL LIMIT: only stop_goal(complete|blocked) is exposed; there is no PAUSED
operation. The requested platform transition cannot be performed. The worker
obeys the explicit user pause and will not auto-continue, mark complete, create
or reset a goal, or substitute a different goal outcome. The final stopped/head
acknowledgement is the boundary for successor integration; no live producer
ownership is silently transferred.
