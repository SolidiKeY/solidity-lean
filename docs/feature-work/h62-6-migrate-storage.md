# H62 item 6 — Storage migration overlay (blocked)

Owner: `solidity-h62-6-20261106/migrate-storage`; repository
`/workspace/solidity-lean`; branch
`codex/solidity-h62-6-20261106/migrate-storage`; exact base
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. The fetched base is an ancestor
of published `origin/master`. Original branch `work` was preserved. No reset,
push, merge, cut-over, freeze, default-branch edit or live-owner transfer occurred.
Checkpoint 1 is complete for the assigned component; checkpoints 2–4 remain
partial/blocked. The entire assignment is NOT complete.

## Checkpoint 1: census and clean old component build — done

All 21 original Storage files are byte-identical to the base: all statements,
definitions, cases, premises and proof budgets are preserved. Census: 360 named
source declarations, 36 external source dependencies, 57 modules including
KeySort, eight direct cross-directory edges, 1,576 downstream affected modules.
Census and whole-source SHA-256: `/workspace/migrate-storage-evidence/census-base.json`.
Lexical declaration rows are navigation aids, not an elaborated ABI proof.

The authoritative baseline is `old-clean-3`: 57/57 modules and 21/21 assigned
originals PASS; wall **160.346414358 s**, peak sampled aggregate RSS
**848093184 bytes**. Actual Lean 4.24.0 commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, Lake
`5.0.0-src+797c613`; `KEYSORT_COMPONENT_PASS`; `COMPONENT_RESULT 0 None`.
Source/control unchanged checks passed, zero OOM kills, private runtime stopped.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item6/migrate-storage/census.py
PYTHONDONTWRITEBYTECODE=1 python3 tests/h62/item6/migrate-storage/acceptance.py
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item6/migrate-storage/measure.py /workspace/.setup/tools/lean-4.24.0-linux /workspace/migrate-storage-evidence/old-clean-3 --image sha256:d9b8c34d61a9b9a3c44cab883d7d2f2619d674966ab520186f799cf32e3e0377
```

All module commands, exits, wall/RSS measurements, archive/executable/source
hashes and cleanup state are in `old-clean-3/result.json` under that evidence
directory; console and per-module logs are adjacent. Reproduction requires a
NEW output directory; the runner refuses an existing directory.

Fixed resources: immutable Ubuntu runtime image above; one CPU; Docker hard
memory cap 12 GiB; total memory+swap 12 GiB (zero swap); 4 GiB available reserve;
one Lean process; `LEAN_NUM_THREADS=1`; `-j1 --tstack=131072 -M10240`.
Sources/toolchains are mounted read-only. Empty private artifact directories,
no Lake or per-master cache. RSS is sampled, not an exact high-water mark;
OS page cache is not normalized. These are per-file component elaborations,
not the repository `./run-lean.sh` full gate. The idle container sentinel is
killed for cleanup; its exit 137 is separate from each recorded Lean exit.

## Checkpoint 2: identical official toolchain — pinned; migration blocked

Coordinator inputs in `/workspace/h62-coordinator-inputs/` were checked against
`sha256.json`. Official `leanprover/lean4:v4.35.0` archive
`lean-4.35.0-linux.tar.zst`, SHA-256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Archive/extraction: `/workspace/migrate-storage-evidence/toolchains/`.
Actual candidate Lean 4.35.0 commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Lake
`5.0.0-src+eb6cafb`. Tracked `lean-toolchain` is unchanged; only root migration
owns its final edit. No alternative compiler or cross-version cache was used.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item6/migrate-storage/measure.py /workspace/migrate-storage-evidence/toolchains/lean-4.35.0-linux /workspace/migrate-storage-evidence/new-clean-2 --image sha256:d9b8c34d61a9b9a3c44cab883d7d2f2619d674966ab520186f799cf32e3e0377
```

`new-clean-2`: KeySort PASS and Keccak PASS, then external
`Solidity/Hash/CollisionBound.lean` FAIL. No assigned Storage module could run;
all 21 depend transitively on this file. Actual errors:

- line 407, `countP_contains_le`: function equality after `congr 1` unsolved;
- line 660, `countP_near_le`: `omega` fails after decide/Prop simplification;
- line 680, `countP_covers_le`: same boundary;
- six subsequent `#guard_msgs` axiom checks detect `sorryAx` from error recovery.

No failed artifact was accepted, no axiom pin changed, no `sorryAx` authorized.
Original and added source contain zero `sorry`, `axiom`, `native_decide`.
Source/control unchanged checks passed and runtime stopped.

Typed blocker **D-HASH-001 / DEPENDENCY_MIGRATION**, owner
`solidity-h62-6-20261106/migrate-hash`. Exact-file request, original source hash,
diagnostics, affected modules, all external dependency owners and root-gate
request are in `/workspace/migrate-storage-evidence/dependency-report.json`.
The hash owner must provide a statement/budget-preserving migration overlay;
this lane made no outside-scope edits. No `relay.sh` is supplied here; the
coordinator retrieves the saved request and committed artifacts from this VM.

## Checkpoint 3: comparison and final gates — blocked

No complete new build exists. Whole-build timing/RSS delta is **null**, not an
improvement or regression claim. Any regression must escalate; >10% slowdown
must STOP. ESCALATE to migrate-root-gate: partial KeySort sampled RSS grew from
261459968 to 522256384 bytes (+99.7462%); this is a per-module observation,
not a completed-build comparison. Measure full wall/RSS again after dependencies
and owned modules pass under identical settings.

Full affected validation (1,576 downstream modules), `./run-lean.sh`, and new
frozen-type comparison remain pending behind D-HASH-001 / G-ROOT-001. Passing
KeySort and provisioning are prerequisites, not proofs of those gates.
No `RUNTIME_GATE_PASS`, full gate pass or assignment completion is claimed.

## Permitted backfill — completed and reviewed

`ApiControls.lean` proves the exact list-membership function equality and the
two local interval implications, retaining the original hypotheses and exact
local copies of `Near`/`Covers`. Three named theorems, two predicate definitions,
two Decidable instances and two negative examples are test-only additions.
Both official toolchains PASS; printed axiom sets contain only `propext`,
`Classical.choice`, `Quot.sound` as applicable. These isolated proofs do not
repair the external module or establish Storage migration success.

`InterfaceHashes.lean` exports metadata-stripped kernel type/level syntax for
**1,065 constants across all 21 original modules**, including generated
constants. Its private helper and command are test-only. `report.py` rejects
duplicates, checks exact module coverage, sorts by module/name and hashes
canonical records. `/workspace/migrate-storage-evidence/frozen-interface-old.json`
is the old type manifest; raw 7.6 MB output stays off git. Type hashes concern
statements; definition semantics additionally rely on unchanged source bytes.
Generated/binder-name drift can conservatively produce different type hashes
without a semantic change. Candidate type hashes are still blocked.

```sh
# Each is bounded, serial, offline and uses a stopped measurement runtime.
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item6/migrate-storage/fixture.py /workspace/migrate-storage-evidence/old-clean-3 tests/h62/item6/migrate-storage/ApiControls.lean /workspace/migrate-storage-evidence/api-controls-old-bound.log
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item6/migrate-storage/fixture.py /workspace/migrate-storage-evidence/new-clean-2 tests/h62/item6/migrate-storage/ApiControls.lean /workspace/migrate-storage-evidence/api-controls-new-bound.log
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item6/migrate-storage/fixture.py /workspace/migrate-storage-evidence/old-clean-3 tests/h62/item6/migrate-storage/InterfaceHashes.lean /workspace/migrate-storage-evidence/frozen-api-old-bound.log
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item6/migrate-storage/report.py /workspace/migrate-storage-evidence
```

Adjacent `*.result.json` binds fixture/runner/control/source hashes, unchanged
checks, actual Lean/Lake versions, archive identity, image and stopped cleanup.
Python negative controls PASS: nested comments, strings, multi-imports, import
cycle rejection, declaration positions, actual owned/external drift and missing
inputs. These tests are tooling acceptance, not EVM/solc differential tests.

Independent read-only finder and skeptic reviews used neither Lean nor its
server. Confirmed findings were fixed: all external input identity checks,
archive/binary/image binding, signal cleanup, bounded Docker calls, host-worker
guards, source positions, PID sampling, bytecode removal, actual mutation
controls, fixture input binding, deterministic export parser. Reviewers verified
fixture definitions/premises against the original failing subgoals and parsed
all 1,065 exported constants. Remaining limits are explicitly recorded above.

Historical failed attempts are retained: `old-clean-1` had an invalid Docker
sampler (missing PID); `new-clean-1` used old CLI syntax `-M=10240`, rejected
before checking source by 4.35. The corrected spelling is `-M10240`; both
versions were rerun identically. The first type exporter used unqualified
`liftIO`; only the corrected, hash-bound export is authoritative. None of these
failed attempts supplies a passing proof or comparison.

## Checkpoint 4: reviewable partial handoff; original goal blocked

All implementation writes are within assigned scripts/tests/doc paths. No
production Storage file, central map/root, axiom pin or toolchain file changed.
No production registration fragment is needed; test-only registration note is
`tests/h62/item6/migrate-storage/registration-fragment.md`.

`export.py` exports the committed patch, prerequisite bundle, handoff, metadata,
deterministic evidence archive and checksums into
`/workspace/migrate-storage-evidence/`. Exact final HEAD is recorded in
`committed-state.json` and the exported handoff; base is stated above.
Original patch: `original.patch`; bundle: `migration.bundle`; handoff:
`handoff.md`; archive: `evidence.tar.gz`; checksums: `checksums.sha256`.
H44 bulk stays off git and is reproducible from committed generators.

Resume this exact VM/branch/existing goal after the hash-owner overlay is
available: validate original interfaces and budgets, build all 21 modules on
4.35, export/compare their types, measure a complete clean candidate against
160.346414358 s / 848093184 sampled bytes, escalate any regression and STOP
>10% slowdown, run required full affected/final gates through the root owner,
repeat independent reviews and export a complete handoff. No new goal or
replacement thread was created. Missing callable `get_goal` is optional per
coordinator; the existing frozen objective remains binding.
