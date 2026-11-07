# H44/H112 split — 2026-11-07

This is a packaging and fixture-reference correction only. The pre-split checkout
was `575d277f7d16f1a30c947711fd69a75004fe4797`, containing inherited coordinator
merges since the H82 acknowledgement. Those commits are preserved. No production
Lean file, theorem, axiom set, gate command, proof budget or resource setting is
changed by this split. No Lean validation or timing STOP rerun is performed.

Seven generated files (73,011 bytes) are removed from Git and preserved exactly
under `/workspace/migrate-optimizer-evidence/h44-split-20261107/files/`.
The 12749-byte archive is
`/workspace/migrate-optimizer-evidence/h44-split-20261107/bulk.tar.gz`.
The committed `tests/h62/item6/migrate-optimizer/BULK-MANIFEST.json` records each
original relative filename, absolute VM path, byte size and SHA256, plus archive
size/hash. These files are immutable historical evidence, not current validation.

The copied-definition Generic and Isolated fixtures are archived; neither is a
canonical test. Their historical success is not a substitute for checking the
real module. `Acceptance.lean` remains the single source of the acceptance cases,
and `Interfaces.lean` records the real imported API. Both import
`Solidity.Optimizer.Controls`, which imports the real production Pass/Laws modules.
No copies of Pass/Preserves/Validator or acceptance bodies are regenerated.
The old copy-only modes are explicitly unsupported; required real-module closure,
KeySort prerequisite, final root gates and resource/proof limits remain unchanged.

`bulk.py` verifies size and SHA256 before loading historical reports. Missing or
modified bulk fails closed; the performance STOP cannot disappear because its
JSON moved out of Git. `summarize.py` writes derived output outside the checkout.
`fixtures.py --check` validates only the retained real-module fixtures. The
historical frozen-base validator still has its original source/ancestry gates;
its clean-base reproduction is distinct from this inherited updated checkout.

The complete original assignment/queues/scope and retirement receipt remain
committed under `tests/h62/item6/migrate-optimizer/retirement/`. Prior handoffs and
raw evidence remain on the VM. H82 retirement and all unresolved migration waits
remain in force; this split does not restart the migration queue or claim a new
passing Lean/root gate. No push, merge, deployment or master change is performed.

Split validation: check_split.py passed exact seven-file preservation, archive
membership/hash and deterministic repack, unchanged canonical fixtures, missing
and same-size-tampered evidence rejection, STOP before job creation, identical
historical report reproduction outside Git, and unchanged production/build files.
Independent read-only finder/skeptic findings (summary output-path shadowing and
stale report paths) were fixed; details are in the lane review record. No Lean
was executed. Historical full migration/final gate failures are not relabeled.

The earlier detailed record below is historical. References to generated files
or copy-fixture checks describe the archived pre-split runs, not current commands.

---

# H62/H63 optimizer migration overlay — blocked handoff

Owner: `solidity-h62-6-20261106/migrate-optimizer`.
Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Repository: `/workspace/migrate-optimizer`.
Branch: `codex/solidity-h62-6-20261106/migrate-optimizer`.
The old clean checkout at `/workspace/solidity-lean` on `work` was preserved.
Published `origin/master` ancestry was verified before creating this isolated worktree.

## Checkpoint state

1. **Done:** pinned-source census and clean v4.24.0 optimizer closure measurement.
   All four assigned modules, all 35 explicit declarations, and 16 external
   prerequisite/dependency modules were inventoried. Whole-source hashes match
   `git show` at the exact base. The full old interface audit records 59 public
   constants, including generated structure API.
2. **Blocked:** official shared v4.35.0 archive verified and KeySort passed;
   the full closure fails in owner-controlled `Syntax/Raw.lean`. Independent
   branch backfill then fails in owner-controlled `Hash/CollisionBound.lean`.
   No original source edits were made or inferred to be owner-approved.
3. **Blocked:** there is no successful new full build to compare with the clean
   old build. A smaller dependency-free fixture passed both versions, but its
   measured regression exceeds 10%; all further Lean work stopped.
4. **Partial:** reviewable tooling, frozen-source and interface hashes,
   dependency requests, evidence and patch/bundle are supplied. This is a blocked
   handoff to `migrate-root-gate`, not completion of the migration or a cut-over.

## Scope and interfaces

Only additive lane tests/scripts and this document changed. The four production
optimizer files and root `lean-toolchain` remain byte-identical to the base.
No generated roots, central module maps, axiom pins, producer ownership or default
branch were changed. No pushes, merges, PRs, deployment or freeze announcement.

`tests/h62/item6/migrate-optimizer/census.json` freezes the complete source text,
imports, lexical declaration starts and budget settings. Declaration starts are
an inventory, not complete type signatures. `Interfaces.lean` logs kernel type
expressions and ordered universe parameters for every public optimizer constant.
`interface-hashes.json` contains SHA256 of whitespace-normalized records; raw
records are outside Git in each evidence run directory. Hygiene binder labels
retain fixture module names, so relocated unequal hashes are not claims of
semantic interface changes. Full original v4.35.0 interface hashing remains blocked.

`fixtures.py` deterministically copies exact original declaration blocks into
Isolated.lean (archived) (32 explicit declarations, three Scoped-dependent declarations
pending) and Generic.lean (archived) (27 explicit declarations, eight dependency-bound
declarations pending). Both preserve copied types and proof bodies. The generic
fixture's **27 explicit interface hashes match across v4.24.0 and v4.35.0**.
Generated namespace API differs in eight common constants and adds
`Pass.pipeline._f` / `Pass.pipeline.eq_def`; the full lists are in the hash report.
These generated-interface changes require root-gate review and are not silently
accepted as full frozen-interface compatibility.

Acceptance fixtures cover arbitrary scalar proposals, mixed accept/reject stages,
noncommutative pipeline order, and typed control/local-index mismatch rejection.
The full old acceptance fixture passed; the generic fixture checks scalar cases
on both versions. Intrinsic negative controls are not claimed to pass on v4.35.0.
No new `sorry`, `axiom`, `native_decide`, trusted shortcut or heartbeat override.
Existing standard axiom dependencies include `propext` and `Quot.sound`, as
printed in the evidence. Failed hash elaboration diagnostics mention `sorryAx`;
those are rejected dependency failures, never accepted proofs or new source axioms.

## Toolchain and measurement

Official Linux release archives are retained under
`/workspace/migrate-optimizer-evidence/toolchains/`:

| Version | Archive SHA256 | Actual versions |
|---|---|---|
| 4.24.0 | `b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec` | Lean 4.24.0 commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake `5.0.0-src+797c613` |
| 4.35.0 | `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d` | Lean 4.35.0 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake `5.0.0-src+eb6cafb` |

The new archive matches `/workspace/h62-coordinator-inputs/toolchain-pin.json`.
All five coordinator input hashes were checked against `sha256.json`.

Fixed Docker image: `sha256:d9b8c34d61a9b9a3c44cab883d7d2f2619d674966ab520186f799cf32e3e0377`.
One CPU; hard 12 GiB cap; memory-plus-swap also 12 GiB; host swap absent;
4 GiB available reserve monitored; no `systemd-run`. `LEAN_NUM_THREADS=1` and
explicit Lean `-j1` apply to every build/check. The private TOML disables artifact
cache and chooses a new build directory per clean run. No v4.24 master cache.
Dependency-ordered individual module invocations keep heavy jobs serial.
`measure.py` holds the writer lock, refuses existing Lean/Lake processes and
uses a Docker-created CID file for exception-safe cleanup of its own container.
No Lean MCP diagnostic tools are exposed; direct bounded per-file fixture checks
were used. The repository lean-verify skill was read; task prohibitions override
its general suggestions concerning temporary sorry/native decisions.

Wall time includes Docker startup/monitoring and Lake invocations. `wait-usage.c`
records kernel maximum child-process RSS and in-container build-shell wall time.
Aggregate process RSS is separately sampled at approximately 0.5-second intervals;
it is a sampled lower bound, not an exact aggregate peak. Neither metric is a
full-machine or full-root build measurement. Raw container inspection and process
samples are retained outside Git.

| Run | Exit | Wall seconds | Kernel max child RSS KiB | Peak sampled aggregate RSS bytes |
|---|---:|---:|---:|---:|
| `reviewed-old` full closure | 0 | 79.965077 | 1251728 | 1374248960 |
| `reviewed-new` full closure | 1 | 16.184862 | 1514844 | 1671446528 |
| `old-audit` warm full interface/acceptance | 0 | 2.671385 | 1177240 | 1289093120 |
| `isolated-old` 32-declaration branch | 0 | 20.674289 | 1165400 | 1290653696 |
| `isolated-new` dependency failure | 1 | 7.936913 | 601848 | 717381632 |
| `generic-old` 27-declaration fixture | 0 | 3.149074 | 1153468 | 1272365056 |
| `generic-new` 27-declaration fixture | 0 | 6.988802 | 1624316 | 1776824320 |

The generic fixture regressed **121.93%** in host wall, **74.37%** in kernel-timed
shell wall and **40.82%** in maximum child RSS. These are single short-fixture
measurements, not a reliable estimate of full-library slowdown. They nevertheless
trigger the required conservative **STOP >10%**; no further Lean checks ran.
The failed full/isolated new runs are not used as successful timing comparisons.
An earlier old sampled-only probe passed in 80.289565 seconds and was superseded
by the kernel-RSS baseline above. The old-audit historical result's generic scope
string predates mode-specific descriptions; it is a warm audit, as its mode states.

## Gates and exact commands

All commands ran from `/workspace/migrate-optimizer`; bulk output lives under
`/workspace/migrate-optimizer-evidence/<run>/build.log`, with `command.json`,
`container.json`, `samples.json`, `usage.json` when available and `result.json`.

| Command | Outcome and decisive evidence |
|---|---|
| `python3 scripts/h62/item6/migrate-optimizer/measure.py 4.24.0 reviewed-old` | PASS exit 0; all 20 modules built, KeySort `Build completed successfully (2 jobs).`, final Controls `Build completed successfully (21 jobs).` |
| `python3 scripts/h62/item6/migrate-optimizer/measure.py 4.35.0 reviewed-new` | FAIL exit 1; KeySort passes; Raw lines 597, 650, 665, 682, 684 fail String/String.Slice applications |
| `python3 scripts/h62/item6/migrate-optimizer/measure.py 4.24.0 old-audit audit-old` | PASS exit 0; 59 interface records and acceptance fixture |
| `python3 scripts/h62/item6/migrate-optimizer/measure.py 4.24.0 isolated-old isolated` | PASS exit 0; exact-source 32-declaration fixture |
| `python3 scripts/h62/item6/migrate-optimizer/measure.py 4.35.0 isolated-new isolated` | FAIL exit 1; CollisionBound lines 407, 660, 680 fail proofs, subsequent pinned messages fail |
| `python3 scripts/h62/item6/migrate-optimizer/measure.py 4.24.0 generic-old generic` | PASS exit 0; KeySort and exact-source 27-declaration scalar fixture |
| `python3 scripts/h62/item6/migrate-optimizer/measure.py 4.35.0 generic-new generic` | Proof fixture PASS exit 0; performance acceptance FAIL >10%, mandatory STOP |
| `python3 scripts/h62/item6/migrate-optimizer/fixtures.py --check` | PASS exit 0; generated byte reproduction |
| `python3 scripts/h62/item6/migrate-optimizer/census.py \| cmp - tests/h62/item6/migrate-optimizer/census.json` | PASS exit 0; census byte reproduction |
| `python3 scripts/h62/item6/migrate-optimizer/summarize.py` | PASS exit 0; 35 originals, 59 full old constants, 27 explicit fixture types identical; STOP recorded |
| `./run-lean.sh` | PENDING, not run: full new dependency failure and mandatory performance STOP. No final runtime gate pass claimed. |

The helper compiled with `cc -O2 -Wall -Wextra -Werror`; a child exit-7 smoke
check propagated exit 7. Static verification and review resolution are below.

## Owner requests and outstanding work

`dependency-report.json` includes all 16 external prerequisite/dependency modules,
their pinned hashes, identified migration owners, the generated incoming root and
exact-file requests `MIG-OPT-SYNTAX-RAW`, `MIG-OPT-HASH-COLLISION`.
Affected read-only consumers also include
`tests/fullscope-20261104/vo1/PipelineControls.lean`,
`tests/fullscope-20261104/vo1/YulValidatorControls.lean`, and
`tests/fullscope-20261104/vo1/ValueValidatorControls.lean` (all import Laws at
line 1). Their new-toolchain validation remains pending.
`MIG-OPT-PERF-STOP` requests root-gate investigation/disposition before resuming.
No `relay.sh` or coordinator relay endpoint exists on this VM. Requests are saved
for coordinator retrieval; absence of a reply never grants editing permission.

Remaining: owner dependency patches, performance disposition, full new original
module builds, all original new interfaces/axioms, clean successful same-profile
before/after comparison, final repository gate and root integration acceptance.
No fresh-thread replacement or new goal was created. This checkpoint is not the
entire four-checkpoint assignment; the persistent goal must be blocked, not complete.

## Independent reviews

Required finder and skeptic reviews ran read-only, with no Lean/server calls.
Both confirmed all 35 lexical declarations, source hashes and baseline limitations.
Confirmed issues fixed: exception-safe owned-container cleanup, pre-existing job
scan, CID-based identity rather than name-based cleanup, ordered universe parameters,
mandatory successful monitor samples, and pinned-base hash verification.
Final finder identified three missing affected test consumers; they are now
listed above and in the dependency report with validation pending. Final skeptic
independently reproduced hashes, declaration/API counts and timing arithmetic,
and confirmed blocked classification. Both made no edits or Lean/server calls.
Full review findings/resolutions are saved in `tests/h62/item6/migrate-optimizer/reviews.md`.

Static verification passed: `static.py` checks ancestry, scope, frozen source,
reproducible generators, trust tokens, pin, stopped bounded containers, sampled
serial processes and headroom. `node scripts/check-layers.mjs` passed with
857 core modules, zero elaborator reachability and zero checked-parser-adapter
reachability. `register.sh --check` and `fragments.sh --check` both exited 0.
No Lean checks occurred after the performance STOP.

The repository-wide documentation-path checker exited 1 because the unchanged
base document `docs/feature-work/after-roadmap-va1.md` cites absent optional
Bridge/.lake/packages/mathlib/MathlibTest/SplitIfs.lean (base line 198). This is
outside lane ownership; the exact base citation was verified with `git show`.
The complete warning log is retained outside Git. This failure is not relabeled
as a passing gate.

The measurement runner now refuses further Lean work when the saved measurement
summary records STOP. Its hash checks intentionally reproduce the pinned-base
snapshot. After owner repairs and performance disposition, root/owner review must
supply a new approved dependency snapshot and preserve both baselines before
resuming; the current script does not silently accept changed imports or sources.
