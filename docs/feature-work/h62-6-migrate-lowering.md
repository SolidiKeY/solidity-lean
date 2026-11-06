# H62 item 6: migrate-lowering

Assignment: `solidity-h62-6-20261106/migrate-lowering`.
Pinned base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Branch: `codex/solidity-h62-6-20261106/migrate-lowering`.
Checkout: `/workspace/migrate-lowering` (isolated worktree).
Original checkout `/workspace/solidity-lean` was clean on `work` at
`6cf853aea0417155aca29ddb91f1767d3f3a3cc4` and was preserved.
Fetched the exact base and `origin/master`; base ancestry succeeded against
`821e3e8f4c7a5ac3a51dc5cba8be813bb173e310`. Assigned remote branch was absent.

## Status and boundaries

All four migration checkpoints remain incomplete. This checkpoint saves the
census, reproduction/resource tooling, and initial evidence. No production Lean
files, declarations, frozen statements, proof budgets, toolchain file, generated
roots, central maps, or axiom pins were changed. No new Lean axioms or `sorry`.
This is an isolated migration overlay; live producer ownership is unchanged.
Existing originals require exact-file coordination before any future edit.
No coordinator relay.sh is present in the discovered checkout/tools.

Coordinator inputs under `/workspace/h62-coordinator-inputs` were independently
verified against their SHA256 manifest. The exact active goal was supplied in
this thread; get_goal is not exposed, as the coordinator explicitly permits.

## Census and reproducibility

Run `python3 scripts/h62/item6/migrate-lowering/census.py --output OUTPUT.json`
from this checkout. The output includes every Lowering source path, whole-file
SHA256, direct imports, transitive project closure, lexical declarations and
budget directives. It is not an elaborated type or axiom audit.

Pinned census: 661 modules; families G19 36, P8 37, P8b 4, P9 15, Readonly 93,
StorageOps 92, V07 164, V08 220. There are 146 direct external import edges and
1,063 project modules in the transitive closure (402 outside Lowering).
Lexical declaration counts: 5,256 definitions, 5,480 theorems, 329 abbreviations,
42 instances, 62 structures, 103 examples, 22 inductives. No local heartbeat or
recursion-budget directives were found by the lexical scanner.

Direct external dependencies include Backend, Source, Frontend, Roadmap,
Language, Semantics, TypeGraph, Yul, Theory and Syntax. External migrations are
owner dependencies; no changes to them are authorized here.

Frozen whole-source hashes (not elaborated type hashes):

- P8/FrozenInterface.lean: `25d6c7e77168309e23710540cfd7d3ba5479d0a3b1727c1caa2b1aa4357ab662`
- P8b/Frozen.lean: `76c73f38899a03bc7d4a94571995427b2139fcf31baeccc79a93be6c04b06e64`

The generated complete census is off Git at
`/workspace/migrate-lowering-artifacts/evidence/census-base.json`.
The repository-wide `bash scripts/check-doc-paths.sh` failed (exit 1) on one
pre-existing reference in docs/feature-work/after-roadmap-va1.md:198 to the
uninstalled Bridge/.lake/packages/mathlib/MathlibTest/SplitIfs.lean. The same
reference is present at the pinned base. It is outside this lane; no fix was
attempted. No missing reference from this new handoff was reported.

Regression controls:
`PYTHONDONTWRITEBYTECODE=1 python3 tests/h62/item6/migrate-lowering/census_controls.py`
passed for local/private instances, examples, comment-hidden imports, dependency
order and cycle rejection. These are external tooling tests, not Lean proofs.

## Toolchains and measurements

Official coordinator pin: `leanprover/lean4:v4.35.0`, asset
`lean-4.35.0-linux.tar.zst`, SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Downloaded archive matched exactly before extraction.

Old: Lean 4.24.0 release, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
Lake `5.0.0-src+797c613` (Lean 4.24.0).
New: Lean 4.35.0 release, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
Lake `5.0.0-src+eb6cafb` (Lean 4.35.0).

VM: 16 GiB hard cgroup cap, CPU quota four cores, no configured host swap.
The runner uses LEAN_NUM_THREADS=1, a 4 GiB host/cgroup available reserve,
250 ms process-group RSS sampling, and foreground command/process-group
assumptions. Per-process Lean memory is bounded with -M11000; this is not a
separate hard 12 GiB aggregate job cgroup. No systemd-run is used.

Both prerequisites passed:
`lean -j1 -M11000 --tstack=131072 Solidity/KeySort.lean` with each absolute
versioned binary. Old: exit 0, 3.012218324 s, sampled peak 257,933,312 bytes.
New: exit 0, 2.276659811 s, sampled peak 506,077,184 bytes.
The RSS increase is about 96%, while wall time improved about 24%.
QPERF1 was resolved by the coordinator on this continuation. Verbatim answer:

> a per-module time or memory increase does not stop a migration lane. Record
> the before/after numbers for that module and continue to the matched clean
> full-build comparison the task requires; the coordinator reports memory/time
> growth to the human with the cut-over escalation.

The KeySort numbers are retained as escalation evidence. They do not block the
matched clean full-build comparison. No RUNTIME_GATE_PASS claim.

The first old full gate was INVALIDATED: its timing/guard runner died across
the previous turn boundary while its child continued. The skeptic detected
this on resume. Only the verified owned orphan group was stopped; partial
logs and build were preserved under invalid-* artifacts and are not accepted
measurements.

The clean old full gate is restarted via a detached `supervise.py` using
`nohup setsid -f`, then `./run-lean.sh`, using a private config
created by `prepare_config.py`: cache disabled, fresh .lake/build, private empty
XDG cache, and -j1 -M11000 on all Lean libraries/executables. A process snapshot
confirmed one Lean worker and the actual bounded arguments. Its final outcome
and complete wall/RSS measurement remain pending. Old/master artifact caches
are not used. The configuration and full log are off Git.

The initial waiting pipeline also died and was not accepted. The replacement
`supervise.py` starts `pipeline.py` only after a passing old gate. It waits
for old results, acquire the writer lock, verify source/configuration provenance,
preserve the old build, create an empty new build, and pass the same held lock
into the new bounded run. Both wall and sampled RSS regressions escalate;
either exceeding 10% stops. Failed/incomplete measurements cannot pass.
No performance comparison is accepted until both complete equivalent runs pass.

## Independent reviews

Read-only finder `/root/finder_setup` and skeptic `/root/skeptic_setup` used no
Lean server or Lean checks. Findings and resolutions:

- Added omitted instances/examples and then seven local instances; regenerated
  census. Skeptic checked all 661 source hashes and counted 42 instances/103 examples.
- Added cycle rejection and explicit dependency-order controls.
- Runner now rereads Git status, checks host reserve and configured host swap,
  and states its sampled/foreground limits. Explicit -j1 verified in active ps.
- Pipeline now acquires lock before reading old result, transfers the same fd
  to its child without an unlocked transition, checks provenance, and compares
  both wall and RSS. Missing metrics now have a typed blocker/nonzero exit.

The resumed finder additionally found two deriving commands and two instance
attribute commands missing from the lexical inventory. API directives are now
recorded, with regression controls and explicit pinned-base source/path checks.

The resumed skeptic detected the dead runner/pipeline and invalidated the old
run. Both reviewers checked the replacement detached supervisor, atomic
five-second runner heartbeats/results, inherited-lock transfer, and reliable
owned-group cleanup even after a leader exits. Lightweight controls passed for
normal completion, inherited locks, signals/descendants, and dead-leader cleanup.
The detached smoke process survived a tool return. Monitoring continuity and
complete final metrics remain required before accepting the restarted run.

Both reviewers confirmed those fixes. Full migration milestone reviews remain
pending; these reviews accept no unrun gate or semantic compatibility claim.

## Outstanding work and handoff

1. Complete clean old baseline and census/API compatibility (checkpoint 1).
2. Obtain exact-file owner coordination for any required edit;
   compile with the identical new toolchain, fixing only assigned originals
   and preserving all types/semantics/proof budgets (checkpoint 2).
3. Build every assigned module, final repository gate, before/after wall/RSS
   comparison and independent migration reviews (checkpoint 3).
4. Export final migration patch/bundle, accepted frozen-interface hashes and
   cross-directory report to migrate-root-gate (checkpoint 4).

No whole-goal completion, push, merge, PR, cut-over, or freeze announcement.
Saved tooling patch/bundle and immutable evidence manifest live under
`/workspace/migrate-lowering-artifacts`; live build logs are not checksum-bound
until closed. See the external handoff for exact committed head and current state.
