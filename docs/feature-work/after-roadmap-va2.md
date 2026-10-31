# VA2 AU03/AU04 handoff

Status: runtime recovered; AU03 supporting notation/measurement controls checked. AU03 walk/closer and AU04 sharing remain incomplete.

Repository: `/workspace/va2-sharing`. Branch:
`codex/solidity-automation-20261031/va2-sharing`. Exact base:
`8bd8742ad987d566f7ba7624372cec1c020be07c`.

## Setup checkpoint

Fetched `origin master` and the exact base from the configured GitHub remote.
`origin/master` equals the base; merge-base ancestry passed. Preserved the
older clean `/workspace/solidity-lean` checkout at `9b24b57311b8daf0d4cd01b52bf420fd024c1d3a`
on `work`, creating this isolated worktree instead. Recorded exact AQ1/AQ2
human answers in `docs/solidity-scope.md` before implementation. No Lean
source edits. `git diff --check` passed.

Independent read-only finder `/root/setup_finder` and skeptic
`/root/setup_skeptic` both found no issues with branch/base/ancestry or exact
approval receipt; neither used the Lean server. Evidence:
`/workspace/va2-sharing-artifacts/evidence/reviews.md`.

## Runtime blocker

Actual tools: Lean 4.24.0, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake 5.0.0-src+797c613
(Lean 4.24.0). Cgroup memory.max is 17179869184 (16 GiB), swap.max is
`max`; OS reports no swap. Required 12 GiB/no-swap process-group bound
is not available: cgroupfs is mounted read-only, user systemd has no bus,
system systemd is not PID 1, and sudo is absent. Per-process address-space
limits do not establish an aggregate process-group limit. No heavy job,
LSP session or build was started. No aggregate build RSS measurement exists.
KeySort and RUNTIME_GATE_PASS remain pending. Raw command outcomes:
`/workspace/va2-sharing-artifacts/evidence/setup.json`.

Unblocking requires an executor with a delegated writable cgroup or an
already-enforced 12 GiB/no-swap scope. No theorem, budget or resource
requirement has been weakened. No automatic approval rejection occurred.

## Full queue accounting

All implementation remains pending: baseline PolySize, doubling family,
joined mapping-key failure, loop leaf past anon and speed-history audit;
AU03 located warning and controls; dependent-assignment joins and general
soundness/size proofs; conditional notation/printer roundtrip and restored
chain rows/ifTrace; Boolean-key kernel split; two-base/beyond-splitMax
joined values; AU04 fresh intrinsic call-result locals with freshness,
evaluation and validity transport; loop repeated-leaf repair and controls.

All backfill remains pending: notation/printer/chain controls;
Int.negSucc affine controls; SplitTo Solidity docstrings; proof_size
relocation/pins; certifyLong context discovery; warning/sharing/loop
fixtures. Integrated narrower gap-worker deliveries still need auditing.
Return to dependencies after backfill; do not take VA1 Decision/Residue,
AU05/AU06 or compiler files.

All required proof/validation gates remain pending: per-file diagnostics,
affected closure, full bounded ./run-lean.sh, strict automatic gate,
trust/axiom audits, docs-versus-exact-base comparison, measurements of walk
and leaf growth/time/RSS, and independent finder/skeptic reviews for each
implementation milestone. Setup reviews do not cover those milestones.
No new theorem premises or external-test correctness claims exist.

Artifacts will include a cumulative patch and Git bundle, this handoff,
evidence archive and SHA256 manifest under `/workspace/va2-sharing-artifacts`.
No push, merge, PR or tags were performed. The assignment is incomplete.

## Investigated runtime recovery (2026-10-31)

The earlier cgroupfs/systemd failure evidence remains intact. No unchanged
cgroupfs/systemd probe was retried. Consulted the supported
`cloud-environment-runtime` skill and its `references/docker.md`.
The same attached VM has the platform-managed Docker 28.4.0 daemon at
`unix:///var/run/docker.sock`; no daemon was installed, started or restarted.
Explicit local endpoint selection cleared Docker endpoint/context/TLS
selectors only, as required by the skill. No policy, authentication,
privilege, catalog or VM changes were made. Podman/nerdctl are absent.

A task-owned child container using pinned image
`debian@sha256:f6b08b09a05725f9431502d3b5714f5c4576e82c1a84fa1debe0c24a7e0c3ec4`
mounted the exact existing `/workspace` tree, including the isolated checkout
and existing toolchain. It ran as UID/GID 1000 with `--network=none`,
`--memory=12g --memory-swap=12g`. Actual child cgroup values were
`memory.max=12884901888` and `memory.swap.max=0`. The daemon reports
MemoryLimit=true and SwapLimit=true. This is the aggregate hard limit;
the RSS sampler is measurement only. Containers were removed on exit.

Actual toolchain in that bounded container:
Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
Lake 5.0.0-src+797c613 (Lean 4.24.0).
With `LEAN_NUM_THREADS=1`, the command
`lake env lean -j1 --tstack=131072 Solidity/KeySort.lean` passed.
The evidence script prints RUNTIME_GATE_PASS only after those cap checks,
version outputs and successful KeySort exit. Recorded wall time is 1 second
(coarse whole-second measurement), sampled aggregate process RSS peak
301932 KiB, and cgroup peak accounted memory 114503680 bytes. These are
different measurements; shared resident pages can be accounted outside this
child cgroup. Neither number is a walk/leaf growth benchmark.

An initial Lake build attempt failed with `permission denied` for `//.cache`
and emitted a Lean command without explicit -j1; it is retained as a failed
attempt and does not support the runtime gate. The passing explicit invocation
sets the existing writable `XDG_CACHE_HOME=/workspace/.setup/cache`.

Original checkpoint `29aec17e607a5dfc585a0e4a49990dc8e3f751c3` and every
original artifact were preserved; all original SHA256SUMS entries verified.
New evidence is separately stored under
`/workspace/va2-sharing-artifacts/runtime-recovery/`, with exact command arrays,
exit codes, raw logs and reproducible probe scripts. No implementation files
were edited; all work/backfill/proof/validation obligations listed above remain
open. The same existing blocked goal awaits coordinator reactivation based on
this evidence; no replacement goal or competing continuation was created.

Independent recovery finder `/root/setup_finder` accepted the runtime evidence
and requested a committed handoff with separately checksum-bound recovery
artifacts. This recovery checkpoint addresses that finding. Independent skeptic
`/root/setup_skeptic` accepted the KeySort runtime gate and flagged that RSS
sampling sums visible `/proc` processes without a separately recorded PID
isolation assertion; treat that RSS number as a visible-process sample, not an
independently certified process-group maximum. Both reviews were read-only,
without Lean server or gate reruns. Evidence: `runtime-recovery/reviews.md`.

## Supporting AU03 checkpoint: notation, measurements and controls

This checkpoint does not finish AU03 or AU04. It supplies the conditional
notation needed to state joined leaves, moves the measurement command out of
an example, and preserves regressions for the smaller M8 items. No rule,
strategy, observation, validity/hash premise, verdict pin, proof budget or
exclusion changed. The unconnected `Syntax/LoopWarnings.lean` working file is
not part of this checkpoint; its classification review is still being applied.

### Frozen-base measurements and source audit

Raw commands and exact archived fixtures are in
`/workspace/va2-sharing-artifacts/work/`. All Lean work runs in the same managed
Docker child, hard `memory.max=12884901888`, `memory.swap.max=0`, network none,
`LEAN_NUM_THREADS=1`, explicit `-j1`, writer lock held, no overlapping build/LSP.
The warm runner is `work/bounded.py`; it records command arrays and elapsed time,
visible-process RSS samples and cgroup memory peak. The RSS sample can count
shared pages more than once; it is a measurement, not the hard cap.

`baseline-cold.log` passed the focused cold build (234 jobs, 1552.67 s wall,
3,577,240 KiB sampled RSS, 4,228,907,008 bytes cgroup peak).
`baseline-measure-build.log` passed the archived baseline fixture (41.89 s,
1,264,396 KiB sampled RSS). Its walk and leaf sizes are separate:

| Family | k | Walk nodes | Leaves (term sizes) |
|---|---|---|---|
| F1 joined assignments | 1,2,3 | 8,13,18 | 25,41,57 |
| F2 invariant loop | 1 | 10 | 17,49,32 |
| F2 invariant loop | 2 | 17 | 17,49,44,78,59 |
| F3 loop with branches | 1 | 14 | 20,64,37 |
| Offset doubling calls | 1,2,3 | 5,5,5 | 20,20,20 |
| Non-offset `x*3+1` doubling calls | 1,2,3 | 5,5,5 | 26,34,50 |

F2's largest leaf past anon took 1.137 s (raw 14,886,087 heartbeats) at k=1,
3.129 s (raw 44,305,622) at k=2; F3 k=1 took 4.830 s (raw 64,045,537).
Usual displayed heartbeat units divide these raw counts by 1000.
`baseline-fuel.log` retains F3 k=2's default-budget failure. No budget increased.
`baseline-extras-tree.log` confirms literal loop bounds 2/4 still unroll to
proved exact results in the kernel strategy; the named proof-tree builder
stops at those `.auto` loops (5 nodes, 1 open leaf). Kernel step counts were
37/61. That named-tree limit must not be reported as kernel unrolling failure.
The actual retained Boolean-key mapping obligation reaches its joined mapping
leaf and still needs `sol_leaf; sol_close`. Multi-assignment branches split.
Two-base/beyond-limit closure and more baseline controls remain to be measured.

Speed history inspected before representation work: `fe105b52` (joins/closer
expansion), `3dbf353a` (strict-redex sharing), `c98bd4b2` (bounded kernel input),
and `00a88bb9` (factor folding). Preserve their whole-leaf/redex safeguards.
Integrated handoffs for kint anchors, quantified ledger, negative memory,
parameter/struct witnesses and written-memory hash were audited; their existing
deliveries are reused, with no edits to those worker modules or VA1 files.

### Implementation and proof boundaries

- `SurfaceNotation` reads conditional terms in both term equality and program
  expression equality through existing intrinsic `NTerm.ite`/ternary readers.
  Nested terms, printed-body rereading, invalid guard/branch types and lazy
  selected versus failing unselected branches have controls. This is not a new
  calculus rule. Broader signed printer/type-inference coverage remains open.
- `#proof_size` moved unchanged from PolySize to Tools/ProofTree, with positive
  walked and false/open pins in Examples/ProofTree. The existing unsafe
  measurement trust entry moved with it. Measurements are not soundness proofs.
- `CloseJ.affine` recognizes normalized literal `Int.ofNat`/`Int.negSucc` and
  conservatively leaves symbolic `Int.negSucc n` as a base. Direct metatests
  cover negative/zero/positive literals and signed addition/subtraction offsets.
  Signed validity/refutation controls use ordinary `sol_close`/`sol_refute`.
- `closeSide`/`closeArith` no longer dereference premises absent from a sibling
  goal's local context. Bound proof IDs flow to `omegaIn`, which already skips
  IDs absent from its local context. Detailed failed range goals are retained.
  **Forced signed sequential closure still fails** at a range side condition:
  `mcp-context-fix-stub.log`, `mcp-signed-literal-detail.log`, archived
  `JoinControls-with-open-step.lean.txt`. General closure is not evidence for
  sequential closure. Earlier solved-state MCP trials were invalid evidence;
  later open-goal trials and per-file diagnostics exposed the limitation.
- SplitTo congruence documentation now states its Solidity context; theorem
  signatures/proofs are unchanged.
- `certifyLong` already discovers the nonempty peeled context correctly in the
  frozen base. Its closed input context `[]` is required by its initial state;
  it extracts and uses the peeled context consistently. No production change
  was appropriate. LongContext supplies `n=5`, pins the resulting nonempty
  context and builds a real kernel certificate refuting a false length claim.
  It also checks no certificate for a true supplied candidate or an unsupplied
  binder. Candidate refusal is not a universal validity proof.

No new axioms/sorry/admit or external dependencies. `lean_verify` on
`conditionalJoined` and `falseLengthRefuted` reports exactly `propext`,
`Classical.choice`, `Quot.sound` (`mcp-backfill-axioms.log`). Its optional source
scan reports rg unavailable inside the child; the host trust/source checks
cover that separate boundary. Kernel theorem certificates establish validity
or refutation, whereas source parser/metatests, sizes and timings are tooling
controls only.

### Gates and independent reviews

All commands below use the absolute work path above; raw `.log` and command
metadata `.json` are retained, including every failed attempt.

- Per-file MCP full diagnostics passed: ProofTree tool, SurfaceNotation,
  LeafSplit, Steps, PolySize, DlNotation, Examples/ProofTree, JoinControls and
  LongContext. The no-build LSP launcher prevents implicit compilation and
  enforces explicit `-j1` server/workers; stale imports produce a failed check
  then a separate bounded build. The early non-j1 implicit setup-file attempt
  was stopped and retained as failure, not a pass.
- `bounded.py backfill-checkpoint-build build` with targets JoinControls,
  LongContext, DlNotation, PolySize, Examples.ProofTree, Tactics.Join passed
  297 jobs, 171.03 s wall; sampled RSS peak 2,933,692 KiB and cgroup peak
  2,304,315,392 bytes. Existing joined-family examples passed unchanged.
- `node scripts/check-automatic.mjs --strict` passed: 491 automatic, 61 with a
  step budget, 0 manual; 11 refuted; 0 pending. This checkpoint's static gate
  does not replace the final TestSuite timed build gate.
- `bash scripts/check-trust.sh` passed: 1050 sources, 248 inventoried
  implementation/recovery sites, 0 findings. `git diff --check` passed.
- `bash scripts/check-doc-paths.sh` **failed** with 48 missing references.
  Exact frozen-base snapshot plus private Git index reproduces byte-identical
  raw output (`base-doc-paths.log` vs `backfill-doc-paths.log`). No new path
  finding; the repository gate itself remains failed, not relabeled pass.
- Root per-file diagnostics and the full final `./run-lean.sh`, full affected
  TestSuite timing/strict gate, full axiom/trust/import audits remain pending
  for the entire assignment. Runtime KeySort passed as recorded above.

Independent read-only finder `/root/setup_finder` and skeptic
`/root/setup_skeptic` reviewed this checkpoint without Lean/server/build/writes.
They requested branch-type rejection, explicit printer-body rereading and root
registration of LongContext; all were added. Both accepted the remaining
changes without a blocking soundness finding, conditional on reporting the
forced signed sequential limitation. The skeptic's bound-ID question was
checked against `omegaIn`'s `lctx.find?` guard. Reviews exclude the pending
warning implementation. Raw review transcription: `work/reviews-backfill.md`.

Shared integration hunks are exactly two additive imports in Solidity.lean,
two new example module-map rows and the ProofTree command clause in its row.
No Rules.lean change. AQ decision hunk remains the setup checkpoint's only
scope-record change. The cumulative patch records the exact hunks.

### Remaining whole-assignment obligations

AU03: connect/review located warnings for DSL/imported/reachable loop bodies,
retain unrolling and remeasure PolySize; sequential dependent-assignment joins
with freshness/order/typing, soundness and size laws; restore original chain
programs/add ifElseJoin row/finish ifTrace; kernel Boolean-atom split with
substitution on the actual mapping-key pin; two-base/beyond-splitMax joined
closure at existing budgets; resolve the signed sequential range limitation.
AU04: genuine bounded non-offset doubling-call leaf sharing through intrinsic
fresh locals with freshness/evaluation/validity proofs; measured walk AND leaf
growth across k; repair and remeasure actual loop leaf cost past anon, with
positive/negative controls. None of those is completed by constant walk size.
Final bounded full gates, timed automatic gate, independent reviews for each
remaining checkpoint, exact final patch/bundle/evidence/checksums remain due.
The existing persistent goal stays incomplete; no competing goal was created.
No push, merge, PR or tag publication.
