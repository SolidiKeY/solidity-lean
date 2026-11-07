# H10 P5 MemoryLoop finite-horizon helper

Helper branch: `codex/solidity-inline-assembly5-20261031/vy2-physical-help`.
Fetched master base: `e7cc378c275eafe7a047c63f672bedbed2fec6ff`.
Checkout: `/workspace/vy2-help-loop-horizon`.
The original VY2 checkout, branch, blocked goal, caches and artifacts are preserved.
This helper is not full Y04/Y05/Y06/Y09.02 completion.

## Reviewed checkpoints and typed interface

`dfafb49dd2d31d9ff7eca240cca5b963b056bdcb` exposes the public interface in
`Evm/MemoryLoopHorizon.lean`, namespace `Solidity.Evm.Memory`.
`3fd596ed8c291d393d8de16c22f5b385865e458b` adds its inhabited controls,
root registrations and a handoff that explicitly left the full wrapper pending.
Those immutable early bundles remain in the evidence directory.

`horizonBody` executes actual `Prog.run` on `body : Prog C Γ Δ`, then performs
the owner's scope drop. `HorizonRelation` relates actual typed source
`Out C σ.H Γ ⊕ TRes (Out C σ.H Γ)` to target `Machine ⊕ Out`.
It preserves actual `LoopPrefix`, `StateRepr L b frame F`, original stack,
`BaseExtends`, and exact-cost `GrowsAllocator`; revert is separate from pending.
`LoopCert.horizon_step`, `horizon_iter`, and `correct_horizon` transport the
actual condition/body step and `TLoop.iterN`/`loopIterN`. Their capacity premise
is the existing all-prefix `LoopRoom`. `pending_target` rules out completed
target results for pending source observations. No private owner names are used.

The additive `Evm/MemoryLoopFiniteHorizon.lean` removes that unnecessary
all-future allocation premise for finite observations:

- `CountedLoopPrefix` is a proof-only source trace indexed by actual typed
  output, exact allocation cost, and successful-body count. `forget` derives
  the owner's prefix. `iterN_eq`, `extend_pending`, and
  `countedPrefix_of_iterN_pending` prove soundness/completeness against the
  actual source iterator; no assumed trace-coverage law is supplied.
- `FiniteLoopRoom ... n` demands the original initial-cursor `AllocationInput`
  only at real prefixes with count strictly below `n` and true condition.
  Reached bodies that revert still require their actual allocation cost.
  `finiteLoopRoom_zero` requires no next-turn allocation capacity.
- `CountedHorizonRelation` preserves the same physical facts. Pending has
  exactly the requested successful-body count. Completion has strictly fewer
  successful bodies and a proved false source condition. `forget` recovers
  the earlier public relation.
- `LoopCert.finite_horizon_step`, `finite_horizon_iter`, and
  `correct_finite_horizon` prove real source/target transport, including
  `currentCount + remainingTurns ≤ budget`. Early completion widens only its
  count bound; it preserves the original exact prefix cost and growth.
  `correct_horizon_of_finite_room` lets existing consumers use this result.

Real premises: actual `LoopCert`, input `StateRepr`, unchanged static frame
capacity `b + frameNeedProg body ≤ frame`, and the stated finite allocation
room. There is no new runtime state, AST, interpreter, arbitrary depth/length
limit, assumed inverse/view/safety law, owner rewrite, or new axiom. The body
still uses actual unbounded `body.run`; recursive per-statement fuel and
whole-program/enclosing-scope horizon composition are not proved here.

## Inhabited controls and boundaries

`Evm/MemoryLoopHorizonControls.lean` uses the owner's populated, aliased heap
at arbitrary horizons: zero pending, false-condition exit, continued pending,
and an actual out-of-bounds condition revert in both evaluators.
`Evm/MemoryLoopHorizonAllocControls.lean` proves reached-allocation and
allocation-before-revert cases. Source heap lengths are 0/1/1 and target
allocator cursors 16/17/17 at horizons 0/1/2. No post-revert machine is invented.

`Evm/MemoryLoopFiniteHorizonControls.lean` constructs arbitrary actual source
prefixes for a constant-true loop allocating one empty array per turn. It
proves cost equals successful-turn count, finite room from the owner's real
strict bound `16 + n < W`, and transport at every such horizon. Separately,
actual prefix `W` contradicts all-prefix room via impossible cost `W + 1`.
This demonstrates the finite interface's usefulness; it does not refute G01,
prove transaction/constructor reachability, or choose resource-failure semantics.
Executable controls show pending counts 0/1/2/3 and cursors 16/17/18/19,
absorbing false-condition exits with no allocation demand, and a full-cursor
capacity negative. Failed capacity preparation is not a language refusal,
successful no-op, cleaning policy or deallocation.

These are kernel/source-target owner-model laws and finite executable checks,
not solc/EVM differential evidence or original Yul/compiler adequacy. Existing
VY2 compiler/EVM observations and settings are untouched.

## Checks, reviews and remaining work

Evidence: `/workspace/vy2-evidence/help-loop-horizon`.
Actual Lean 4.24.0 / Lake 5.0.0-src+797c613; KeySort exits 0 with 2 jobs.
Initial policy wrapper exits 0: 1268 default jobs, 286 TestSuite jobs and 131
pinned sort annotations. All five per-file checks pass. Expanded signature
checks cover 34 exports and all 25 exported theorems, standard axioms only.
The final wrapper including the two finite-room imports exits 0: 1270 default
jobs, 286 TestSuite jobs, and all 131 pinned sort annotations. The warmed-cache
confirmation took 3.06 seconds; the initial cold wrapper took 12277.04 seconds.

Initial control naming/type errors and finite-proof parser/match errors are
retained with their raw failed exits; fixes changed proof reductions/names,
not statements, expected observations, limits or budgets. The initial default
TestSuite parity path failure is retained; specifying the existing pinned
checkout passes. Strict/trust/layers/orphans and configured parity pass.
Documentation current/base checks both exit 1 with identical bytes against the
exact helper base; equality passes separately and is not a global docs pass.

Separate independent finder/skeptic design, source and final reviews are clear.
Reviewers ran no Lean/server/build/tests and edited nothing. The parent owns
all actual gate results. Existing writer/private Lean locks, serial `-j1`,
`LEAN_NUM_THREADS=1`, aggregate 12 GiB/no-swap and OS/RSS/disk monitoring are
preserved. Parent max-counter growth from cache/build activity remains in raw
logs; no unchanged-counter claim is made.

Original queues remain partial/blocked: general storage/path/hash/dirty/
transient ownership and source-frame adequacy; universal memory/writeback,
shared-zero/interior/pointers and reachable nondeterministic allocation
refinement; concrete V10/V11 agreements; full Y06 source/Yul bindings;
Y09.02 notation/printers/Lean-only rules and actual source/compiler/joint closure.
Original backfills A/B remain open beyond their supported canonical domains.
The coordinator controls original producer handoff, goal status and integration.
No goal was created, reset, reactivated or completed; no push/merge/PR occurred.
