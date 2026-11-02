# H10 P5 MemoryLoop finite-horizon helper

This helper starts at fetched master `e7cc378c275eafe7a047c63f672bedbed2fec6ff`
on `codex/solidity-inline-assembly5-20261031/vy2-physical-help`, in
`/workspace/vy2-help-loop-horizon`. The original VY2 checkout/goal is preserved;
this is a helper checkpoint, not full VY2 completion.

## Typed interface checkpoint

`Solidity/Evm/MemoryLoopHorizon.lean`, namespace `Solidity.Evm.Memory`:

- `horizonBody` executes actual `Prog.run` on `body : Prog C Γ Δ` and drops `body.ext`.
- `HorizonRelation` indexes actual source `Out C σ.H Γ ⊕ TRes (Out C σ.H Γ)`
  and target `Machine ⊕ Out`. Pending and successful results retain the real
  `LoopPrefix`, `StateRepr L b frame F`, original stack, `BaseExtends`, and
  exact-cost `GrowsAllocator`. Revert is a separate constructor.
- `LoopCert.horizon_step` transports one real condition/body turn.
- `LoopCert.horizon_iter` transports any finite number of turns from a reached
  represented prefix, retaining its original allocator and accumulated cost.
- `LoopCert.correct_horizon` starts at the actual initial source/target states
  and works at every `n : Nat`, including zero.
- `HorizonRelation.pending_target` rules out a completed target for a pending
  source observation.

Premises are actual `LoopCert`, `StateRepr`, `b + frameNeedProg body ≤ frame`
and existing `LoopRoom`. The latter covers all reached allocating prefixes,
not only the requested finite horizon. The body uses actual unbounded `run`;
this is not recursive per-statement fuel or a whole-program horizon theorem.
No owner definition or semantic representation is changed. The proof exposes
public transport reconstructed from the owner's private proof, using actual
condition/body correctness, with no private-name access or assumed simulation.

Initial per-file kernel check: `lake build Solidity.Evm.MemoryLoopHorizon`
(reached within the serial focused build), exit not yet available for the
whole focused command; the module itself reported Built in 1.0s. Raw log:
`/workspace/vy2-evidence/help-loop-horizon/focused.log`.
Independent finder/skeptic read-only design and source reviews found no
semantic defect. Their control gap prompted allocating/reverting witnesses;
those controls and final policy gates are still being checked at this early
interface checkpoint. No full-gate pass is claimed here.

## Remaining obligations

Complete controls and required final checks/reviews. Finite-only capacity
weakening, recursive body fuel and enclosing-program scope/program transport
remain separate interfaces. H10 helper completion does not discharge original
Y04/Y05/Y06/Y09.02, broader storage/memory/dirty/shared-zero/interior ownership,
allocation refinement, V10/V11 agreements, Yul source/calculus/compiler closure.

## Inhabited controls and validation in progress

`MemoryLoopHorizonControls.lean` instantiates the public theorem at arbitrary
horizons over the existing populated two-object, aliased-memory witness. It
checks zero-horizon pending, one-turn false-condition success, a spinning
nonallocating loop remaining pending, and a real out-of-bounds condition
returning revert in both actual evaluators.

`MemoryLoopHorizonAllocControls.lean` instantiates the theorem with a reached
allocation and real one-turn capacity. Source heap lengths are 0/1/1 at
horizons 0/1/2; target allocator cursors are 16/17/17. Allocation-before-revert
is checked at horizons 1 and 2. A revert observation does not manufacture or
claim a post-revert machine state.

The first control build failed on the new test's operator name and ambiguous
heap-typing name. They were repaired to actual `BinOp.eqB` and the qualified
fixture heap typing. The initial exit 1 is preserved; corrected focused build
passes 198 jobs, and all three explicit per-file checks exit 0. Signature audit
covers 14 exported declarations and all 8 exported theorems, with only standard
axioms or none. Lean 4.24.0, Lake 5.0.0-src+797c613; actual KeySort build exits 0
with 2 jobs. No proof budgets changed and no new axiom was introduced.

Strict, trust, layers, orphans and configured TestSuite parity checks pass.
The first parity command's default sibling path was absent; explicitly using
the existing pinned SolKey checkout fixes that configuration, with both runs
retained. Full `./run-lean.sh` is still in progress at this documentation stage;
no final full-build success is asserted yet. Documentation current/base checks
both exit 1 with identical bytes against helper base `e7cc378c`; their equality
check exits 0. This is zero regression, not a passing global documentation gate.

Independent read-only finder and skeptic reviews found no semantic defect.
Their initial allocation/revert control gap is addressed by the above real
witnesses. Reviewers ran no Lean, server, build or tests. The parent performs
all validation. Runtime is the existing hard 12 GiB/no-swap container, serial
Lean `-j1`, `LEAN_NUM_THREADS=1`, private Lean lock and writer lock; disk caches
are preserved. Resource logs retain parent-cgroup max-counter growth during
cache/build activity, not a claim of unchanged event counters.
