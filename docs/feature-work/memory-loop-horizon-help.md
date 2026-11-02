# H10 P5 MemoryLoop finite-horizon helper

This helper starts at fetched master `e7cc378c275eafe7a047c63f672bedbed2fec6ff`
on `codex/solidity-inline-assembly5-20261031/vy2-physical-help`, in
`/workspace/vy2-help-loop-horizon`. The original VY2 checkout/goal is preserved;
this is a helper checkpoint, not full VY2 completion.

## Typed interface checkpoint

`Solidity/Evm/MemoryLoopHorizon.lean`, namespace `Solidity.Evm.Memory`:

- `horizonBody` executes actual `Prog C Γ Δ.run` and drops `body.ext`.
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
