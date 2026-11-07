import Solidity.Evm.MemoryLoopHorizonPending
import Solidity.Evm.MemoryLoopHorizonRestriction

/-! Continue actual pending target execution under one finite capacity witness.
The matching source prefix, memory representation, unchanged stack and allocator
history are derived from the observed target prefix. Resumption retains elapsed
turns and accumulated cost; neither is reset at the continuation boundary. -/
namespace Solidity.Evm.Memory
variable {C : Contract} {Γ Δ : Ctx}

theorem LoopCert.resume_pending {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {initial reached : Machine}
    (elapsed remaining : Nat) (repr : StateRepr L b frame F σ base initial)
    (cap : b + frameNeedProg body ≤ frame)
    (room : FiniteLoopRoom b frame c body σ base initial (elapsed+remaining))
    (pending : loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) elapsed initial=.inl reached) :
    ∃ (o : Solidity.Out C σ.H Γ),
      TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) elapsed ⟨σ,List.prefix_refl _⟩=.inl o ∧
      CountedHorizonRelation L b frame F c body σ base initial (elapsed+remaining)
        (TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) remaining o)
        (loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) remaining reached) := by
  obtain ⟨o,nextBase,cost,observed,hp,current,stack,bases,grows⟩ :=
    cert.target_pending_prefix elapsed repr cap (room.restrict (by omega)) pending
  refine ⟨o,observed,?_⟩
  exact cert.finite_horizon_iter room cap remaining elapsed (by omega) hp current stack bases grows

end Solidity.Evm.Memory
