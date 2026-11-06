import Solidity.Evm.MemoryLoopHorizonObjectPendingAllocator
import Solidity.Evm.MemoryLoopHorizonObjectCapacity

/-! Resume actual pending complete-object target execution using one finite
room witness. The source prefix, strong state representation and complete
allocator growth history come from the observed target prefix. Elapsed turns
and accumulated construction cost remain relative to the original state;
resumption supplies no new capacity, termination or Source adequacy premise. -/
namespace Solidity.Evm.Memory.Construction
variable {C : Contract} {Γ Δ : Ctx}

theorem LoopCert.resume_pending {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {initial reached : Machine}
    (elapsed remaining : Nat) (repr : Objects.StateRepr L b frame F σ base initial)
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

end Solidity.Evm.Memory.Construction
