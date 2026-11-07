import Solidity.Evm.MemoryLoopHorizonCompleted
import Solidity.Evm.MemoryLoopHorizonPrefixCapacity

/-! Successful finite target completion retains stopped source-prefix facts
and exposes the loop owner's exact grown struct allocator at positive cost.
No complete-object promotion is made: the predicate is StructAllocatorRepr.
Zero cost remains vacuous, and actual completion is an explicit observation. -/
namespace Solidity.Evm.Memory
variable {C : Contract} {Γ Δ : Ctx}

theorem LoopCert.completed_allocator {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {initial reached : Machine}
    (n : Nat) (repr : StateRepr L b frame F σ base initial)
    (cap : b + frameNeedProg body ≤ frame) (room : FiniteLoopRoom b frame c body σ base initial n)
    (completed : loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) n initial=.inr (.ok reached 0)) :
    ∃ (o : Solidity.Out C σ.H Γ) (nextBase : Nat → Fin W) (cost count : Nat),
      TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n ⟨σ,List.prefix_refl _⟩=.inr (.ok o) ∧
      CountedLoopPrefix c body σ o cost count ∧ count<n ∧ c.evalT o.st=.ok false ∧
      StateRepr L b frame F o.st nextBase reached ∧ reached.stack=initial.stack ∧
      BaseExtends σ.H base nextBase ∧ GrowsAllocator b frame cost σ base initial o.st nextBase reached ∧
      (0 < cost → 0 < b ∧ ∃ (cursor : Fin W) (space : cursor.val+cost < W),
        StructAllocatorRepr σ.heap base frame cursor initial ∧
        StructAllocatorRepr o.st.heap nextBase frame ⟨cursor.val+cost,space⟩ reached) := by
  obtain ⟨o,nextBase,cost,count,observed,hp,earlier,stopped,current,stack,bases,grows⟩ :=
    cert.target_completed_prefix n repr cap room completed
  refine ⟨o,nextBase,cost,count,observed,hp,earlier,stopped,current,stack,bases,grows,?_⟩
  intro positive
  rcases room.prefix_input hp (Nat.le_of_lt earlier) with zero | ⟨enabled,cursor,initialAllocator,space⟩
  · omega
  · exact ⟨enabled,cursor,space,initialAllocator,grows cursor enabled initialAllocator space⟩

end Solidity.Evm.Memory
