import Solidity.Evm.MemoryLoopHorizonObjectAllocatingPrefixes
import Solidity.Evm.MemoryLoopHorizonObjectCompile
import Solidity.Evm.MemoryLoopHorizonObjectCost

/-! Actual target execution for the cost-one allocating body. Genuine source
prefixes force the strong finite relation into its pending branch. Exact cost
uniqueness then gives n-cell complete allocator growth. A supplied complete
initial allocator yields its cursor advanced by exactly n, under explicit
word-space and frame bounds. No unbounded physical capacity is inferred. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
variable {C : Contract} {Γ : Ctx}

theorem target_pending {L b frame : Nat}
    (compiled : Construction.CompiledLoop b (Frag.init Γ) (.simple (.bool true) : Val C Γ .bool) body)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine} (n : Nat)
    (repr : Objects.StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b + frameNeedProg (body : Prog C Γ _) ≤ frame)
    (demand : Objects.AllocationInput b frame n state base machine) :
    ∃ (out : Solidity.Out C state.H Γ) (nextBase : Nat → Fin W) (reached : Machine),
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        n machine = .inl reached ∧
      TLoop.iterN (horizonBody body) (fun o => (.simple (.bool true) : Val C Γ .bool).evalT o.st)
        n ⟨state,List.prefix_refl _⟩ = .inl out ∧
      Construction.CountedLoopPrefix (.simple (.bool true)) body state out n n ∧
      Objects.StateRepr L b frame (Frag.init Γ) out.st nextBase reached ∧
      reached.stack=machine.stack ∧ BaseExtends state.H base nextBase ∧
      Objects.GrowsAllocator b frame n state base machine out.st nextBase reached := by
  obtain ⟨out,hp⟩ := prefixes state n
  have relation := compiled.correct_finite_horizon n repr capacity (room n demand)
  rw [hp.iterN_eq] at relation
  generalize observed : loopIterN _ _ n machine = target at relation
  cases relation with
  | more actual current stack bases grows =>
    rw [actual.cost_unique hp] at grows
    exact ⟨out,_,_,rfl,hp.iterN_eq,hp,current,stack,bases,grows⟩

theorem target_allocator {L b frame : Nat}
    (compiled : Construction.CompiledLoop b (Frag.init Γ) (.simple (.bool true) : Val C Γ .bool) body)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine} (n : Nat)
    (repr : Objects.StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b + frameNeedProg (body : Prog C Γ _) ≤ frame)
    (enabled : 0 < b) {cursor : Fin W}
    (initialAllocator : Objects.AllocatorRepr state.heap base frame cursor machine)
    (space : cursor.val+n < W) :
    ∃ (out : Solidity.Out C state.H Γ) (nextBase : Nat → Fin W) (reached : Machine),
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        n machine = .inl reached ∧
      TLoop.iterN (horizonBody body) (fun o => (.simple (.bool true) : Val C Γ .bool).evalT o.st)
        n ⟨state,List.prefix_refl _⟩ = .inl out ∧
      Construction.CountedLoopPrefix (.simple (.bool true)) body state out n n ∧
      Objects.StateRepr L b frame (Frag.init Γ) out.st nextBase reached ∧
      reached.stack=machine.stack ∧ BaseExtends state.H base nextBase ∧
      Objects.AllocatorRepr out.st.heap nextBase frame ⟨cursor.val+n,space⟩ reached := by
  obtain ⟨out,nextBase,reached,target,source,hp,current,stack,bases,grows⟩ :=
    target_pending compiled n repr capacity (.inr ⟨enabled,cursor,initialAllocator,space⟩)
  exact ⟨out,nextBase,reached,target,source,hp,current,stack,bases,
    grows cursor enabled initialAllocator space⟩

end Solidity.Evm.Memory.HorizonObjectAllocating
