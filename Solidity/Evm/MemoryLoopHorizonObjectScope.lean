import Solidity.Evm.MemoryObjectAllocationCost
import Solidity.Evm.MemoryScope

/-! Scope exit for the complete-object memory representation. The strong heap
ownership field is retained directly; legacy projection is used only for core,
pointer and local facts. Growing results keep the same actual heap, machine,
base extension and complete-object allocator growth. No legacy allocator is
promoted to complete-object ownership and no Source definition is changed. -/
namespace Solidity.Evm.Memory.Objects
variable {C : Contract}

theorem StateRepr.drop {L b frame : Nat} {Γ Δ : Ctx} {F : Frag Δ}
    {σ : State C Δ} {base : Nat → Fin W} {machine : Machine}
    (repr : StateRepr L b frame F σ base machine) (scope : Ext Γ Δ) :
    StateRepr L b frame (F.restrict Γ) (σ.drop scope) base machine := by
  have retained := repr.legacy.drop scope
  exact ⟨retained.core,repr.heap,retained.pointers,retained.locals⟩

theorem GrowingResult.drop {L b frame cost : Nat} {Ξ Γ Δ : Ctx} {F : Frag Δ}
    {σ : State C Ξ} {base : Nat → Fin W} {initial : Machine}
    {source : TRes (Solidity.Out C σ.H Δ)} {target : Out}
    (result : GrowingResult L b frame cost F σ base initial source target) (scope : Ext Γ Δ) :
    GrowingResult L b frame cost (F.restrict Γ) σ base initial
      (source.map (fun o => ⟨o.st.drop scope,o.ext⟩)) target := by
  rcases result with ⟨o,reached,nextBase,sourceRun,targetRun,repr,stack,bases,grows⟩ | ⟨sourceRun,targetRun⟩
  · refine .inl ⟨⟨o.st.drop scope,o.ext⟩,reached,nextBase,?_,targetRun,repr.drop scope,stack,bases,grows⟩
    rw [sourceRun]
    rfl
  · refine .inr ⟨?_,targetRun⟩
    rw [sourceRun]
    rfl

end Solidity.Evm.Memory.Objects
