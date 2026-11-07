import Solidity.Evm.MemoryObjectConstructionCompile
import Solidity.Evm.MemoryLoopHorizonObjectScope

/-! Compile a complete-object body and leave its local scope. This composes the
existing construction compiler with strong scope transport, retaining the exact
construction allocation cost, target execution, base extension and allocator
growth. Capacity and complete-object allocation input remain explicit. This is
body transport only; it does not assert loop correctness or Source adequacy. -/
namespace Solidity.Evm.Memory.Construction
variable {C : Contract}

theorem ProgFrag.correct_scope {b L frame : Nat} {Ξ Γ Δ : Ctx}
    {F : Frag Γ} {G : Frag Δ} {P : Prog C Γ Δ} {code : List Instr}
    (compiled : ProgFrag b F G P code) (scope : Ext Ξ Δ)
    {σ : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (repr : Objects.StateRepr L b frame F σ base machine)
    (capacity : b + frameNeedProg P ≤ frame)
    (input : Objects.AllocationInput b frame (allocationCostProg P σ) σ base machine) :
    Objects.GrowingResult L b frame (allocationCostProg P σ) (G.restrict Ξ) σ base machine
      ((P.run σ).map (fun o => ⟨o.st.drop scope,o.ext⟩)) (run code machine) := by
  exact (compiled.correct repr capacity input).drop scope

end Solidity.Evm.Memory.Construction
