import Solidity.Assurance.NonVacuityH28.CheckedFamilies

/-! The scalar loop-contract clients have an actual reached zero demand/cost.
Positive allocating loop demand remains an explicit coverage finding. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics
variable (C : Contract)

theorem scalar_loop_demand (σ : State C MemCtx) :
    Evm.Memory.Loops.Demand (loopResult C).cert σ 0 :=
  Evm.Memory.Loops.Demand.head rfl

theorem scalar_loop_cost (σ : State C MemCtx) :
    Evm.Memory.Loops.Cost (loopResult C).cert σ ⟨σ, List.prefix_refl _⟩ 0 :=
  by
    refine .cons (o := ⟨σ, List.prefix_refl _⟩) (o' := ⟨σ, List.prefix_refl _⟩)
      (cost := 0) (rest := 0) rfl ?_ (.nil σ)
    rfl

theorem scalar_scope_demand (σ : State C MemCtx) :
    Evm.Memory.LoopScopes.Demand (scopeResult C).cert σ 0 :=
  .head (.base (Evm.Memory.Loops.Demand.head rfl))

theorem scalar_scope_cost (σ : State C MemCtx) :
    Evm.Memory.LoopScopes.Cost (scopeResult C).cert σ ⟨σ, List.prefix_refl _⟩ 0 :=
  by
    refine .cons (o := ⟨σ, List.prefix_refl _⟩) (o' := ⟨σ, List.prefix_refl _⟩)
      (cost := 0) (rest := 0) rfl ?_ (.nil σ)
    refine .base ?_
    refine .cons (o := ⟨σ, List.prefix_refl _⟩) (o' := ⟨σ, List.prefix_refl _⟩)
      (cost := 0) (rest := 0) rfl ?_ (.nil σ)
    rfl

end Solidity.Assurance.NonVacuityH28
