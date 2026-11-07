import Solidity.Evm.MemoryLoopHorizonCostGrowth
import Solidity.Evm.MemoryLoopHorizonCostControls
import Solidity.Evm.MemoryLoopHorizonTurnBoundControls

/-! Actual two-turn pending execution extends the one-turn spinning prefix.
Its cost is monotone but remains zero, exhibiting why cost growth is not strict
and cannot be substituted for turn count or a termination argument. -/
namespace Solidity.Evm.Memory.HorizonCostGrowthControls
open CompileExamples

theorem spin_source_two :
    TLoop.iterN (horizonBody HorizonControls.body) (fun o => HorizonControls.spin.evalT o.st) 2
      ⟨σ,List.prefix_refl _⟩=.inl ⟨σ,List.prefix_refl _⟩ := by
  rfl

theorem spin_extension :
    ∃ cost, CountedLoopPrefix HorizonControls.spin HorizonControls.body σ ⟨σ,List.prefix_refl _⟩ cost 2 ∧
      ¬ 0 < cost ∧ cost=0 := by
  obtain ⟨cost,extended,_lower⟩ := HorizonCostControls.spin_unique_zero_cost.1.extend_pending_mono 1
    HorizonCostControls.spin_source_one
  have zero : cost=0 := extended.forget.cost_zero (by rfl)
  exact ⟨cost,extended,by omega,zero⟩

theorem allocating_cost_exact {C : Contract} {Γ : Ctx} {state : State C Γ}
    {reached : Solidity.Out C state.H Γ} {cost turns : Nat}
    (hp : CountedLoopPrefix (.simple (.bool true)) HorizonTurnBoundControls.body
      state reached cost turns) : cost=turns := by
  induction hp with
  | start => rfl
  | next hp hc hs ih => rw [ih, HorizonTurnBoundControls.body_cost]

end Solidity.Evm.Memory.HorizonCostGrowthControls
