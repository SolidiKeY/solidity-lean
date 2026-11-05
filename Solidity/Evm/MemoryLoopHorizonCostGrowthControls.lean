import Solidity.Evm.MemoryLoopHorizonCostGrowth
import Solidity.Evm.MemoryLoopHorizonCostControls

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
      0 ≤ cost ∧ cost=0 := by
  obtain ⟨cost,extended,lower⟩ := HorizonCostControls.spin_unique_zero_cost.1.extend_pending_mono 1
    HorizonCostControls.spin_source_one
  exact ⟨cost,extended,lower,extended.forget.cost_zero (by rfl)⟩

end Solidity.Evm.Memory.HorizonCostGrowthControls
