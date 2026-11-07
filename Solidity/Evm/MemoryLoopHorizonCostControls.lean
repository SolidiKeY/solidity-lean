import Solidity.Evm.MemoryLoopHorizonCost
import Solidity.Evm.MemoryLoopHorizonControls

/-! One actual spinning source turn on populated aliased memory has a unique
zero allocation cost. Successful turn count and accumulated allocation demand
are distinct; a zero cost does not imply termination or zero turns. -/
namespace Solidity.Evm.Memory.HorizonCostControls
open CompileExamples

theorem spin_source_one :
    TLoop.iterN (horizonBody HorizonControls.body) (fun o => HorizonControls.spin.evalT o.st) 1
      ⟨σ,List.prefix_refl _⟩=.inl ⟨σ,List.prefix_refl _⟩ := by
  rfl

theorem spin_unique_zero_cost :
    CountedLoopPrefix HorizonControls.spin HorizonControls.body σ ⟨σ,List.prefix_refl _⟩ 0 1 ∧
    ∀ other, CountedLoopPrefix HorizonControls.spin HorizonControls.body σ ⟨σ,List.prefix_refl _⟩ other 1 → other=0 := by
  obtain ⟨cost,hp,unique⟩ := countedPrefix_of_iterN_pending_unique spin_source_one
  have zero := hp.forget.cost_zero (by rfl)
  subst cost
  exact ⟨hp,unique⟩

end Solidity.Evm.Memory.HorizonCostControls
