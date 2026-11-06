import Solidity.Evm.MemoryLoopHorizonStability
import Solidity.Evm.MemoryLoopHorizonCapacityControls

/-! The populated-memory stopped loop has an actual terminal observation at
horizon one. Its one-turn finite certificate supplies every requested counted
transport, including zero and larger horizons, without a global-room witness. -/
namespace Solidity.Evm.Memory.HorizonStabilityControls
open CompileExamples

theorem stop_source_one :
    TLoop.iterN (horizonBody HorizonControls.body) (fun o => HorizonControls.stop.evalT o.st) 1
      ⟨σ,List.prefix_refl _⟩=.inr (.ok ⟨σ,List.prefix_refl _⟩) := by
  rfl

theorem stop_all_horizons (horizon : Nat) :
    CountedHorizonRelation 1 0 4 (Frag.init Γ) HorizonControls.stop HorizonControls.body σ base machine horizon
      (TLoop.iterN (horizonBody HorizonControls.body) (fun o => HorizonControls.stop.evalT o.st) horizon
        ⟨σ,List.prefix_refl _⟩)
      (loopIterN (fun m => exec (Evm.compileVal 0 (.simple (.bool false) : Val C Γ .bool)) 0 m)
        (fun m => exec [] 0 m) horizon machine) := by
  exact (HorizonControls.cert false).correct_horizons_after_completion 1 fixture_repr
    (by decide +kernel) HorizonCapacityControls.stop_room_one stop_source_one horizon

end Solidity.Evm.Memory.HorizonStabilityControls
