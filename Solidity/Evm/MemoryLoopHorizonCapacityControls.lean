import Solidity.Evm.MemoryLoopHorizonCapacity
import Solidity.Evm.MemoryLoopHorizonControls

/-! Successor capacity is constructed from the empty horizon at a stopped
boundary and a true nonallocating boundary. The stopped transport consumes this
finite certificate directly on the populated aliased-memory fixture; no global
LoopRoom witness is required by these controls. -/
namespace Solidity.Evm.Memory.HorizonCapacityControls
open CompileExamples

theorem stop_room_one : FiniteLoopRoom 0 4 HorizonControls.stop HorizonControls.body σ base machine 1 := by
  apply FiniteLoopRoom.succ_of_stopped
    (finiteLoopRoom_zero 0 4 HorizonControls.stop HorizonControls.body σ base machine)
  intro o cost hp
  cases hp
  rfl

theorem spin_room_one : FiniteLoopRoom 0 4 HorizonControls.spin HorizonControls.body σ base machine 1 := by
  apply FiniteLoopRoom.succ_iff.mpr
  refine ⟨finiteLoopRoom_zero 0 4 HorizonControls.spin HorizonControls.body σ base machine,?_⟩
  intro o cost hp condition
  cases hp
  exact .inl rfl

theorem stop_transport :
    CountedHorizonRelation 1 0 4 (Frag.init Γ) HorizonControls.stop HorizonControls.body σ base machine 1
      (TLoop.iterN (horizonBody HorizonControls.body) (fun o => HorizonControls.stop.evalT o.st) 1
        ⟨σ,List.prefix_refl _⟩)
      (loopIterN (fun m => exec (Evm.compileVal 0 (.simple (.bool false) : Val C Γ .bool)) 0 m)
        (fun m => exec [] 0 m) 1 machine) := by
  exact (HorizonControls.cert false).correct_finite_horizon 1 fixture_repr (by decide +kernel) stop_room_one

end Solidity.Evm.Memory.HorizonCapacityControls
