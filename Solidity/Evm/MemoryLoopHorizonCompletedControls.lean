import Solidity.Evm.MemoryLoopHorizonCompleted
import Solidity.Evm.MemoryLoopHorizonControls

/-! A real stopped target turn on populated aliased memory determines both
existing unbounded run results through the finite completion consumer. This
instantiates observed completion, not a general termination assumption. -/
namespace Solidity.Evm.Memory.HorizonCompletedControls
open CompileExamples

theorem stop_target_one : loopIterN (fun m => exec (Evm.compileVal 0 (.simple (.bool false) : Val C Γ .bool)) 0 m) (fun m => exec [] 0 m) 1 machine=.inr (.ok machine 0) := by
  rfl

theorem stop_runs :
    ∃ (o : Solidity.Out C σ.H Γ),
      TLoop.run (horizonBody HorizonControls.body) (fun o => HorizonControls.stop.evalT o.st)
        ⟨σ,List.prefix_refl _⟩=.ok o ∧ loopRun (fun m => exec (Evm.compileVal 0 (.simple (.bool false) : Val C Γ .bool)) 0 m) (fun m => exec [] 0 m) machine=.ok machine 0 := by
  exact (HorizonControls.cert false).completed_runs 1 fixture_repr (by decide +kernel)
    ((loopRoom_nonallocating HorizonControls.stop HorizonControls.body rfl σ base machine).finite 1)
    stop_target_one

end Solidity.Evm.Memory.HorizonCompletedControls
