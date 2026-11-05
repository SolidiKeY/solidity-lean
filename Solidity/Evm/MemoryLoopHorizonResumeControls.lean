import Solidity.Evm.MemoryLoopHorizonResume
import Solidity.Evm.MemoryLoopHorizonPendingControls

/-! Resume the actual one-turn pending target fixture for any remaining
horizon, including zero. The counted relation retains the already elapsed turn
and physical history. The fixture body is nonallocating; no global capacity for
allocating loops or termination is asserted. -/
namespace Solidity.Evm.Memory.HorizonResumeControls
open CompileExamples

theorem spin_resume (remaining : Nat) :
    ∃ (o : Solidity.Out C σ.H Γ),
      TLoop.iterN (horizonBody HorizonControls.body) (fun o => HorizonControls.spin.evalT o.st) 1
        ⟨σ,List.prefix_refl _⟩=.inl o ∧
      CountedHorizonRelation 1 0 4 (Frag.init Γ) HorizonControls.spin HorizonControls.body σ base machine (1+remaining)
        (TLoop.iterN (horizonBody HorizonControls.body) (fun o => HorizonControls.spin.evalT o.st) remaining o)
        (loopIterN (fun m => exec (Evm.compileVal 0 (.simple (.bool true) : Val C Γ .bool)) 0 m)
          (fun m => exec [] 0 m) remaining machine) := by
  exact (HorizonControls.cert true).resume_pending 1 remaining fixture_repr (by decide +kernel)
    ((loopRoom_nonallocating HorizonControls.spin HorizonControls.body rfl σ base machine).finite (1+remaining))
    HorizonPendingControls.spin_target_one

end Solidity.Evm.Memory.HorizonResumeControls
