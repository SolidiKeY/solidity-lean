import Solidity.Evm.MemoryLoopHorizonPending
import Solidity.Evm.MemoryLoopHorizonControls

/-! An actual spinning target turn is pending on the populated aliased-memory
fixture. Its observation supplies the matching counted source prefix and full
represented physical-state/allocator facts through the finite consumer. -/
namespace Solidity.Evm.Memory.HorizonPendingControls
open CompileExamples

theorem spin_target_one :
    loopIterN (fun m => exec (Evm.compileVal 0 (.simple (.bool true) : Val C Γ .bool)) 0 m)
      (fun m => exec [] 0 m) 1 machine=.inl machine := by
  rfl

theorem spin_prefix_one :
    ∃ (o : Solidity.Out C σ.H Γ) (nextBase : Nat → Fin W) (cost : Nat),
      TLoop.iterN (horizonBody HorizonControls.body) (fun o => HorizonControls.spin.evalT o.st) 1
        ⟨σ,List.prefix_refl _⟩=.inl o ∧
      CountedLoopPrefix HorizonControls.spin HorizonControls.body σ o cost 1 ∧
      StateRepr 1 0 4 (Frag.init Γ) o.st nextBase machine ∧ machine.stack=machine.stack ∧
      BaseExtends σ.H base nextBase ∧ GrowsAllocator 0 4 cost σ base machine o.st nextBase machine := by
  exact (HorizonControls.cert true).target_pending_prefix 1 fixture_repr (by decide +kernel)
    ((loopRoom_nonallocating HorizonControls.spin HorizonControls.body rfl σ base machine).finite 1)
    spin_target_one

end Solidity.Evm.Memory.HorizonPendingControls
