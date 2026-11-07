import Solidity.Evm.MemoryLoopHorizonAppend
import Solidity.Evm.MemoryLoopHorizonCostControls
import Solidity.Evm.MemoryLoopHorizonPendingControls

/-! Concrete source and target pending observations on populated aliased memory
support exact concatenation for any remaining horizon, including zero. Each
side uses its independently proved actual observation, not an assumed pairing. -/
namespace Solidity.Evm.Memory.HorizonAppendControls
open CompileExamples

theorem source_append (remaining : Nat) :
    TLoop.iterN (horizonBody HorizonControls.body) (fun o => HorizonControls.spin.evalT o.st) (1+remaining) ⟨σ,List.prefix_refl _⟩=TLoop.iterN (horizonBody HorizonControls.body) (fun o => HorizonControls.spin.evalT o.st) remaining ⟨σ,List.prefix_refl _⟩ := by
  exact iterN_add_of_pending HorizonCostControls.spin_source_one remaining

theorem target_append (remaining : Nat) :
    loopIterN (fun m => exec (Evm.compileVal 0 (.simple (.bool true) : Val C Γ .bool)) 0 m) (fun m => exec [] 0 m) (1+remaining) machine=loopIterN (fun m => exec (Evm.compileVal 0 (.simple (.bool true) : Val C Γ .bool)) 0 m) (fun m => exec [] 0 m) remaining machine := by
  exact loopIterN_add_of_pending HorizonPendingControls.spin_target_one remaining

end Solidity.Evm.Memory.HorizonAppendControls
