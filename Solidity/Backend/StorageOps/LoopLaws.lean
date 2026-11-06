import Solidity.Evm.Machine

/-! Shared intrinsic loop adapters for storage-operation programs.
Condition/body equations and a finished loopRun remain explicit premises;
these laws do not supply a ranking, Source compilation or world refinement. -/
namespace Solidity.Backend.StorageOps.LoopLaws

theorem turn_step (rc rb : Evm.Machine → Evm.Out) (machine result : Evm.Machine)
    (flag : Fin Evm.W) (nonzero : flag.val ≠ 0)
    (cond : rc machine = .ok { machine with stack := .val flag :: machine.stack } 0)
    (step : rb machine = .ok result 0) : Evm.loopTurn rc rb machine = .inl result := by
  simp only [Evm.loopTurn,cond,if_neg nonzero,step]

theorem turn_exit (rc rb : Evm.Machine → Evm.Out) (machine : Evm.Machine)
    (cond : rc machine = .ok { machine with stack := .val ⟨0,by decide⟩ :: machine.stack } 0) :
    Evm.loopTurn rc rb machine = .inr (.ok machine 0) := by
  simp only [Evm.loopTurn,cond,ite_true]

theorem run_single_loop (cond body : List Evm.Instr) (machine result : Evm.Machine)
    (finished : Evm.loopRun (Evm.run cond) (Evm.run body) machine = .ok result 0) :
    Evm.run [.loop cond body] machine = .ok result 0 := by
  exact congrArg (fun out => out.bind (fun m k => Evm.exec [] k m)) finished

/-- info: 'Solidity.Backend.StorageOps.LoopLaws.turn_step' depends on axioms: [propext] -/
#guard_msgs in #print axioms turn_step
/-- info: 'Solidity.Backend.StorageOps.LoopLaws.turn_exit' depends on axioms: [propext] -/
#guard_msgs in #print axioms turn_exit
/-- info: 'Solidity.Backend.StorageOps.LoopLaws.run_single_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_single_loop
end Solidity.Backend.StorageOps.LoopLaws
