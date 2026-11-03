import Solidity.Evm.Machine

/-! Runtime-word storage operand adapter over existing instructions.
The code contains only the destination slot; the value arrives on the stack.
No Source expression, address compiler or world/bytecode claim. -/
namespace Solidity.Backend.StorageOps.StackWordWrite

def code (slot : Evm.Slot) : List Evm.Instr := [.push (.slot slot),.sstore]

theorem run (slot : Evm.Slot) (word : Fin Evm.W) (machine : Evm.Machine) :
    Evm.run (code slot) {machine with stack := .val word :: machine.stack} =
      .ok {machine with store := Evm.WordStore.write machine.store slot word.val} 0 := by
  rfl

/-- info: 'Solidity.Backend.StorageOps.StackWordWrite.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run
end Solidity.Backend.StorageOps.StackWordWrite
