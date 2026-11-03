import Solidity.Yul.Compilation.MachineAdapter

/-! Dependency-free selection into the actual existing compiler machine.
This extends the stack-only adapter with ten numeric operators. It does not
change the machine, source AST, source admission or function calling convention.
PUSH width is erased by this model adapter; raw byte equality is not asserted.
No run theorem is proved here: `MachineAdapter.stackCode` covers only
PUSH/DUP/SWAP/POP, so arithmetic code is not translated. -/
namespace Solidity.Yul.Compilation.NumericMachine
open Backend Scalar

def selectInstr : Backend.Instr → Option Evm.Instr
  | .op .ADD => some .add
  | .op .SUB => some .sub
  | .op .MUL => some .mul
  | .op .DIV => some .div
  | .op .MOD => some .mod
  | .op .AND => some .and
  | .op .OR => some .or
  | .op .XOR => some .xor
  | .op .SHL => some .shl
  | .op .SHR => some .shr
  | i => MachineAdapter.selectStack i

def selectCode : Backend.Program → Option (List Evm.Instr)
  | [] => some []
  | i :: p => (selectInstr i).bind (fun j => (selectCode p).map (fun q => j :: q))

theorem select_pushWord (value : Word) :
    selectInstr (pushWord value) = some (.push (MachineAdapter.coreWord value)) :=
  MachineAdapter.selectStack_pushWord value

#print axioms select_pushWord
end Solidity.Yul.Compilation.NumericMachine
