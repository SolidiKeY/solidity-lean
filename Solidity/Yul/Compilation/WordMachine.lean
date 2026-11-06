import Solidity.Yul.Compilation.NumericMachine

/-! Combined actual target-model selector: the earlier ten numeric operators,
unsigned LT/GT/EQ, EXP, ISZERO/NOT and the existing stack instructions. The earlier selector/refusal
contracts are preserved. This is a target adapter, not source admission or a new
AST/state/convention. PUSH widths are erased; byte/resource identity is absent. -/
namespace Solidity.Yul.Compilation.WordMachine
open Backend Scalar

def selectInstr : Backend.Instr → Option Evm.Instr
  | .op .EXP => some .exp
  | .op .LT => some .lt
  | .op .GT => some .gt
  | .op .EQ => some .eq
  | .op .ISZERO => some .iszero
  | .op .NOT => some .not
  | i => NumericMachine.selectInstr i

def selectCode : Backend.Program → Option (List Evm.Instr)
  | [] => some []
  | i :: p => (selectInstr i).bind (fun j => (selectCode p).map (fun q => j :: q))

theorem select_pushWord (value : Word) :
    selectInstr (pushWord value) = some (.push (MachineAdapter.coreWord value)) :=
  NumericMachine.select_pushWord value

#print axioms select_pushWord
end Solidity.Yul.Compilation.WordMachine
