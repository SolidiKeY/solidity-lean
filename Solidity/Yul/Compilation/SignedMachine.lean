import Solidity.Yul.Compilation.WordMachine

/-! Actual target adapter adding SDIV/SMOD/SLT/SGT to the existing word subset.
Earlier selectors and refusal contracts remain unchanged. Eighteen binary and
two unary operators plus existing stack instructions are selected; SAR and
SIGNEXTEND are not supplied. No source AST/state/admission/convention is added.
PUSH width is erased; native byte/resource identity is not asserted. -/
namespace Solidity.Yul.Compilation.SignedMachine
open Backend Scalar

def selectInstr : Backend.Instr → Option Evm.Instr
  | .op .SDIV => some .sdiv
  | .op .SMOD => some .smod
  | .op .SLT => some .slt
  | .op .SGT => some .sgt
  | i => WordMachine.selectInstr i

def selectCode : Backend.Program → Option (List Evm.Instr)
  | [] => some []
  | i::p => (selectInstr i).bind (fun j => (selectCode p).map (fun q => j::q))

theorem select_pushWord (value : Word) :
    selectInstr (pushWord value) = some (.push (MachineAdapter.coreWord value)) :=
  WordMachine.select_pushWord value

#print axioms select_pushWord
end Solidity.Yul.Compilation.SignedMachine
