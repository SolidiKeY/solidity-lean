import Solidity.Yul.Compilation.WordMachine
import Solidity.Yul.Compilation.MachineControl

/-! Structured target selection for the combined word compiler. This reuses
existing Backend.Block and actual model branch/loop conventions; no source AST,
state, function convention or native byte-offset interpretation is introduced.
Earlier NumericMachine/MachineControl selection contracts remain unchanged. -/
namespace Solidity.Yul.Compilation.WordControl
open Backend Scalar

def blockCode : Backend.Block → Option (List Evm.Instr)
  | .code p => WordMachine.selectCode p
  | .seq a b => (blockCode a).bind (fun x => (blockCode b).map (fun y => x ++ y))
  | .ite c a b => (WordMachine.selectCode c).bind (fun x =>
      (blockCode a).bind (fun y => (blockCode b).map (fun z => MachineControl.branchCode x y z)))
  | .loop c b => (WordMachine.selectCode c).bind (fun x =>
      (blockCode b).map (fun y => [Evm.Instr.loop x y]))

def lowerBranch {n : Nat} {condition : Vector Word n → Word}
    {yes no : Vector Word n → Vector Word n}
    (c : LoweredExpr n condition) (a : LoweredStmt n yes) (b : LoweredStmt n no)
    (depth : Nat) : Option (List Evm.Instr) :=
  (Solidity.Yul.Compilation.lowerBranch c a b depth).bind blockCode

end Solidity.Yul.Compilation.WordControl
