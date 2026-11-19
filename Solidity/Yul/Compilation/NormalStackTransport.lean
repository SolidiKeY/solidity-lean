import Solidity.Yul.Compilation.NormalControl
/-! Concrete whole-block execution of compiled normal control when every leaf
is selected by the existing stack-only MachineAdapter. No word selector is
silently widened: arithmetic and loops refuse in this model consumer.
This is the existing Evm.Machine model, not native/charged/Source/G24 adequacy. -/
namespace Solidity.Yul.Compilation.NormalStackTransport
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def blockCode : Backend.Block → Option (List Evm.Instr)
  | .code p => MachineAdapter.stackCode p
  | .seq a b => (blockCode a).bind (fun x => (blockCode b).map (fun y => x ++ y))
  | .ite c a b => (MachineAdapter.stackCode c).bind (fun x =>
      (blockCode a).bind (fun y => (blockCode b).map (fun z => MachineControl.branchCode x y z)))
  | .loop _ _ => none

/-- Actual emitted blocks and concrete model selection derive all operands,
intermediate states and arm executions; no desired execution is a premise. -/
theorem machine {c n fuel} {stmt : Stmt [] [] c n}
    (compiled : NormalControl.Derivation fuel stmt) (depth : Nat)
    (block : Backend.Block) (code : List Evm.Instr)
    (emitted : compiled.emit depth = some block)
    (translated : blockCode block = some code)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
      .ok {m with stack := (newer.toList ++ (compiled.update locals).toList).map coreWord ++ caller} 0 :=
  NormalControl.machine_with MachineAdapter.stackCode blockCode
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) rfl
    MachineAdapter.loweredStmt_machine MachineAdapter.loweredExpr_machine
    compiled depth block code emitted translated locals newer m caller

#print axioms machine
end Solidity.Yul.Compilation.NormalStackTransport
