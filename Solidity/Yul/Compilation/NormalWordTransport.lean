import Solidity.Yul.Compilation.NormalControl
import Solidity.Yul.Compilation.WordExecution
import Solidity.Yul.Compilation.WordControl

/-! Whole word normal-control execution using the EXISTING WordControl.blockCode
selector and existing indexed NormalControl.Derivation. Word leaves and
conditions derive their runs from real compiler certificates. This supplies
no loop, byte/PC, gas, native-capacity or logical Source/G24/world adequacy. -/
namespace Solidity.Yul.Compilation.NormalWordTransport
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

/-- Actual emitted blocks and concrete model selection derive all operands,
intermediate states and arm executions; no desired execution is a premise. -/
theorem machine {c n fuel} {stmt : Stmt [] [] c n}
    (compiled : NormalControl.Derivation fuel stmt) (depth : Nat)
    (block : Backend.Block) (code : List Evm.Instr)
    (emitted : compiled.emit depth = some block)
    (translated : WordControl.blockCode block = some code)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
      .ok {m with stack := (newer.toList ++ (compiled.update locals).toList).map coreWord ++ caller} 0 :=
  NormalControl.machine_with WordMachine.selectCode WordControl.blockCode
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) rfl
    WordExecution.loweredStmt_machine WordExecution.loweredExpr_machine
    compiled depth block code emitted translated locals newer m caller


/-- Original same-horizon closed-source result and complete selected model run.
The real visitor/emission/selection remain explicit, not source admission. -/
theorem source_machine {c n fuel} (stmt : Stmt [] [] c n)
    (compiled : NormalControl.Derivation fuel stmt)
    (_visited : NormalControl.compile fuel stmt = some compiled) (depth : Nat)
    (block : Backend.Block) (code : List Evm.Instr)
    (emitted : compiled.emit depth = some block)
    (translated : WordControl.blockCode block = some code)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (caller : List Evm.Word) :
    (evalStmt fuel .nil True.intro stmt compiled.profile (ProducerExpressions.sourceLocals locals) =
      some ⟨ProducerExpressions.sourceLocals (compiled.update locals),.normal⟩) ∧
    Evm.run code {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
      .ok {m with stack := (newer.toList++(compiled.update locals).toList).map coreWord++caller} 0 :=
  ⟨compiled.source locals,machine compiled depth block code emitted translated locals newer m caller⟩

/-- info: 'Solidity.Yul.Compilation.NormalWordTransport.machine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms machine
/-- info: 'Solidity.Yul.Compilation.NormalWordTransport.source_machine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_machine

end Solidity.Yul.Compilation.NormalWordTransport
