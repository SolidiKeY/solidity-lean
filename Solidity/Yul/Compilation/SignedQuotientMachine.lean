import Solidity.Yul.Compilation.SignedMachine
import Solidity.Yul.Compilation.PureExpressions
import Solidity.Yul.EvmSigned
/-! Actual signed quotient compilation consuming the published VY1 step bodies.
No duplicate signed arithmetic/range proof, source AST/state, selector/admission
or native convention. General Source/G24 and native closure remain separate. -/
namespace Solidity.Yul.Compilation.SignedQuotientMachine
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def sdivExpr : Expr [] [] 2 1 :=
  .builtin (.pure .sdiv) (Fin.cases (.local 0) (fun _ => .local 1))
def sdivCompiled := (PureExpressions.compile 2 sdivExpr).get (by rfl)
def sdivProgram : Backend.Program := [.op (.DUP 1),.op (.DUP 1),.op .SDIV]
theorem sdiv_origin : sdivCompiled.lowered.code 0 = some sdivProgram := rfl
theorem sdiv_selection : SignedMachine.selectCode sdivProgram =
    some [.dup 2,.dup 2,.sdiv] := rfl

/-- All-word compiler-selected run from the actual VY1 producer, including
zero divisor and signed wrap. No result/run or extra range premise is assumed. -/
theorem sdiv_run (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.dup 2,.dup 2,.sdiv] {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord ((Scalar.binary .SDIV).getD (fun _ _ => 0) a b) :: coreWord a :: coreWord b :: tail} 0 := by
  change Evm.run [.sdiv] {m with stack := coreWord a :: coreWord b :: coreWord a :: coreWord b :: tail} = _
  rw [Evm.run,Evm.exec_cons_zero]
  have producer := EvmSigned.step_sdiv m a.toFin b.toFin (coreWord a :: coreWord b :: tail)
  have result : Pure.eval .sdiv (EvmSigned.args a.toFin b.toFin) =
      ((Scalar.binary .SDIV).getD (fun _ _ => 0) a b).toFin :=
    (SignedExpressions.sdivBridge.agrees a b).symm
  rw [result] at producer
  change Evm.Instr.step .sdiv {m with stack := coreWord a :: coreWord b :: coreWord a :: coreWord b :: tail} =
    Evm.Out.ok {m with stack := coreWord ((Scalar.binary .SDIV).getD (fun _ _ => 0) a b) :: coreWord a :: coreWord b :: tail} 0 at producer
  rw [producer,Evm.Out.ok_bind]
  rfl
#print axioms sdiv_run

def smodExpr : Expr [] [] 2 1 :=
  .builtin (.pure .smod) (Fin.cases (.local 0) (fun _ => .local 1))
def smodCompiled := (PureExpressions.compile 2 smodExpr).get (by rfl)
def smodProgram : Backend.Program := [.op (.DUP 1),.op (.DUP 1),.op .SMOD]
theorem smod_origin : smodCompiled.lowered.code 0 = some smodProgram := rfl
theorem smod_selection : SignedMachine.selectCode smodProgram =
    some [.dup 2,.dup 2,.smod] := rfl

/-- All-word compiler-selected run from the actual VY1 producer, including
zero divisor and signed wrap. No result/run or extra range premise is assumed. -/
theorem smod_run (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.dup 2,.dup 2,.smod] {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord ((Scalar.binary .SMOD).getD (fun _ _ => 0) a b) :: coreWord a :: coreWord b :: tail} 0 := by
  change Evm.run [.smod] {m with stack := coreWord a :: coreWord b :: coreWord a :: coreWord b :: tail} = _
  rw [Evm.run,Evm.exec_cons_zero]
  have producer := EvmSigned.step_smod m a.toFin b.toFin (coreWord a :: coreWord b :: tail)
  have result : Pure.eval .smod (EvmSigned.args a.toFin b.toFin) =
      ((Scalar.binary .SMOD).getD (fun _ _ => 0) a b).toFin :=
    (SignedExpressions.smodBridge.agrees a b).symm
  rw [result] at producer
  change Evm.Instr.step .smod {m with stack := coreWord a :: coreWord b :: coreWord a :: coreWord b :: tail} =
    Evm.Out.ok {m with stack := coreWord ((Scalar.binary .SMOD).getD (fun _ _ => 0) a b) :: coreWord a :: coreWord b :: tail} 0 at producer
  rw [producer,Evm.Out.ok_bind]
  rfl
#print axioms smod_run
end Solidity.Yul.Compilation.SignedQuotientMachine
