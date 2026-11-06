import Solidity.Yul.Compilation.NumericMachine
import Solidity.Yul.Compilation.PureExpressions
/-! Actual AND/OR/XOR compiler-model execution. No new word semantics, AST,
selector/admission or machine convention. Native/G24 closure remains separate. -/
namespace Solidity.Yul.Compilation.BitMachineExecution
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def reads : Backend.Program := [.op (.DUP 1),.op (.DUP 1)]

/-- Actual intrinsic expression and checked compiler certificate. -/
def andExpr : Expr [] [] 2 1 :=
  .builtin (.pure .and) (Fin.cases (.local 0) (fun _ => .local 1))
def andCompiled := (PureExpressions.compile 2 andExpr).get (by rfl)
def andProgram : Backend.Program := reads ++ [.op .AND]
theorem and_origin : andCompiled.lowered.code 0 = some andProgram := rfl
theorem and_selection : NumericMachine.selectCode andProgram =
    some [.dup 2,.dup 2,.and] := rfl

/-- Full actual compiler-selected sequence for all operands and arbitrary
machine/symbolic caller; no desired execution premise or dirty-bit cleanup. -/
theorem and_run (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.dup 2,.dup 2,.and] {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord (a &&& b) :: coreWord a :: coreWord b :: tail} 0 := by
  simp only [Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
    coreWord,BitVec.toNat_and]
  rfl
#print axioms and_run

/-- Actual intrinsic expression and checked compiler certificate. -/
def orExpr : Expr [] [] 2 1 :=
  .builtin (.pure .or) (Fin.cases (.local 0) (fun _ => .local 1))
def orCompiled := (PureExpressions.compile 2 orExpr).get (by rfl)
def orProgram : Backend.Program := reads ++ [.op .OR]
theorem or_origin : orCompiled.lowered.code 0 = some orProgram := rfl
theorem or_selection : NumericMachine.selectCode orProgram =
    some [.dup 2,.dup 2,.or] := rfl

/-- Full actual compiler-selected sequence for all operands and arbitrary
machine/symbolic caller; no desired execution premise or dirty-bit cleanup. -/
theorem or_run (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.dup 2,.dup 2,.or] {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord (a ||| b) :: coreWord a :: coreWord b :: tail} 0 := by
  simp only [Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
    coreWord,BitVec.toNat_or]
  rfl
#print axioms or_run

/-- Actual intrinsic expression and checked compiler certificate. -/
def xorExpr : Expr [] [] 2 1 :=
  .builtin (.pure .xor) (Fin.cases (.local 0) (fun _ => .local 1))
def xorCompiled := (PureExpressions.compile 2 xorExpr).get (by rfl)
def xorProgram : Backend.Program := reads ++ [.op .XOR]
theorem xor_origin : xorCompiled.lowered.code 0 = some xorProgram := rfl
theorem xor_selection : NumericMachine.selectCode xorProgram =
    some [.dup 2,.dup 2,.xor] := rfl

/-- Full actual compiler-selected sequence for all operands and arbitrary
machine/symbolic caller; no desired execution premise or dirty-bit cleanup. -/
theorem xor_run (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.dup 2,.dup 2,.xor] {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord (a ^^^ b) :: coreWord a :: coreWord b :: tail} 0 := by
  simp only [Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
    coreWord,BitVec.toNat_xor]
  rfl
#print axioms xor_run
end Solidity.Yul.Compilation.BitMachineExecution
