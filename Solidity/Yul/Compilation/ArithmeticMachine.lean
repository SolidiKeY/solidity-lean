import Solidity.Yul.Compilation.NumericMachine
import Solidity.Yul.Compilation.ProducerExpressions
/-! Actual ADD/MUL execution in the existing compiler machine. No selector,
source AST, machine state, calling convention or word semantics is changed.
PUSH width/PC/gas/capacity/native and Source/G24 adequacy remain separate. -/
namespace Solidity.Yul.Compilation.ArithmeticMachine
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

theorem add_step (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.Instr.step .add {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord (a+b) :: tail} 0 := by
  simp only [Evm.Instr.step,coreWord,BitVec.toNat_add,Evm.wmod,Evm.W]
  rfl

theorem mul_step (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.Instr.step .mul {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord (a*b) :: tail} 0 := by
  simp only [Evm.Instr.step,coreWord,BitVec.toNat_mul,Evm.wmod,Evm.W]
  rfl

/-- Actual VY1 expression and actual compiler certificate, not an arbitrary
function posing as source semantics. -/
def addExpr : Expr [] [] 2 1 :=
  .builtin (.pure .add) (Fin.cases (.local 0) (fun _ => .local 1))
def mulExpr : Expr [] [] 2 1 :=
  .builtin (.pure .mul) (Fin.cases (.local 0) (fun _ => .local 1))
def addCompiled := (ProducerExpressions.compile 2 addExpr).get (by rfl)
def mulCompiled := (ProducerExpressions.compile 2 mulExpr).get (by rfl)
def reads : Backend.Program := [.op (.DUP 1),.op (.DUP 1)]
def addProgram : Backend.Program := reads ++ [.op .ADD]
def mulProgram : Backend.Program := reads ++ [.op .MUL]
theorem add_origin : addCompiled.lowered.code 0 = some addProgram := rfl
theorem mul_origin : mulCompiled.lowered.code 0 = some mulProgram := rfl
theorem add_selection : NumericMachine.selectCode addProgram = some [.dup 2,.dup 2,.add] := rfl
theorem mul_selection : NumericMachine.selectCode mulProgram = some [.dup 2,.dup 2,.mul] := rfl


/-- Complete actual compiler-selected sequence; numeric operands are explicit,
while every caller word may remain symbolic. No generic run premise. -/
theorem add_run (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.dup 2,.dup 2,.add] {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord (a+b) :: coreWord a :: coreWord b :: tail} 0 := by
  simp only [Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
    coreWord,BitVec.toNat_add,Evm.wmod,Evm.W]
  rfl

/-- Complete actual compiler-selected sequence; numeric operands are explicit,
while every caller word may remain symbolic. No generic run premise. -/
theorem mul_run (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.dup 2,.dup 2,.mul] {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord (a*b) :: coreWord a :: coreWord b :: tail} 0 := by
  simp only [Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
    coreWord,BitVec.toNat_mul,Evm.wmod,Evm.W]
  rfl

#print axioms add_run
#print axioms mul_run
#print axioms add_step
#print axioms mul_step
end Solidity.Yul.Compilation.ArithmeticMachine
