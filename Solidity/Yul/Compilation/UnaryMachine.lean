import Solidity.Yul.Compilation.WordMachine
import Solidity.Yul.Compilation.PureExpressions
/-! Actual unary word compiler-model execution, using original AST/semantics.
No selector/admission change or native/Source/G24 closure is inferred. -/
namespace Solidity.Yul.Compilation.UnaryMachine
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def iszeroExpr : Expr [] [] 1 1 :=
  .builtin (.pure .iszero) (fun _ => .local 0)
def iszeroCompiled := (PureExpressions.compile 2 iszeroExpr).get (by rfl)
def iszeroProgram : Backend.Program := [.op (.DUP 0),.op .ISZERO]
theorem iszero_origin : iszeroCompiled.lowered.code 0 = some iszeroProgram := rfl
theorem iszero_selection : WordMachine.selectCode iszeroProgram = some [.dup 1,.iszero] := rfl

/-- Derive complete actual emitted unary execution for all words, arbitrary
machine fields and symbolic caller tails, retaining the original operand. -/
theorem iszero_run (a : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.dup 1,.iszero] {m with stack := coreWord a :: tail} =
      .ok {m with stack := coreWord ((Scalar.unary .ISZERO).getD (fun _ => 0) a) :: coreWord a :: tail} 0 := by
  change Evm.run [.iszero] {m with stack := coreWord a :: coreWord a :: tail} = _
  by_cases z : a = 0
  · subst a
    rfl
  · have nz : a.toNat ≠ 0 := fun h => z (BitVec.eq_of_toNat_eq h)
    simp only [Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
      coreWord,Scalar.unary,Scalar.flag,Evm.bword,Option.getD_some,
      beq_eq_false_iff_ne.mpr z,decide_eq_false_iff_not.mpr nz,Bool.false_eq_true,↓reduceIte]
    rfl
#print axioms iszero_run

def notExpr : Expr [] [] 1 1 :=
  .builtin (.pure .not) (fun _ => .local 0)
def notCompiled := (PureExpressions.compile 2 notExpr).get (by rfl)
def notProgram : Backend.Program := [.op (.DUP 0),.op .NOT]
theorem not_origin : notCompiled.lowered.code 0 = some notProgram := rfl
theorem not_selection : WordMachine.selectCode notProgram = some [.dup 1,.not] := rfl

/-- Derive complete actual emitted unary execution for all words, arbitrary
machine fields and symbolic caller tails, retaining the original operand. -/
theorem not_run (a : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.dup 1,.not] {m with stack := coreWord a :: tail} =
      .ok {m with stack := coreWord ((Scalar.unary .NOT).getD (fun _ => 0) a) :: coreWord a :: tail} 0 := by
  simp only [Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
    coreWord,Scalar.unary,Option.getD_some,BitVec.toNat_not,Evm.W]
  rfl
#print axioms not_run
end Solidity.Yul.Compilation.UnaryMachine
