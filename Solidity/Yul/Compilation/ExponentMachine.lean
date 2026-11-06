import Solidity.Yul.Compilation.WordMachine
import Solidity.Yul.Compilation.PureExpressions
/-! Actual unsigned exponent compiler-model execution. Existing full-word
semantics and original intrinsic source/compiler are reused. No selector,
admission, AST/state or native gas/resource convention is introduced. -/
namespace Solidity.Yul.Compilation.ExponentMachine
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def expr : Expr [] [] 2 1 :=
  .builtin (.pure .exp) (Fin.cases (.local 0) (fun _ => .local 1))
def compiled := (PureExpressions.compile 2 expr).get (by rfl)
def program : Backend.Program := [.op (.DUP 1),.op (.DUP 1),.op .EXP]
theorem origin : compiled.lowered.code 0 = some program := rfl
theorem selection : WordMachine.selectCode program = some [.dup 2,.dup 2,.exp] := rfl

/-- Actual full selected sequence for all base/exponent words and arbitrary
machine/symbolic caller. No desired-run premise, exponent cleaning or resource
bound is assumed. The base is on top and both original operands are retained. -/
theorem model_run (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.dup 2,.dup 2,.exp] {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord ((Scalar.binary .EXP).getD (fun _ _ => 0) a b) :: coreWord a :: coreWord b :: tail} 0 := by
  simp only [Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
    coreWord,Scalar.binary,Option.getD_some,BitVec.toNat_ofNat,Evm.W]
  rfl
#print axioms model_run
end Solidity.Yul.Compilation.ExponentMachine
