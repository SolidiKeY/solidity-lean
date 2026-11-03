import Solidity.Yul.Compilation.SignedMachine
import Solidity.Yul.Compilation.PureExpressions
/-! Actual signed-comparison compiler-model transport. No new signed word
meaning, AST/state, selector/admission or native/G24 convention. -/
namespace Solidity.Yul.Compilation.SignedComparisonMachine
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter
/-- Existing machine signed reading agrees with the actual producer's BitVec
reading. Normalize the cast instead of evaluating giant powers by conversion. -/
theorem reading (a : Scalar.Word) : Evm.sgn a.toNat = a.toInt := by
  simp only [Evm.sgn,Evm.H,Evm.W,Int.natCast_pow]
  exact SignedExpressions.signed_word a
#print axioms reading


def sltExpr : Expr [] [] 2 1 :=
  .builtin (.pure .slt) (Fin.cases (.local 0) (fun _ => .local 1))
def sltCompiled := (PureExpressions.compile 2 sltExpr).get (by rfl)
def sltProgram : Backend.Program := [.op (.DUP 1),.op (.DUP 1),.op .SLT]
theorem slt_origin : sltCompiled.lowered.code 0 = some sltProgram := rfl
theorem slt_selection : SignedMachine.selectCode sltProgram =
    some [.dup 2,.dup 2,.slt] := rfl

/-- Full actual signed comparison run for all words, arbitrary machine fields
and symbolic caller. Full raw bits determine the signed reading; no run premise. -/
theorem slt_run (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.dup 2,.dup 2,.slt] {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord ((Scalar.binary .SLT).getD (fun _ _ => 0) a b) :: coreWord a :: coreWord b :: tail} 0 := by
  change Evm.run [.slt] {m with stack := coreWord a :: coreWord b :: coreWord a :: coreWord b :: tail} = _
  cases test : decide (a.toInt < b.toInt) <;>
    simp only [Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
      coreWord,reading,Scalar.binary,Scalar.flag,Evm.bword,Option.getD_some,test,↓reduceIte] <;> rfl
#print axioms slt_run

def sgtExpr : Expr [] [] 2 1 :=
  .builtin (.pure .sgt) (Fin.cases (.local 0) (fun _ => .local 1))
def sgtCompiled := (PureExpressions.compile 2 sgtExpr).get (by rfl)
def sgtProgram : Backend.Program := [.op (.DUP 1),.op (.DUP 1),.op .SGT]
theorem sgt_origin : sgtCompiled.lowered.code 0 = some sgtProgram := rfl
theorem sgt_selection : SignedMachine.selectCode sgtProgram =
    some [.dup 2,.dup 2,.sgt] := rfl

/-- Full actual signed comparison run for all words, arbitrary machine fields
and symbolic caller. Full raw bits determine the signed reading; no run premise. -/
theorem sgt_run (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.dup 2,.dup 2,.sgt] {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord ((Scalar.binary .SGT).getD (fun _ _ => 0) a b) :: coreWord a :: coreWord b :: tail} 0 := by
  change Evm.run [.sgt] {m with stack := coreWord a :: coreWord b :: coreWord a :: coreWord b :: tail} = _
  cases test : decide (b.toInt < a.toInt) <;>
    simp only [Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
      coreWord,reading,Scalar.binary,Scalar.flag,Evm.bword,Option.getD_some,test,↓reduceIte] <;> rfl
#print axioms sgt_run
end Solidity.Yul.Compilation.SignedComparisonMachine
