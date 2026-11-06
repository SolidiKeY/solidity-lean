import Solidity.Yul.Compilation.WordMachine
import Solidity.Yul.Compilation.PureExpressions
/-! Actual unsigned comparison compiler-model execution. No new AST, state,
word meanings, selector/admission or native/Source-G24 convention. -/
namespace Solidity.Yul.Compilation.ComparisonMachine
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def reads : Backend.Program := [.op (.DUP 1),.op (.DUP 1)]

def ltExpr : Expr [] [] 2 1 :=
  .builtin (.pure .lt) (Fin.cases (.local 0) (fun _ => .local 1))
def ltCompiled := (PureExpressions.compile 2 ltExpr).get (by rfl)
def ltProgram : Backend.Program := reads ++ [.op .LT]
theorem lt_origin : ltCompiled.lowered.code 0 = some ltProgram := rfl
theorem lt_selection : WordMachine.selectCode ltProgram =
    some [.dup 2,.dup 2,.lt] := rfl

/-- Complete actual selected run for all full words, arbitrary machine fields
and symbolic caller, retaining both original operands. No run premise. -/
theorem lt_run (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.dup 2,.dup 2,.lt] {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord ((Scalar.binary .LT).getD (fun _ _ => 0) a b) :: coreWord a :: coreWord b :: tail} 0 := by
  change Evm.run [.lt] {m with stack := coreWord a :: coreWord b :: coreWord a :: coreWord b :: tail} = _
  cases test : decide (a.toNat < b.toNat) <;>
    simp only [Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
      coreWord,Scalar.binary,Scalar.flag,Evm.bword,Option.getD_some,test,↓reduceIte] <;> rfl
#print axioms lt_run

def gtExpr : Expr [] [] 2 1 :=
  .builtin (.pure .gt) (Fin.cases (.local 0) (fun _ => .local 1))
def gtCompiled := (PureExpressions.compile 2 gtExpr).get (by rfl)
def gtProgram : Backend.Program := reads ++ [.op .GT]
theorem gt_origin : gtCompiled.lowered.code 0 = some gtProgram := rfl
theorem gt_selection : WordMachine.selectCode gtProgram =
    some [.dup 2,.dup 2,.gt] := rfl

/-- Complete actual selected run for all full words, arbitrary machine fields
and symbolic caller, retaining both original operands. No run premise. -/
theorem gt_run (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.dup 2,.dup 2,.gt] {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord ((Scalar.binary .GT).getD (fun _ _ => 0) a b) :: coreWord a :: coreWord b :: tail} 0 := by
  change Evm.run [.gt] {m with stack := coreWord a :: coreWord b :: coreWord a :: coreWord b :: tail} = _
  cases test : decide (b.toNat < a.toNat) <;>
    simp only [Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
      coreWord,Scalar.binary,Scalar.flag,Evm.bword,Option.getD_some,test,↓reduceIte] <;> rfl
#print axioms gt_run

def eqExpr : Expr [] [] 2 1 :=
  .builtin (.pure .eq) (Fin.cases (.local 0) (fun _ => .local 1))
def eqCompiled := (PureExpressions.compile 2 eqExpr).get (by rfl)
def eqProgram : Backend.Program := reads ++ [.op .EQ]
theorem eq_origin : eqCompiled.lowered.code 0 = some eqProgram := rfl
theorem eq_selection : WordMachine.selectCode eqProgram =
    some [.dup 2,.dup 2,.eq] := rfl

/-- Complete actual selected run for all full words, arbitrary machine fields
and symbolic caller, retaining both original operands. No run premise. -/
theorem eq_run (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.dup 2,.dup 2,.eq] {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord ((Scalar.binary .EQ).getD (fun _ _ => 0) a b) :: coreWord a :: coreWord b :: tail} 0 := by
  change Evm.run [.eq] {m with stack := coreWord a :: coreWord b :: coreWord a :: coreWord b :: tail} = _
  by_cases z : a = b
  · subst b
    simp only [Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
      coreWord,Scalar.binary,Scalar.flag,Evm.bword,Option.getD_some,
      beq_self_eq_true,decide_true,↓reduceIte] <;> rfl
  · have nz : a.toNat ≠ b.toNat := fun h => z (BitVec.eq_of_toNat_eq h)
    simp only [Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
      coreWord,Scalar.binary,Scalar.flag,Evm.bword,Option.getD_some,
      beq_eq_false_iff_ne.mpr z,decide_eq_false_iff_not.mpr nz,Bool.false_eq_true,↓reduceIte] <;> rfl
#print axioms eq_run
end Solidity.Yul.Compilation.ComparisonMachine
