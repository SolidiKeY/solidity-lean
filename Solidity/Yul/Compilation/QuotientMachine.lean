import Solidity.Yul.Compilation.NumericMachine
import Solidity.Yul.Compilation.PureExpressions
/-! Actual unsigned DIV/MOD compiler-model execution. No new AST, word meaning,
selector/admission or machine convention; native/G24 closure remains separate. -/
namespace Solidity.Yul.Compilation.QuotientMachine
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def reads : Backend.Program := [.op (.DUP 1),.op (.DUP 1)]

def divExpr : Expr [] [] 2 1 :=
  .builtin (.pure .div) (Fin.cases (.local 0) (fun _ => .local 1))
def divCompiled := (PureExpressions.compile 2 divExpr).get (by rfl)
def divProgram : Backend.Program := reads ++ [.op .DIV]
theorem div_origin : divCompiled.lowered.code 0 = some divProgram := rfl
theorem div_selection : NumericMachine.selectCode divProgram =
    some [.dup 2,.dup 2,.div] := rfl

/-- Actual full compiler-selected execution for all numeric operands,
including zero divisor, arbitrary machine fields and symbolic caller tail.
No desired-run premise, Solidity panic or cleaning of dirty bits. -/
theorem div_run (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.dup 2,.dup 2,.div] {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord ((Scalar.binary .DIV).getD (fun _ _ => 0) a b) :: coreWord a :: coreWord b :: tail} 0 := by
  change Evm.run [.div] {m with stack := coreWord a :: coreWord b :: coreWord a :: coreWord b :: tail} = _
  by_cases z : b = 0
  · subst b
    rfl
  · have nz : b.toNat ≠ 0 := fun h => z (BitVec.eq_of_toNat_eq h)
    simp only [Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
      coreWord,Scalar.binary,Option.getD_some,beq_eq_false_iff_ne.mpr z,
      Bool.false_eq_true,if_neg nz,↓reduceIte,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self a.toNat b.toNat) a.isLt)]
#print axioms div_run

def modExpr : Expr [] [] 2 1 :=
  .builtin (.pure .mod) (Fin.cases (.local 0) (fun _ => .local 1))
def modCompiled := (PureExpressions.compile 2 modExpr).get (by rfl)
def modProgram : Backend.Program := reads ++ [.op .MOD]
theorem mod_origin : modCompiled.lowered.code 0 = some modProgram := rfl
theorem mod_selection : NumericMachine.selectCode modProgram =
    some [.dup 2,.dup 2,.mod] := rfl

/-- Actual full compiler-selected execution for all numeric operands,
including zero divisor, arbitrary machine fields and symbolic caller tail.
No desired-run premise, Solidity panic or cleaning of dirty bits. -/
theorem mod_run (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.dup 2,.dup 2,.mod] {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord ((Scalar.binary .MOD).getD (fun _ _ => 0) a b) :: coreWord a :: coreWord b :: tail} 0 := by
  change Evm.run [.mod] {m with stack := coreWord a :: coreWord b :: coreWord a :: coreWord b :: tail} = _
  by_cases z : b = 0
  · subst b
    rfl
  · have nz : b.toNat ≠ 0 := fun h => z (BitVec.eq_of_toNat_eq h)
    simp only [Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
      coreWord,Scalar.binary,Option.getD_some,beq_eq_false_iff_ne.mpr z,
      Bool.false_eq_true,if_neg nz,↓reduceIte,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le a.toNat b.toNat) a.isLt)]
#print axioms mod_run
end Solidity.Yul.Compilation.QuotientMachine
