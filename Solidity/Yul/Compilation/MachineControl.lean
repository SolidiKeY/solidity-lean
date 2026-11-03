import Solidity.Yul.Compilation.NumericMachine
import Solidity.Yul.Compilation.ControlLowering

/-! Target model adapter for existing structured Backend.Block. Relative
instruction skips below are Evm.Machine conventions, not native byte offsets.
No source AST, loop semantics or V12 runtime convention is introduced. -/
namespace Solidity.Yul.Compilation.MachineControl
open Backend Scalar

/-- Nonzero skips the else body and its terminal skip; zero executes else and
skips then. Both paths consume exactly the condition word. -/
def branchTail (yes no : List Evm.Instr) : List Evm.Instr :=
  .jumpi (no.length + 1) :: (no ++ (.jump yes.length :: yes))
def branchCode (condition yes no : List Evm.Instr) : List Evm.Instr :=
  condition ++ branchTail yes no

/-- Concrete code selection into the existing model, reusing its loop opcode.
Selection alone is not a correctness theorem for loops or native assembled code. -/
def blockCode : Backend.Block → Option (List Evm.Instr)
  | .code p => NumericMachine.selectCode p
  | .seq a b => (blockCode a).bind (fun x => (blockCode b).map (fun y => x ++ y))
  | .ite c a b => (NumericMachine.selectCode c).bind (fun x =>
      (blockCode a).bind (fun y => (blockCode b).map (fun z => branchCode x y z)))
  | .loop c b => (NumericMachine.selectCode c).bind (fun x =>
      (blockCode b).map (fun y => [Evm.Instr.loop x y]))

/-- Actual accepted structured branch lowering followed by model selection. -/
def lowerBranch {n : Nat} {condition : Vector Word n → Word}
    {yes no : Vector Word n → Vector Word n}
    (c : LoweredExpr n condition) (a : LoweredStmt n yes) (b : LoweredStmt n no)
    (depth : Nat) : Option (List Evm.Instr) :=
  (Solidity.Yul.Compilation.lowerBranch c a b depth).bind blockCode

theorem branchTail_run (condition : Fin Evm.W) (yes no : List Evm.Instr)
    (m my mn : Evm.Machine) (yesRun : Evm.run yes m = .ok my 0)
    (noRun : Evm.run no m = .ok mn 0) :
    Evm.run (branchTail yes no) {m with stack := .val condition :: m.stack} =
      .ok (if condition.val = 0 then mn else my) 0 := by
  by_cases zero : condition.val = 0
  · simp only [branchTail, Evm.run, Evm.exec_cons_zero, Evm.Instr.step,
      zero, ite_true, Evm.Out.ok_bind]
    change Evm.run (no ++ (.jump yes.length :: yes)) m = _
    rw [Evm.run_append_ok noRun]
    change Evm.exec yes yes.length mn = _
    exact Evm.exec_length yes mn
  · simp only [branchTail, Evm.run, Evm.exec_cons_zero, Evm.Instr.step,
      zero, ite_false, Evm.Out.ok_bind]
    rw [Evm.exec_skip_append]
    exact yesRun

/-- Exact model driver: real condition/arm executions are the premises here;
compiler-certificate corollaries must discharge them concretely. -/
theorem branchCode_run (condition : Fin Evm.W) (cc yes no : List Evm.Instr)
    (m my mn : Evm.Machine)
    (conditionRun : Evm.run cc m = .ok {m with stack := .val condition :: m.stack} 0)
    (yesRun : Evm.run yes m = .ok my 0) (noRun : Evm.run no m = .ok mn 0) :
    Evm.run (branchCode cc yes no) m = .ok (if condition.val = 0 then mn else my) 0 := by
  rw [branchCode, Evm.run_append_ok conditionRun]
  exact branchTail_run condition yes no m my mn yesRun noRun

#print axioms branchTail_run
#print axioms branchCode_run
end Solidity.Yul.Compilation.MachineControl
