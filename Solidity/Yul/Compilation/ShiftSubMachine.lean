import Solidity.Yul.Compilation.NumericMachine
import Solidity.Yul.Compilation.PureExpressions
/-! Actual SUB/SHL/SHR compiler-model execution. No source AST, state, selector,
word meaning or calling convention change; native/G24 closure remains separate. -/
namespace Solidity.Yul.Compilation.ShiftSubMachine
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def reads : Backend.Program := [.op (.DUP 1),.op (.DUP 1)]

def subExpr : Expr [] [] 2 1 :=
  .builtin (.pure .sub) (Fin.cases (.local 0) (fun _ => .local 1))
def subCompiled := (PureExpressions.compile 2 subExpr).get (by rfl)
def subProgram : Backend.Program := reads ++ [.op .SUB]
theorem sub_origin : subCompiled.lowered.code 0 = some subProgram := rfl
theorem sub_selection : NumericMachine.selectCode subProgram =
    some [.dup 2,.dup 2,.sub] := rfl

/-- Actual complete compiler-selected execution for all words, arbitrary
machine and symbolic caller. Operands and nonstack fields remain unchanged. -/
theorem sub_run (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.dup 2,.dup 2,.sub] {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord (a-b) :: coreWord a :: coreWord b :: tail} 0 := by
  simp only [Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
    coreWord,BitVec.toNat_sub,Evm.W,Nat.add_comm]
  rfl
#print axioms sub_run

def shlExpr : Expr [] [] 2 1 :=
  .builtin (.pure .shl) (Fin.cases (.local 0) (fun _ => .local 1))
def shlCompiled := (PureExpressions.compile 2 shlExpr).get (by rfl)
def shlProgram : Backend.Program := reads ++ [.op .SHL]
theorem shl_origin : shlCompiled.lowered.code 0 = some shlProgram := rfl
theorem shl_selection : NumericMachine.selectCode shlProgram =
    some [.dup 2,.dup 2,.shl] := rfl

/-- Actual complete compiler-selected execution for all words, arbitrary
machine and symbolic caller. Operands and nonstack fields remain unchanged. -/
theorem shl_run (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.dup 2,.dup 2,.shl] {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord ((Scalar.binary .SHL).getD (fun _ _ => 0) a b) :: coreWord a :: coreWord b :: tail} 0 := by
  change Evm.run [.shl] {m with stack := coreWord a :: coreWord b :: coreWord a :: coreWord b :: tail} = _
  by_cases h : a.toNat < 256 <;>
    simp only [Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
      coreWord,Scalar.binary,Option.getD_some,h,↓reduceIte,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Evm.wmod,Evm.W] <;> rfl
#print axioms shl_run

def shrExpr : Expr [] [] 2 1 :=
  .builtin (.pure .shr) (Fin.cases (.local 0) (fun _ => .local 1))
def shrCompiled := (PureExpressions.compile 2 shrExpr).get (by rfl)
def shrProgram : Backend.Program := reads ++ [.op .SHR]
theorem shr_origin : shrCompiled.lowered.code 0 = some shrProgram := rfl
theorem shr_selection : NumericMachine.selectCode shrProgram =
    some [.dup 2,.dup 2,.shr] := rfl

/-- Actual complete compiler-selected execution for all words, arbitrary
machine and symbolic caller. Operands and nonstack fields remain unchanged. -/
theorem shr_run (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.dup 2,.dup 2,.shr] {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord ((Scalar.binary .SHR).getD (fun _ _ => 0) a b) :: coreWord a :: coreWord b :: tail} 0 := by
  change Evm.run [.shr] {m with stack := coreWord a :: coreWord b :: coreWord a :: coreWord b :: tail} = _
  by_cases h : a.toNat < 256 <;>
    simp only [Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
      coreWord,Scalar.binary,Option.getD_some,h,↓reduceIte,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,Evm.W] <;> rfl
#print axioms shr_run
end Solidity.Yul.Compilation.ShiftSubMachine
