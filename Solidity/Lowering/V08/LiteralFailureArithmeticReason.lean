import Solidity.Lowering.V08.LiteralFailureLowering
import Solidity.Source.ValueProgress

/-! Panic provenance from real arithmetic with an effectful denominator.
The target endpoint is only the existing constant-packet terminal slice. -/
namespace Solidity.Lowering.V08.LiteralFailureArithmeticReason
open Solidity Source Backend

def context (Γ : RCtx) : RCtx := .int IntTy.u256 :: .int IntTy.u256 :: Γ

def zero {D : Source.Layout} : Source.Val D (.int IntTy.u256) := .int 0 (by decide +kernel)

def caller {E : Env} {Γ : RCtx} (x : Source.Val E.layout (.int IntTy.u256))
 (older : Locals E.layout Γ) : Locals E.layout (context Γ) := .cons x (.cons zero older)

def denominator {E : Env} {Γ : RCtx} : RExpr E (context Γ) (.int IntTy.u256) :=
 .assign (.local .here) (.local (.there .here))

def operation {E : Env} {Γ : RCtx} (modulo : Bool) : RExpr E (context Γ) (.int IntTy.u256) :=
 .binary (if modulo then .mod else .div) (.local .here) denominator

/-- Both original operand orders really execute the assignment before panicking.
Unchecked arithmetic does not suppress division/modulo-by-zero panic. -/
theorem execution {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat) (modulo : Bool)
 (x : Source.Val E.layout (.int IntTy.u256)) (older : Locals E.layout Γ) (state : St E) :
 (evalE G F (n+8) (operation modulo)).run (caller x older,state)=
 (.error (.revert (panicData .divZero)),(caller zero older,state)) := by
 obtain ⟨value,valid,rfl⟩ := Source.Val.eq_int x
 cases order : G.pipeline <;> cases modulo <;>
  simp only [operation,denominator,caller,evalE,evalPair,order,evalLoc,writeLoc,
   getV,RVal.get,zero,Bool.false_eq_true,↓reduceIte] <;> rfl

/-- Pair the real Source panic with the existing known-packet emitter.
This does not compile the arithmetic expression or relate the two machines. -/
theorem packet {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat) (modulo : Bool)
 (x : Source.Val E.layout (.int IntTy.u256)) (older : Locals E.layout Γ) (state : St E)
 (address : Nat) (tail : Program) (machine : Failure.Slice.Machine)
 (fits : Failure.Fits address (panicData .divZero)) (stack : machine.stack.length+2≤1024) :
 (evalE G F (n+8) (operation modulo)).run (caller x older,state)=
  (.error (.revert (panicData .divZero)),(caller zero older,state)) ∧
 Failure.Slice.checkedRun (Failure.emit address (LiteralFailureLowering.panicInput .divZero) ++ tail) machine=
 some ({machine with memory:=Failure.Slice.putBytes machine.memory address (panicData .divZero)},
 some (revertOutcome (panicData .divZero))) :=
 ⟨execution G F n modulo x older state,
  LiteralFailureLowering.panic_checked .divZero address tail machine fits stack⟩
end Solidity.Lowering.V08.LiteralFailureArithmeticReason
