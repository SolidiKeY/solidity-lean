import Solidity.Yul.Compilation.ProducerStatements
/-! Recursive extension over the ORIGINAL VY1 intrinsic expression AST.
Unsigned DIV/MOD include zero-divisor results and preserve every dirty bit.
The original compiler/refusal controls are unchanged. This extension supports
ADD/SUB/MUL/DIV/MOD, not general Yul admission or source/session/G24 adequacy. -/
namespace Solidity.Yul.Compilation.QuotientExpressions
open Backend Scalar
open Solidity.Yul.Closed ProducerExpressions

def divBridge : BinaryBridge .div := ⟨selectDiv,by
  intro a b
  apply Fin.ext
  change (if b == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 (a.toNat/b.toNat)).toNat =
    (a.toNat/b.toNat) % 2^256
  by_cases zero : b = 0
  · subst b
    change 0 = (a.toNat/0) % 2^256
    rw [Nat.div_zero]
  · rw [beq_eq_false_iff_ne.mpr zero]
    rfl⟩

def modBridge : BinaryBridge .mod := ⟨selectMod,by
  intro a b
  apply Fin.ext
  change (if b == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 (a.toNat%b.toNat)).toNat =
    (if b.toNat = 0 then (word 0) else word (a.toNat%b.toNat)).val
  by_cases zero : b = 0
  · subst b
    rfl
  · have nonzero : b.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
    rw [beq_eq_false_iff_ne.mpr zero,if_neg nonzero]
    rfl⟩

/-- Actual recursive compiler certificates at the SAME source horizon. -/
def compile {n r : Nat} (fuel : Nat) (expr : Expr [] [] n r) : Option (Compiled fuel expr) :=
  match fuel with
  | 0 => none
  | fuel+1 => by
      apply Expr.casesOn (motive := fun r expr => Option (Compiled (fuel+1) expr)) expr
      case literal => intro w; exact some (literal fuel w)
      case «local» => intro i; exact some (localExpr fuel i)
      case external => intro ref; cases ref.index
      case call => intro sig f args; cases f
      case builtin =>
        intro a r builtin args
        cases builtin with
        | pure op =>
            cases op with
            | add => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary addBridge left right)
            | sub => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary subBridge left right)
            | mul => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary mulBridge left right)
            | «div» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary divBridge left right)
            | «mod» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary modBridge left right)
            | _ => exact none
        | _ => exact none
termination_by structural fuel

/-- Single-target assignment uses the existing real statement certificate. -/
def assignment {fuel n : Nat} {c : Control} (targets : Fin 1 → Target [] n) (expr : Expr [] [] n 1) :
    Option (ProducerStatements.Compiled (fuel+1) (Stmt.assign (c := c) targets expr)) :=
  (compile fuel expr).map (ProducerStatements.assignTargets targets)

#print axioms divBridge
#print axioms modBridge
#print axioms compile
#print axioms assignment
end Solidity.Yul.Compilation.QuotientExpressions
