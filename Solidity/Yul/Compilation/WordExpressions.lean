import Solidity.Yul.Compilation.QuotientExpressions
/-! Actual original-AST word visitor: arithmetic/unsigned quotients plus
ISZERO/NOT/LT/GT/EQ. Older visitors and their refusal controls stay unchanged.
No source AST, word semantics or calling convention is added. -/
namespace Solidity.Yul.Compilation.WordExpressions
open Backend Scalar
open Solidity.Yul.Closed ProducerExpressions

structure UnaryBridge (op : Pure 1) where
  selection : UnarySelection
  agrees : ∀ a : Scalar.Word, (selection.value a).toFin = op.eval (fun _ => a.toFin)

private theorem zero_test (a : Scalar.Word) : (a == 0) = (a.toNat == 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact ⟨fun h => congrArg BitVec.toNat h,fun h => BitVec.eq_of_toNat_eq h⟩

def iszeroBridge : UnaryBridge .iszero := ⟨selectIsZero,by
  intro a
  change (flag (a == 0)).toFin = truth (a.toNat == 0)
  rw [zero_test]
  cases a.toNat == 0 <;> rfl⟩

def notBridge : UnaryBridge .not := ⟨selectNot,by
  intro a
  apply Fin.ext
  change (~~~a).toNat = (2^256-1-a.toNat) % 2^256
  rw [BitVec.toNat_not,Nat.mod_eq_of_lt (by
    have positive : 0 < 2^256 := by decide
    omega)]⟩

def selectLt : BinarySelection := ⟨.LT,(Scalar.binary .LT).getD (fun _ _ => 0),fun _ _ _ => rfl⟩
def selectGt : BinarySelection := ⟨.GT,(Scalar.binary .GT).getD (fun _ _ => 0),fun _ _ _ => rfl⟩
def selectEq : BinarySelection := ⟨.EQ,(Scalar.binary .EQ).getD (fun _ _ => 0),fun _ _ _ => rfl⟩

def ltBridge : BinaryBridge .lt := ⟨selectLt,by
  intro a b
  change (flag (a.toNat < b.toNat)).toFin = truth (a.toNat < b.toNat)
  cases decide (a.toNat < b.toNat) <;> rfl⟩
def gtBridge : BinaryBridge .gt := ⟨selectGt,by
  intro a b
  change (flag (b.toNat < a.toNat)).toFin = truth (b.toNat < a.toNat)
  cases decide (b.toNat < a.toNat) <;> rfl⟩
def eqBridge : BinaryBridge .eq := ⟨selectEq,by
  intro a b
  have test : (a == b) = (a.toNat == b.toNat) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact ⟨congrArg BitVec.toNat,BitVec.eq_of_toNat_eq⟩
  change (flag (a == b)).toFin = truth (a.toNat == b.toNat)
  rw [test]
  cases a.toNat == b.toNat <;> rfl⟩

private theorem unaryProfile {fuel n : Nat} {args : Fin 1 → Expr [] [] n 1}
    (argument : Compiled fuel (args 0)) (i : Fin 1) : ExprWordP (args i) := by
  have equal : i = 0 := by omega
  subst i
  exact argument.profile

def unary {fuel n : Nat} {args : Fin 1 → Expr [] [] n 1} {op : Pure 1}
    (bridge : UnaryBridge op) (argument : Compiled fuel (args 0)) :
    Compiled (fuel+1) (.builtin (.pure op) args) where
  one := rfl
  profile := ⟨rfl,unaryProfile argument⟩
  value := fun locals => bridge.selection.value (argument.value locals)
  lowered := lowerUnary bridge.selection argument.lowered
  source := by
    intro locals
    rw [evalExpr_builtin fuel .nil True.intro (.pure op) (.pure op)]
    have operands : (fun i : Fin 1 =>
        (evalExpr fuel .nil True.intro (args i) (unaryProfile argument i) (sourceLocals locals)).map
          (fun result : Values 1 => result 0)) =
        (fun _ => some (argument.value locals).toFin) := by
      funext i
      have equal : i = 0 := by omega
      subst i
      rw [argument.source]
      rfl
    rw [operands,collectValues_allSome]
    change some (fun _ => op.eval _) = some (fun _ => _)
    rw [bridge.agrees]

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
                pure (ProducerExpressions.binary QuotientExpressions.divBridge left right)
            | «mod» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary QuotientExpressions.modBridge left right)
            | lt => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary ltBridge left right)
            | gt => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary gtBridge left right)
            | eq => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary eqBridge left right)
            | iszero => exact do
                let arg ← compile fuel (args 0)
                pure (unary iszeroBridge arg)
            | «not» => exact do
                let arg ← compile fuel (args 0)
                pure (unary notBridge arg)
            | _ => exact none
        | _ => exact none
termination_by structural fuel

/-- Single-target assignment uses the existing real statement certificate. -/
def assignment {fuel n : Nat} {c : Control} (targets : Fin 1 → Target [] n) (expr : Expr [] [] n 1) :
    Option (ProducerStatements.Compiled (fuel+1) (Stmt.assign (c := c) targets expr)) :=
  (compile fuel expr).map (ProducerStatements.assignTargets targets)

#print axioms iszeroBridge
#print axioms notBridge
#print axioms ltBridge
#print axioms gtBridge
#print axioms eqBridge
#print axioms unary
#print axioms compile
end Solidity.Yul.Compilation.WordExpressions
