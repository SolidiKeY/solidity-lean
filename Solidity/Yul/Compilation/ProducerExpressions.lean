import Solidity.Yul.Compilation.PureLowering
import Solidity.Yul.WordUpdates

/-! Concrete consumer of VY1's original intrinsic Expr and evaluator.
Fuel is the SAME source expression horizon, not target gas or a new budget.
This initial compiler may refuse forms/depths; no admission change follows.
Source word Fin and target BitVec are transported without cleaning any bits. -/
namespace Solidity.Yul.Compilation.ProducerExpressions
open Backend Scalar
open Solidity.Yul.Closed

abbrev sourceLocals {n : Nat} (locals : Vector Scalar.Word n) : Values n :=
  fun i => locals[i.val].toFin

structure Compiled (fuel : Nat) {n r : Nat} (expr : Expr [] [] n r) where
  one : r = 1
  profile : ExprWordP expr
  value : Vector Scalar.Word n → Scalar.Word
  lowered : LoweredExpr n value
  source : ∀ locals, evalExpr fuel .nil True.intro expr profile (sourceLocals locals) =
    some (fun _ => (value locals).toFin)

structure BinaryBridge (op : Pure 2) where
  selection : BinarySelection
  agrees : ∀ a b : Scalar.Word, (selection.value a b).toFin =
    op.eval (Fin.cases a.toFin (fun _ => b.toFin))

def addBridge : BinaryBridge .add := ⟨selectAdd, fun _ _ => rfl⟩
def mulBridge : BinaryBridge .mul := ⟨selectMul, fun _ _ => rfl⟩
def subBridge : BinaryBridge .sub := ⟨selectSub, by
  intro a b
  apply Fin.ext
  change ((2^256-b.toNat)+a.toNat) % 2^256 = (a.toNat+2^256-b.toNat) % 2^256
  exact congrArg (fun k => k % 2^256) (by have bound := b.isLt; omega)⟩

def literal (fuel : Nat) {n : Nat} (w : Solidity.Yul.Word) :
    Compiled (fuel+1) (Expr.literal (n := n) w) :=
  ⟨rfl, True.intro, fun _ => BitVec.ofFin w, lowerLiteral (BitVec.ofFin w), fun _ => rfl⟩

def localExpr (fuel : Nat) {n : Nat} (i : Fin n) :
    Compiled (fuel+1) (Expr.local (X := []) i) :=
  ⟨rfl, True.intro, fun locals => locals[i.val], lowerLocal i, fun _ => rfl⟩

private theorem binaryProfile {fuel n : Nat} {args : Fin 2 → Expr [] [] n 1}
    (left : Compiled fuel (args 0)) (right : Compiled fuel (args 1))
    (i : Fin 2) : ExprWordP (args i) := by
  have h : i = 0 ∨ i = 1 := by omega
  rcases h with h | h
  · subst i; exact left.profile
  · subst i; exact right.profile

def binary {fuel n : Nat} {args : Fin 2 → Expr [] [] n 1} {op : Pure 2}
    (bridge : BinaryBridge op) (left : Compiled fuel (args 0))
    (right : Compiled fuel (args 1)) :
    Compiled (fuel+1) (.builtin (.pure op) args) where
  one := rfl
  profile := ⟨rfl, binaryProfile left right⟩
  value := fun locals => bridge.selection.value (left.value locals) (right.value locals)
  lowered := lowerBinary bridge.selection left.lowered right.lowered
  source := by
    intro locals
    rw [evalExpr_builtin fuel .nil True.intro (.pure op) (.pure op)]
    have operands : (fun i : Fin 2 =>
        (evalExpr fuel .nil True.intro (args i) (binaryProfile left right i) (sourceLocals locals)).map
          (fun result : Values 1 => result 0)) =
        (fun i => some (Fin.cases (left.value locals).toFin
          (fun _ => (right.value locals).toFin) i)) := by
      funext i
      have h : i = 0 ∨ i = 1 := by omega
      rcases h with h | h
      · subst i; rw [left.source]; rfl
      · subst i; rw [right.source]; rfl
    rw [operands, collectValues_allSome]
    change some (fun _ => op.eval _) = some (fun _ => _)
    rw [bridge.agrees]

/-- Real recursive visitor on the producer AST. Unsupported constructors return
none; no untyped expression tree or assumed source execution is introduced. -/
def compile {n r : Nat} (fuel : Nat) (expr : Expr [] [] n r) :
    Option (Compiled fuel expr) :=
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
                pure (binary addBridge left right)
            | sub => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (binary subBridge left right)
            | mul => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (binary mulBridge left right)
            | _ => exact none
        | _ => exact none
termination_by structural fuel

/-- Conditional only on actual target emission; source completion is derived.
DUP depth and 1024 capacity remain separate obligations. -/
theorem executes {fuel n : Nat} {expr : Expr [] [] n 1}
    (compiled : Compiled fuel expr) (depth : Nat) (code : Program)
    (emitted : compiled.lowered.code depth = some code) (locals : Vector Scalar.Word n)
    (newer : Vector Scalar.Word depth) (caller : Stack) :
    evalExpr fuel .nil True.intro expr compiled.profile (sourceLocals locals) =
      some (fun _ => (compiled.value locals).toFin) ∧
    run code (newer.toList ++ (locals.toList ++ caller)) =
      some (compiled.value locals :: (newer.toList ++ (locals.toList ++ caller))) :=
  ⟨compiled.source locals, compiled.lowered.correct depth code emitted locals newer caller⟩

#print axioms compile
#print axioms executes
end Solidity.Yul.Compilation.ProducerExpressions
