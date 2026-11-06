import Solidity.Yul.Compilation.RemainingWordBridges
/-! Compiler certificates for every producer Pure constructor. BYTE and CLZ
use existing software expansions; non-pure builtins remain refused. Source
horizons, emission/accessibility and target capacity stay distinct obligations. -/
namespace Solidity.Yul.Compilation.PureExpressions
open Backend Scalar
open Solidity.Yul.Closed ProducerExpressions WordExpressions BitExpressions SignedExpressions ModularExpressions RemainingWordBridges

private theorem unaryProfile {fuel n : Nat} {args : Fin 1 → Expr [] [] n 1}
    (argument : Compiled fuel (args 0)) (i : Fin 1) : ExprWordP (args i) := by
  have equal : i = 0 := by omega
  subst i
  exact argument.profile

def clz {fuel n : Nat} {args : Fin 1 → Expr [] [] n 1} 
    (argument : Compiled fuel (args 0)) :
    Compiled (fuel+1) (.builtin (.pure .clz) args) where
  one := rfl
  profile := ⟨rfl,unaryProfile argument⟩
  value := fun locals => (argument.value locals).clz
  lowered := lowerClzExpanded argument.lowered
  source := by
    intro locals
    rw [evalExpr_builtin fuel .nil True.intro (.pure .clz) (.pure .clz)]
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
    change some (fun _ : Fin 1 => Solidity.Yul.clz (argument.value locals).toFin) =
      some (fun _ : Fin 1 => (argument.value locals).clz.toFin)
    rw [clz_agreement]

private theorem binaryProfile {fuel n : Nat} {args : Fin 2 → Expr [] [] n 1}
    (left : Compiled fuel (args 0)) (right : Compiled fuel (args 1))
    (i : Fin 2) : ExprWordP (args i) := by
  have h : i = 0 ∨ i = 1 := by omega
  rcases h with h | h
  · subst i; exact left.profile
  · subst i; exact right.profile

def byte {fuel n : Nat} {args : Fin 2 → Expr [] [] n 1} 
    (left : Compiled fuel (args 0))
    (right : Compiled fuel (args 1)) :
    Compiled (fuel+1) (.builtin (.pure .byte) args) where
  one := rfl
  profile := ⟨rfl, binaryProfile left right⟩
  value := fun locals => indexedByteWindow (left.value locals) (right.value locals)
  lowered := lowerByte left.lowered right.lowered
  source := by
    intro locals
    rw [evalExpr_builtin fuel .nil True.intro (.pure .byte) (.pure .byte)]
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
    change some (fun _ => (Pure.byte).eval _) = some (fun _ => _)
    rw [byte_agreement]

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
                pure (WordExpressions.unary iszeroBridge arg)
            | «not» => exact do
                let arg ← compile fuel (args 0)
                pure (WordExpressions.unary notBridge arg)
            | «and» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary andBridge left right)
            | «or» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary orBridge left right)
            | «xor» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary xorBridge left right)
            | «shl» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary shlBridge left right)
            | «shr» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary shrBridge left right)
            | sdiv => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary sdivBridge left right)
            | smod => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary smodBridge left right)
            | slt => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary sltBridge left right)
            | sgt => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary sgtBridge left right)
            | sar => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary sarBridge left right)
            | addmod => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                let modulus ← compile fuel (args 2)
                pure (ModularExpressions.ternary addmodBridge left right modulus)
            | mulmod => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                let modulus ← compile fuel (args 2)
                pure (ModularExpressions.ternary mulmodBridge left right modulus)
            | exp => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary expBridge left right)
            | signextend => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary signextendBridge left right)
            | byte => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (PureExpressions.byte left right)
            | clz => exact do
                let argument ← compile fuel (args 0)
                pure (PureExpressions.clz argument)
        | _ => exact none
termination_by structural fuel

/-- Single-target assignment uses the existing real statement certificate. -/
def assignment {fuel n : Nat} {c : Control} (targets : Fin 1 → Target [] n) (expr : Expr [] [] n 1) :
    Option (ProducerStatements.Compiled (fuel+1) (Stmt.assign (c := c) targets expr)) :=
  (compile fuel expr).map (ProducerStatements.assignTargets targets)

#print axioms clz
#print axioms byte
#print axioms compile
end Solidity.Yul.Compilation.PureExpressions
