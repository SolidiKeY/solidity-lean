import Solidity.Yul.Compilation.SignedExpressions
import Solidity.Yul.Compilation.OpcodeLowering
/-! Actual original-AST ternary modular arithmetic compilation. Existing typed
arity-three lowering and unbounded-intermediate word semantics are reused;
no AST, word semantics, calling convention or owner machinery is duplicated. -/
namespace Solidity.Yul.Compilation.ModularExpressions
open Backend Scalar
open Solidity.Yul.Closed ProducerExpressions WordExpressions BitExpressions SignedExpressions

structure TernaryBridge (op : Pure 3) where
  selection : TernarySelection
  agrees : ∀ a b k : Scalar.Word, (selection.value a b k).toFin =
    op.eval (Fin.cases a.toFin (Fin.cases b.toFin (fun _ => k.toFin)))

def addmodBridge : TernaryBridge .addmod := ⟨selectAddMod,by
  intro a b k
  change (if k == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 ((a.toNat+b.toNat)%k.toNat)).toFin =
    (if k.toNat = 0 then word 0 else word ((a.toNat+b.toNat)%k.toNat))
  by_cases zero : k = 0
  · subst k
    rfl
  · have nonzero : k.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
    rw [beq_eq_false_iff_ne.mpr zero,if_neg nonzero]
    rfl⟩
def mulmodBridge : TernaryBridge .mulmod := ⟨selectMulMod,by
  intro a b k
  change (if k == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 ((a.toNat*b.toNat)%k.toNat)).toFin =
    (if k.toNat = 0 then word 0 else word ((a.toNat*b.toNat)%k.toNat))
  by_cases zero : k = 0
  · subst k
    rfl
  · have nonzero : k.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
    rw [beq_eq_false_iff_ne.mpr zero,if_neg nonzero]
    rfl⟩

private theorem ternaryProfile {fuel n : Nat} {args : Fin 3 → Expr [] [] n 1}
    (left : Compiled fuel (args 0)) (right : Compiled fuel (args 1))
    (modulus : Compiled fuel (args 2)) (i : Fin 3) : ExprWordP (args i) := by
  have indices : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases indices with equal | equal | equal
  · subst i; exact left.profile
  · subst i; exact right.profile
  · subst i; exact modulus.profile

def ternary {fuel n : Nat} {args : Fin 3 → Expr [] [] n 1} {op : Pure 3}
    (bridge : TernaryBridge op) (left : Compiled fuel (args 0))
    (right : Compiled fuel (args 1)) (modulus : Compiled fuel (args 2)) :
    Compiled (fuel+1) (.builtin (.pure op) args) where
  one := rfl
  profile := ⟨rfl,ternaryProfile left right modulus⟩
  value := fun locals => bridge.selection.value (left.value locals) (right.value locals) (modulus.value locals)
  lowered := lowerTernary bridge.selection left.lowered right.lowered modulus.lowered
  source := by
    intro locals
    rw [evalExpr_builtin fuel .nil True.intro (.pure op) (.pure op)]
    have operands : (fun i : Fin 3 =>
        (evalExpr fuel .nil True.intro (args i) (ternaryProfile left right modulus i) (sourceLocals locals)).map
          (fun result : Values 1 => result 0)) =
        (fun i => some (Fin.cases (left.value locals).toFin
          (Fin.cases (right.value locals).toFin (fun _ => (modulus.value locals).toFin)) i)) := by
      funext i
      have indices : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases indices with equal | equal | equal
      · subst i; rw [left.source]; rfl
      · subst i; rw [right.source]; rfl
      · subst i; rw [modulus.source]; rfl
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
            | add => exact ProducerExpressions.visitBinary addBridge (fun i => compile fuel (args i))
            | sub => exact ProducerExpressions.visitBinary subBridge (fun i => compile fuel (args i))
            | mul => exact ProducerExpressions.visitBinary mulBridge (fun i => compile fuel (args i))
            | «div» => exact ProducerExpressions.visitBinary QuotientExpressions.divBridge (fun i => compile fuel (args i))
            | «mod» => exact ProducerExpressions.visitBinary QuotientExpressions.modBridge (fun i => compile fuel (args i))
            | lt => exact ProducerExpressions.visitBinary ltBridge (fun i => compile fuel (args i))
            | gt => exact ProducerExpressions.visitBinary gtBridge (fun i => compile fuel (args i))
            | eq => exact ProducerExpressions.visitBinary eqBridge (fun i => compile fuel (args i))
            | iszero => exact do
                let arg ← compile fuel (args 0)
                pure (WordExpressions.unary iszeroBridge arg)
            | «not» => exact do
                let arg ← compile fuel (args 0)
                pure (WordExpressions.unary notBridge arg)
            | «and» => exact ProducerExpressions.visitBinary andBridge (fun i => compile fuel (args i))
            | «or» => exact ProducerExpressions.visitBinary orBridge (fun i => compile fuel (args i))
            | «xor» => exact ProducerExpressions.visitBinary xorBridge (fun i => compile fuel (args i))
            | «shl» => exact ProducerExpressions.visitBinary shlBridge (fun i => compile fuel (args i))
            | «shr» => exact ProducerExpressions.visitBinary shrBridge (fun i => compile fuel (args i))
            | sdiv => exact ProducerExpressions.visitBinary sdivBridge (fun i => compile fuel (args i))
            | smod => exact ProducerExpressions.visitBinary smodBridge (fun i => compile fuel (args i))
            | slt => exact ProducerExpressions.visitBinary sltBridge (fun i => compile fuel (args i))
            | sgt => exact ProducerExpressions.visitBinary sgtBridge (fun i => compile fuel (args i))
            | sar => exact ProducerExpressions.visitBinary sarBridge (fun i => compile fuel (args i))
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
            | _ => exact none
        | _ => exact none
termination_by structural fuel

/-- Single-target assignment uses the existing real statement certificate. -/
def assignment {fuel n : Nat} {c : Control} (targets : Fin 1 → Target [] n) (expr : Expr [] [] n 1) :
    Option (ProducerStatements.Compiled (fuel+1) (Stmt.assign (c := c) targets expr)) :=
  (compile fuel expr).map (ProducerStatements.assignTargets targets)

#print axioms addmodBridge
#print axioms mulmodBridge
#print axioms ternary
#print axioms compile
end Solidity.Yul.Compilation.ModularExpressions
