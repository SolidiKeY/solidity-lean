import Solidity.Yul.Compilation.PureStatements
import Solidity.Yul.Compilation.WordControl
/-! Recursive normally completing control lowering over the ORIGINAL VY1 Stmt.
Derivation is indexed compiler evidence, not a second AST/evaluator/state.
Fuel follows original source horizons; admission, native layout, charged bounds,
physical/source-session/G24 and early control remain separate obligations. -/
namespace Solidity.Yul.Compilation.NormalControl
open Backend Scalar Solidity.Yul.Closed ProducerExpressions

inductive Derivation {c : Control} {n : Nat} : Nat → Stmt [] [] c n → Type where
  | scalar {fuel : Nat} {stmt : Stmt [] [] c n}
      (compiled : ProducerStatements.Compiled fuel stmt) : Derivation fuel stmt
  | seq {fuel : Nat} {a b : Stmt [] [] c n}
      (first : Derivation fuel a) (second : Derivation fuel b) :
      Derivation (fuel+1) (.seq a b)
  | branch {fuel : Nat} {test : Expr [] [] n 1} {body : Stmt [] [] c n}
      (condition : ProducerExpressions.Compiled fuel test) (arm : Derivation fuel body) :
      Derivation (fuel+1) (.if_ test body)

def Derivation.profile {c n fuel} {stmt : Stmt [] [] c n}
    (compiled : Derivation fuel stmt) : StmtWordP stmt := by
  apply Derivation.casesOn (motive := fun _ stmt _ => StmtWordP stmt) compiled
  case scalar => intro fuel stmt leaf; exact leaf.profile
  case seq => intro fuel a b first second; exact ⟨first.profile,second.profile⟩
  case branch => intro fuel test body condition arm; exact ⟨condition.profile,arm.profile⟩
termination_by structural compiled

def Derivation.update {c n fuel} {stmt : Stmt [] [] c n}
    (compiled : Derivation fuel stmt) (locals : Vector Scalar.Word n) : Vector Scalar.Word n := by
  apply Derivation.casesOn (motive := fun _ _ _ => Vector Scalar.Word n) compiled
  case scalar => intro fuel stmt leaf; exact leaf.update locals
  case seq => intro fuel a b first second; exact second.update (first.update locals)
  case branch => intro fuel test body condition arm
                 exact if condition.value locals = 0 then locals else arm.update locals
termination_by structural compiled

def Derivation.emit {c n fuel} {stmt : Stmt [] [] c n}
    (compiled : Derivation fuel stmt) (depth : Nat) : Option Backend.Block := by
  apply Derivation.casesOn (motive := fun _ _ _ => Option Backend.Block) compiled
  case scalar => intro fuel stmt leaf; exact (leaf.lowered.code depth).map Backend.Block.code
  case seq =>
    intro fuel a b first second
    exact do
      let a ← first.emit depth
      let b ← second.emit depth
      pure (.seq a b)
  case branch =>
    intro fuel test body condition arm
    exact do
      let test ← condition.lowered.code depth
      let body ← arm.emit depth
      pure (.ite test body (.code []))
termination_by structural compiled

/-- Concrete visitor: sequence and if recurse into the SAME original AST;
all other implemented straight-line forms reuse their existing certificates. -/
def compile {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) :
    Option (Derivation fuel stmt) :=
  match fuel with
  | 0 => none
  | fuel+1 => by
      apply Stmt.casesOn (motive_1 := fun F X c n stmt =>
        match F,X with
        | [],[] => Option (Derivation (fuel+1) stmt)
        | _,_ => Unit) stmt
      case seq =>
        intro F X c n a b
        cases F <;> cases X
        · exact do
            let first ← compile fuel a
            let second ← compile fuel b
            pure (.seq first second)
        all_goals exact ()
      case if_ =>
        intro F X c n test body
        cases F <;> cases X
        · exact do
            let condition ← PureExpressions.compile fuel test
            let arm ← compile fuel body
            pure (.branch condition arm)
        all_goals exact ()
      all_goals intro F X; cases F <;> cases X <;> intros <;>
        first | exact (PureStatements.compile (fuel+1) _).map Derivation.scalar | exact ()
termination_by structural fuel

/-- Actual source evaluation for arbitrary nested normal branches/sequences.
The child horizons, condition values and caller locals are the original ones. -/
theorem Derivation.source {c n fuel} {stmt : Stmt [] [] c n}
    (compiled : Derivation fuel stmt) (locals : Vector Scalar.Word n) :
    evalStmt fuel .nil True.intro stmt compiled.profile (sourceLocals locals) =
      some ⟨sourceLocals (compiled.update locals),.normal⟩ := by
  induction compiled generalizing locals with
  | scalar leaf => exact leaf.source locals
  | seq first second ihFirst ihSecond =>
    change (do
      let result ← evalStmt _ .nil True.intro _ first.profile (sourceLocals locals)
      match result.flow with
      | .normal => evalStmt _ .nil True.intro _ second.profile result.vars
      | _ => pure result) = _
    rw [ihFirst]
    exact ihSecond (first.update locals)
  | branch condition arm ih =>
    change (do
      let result ← evalExpr _ .nil True.intro _ condition.profile (sourceLocals locals)
      if (result 0).val = 0 then pure (⟨sourceLocals locals,.normal⟩ : Outcome _ _)
      else evalStmt _ .nil True.intro _ arm.profile (sourceLocals locals)) = _
    rw [condition.source]
    change (if (condition.value locals).toNat = 0 then _ else _) = _
    have truth : (condition.value locals).toNat = 0 ↔ condition.value locals = 0 :=
      ⟨fun h => BitVec.eq_of_toNat_eq h,fun h => congrArg BitVec.toNat h⟩
    change _ = some (⟨sourceLocals (if condition.value locals = 0 then locals else arm.update locals),.normal⟩ : Outcome c n)
    by_cases zero : condition.value locals = 0
    · rw [if_pos (truth.mpr zero)]
      simp only [if_pos zero]
      rfl
    · rw [if_neg (fun h => zero (truth.mp h)),ih]
      simp only [if_neg zero]

#print axioms Derivation.source
#print axioms compile
end Solidity.Yul.Compilation.NormalControl
