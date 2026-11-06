import Solidity.Yul.WordAdapter

/-! Direct tier-A expression execution on the original intrinsic AST, with
actual raw external cells and declared constants. The empty function context
makes calls uninhabited; this module does not model function/statement execution.
Builtin arithmetic and right-to-left operand collection reuse the word model,
but no expression is lowered or executed by Closed.evalExpr here. -/
namespace Solidity.Yul.DirectWords
open Closed

def read {X} (operand : WordRead X) (cells : WordCells X) : Word :=
  match operand with
  | .cell cell => cells cell
  | .literal value => value

def eval (fuel : Nat) {X n r} (code : Expr [] X n r) :
    Policy.ExprP .A code → WordState X n → Option (Values r) :=
  match fuel with
  | 0 => fun _ _ => none
  | k + 1 => by
    apply Expr.casesOn (motive := fun r code =>
      Policy.ExprP .A code → WordState X n → Option (Values r)) code
    case literal =>
      intro value
      exact fun _ _ => some (fun _ => value)
    case «local» =>
      intro index
      exact fun _ state => some (fun _ => state.locals index)
    case external =>
      intro ref
      exact fun policy state => some (fun _ => read (ref.wordRead policy) state.cells)
    case builtin =>
      intro a r builtin args
      exact fun policy state => do
        let inputs ← collectValues a (fun i =>
          (eval k (args i) (policy.2 i) state).map (fun values => values 0))
        match found : checkWordBuiltin builtin with
        | some operation => pure (operation.eval inputs)
        | none => False.elim (by
            have supported := (checkWordBuiltin_iff builtin).mpr
              ((Policy.builtin_iff .A builtin).mpr policy.1)
            rw [found] at supported
            cases supported)
    case call =>
      intro sig function args
      exact PEmpty.elim (peelMember function)
termination_by structural fuel

theorem zero {X n r} (code : Expr [] X n r) (policy : Policy.ExprP .A code)
    (state : WordState X n) : eval 0 code policy state = none := rfl

/-- Coordinate assumptions state exactly what the arbitrary packed valuation
must represent. The concrete WordState.pack corollary discharges both. -/
theorem agrees (fuel : Nat) {X n r} (code : Expr [] X n r)
    (policy : Policy.ExprP .A code) (state : WordState X n)
    {m : Nat} (locals : Fin n → Fin m) (cells : WordCell X → Fin m)
    (values : Values m)
    (local_eq : ∀ i, values (locals i) = state.locals i)
    (cell_eq : ∀ cell, values (cells cell) = state.cells cell) :
    eval fuel code policy state =
      evalExpr fuel .nil True.intro
        (WordAdapter.expression code policy locals cells).code
        (WordAdapter.expression code policy locals cells).words values := by
  induction fuel generalizing n r m with
  | zero => rfl
  | succ fuel ih =>
    cases code with
    | literal value => rfl
    | «local» index =>
      change some (fun _ => state.locals index) = some (fun _ => values (locals index))
      rw [local_eq]
    | external ref =>
      change some (fun _ => read (ref.wordRead policy) state.cells) =
        evalExpr (fuel+1) .nil True.intro
          ((ref.wordRead policy).expression cells) (WordAdapter.operand_words _ cells) values
      generalize operand_eq : ref.wordRead policy = operand
      cases operand with
      | cell cell =>
        change some (fun _ => state.cells cell) = some (fun _ => values (cells cell))
        rw [cell_eq]
      | literal value => rfl
    | @builtin a r builtin args =>
      rw [eval,WordAdapter.expression,evalExpr]
      simp only [WordAdapter.tabulate_eq]
      have operands : (fun i : Fin a =>
          (eval fuel (args i) (policy.2 i) state).map (fun result : Values 1 => result 0)) =
        (fun i : Fin a =>
          (evalExpr fuel .nil True.intro
            (WordAdapter.expression (args i) (policy.2 i) locals cells).code
            (WordAdapter.expression (args i) (policy.2 i) locals cells).words
            values).map (fun result : Values 1 => result 0)) := by
        funext i
        rw [ih (args i) (policy.2 i) state locals cells values local_eq cell_eq]
      rw [operands]
      rfl
    | call function args => exact PEmpty.elim (peelMember function)

theorem packed_agrees (fuel : Nat) {X n r} (code : Expr [] X n r)
    (policy : Policy.ExprP .A code) (state : WordState X n) :
    eval fuel code policy state =
      evalExpr fuel .nil True.intro
        (WordAdapter.expression code policy (Fin.castAdd (wordCellCount X))
          (fun cell => Fin.natAdd n cell.slot)).code
        (WordAdapter.expression code policy (Fin.castAdd (wordCellCount X))
          (fun cell => Fin.natAdd n cell.slot)).words state.pack :=
  agrees fuel code policy state _ _ state.pack state.pack_local state.pack_cell


theorem stable {lo hi : Nat} (bound : lo ≤ hi) {X n r}
    (code : Expr [] X n r) (policy : Policy.ExprP .A code) (state : WordState X n)
    {result : Values r} (done : eval lo code policy state = some result) :
    eval hi code policy state = some result := by
  rw [packed_agrees] at done ⊢
  exact evalExpr_stable bound .nil True.intro _ _ state.pack done

theorem evidence_independent {X n r} (code : Expr [] X n r)
    (one two : Policy.ExprP .A code) (fuel : Nat) (state : WordState X n) :
    eval fuel code one state = eval fuel code two state := rfl

end Solidity.Yul.DirectWords
