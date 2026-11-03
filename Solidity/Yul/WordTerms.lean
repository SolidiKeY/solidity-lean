import Solidity.Yul.WordNotation

/-! Expression modalities and concrete arbitrary-RHS assignment/discard
composition against the actual closed evaluator. No completion assumption,
no inlining oracle and no conversion of a horizon timeout to divergence. -/
namespace Solidity.Yul.Logic
open Solidity.Yul.Closed
open Solidity (Modality)

def Program.assignment {F c n r} (targets : Fin r → Target [] n) (term : Term F n r) :
    Program F c n := ⟨.assign targets term.code,⟨fun i => targetWordP_closed (targets i),term.words⟩⟩

def Program.discard {F c n} (term : Term F n 0) : Program F c n :=
  ⟨.discard term.code,term.words⟩

def assignmentPost {c n r} (targets : Fin r → Target [] n)
    (post : Flow c → Fml n) (values : Values r) : Fml n :=
  .subst (writeValues r targets values) (post .normal)

theorem eval_assignment (fuel : Nat) {F c n r} (model : Model F)
    (targets : Fin r → Target [] n) (term : Term F n r) (vars : Values n) :
    evalStmt (fuel+1) model.environment model.words
      (Program.assignment (c := c) targets term).code
      (Program.assignment (c := c) targets term).words vars =
    (do let values ← evalExpr fuel model.environment model.words term.code term.words vars
        pure ⟨writeValues r targets values vars,.normal⟩) := rfl

theorem term_completed {F n r fuel} (mode : Modality) (model : Model F)
    (term : Term F n r) (post : Values r → Fml n) (vars : Values n) (values : Values r)
    (completed : evalExpr fuel model.environment model.words term.code term.words vars = some values) :
    (Fml.termModal mode model term post).holds vars ↔ (post values).holds vars := by
  cases mode with
  | box =>
    constructor
    · intro all; exact all fuel values completed
    · intro after other actual ran
      have same := evalExpr_completed_unique model.environment model.words term.code
        term.words vars completed ran
      cases same
      exact after
  | diamond =>
    constructor
    · rintro ⟨other,actual,ran,after⟩
      have same := evalExpr_completed_unique model.environment model.words term.code
        term.words vars completed ran
      cases same
      exact after
    · intro after; exact ⟨fuel,values,completed,after⟩

theorem modal_assignment {F c n r} (mode : Modality) (model : Model F)
    (targets : Fin r → Target [] n) (term : Term F n r)
    (post : Flow c → Fml n) (vars : Values n) :
    (Fml.modal mode model (Program.assignment targets term) post).holds vars ↔
      (Fml.termModal mode model term (assignmentPost targets post)).holds vars := by
  cases mode with
  | box =>
    constructor
    · intro all fuel values ran
      exact all (fuel+1) ⟨writeValues r targets values vars,.normal⟩
        (by rw [eval_assignment,ran]; rfl)
    · intro all fuel result ran
      cases fuel with
      | zero => cases ran
      | succ fuel =>
        rw [eval_assignment] at ran
        cases exprRan : evalExpr fuel model.environment model.words term.code term.words vars with
        | none => rw [exprRan] at ran; cases ran
        | some values =>
          rw [exprRan] at ran
          cases ran
          exact all fuel values exprRan
  | diamond =>
    constructor
    · rintro ⟨fuel,result,ran,after⟩
      cases fuel with
      | zero => cases ran
      | succ fuel =>
        rw [eval_assignment] at ran
        cases exprRan : evalExpr fuel model.environment model.words term.code term.words vars with
        | none => rw [exprRan] at ran; cases ran
        | some values =>
          rw [exprRan] at ran
          cases ran
          exact ⟨fuel,values,exprRan,after⟩
    · rintro ⟨fuel,values,ran,after⟩
      exact ⟨fuel+1,⟨writeValues r targets values vars,.normal⟩,
        (by rw [eval_assignment,ran]; rfl),after⟩

theorem eval_discard_program (fuel : Nat) {F c n} (model : Model F)
    (term : Term F n 0) (vars : Values n) :
    evalStmt (fuel+1) model.environment model.words
      (Program.discard (c := c) term).code (Program.discard (c := c) term).words vars =
    (do let _ ← evalExpr fuel model.environment model.words term.code term.words vars
        pure ⟨vars,.normal⟩) := rfl

theorem modal_discard {F c n} (mode : Modality) (model : Model F)
    (term : Term F n 0) (post : Flow c → Fml n) (vars : Values n) :
    (Fml.modal mode model (Program.discard term) post).holds vars ↔
      (Fml.termModal mode model term (fun _ => post .normal)).holds vars := by
  cases mode with
  | box =>
    constructor
    · intro all fuel values ran
      exact all (fuel+1) ⟨vars,.normal⟩
        (by rw [eval_discard_program,ran]; rfl)
    · intro all fuel result ran
      cases fuel with
      | zero => cases ran
      | succ fuel =>
        rw [eval_discard_program] at ran
        cases exprRan : evalExpr fuel model.environment model.words term.code term.words vars with
        | none => rw [exprRan] at ran; cases ran
        | some values =>
          rw [exprRan] at ran
          cases ran
          exact all fuel values exprRan
  | diamond =>
    constructor
    · rintro ⟨fuel,result,ran,after⟩
      cases fuel with
      | zero => cases ran
      | succ fuel =>
        rw [eval_discard_program] at ran
        cases exprRan : evalExpr fuel model.environment model.words term.code term.words vars with
        | none => rw [exprRan] at ran; cases ran
        | some values =>
          rw [exprRan] at ran
          cases ran
          exact ⟨fuel,values,exprRan,after⟩
    · rintro ⟨fuel,values,ran,after⟩
      exact ⟨fuel+1,⟨vars,.normal⟩,
        (by rw [eval_discard_program,ran]; rfl),after⟩

end Solidity.Yul.Logic
