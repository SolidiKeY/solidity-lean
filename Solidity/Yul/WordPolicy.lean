import Solidity.Yul.TierPolicy
import Solidity.Yul.ClosedProfile

/-! A real tier-A check of an emitted AST with the ACTUAL empty external
context supplies the erased profile required by the closed-word interpreter.
The generalized proof states its precise no-external-members premise; the
public closed theorem discharges it concretely, not by a caller assumption.
This is not Source occurrence/namespace, flags/safety or compiler agreement. -/
namespace Solidity.Yul.Closed

theorem globals_no_members {X : List ExternalType}
    (empty : ∀ ty, Member X ty → False) : ∀ ty, Member (globals X) ty → False := by
  have hx : X = [] := by
    cases X with
    | nil => rfl
    | cons ty rest => exact False.elim (empty ty .here)
  subst X
  intro ty index
  cases index

theorem expr_policy_words {F X n r} (expression : Expr F X n r)
    (empty : ∀ ty, Member X ty → False) (policy : Policy.ExprP .A expression) :
    ExprWordP expression := by
  revert empty policy
  apply Expr.casesOn (motive := fun r expression =>
    (∀ ty, Member X ty → False) → Policy.ExprP .A expression → ExprWordP expression) expression
  case literal => intros; exact True.intro
  case «local» => intros; exact True.intro
  case external => intro ref empty policy; exact False.elim (empty ref.ty ref.index)
  case builtin =>
    intro a r builtin args empty policy
    exact ⟨(checkWordBuiltin_iff builtin).mpr ((Policy.builtin_iff .A builtin).mpr policy.1),
      fun i => expr_policy_words (args i) empty (policy.2 i)⟩
  case call =>
    intro sig function args empty policy
    exact fun i => expr_policy_words (args i) empty (policy i)
termination_by structural expression

theorem target_policy_words {X n} (target : Target X n)
    (empty : ∀ ty, Member X ty → False) : TargetWordP target := by
  cases target with
  | «local» position => exact True.intro
  | external ref => exact False.elim (empty ref.ty ref.index)

mutual
theorem stmt_policy_words {F X c n} (code : Stmt F X c n)
    (empty : ∀ ty, Member X ty → False) (policy : Policy.StmtP .A code) : StmtWordP code := by
  revert empty policy
  apply Stmt.casesOn (motive_1 := fun F X c n code =>
    (∀ ty, Member X ty → False) → Policy.StmtP .A code → StmtWordP code) code
  case skip => intros; exact True.intro
  case seq =>
    intro F X c n first rest empty policy
    exact ⟨stmt_policy_words first empty policy.1, stmt_policy_words rest empty policy.2⟩
  case assign =>
    intro F X c n r targets expression empty policy
    exact ⟨fun i => target_policy_words (targets i) empty,
      expr_policy_words expression empty policy.2⟩
  case discard =>
    intro F X c n expression empty policy
    exact expr_policy_words expression empty policy
  case let_ =>
    intro F X c n r expression body empty policy
    exact ⟨expr_policy_words expression empty policy.1, stmt_policy_words body empty policy.2⟩
  case zero =>
    intro F X c n r body empty policy
    exact stmt_policy_words body empty policy
  case if_ =>
    intro F X c n expression body empty policy
    exact ⟨expr_policy_words expression empty policy.1, stmt_policy_words body empty policy.2⟩
  case switch =>
    intro F X c n expression arms fallback empty policy
    exact ⟨expr_policy_words expression empty policy.1,
      cases_policy_words arms empty policy.2.1, stmt_policy_words fallback empty policy.2.2⟩
  case for_ =>
    intro F X c n pre condition post body empty policy
    exact ⟨stmt_policy_words pre empty policy.1, expr_policy_words condition empty policy.2.1,
      stmt_policy_words post empty policy.2.2.1, stmt_policy_words body empty policy.2.2.2⟩
  case leave => intros; exact True.intro
  case break_ => intros; exact True.intro
  case continue_ => intros; exact True.intro
  case functions =>
    intro F X c n signatures bodies rest empty policy
    exact ⟨bodies_policy_words bodies (globals_no_members empty) policy.1,
      stmt_policy_words rest empty policy.2⟩
termination_by structural code

theorem cases_policy_words {F X c n} (code : Cases F X c n)
    (empty : ∀ ty, Member X ty → False) (policy : Policy.CasesP .A code) : CasesWordP code := by
  revert empty policy
  apply Cases.casesOn (motive_2 := fun F X c n code =>
    (∀ ty, Member X ty → False) → Policy.CasesP .A code → CasesWordP code) code
  case nil => intros; exact True.intro
  case cons =>
    intro F X c n value body rest empty policy
    exact ⟨stmt_policy_words body empty policy.1, cases_policy_words rest empty policy.2⟩
termination_by structural code

theorem bodies_policy_words {F X signatures} (code : Bodies F X signatures)
    (empty : ∀ ty, Member X ty → False) (policy : Policy.BodiesP .A code) : BodiesWordP code := by
  revert empty policy
  apply Bodies.casesOn (motive_3 := fun F X signatures code =>
    (∀ ty, Member X ty → False) → Policy.BodiesP .A code → BodiesWordP code) code
  case nil => intros; exact True.intro
  case cons =>
    intro F X signature signatures body rest empty policy
    exact ⟨stmt_policy_words body empty policy.1, bodies_policy_words rest empty policy.2⟩
termination_by structural code
end

theorem checked_stmt_words {F c n} (code : Stmt F [] c n)
    (checked : Policy.checkStmt .A code = .ok ()) : StmtWordP code :=
  stmt_policy_words code (fun _ index => by cases index) ((Policy.stmt_iff .A code).mp checked)

theorem checked_bodies_words {F signatures} (code : Bodies F [] signatures)
    (checked : Policy.checkBodies .A code = .ok ()) : BodiesWordP code :=
  bodies_policy_words code (fun _ index => by cases index) ((Policy.bodies_iff .A code).mp checked)

end Solidity.Yul.Closed
