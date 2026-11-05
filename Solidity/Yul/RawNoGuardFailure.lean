import Solidity.Yul.RawSourceForPost

/-! Finite noncompletion of concrete omitted-guard raw loops without break.
The structural no-break test is a sufficient premise, not an admission checker
or a completeness claim. Errors and timeout frames are not classified here. -/
namespace Solidity.Yul.RawNoGuardFailure

def noBreak {ctx returns modifier u stmt}
    (body : RawLoopBody.Supported ctx returns modifier u stmt) : Bool := by
  apply RawLoopBody.Supported.casesOn (motive := fun _ _ => Bool) body
  case plain =>
    intro items inside
    exact true
  case skip => exact true
  case break_ => exact false
  case continue_ => exact true
  case ifThen =>
    intro condition stmt test inside
    exact noBreak inside
termination_by structural body

theorem run_no_break : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawLoopBody.run body fuel state).1 ≠ .ok (.break_ rfl) := by
  intro ctx returns modifier u stmt body
  induction body with
  | plain inside =>
    intro safe fuel state bad
    dsimp only [Solidity.Yul.RawLoopBody.run] at bad
    cases actual : Solidity.Yul.RawSequence.block inside fuel state with
    | mk tag next =>
      rw [actual] at bad
      cases tag <;> cases bad
  | skip =>
    intro safe fuel state
    cases fuel <;> intro bad <;> cases bad
  | break_ =>
    intro safe
    cases safe
  | continue_ =>
    intro safe fuel state
    cases fuel <;> intro bad <;> cases bad
  | ifThen test inside ih =>
    intro safe fuel state
    cases fuel with
    | zero => intro bad; cases bad
    | succ fuel =>
      rw [Solidity.Yul.RawLoopBody.run_ifThen]
      cases actual : Solidity.Yul.RawCondition.eval test fuel state with
      | mk tag next =>
        cases tag with
        | error halt => intro bad; cases bad
        | ok choice =>
          cases choice with
          | false => intro bad; cases bad
          | true => exact ih safe fuel next

theorem literal_no_false : ∀ (ctx : Solidity.Source.Ctx) (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawCondition.eval (.base (.literal true)) fuel state).1 ≠ .ok false := by
  intro ctx fuel state
  cases fuel <;> intro bad <;> cases bad

theorem run_no_ok : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSourceForPost.run (.base (.literal true)) step (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 ≠ .ok () := by
  intro ctx returns modifier u stmt body safe post step fuel
  induction fuel with
  | zero => intro state bad; cases bad
  | succ fuel ih =>
    intro state bad
    rw [Solidity.Yul.RawSourceForPost.run] at bad
    dsimp only [Solidity.Yul.RawSourceAdapter.body] at bad
    cases guardActual : Solidity.Yul.RawCondition.eval (.base (.literal true)) fuel state with
    | mk tag next =>
      rw [guardActual] at bad
      cases tag with
      | error halt => cases bad
      | ok choice =>
        cases choice with
        | false =>
          exact literal_no_false ctx fuel state (by rw [guardActual])
        | true =>
          cases bodyActual : Solidity.Yul.RawLoopBody.run body fuel next with
          | mk tag after =>
            rw [bodyActual] at bad
            cases tag with
            | error halt => cases bad
            | ok flow =>
              cases flow with
              | normal | continue_ _ =>
                dsimp only at bad
                unfold Solidity.Yul.RawSourceForPost.after at bad
                cases postActual : Solidity.Yul.RawSourceForPost.discard step fuel after with
                | mk tag finalState =>
                  rw [postActual] at bad
                  cases tag with
                  | error halt => cases bad
                  | ok value => exact ih finalState bad
              | break_ h =>
                exact run_no_break ctx returns modifier u stmt body safe fuel next (by rw [bodyActual])
              | leave_ impossible => cases impossible

theorem initialized_no_ok : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
 (initial : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (initializer : Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u initial)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSourceForPost.Initialized.run initializer (.base (.literal true)) step (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 ≠ .ok () := by
  intro ctx returns modifier u stmt body safe post step initial initializer fuel state bad
  cases fuel with
  | zero => cases bad
  | succ fuel =>
    rw [Solidity.Yul.RawSourceForPost.Initialized.run] at bad
    cases actual : initializer.run fuel state with
    | mk tag next =>
      rw [actual] at bad
      cases tag with
      | error halt => cases bad
      | ok flow =>
        cases flow with
        | normal => exact run_no_ok ctx returns modifier u stmt body safe post step fuel next bad
        | break_ _ | continue_ _ => cases bad
        | leave_ impossible => cases impossible

theorem adapter_no_normal : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
 (initial : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (initializer : Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u initial)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 ((Solidity.Yul.RawSourceForPost.Absent.adapter (Solidity.Yul.RawSourceForPost.Initialized.adapter initializer (.base (.literal true)) step (Solidity.Yul.RawSourceAdapter.body body))).run fuel state).1 ≠ .ok .normal := by
  intro ctx returns modifier u stmt body safe post step initial initializer fuel state
  change (Solidity.Yul.RawSourceForPost.Initialized.run initializer (.base (.literal true)) step
    (Solidity.Yul.RawSourceAdapter.body body) fuel state).1.map
      (fun _ => (Solidity.Yul.Closed.Flow.normal : Solidity.Yul.RawLoopBody.Flow)) ≠ .ok .normal
  intro bad
  cases actual : (Solidity.Yul.RawSourceForPost.Initialized.run initializer (.base (.literal true)) step
      (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 with
  | error halt =>
    rw [actual] at bad
    cases bad
  | ok value =>
    cases value
    exact initialized_no_ok ctx returns modifier u stmt body safe post step initial initializer fuel state actual

end Solidity.Yul.RawNoGuardFailure
