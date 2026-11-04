import Solidity.Yul.RawSourceForPost
import Solidity.Yul.RawLoopBodyHorizon

/-! Actual for-iteration post steps preserve completed entire raw frames.
Concrete body certificates are required; clean Source correctness is separate.
No raw stability for arbitrary adapters is assumed. -/
namespace Solidity.Yul.RawForPostHorizon

theorem discardSuccessor : ∀ (ctx : Solidity.Source.Ctx)
 (post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSourceForPost.discard step fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawSourceForPost.discard step (fuel+1) state =
 Solidity.Yul.RawSourceForPost.discard step fuel state := by
  intro ctx post step fuel state terminal
  exact Solidity.Yul.RawStatementHorizon.coherentSuccessor ctx [] false Solidity.Source.SCtx.body
    (.expr post) (.expression step) (fuel+1) state terminal

theorem successor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSourceForPost.run test step (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawSourceForPost.run test step (Solidity.Yul.RawSourceAdapter.body body) (fuel+1) state = Solidity.Yul.RawSourceForPost.run test step (Solidity.Yul.RawSourceAdapter.body body) fuel state := by
  intro ctx returns modifier u condition test post step stmt body fuel
  induction fuel with
  | zero => intro state terminal; exact False.elim (terminal rfl)
  | succ fuel ih =>
    intro state terminal
    have tail : ∀ next : Solidity.Yul.RawFrame.State ctx,
        (Solidity.Yul.RawSourceForPost.after step
          (Solidity.Yul.RawSourceForPost.run test step (Solidity.Yul.RawSourceAdapter.body body) fuel) fuel next).1 ≠ .error .timeout →
        Solidity.Yul.RawSourceForPost.after step
          (Solidity.Yul.RawSourceForPost.run test step (Solidity.Yul.RawSourceAdapter.body body) (fuel+1)) (fuel+1) next =
        Solidity.Yul.RawSourceForPost.after step
          (Solidity.Yul.RawSourceForPost.run test step (Solidity.Yul.RawSourceAdapter.body body) fuel) fuel next := by
      intro next ready
      have postReady : (Solidity.Yul.RawSourceForPost.discard step fuel next).1 ≠ .error .timeout := by
        intro bad
        apply ready
        simp only [Solidity.Yul.RawSourceForPost.after,bad]
      have same := discardSuccessor ctx post step fuel next postReady
      unfold Solidity.Yul.RawSourceForPost.after
      rw [same]
      cases actual : Solidity.Yul.RawSourceForPost.discard step fuel next with
      | mk tag after =>
        cases tag with
        | error halt => rfl
        | ok value =>
          apply ih after
          simp only [Solidity.Yul.RawSourceForPost.after,actual] at ready
          exact ready
    have conditionReady : (Solidity.Yul.RawCondition.eval test fuel state).1 ≠ .error .timeout := by
      intro bad
      apply terminal
      rw [Solidity.Yul.RawSourceForPost.run]
      dsimp only
      rw [bad]
    have conditionSame := Solidity.Yul.RawLoopBodyHorizon.conditionSuccessor ctx condition test fuel state conditionReady
    conv => lhs; rw [Solidity.Yul.RawSourceForPost.run]
    conv => rhs; rw [Solidity.Yul.RawSourceForPost.run]
    rw [conditionSame]
    cases actual : Solidity.Yul.RawCondition.eval test fuel state with
    | mk result next =>
      cases result with
      | error halt => rfl
      | ok choice =>
        cases choice with
        | false => rfl
        | true =>
          have bodyReady : (Solidity.Yul.RawLoopBody.run body fuel next).1 ≠ .error .timeout := by
            intro bad
            apply terminal
            rw [Solidity.Yul.RawSourceForPost.run,actual]
            dsimp only [Solidity.Yul.RawSourceAdapter.body]
            rw [bad]
            rfl
          have bodySame := Solidity.Yul.RawLoopBodyHorizon.successor ctx returns modifier u stmt body fuel next bodyReady
          dsimp only [Solidity.Yul.RawSourceAdapter.body]
          rw [bodySame]
          cases bodyActual : Solidity.Yul.RawLoopBody.run body fuel next with
          | mk tag after =>
            cases tag with
            | error halt => rfl
            | ok flow =>
              cases flow with
              | normal | continue_ _ =>
                apply tail after
                rw [Solidity.Yul.RawSourceForPost.run,actual] at terminal
                dsimp only [Solidity.Yul.RawSourceAdapter.body] at terminal
                rw [bodyActual] at terminal
                exact terminal
              | break_ _ => rfl
              | leave_ impossible => cases impossible

theorem extension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSourceForPost.run test step (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawSourceForPost.run test step (Solidity.Yul.RawSourceAdapter.body body) (fuel+extra) state = Solidity.Yul.RawSourceForPost.run test step (Solidity.Yul.RawSourceAdapter.body body) fuel state := by
  intro ctx returns modifier u condition test post step stmt body fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : (Solidity.Yul.RawSourceForPost.run test step (Solidity.Yul.RawSourceAdapter.body body) (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (successor ctx returns modifier u condition test post step stmt body (fuel+extra) state ready).trans ih

end Solidity.Yul.RawForPostHorizon
