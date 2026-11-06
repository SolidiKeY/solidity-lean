import Solidity.Yul.RawBoolFailure
import Solidity.Yul.RawNoPostFailure
import Solidity.Yul.RawSourceAdapterDoWhile

/-! Error classification for actual Boolean-certificate loop drivers with the
concrete body factory. Omitted true guards plus noBreak yield finite timeout tags.
No arbitrary Adapter, initialized-loop, general Yul or dirty Source claim.
The runners and their reached frames are unchanged. -/
namespace Solidity.Yul.RawLoopFailure

theorem while_error : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx) (halt : Solidity.Source.Halt),
 (Solidity.Yul.RawControlledWhile.run test body fuel state).1 = .error halt → halt = .timeout := by
  intro ctx returns modifier u condition test stmt body fuel
  induction fuel with
  | zero => intro state halt failed; cases failed; rfl
  | succ fuel ih =>
    intro state halt failed
    rw [Solidity.Yul.RawControlledWhile.run] at failed
    cases guardActual : Solidity.Yul.RawCondition.eval test fuel state with
    | mk tag next =>
      rw [guardActual] at failed
      cases tag with
      | error error =>
        have same := Solidity.Yul.RawBoolFailure.condition ctx condition test fuel state error (congrArg Prod.fst guardActual)
        cases failed
        exact same
      | ok choice =>
        cases choice with
        | false => cases failed
        | true =>
          cases bodyActual : Solidity.Yul.RawLoopBody.run body fuel next with
          | mk tag after =>
            rw [bodyActual] at failed
            cases tag with
            | error error =>
              have same := Solidity.Yul.RawBoolFailure.body ctx returns modifier u stmt body fuel next error (congrArg Prod.fst bodyActual)
              cases failed
              exact same
            | ok flow =>
              cases flow with
              | normal | continue_ _ => exact ih after halt failed
              | break_ _ => cases failed
              | leave_ impossible => cases impossible

theorem do_while_error : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx) (halt : Solidity.Source.Halt),
 (Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 = .error halt → halt = .timeout := by
  intro ctx returns modifier u condition test stmt body fuel
  induction fuel with
  | zero => intro state halt failed; cases failed; rfl
  | succ fuel ih =>
    intro state halt failed
    rw [Solidity.Yul.RawSourceAdapterDoWhile.run] at failed
    dsimp only [Solidity.Yul.RawSourceAdapter.body] at failed
    cases bodyActual : Solidity.Yul.RawLoopBody.run body fuel state with
    | mk tag after =>
      rw [bodyActual] at failed
      cases tag with
      | error error =>
        have same := Solidity.Yul.RawBoolFailure.body ctx returns modifier u stmt body fuel state error (congrArg Prod.fst bodyActual)
        cases failed
        exact same
      | ok flow =>
        cases flow with
        | normal | continue_ _ =>
          dsimp only at failed
          unfold Solidity.Yul.RawSourceAdapterDoWhile.after at failed
          cases guardActual : Solidity.Yul.RawCondition.eval test fuel after with
          | mk tag next =>
            rw [guardActual] at failed
            cases tag with
            | error error =>
              have same := Solidity.Yul.RawBoolFailure.condition ctx condition test fuel after error (congrArg Prod.fst guardActual)
              cases failed
              exact same
            | ok choice =>
              cases choice with
              | false => cases failed
              | true => exact ih next halt failed
        | break_ _ => cases failed
        | leave_ impossible => cases impossible

theorem discard_error : ∀ (ctx : Solidity.Source.Ctx)
 (post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx) (halt : Solidity.Source.Halt),
 (Solidity.Yul.RawSourceForPost.discard step fuel state).1 = .error halt → halt = .timeout := by
  intro ctx post step fuel state halt failed
  exact Solidity.Yul.RawBoolFailure.statement ctx [] false Solidity.Source.SCtx.body
    (.expr post) (.expression step) (fuel+1) state halt failed

theorem post_error : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx) (halt : Solidity.Source.Halt),
 (Solidity.Yul.RawSourceForPost.run test step (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 = .error halt → halt = .timeout := by
  intro ctx returns modifier u condition test stmt body post step fuel
  induction fuel with
  | zero => intro state halt failed; cases failed; rfl
  | succ fuel ih =>
    intro state halt failed
    rw [Solidity.Yul.RawSourceForPost.run] at failed
    dsimp only [Solidity.Yul.RawSourceAdapter.body] at failed
    cases guardActual : Solidity.Yul.RawCondition.eval test fuel state with
    | mk tag next =>
      rw [guardActual] at failed
      cases tag with
      | error error =>
        have same := Solidity.Yul.RawBoolFailure.condition ctx condition test fuel state error (congrArg Prod.fst guardActual)
        cases failed
        exact same
      | ok choice =>
        cases choice with
        | false => cases failed
        | true =>
          cases bodyActual : Solidity.Yul.RawLoopBody.run body fuel next with
          | mk tag after =>
            rw [bodyActual] at failed
            cases tag with
            | error error =>
              have same := Solidity.Yul.RawBoolFailure.body ctx returns modifier u stmt body fuel next error (congrArg Prod.fst bodyActual)
              cases failed
              exact same
            | ok flow =>
              cases flow with
              | normal | continue_ _ =>
                dsimp only at failed
                unfold Solidity.Yul.RawSourceForPost.after at failed
                cases postActual : Solidity.Yul.RawSourceForPost.discard step fuel after with
                | mk tag next =>
                  rw [postActual] at failed
                  cases tag with
                  | error error =>
                    have same := discard_error ctx post step fuel after error (congrArg Prod.fst postActual)
                    cases failed
                    exact same
                  | ok value => exact ih next halt failed
              | break_ _ => cases failed
              | leave_ impossible => cases impossible

theorem no_post_timeout : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawControlledWhile.run (.base (.literal true)) body fuel state).1 = .error .timeout := by
  intro ctx returns modifier u stmt body safe fuel state
  cases actual : Solidity.Yul.RawControlledWhile.run (.base (.literal true)) body fuel state with
  | mk tag next =>
    cases tag with
    | error halt =>
      have same := while_error ctx returns modifier u (.bool true) (.base (.literal true))
        stmt body fuel state halt (congrArg Prod.fst actual)
      rw [same]
    | ok value =>
      cases value
      exact False.elim (Solidity.Yul.RawNoPostFailure.loop_no_ok ctx returns modifier u stmt body safe fuel state (by rw [actual]))

theorem post_timeout : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSourceForPost.run (.base (.literal true)) step (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 = .error .timeout := by
  intro ctx returns modifier u stmt body safe post step fuel state
  cases actual : Solidity.Yul.RawSourceForPost.run (.base (.literal true)) step
      (Solidity.Yul.RawSourceAdapter.body body) fuel state with
  | mk tag next =>
    cases tag with
    | error halt =>
      have same := post_error ctx returns modifier u (.bool true) (.base (.literal true))
        stmt body post step fuel state halt (congrArg Prod.fst actual)
      rw [same]
    | ok value =>
      cases value
      exact False.elim (Solidity.Yul.RawNoGuardFailure.run_no_ok ctx returns modifier u stmt body safe post step fuel state (by rw [actual]))

end Solidity.Yul.RawLoopFailure
