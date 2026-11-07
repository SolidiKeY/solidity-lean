import Solidity.Yul.RawCheckedAdapter
import Solidity.Yul.RawSourceForPost

/-! Checked same-context Source for iterations with a present boolean post.
Reuses the existing post evaluator and exact Source horizon; this does not
supply initialized/context-growing for-loop admission. -/
namespace Solidity.Yul.RawCheckedForPost

def run {ctx returns modifier u condition post body}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (step : LocalBoolControl.Supported ctx.env ctx.tys post)
    (inside : RawCheckedAdapter.Adapter ctx returns modifier u body)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) : Solidity.Source.R Unit × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    let guard := RawCondition.eval test n state
    match guard.1 with
    | .error halt => (.error halt,guard.2)
    | .ok choice => if choice then
      let branch := inside.run pipeline n guard.2
      match branch.1 with
      | .error halt => (.error halt,branch.2)
      | .ok flow => match flow with
        | .normal | .continue_ _ => RawSourceForPost.after step (run test step inside pipeline n) n branch.2
        | .break_ _ => (.ok (),branch.2)
        | .leave_ impossible => nomatch impossible
      else (.ok (),guard.2)

end Solidity.Yul.RawCheckedForPost

namespace Solidity.Yul.RawCheckedForPost
theorem correct : ∀ {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier u : Bool}
  {condition post : Solidity.Source.RExpr ctx.env ctx.tys .bool}
  {body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys}
  (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
  (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
  (inside : Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u body)
  (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
  (checked : frame.checked = true) (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
  (state : Solidity.Yul.RawFrame.State ctx) (_same : Solidity.Yul.RawCoherent.coherent state = true),
  Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedForPost.run test step inside glob.pipeline fuel state).2 = true ∧
    (Solidity.Source.forIter glob frame fuel nps ph (.some condition) (.some post) body state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) =
        Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedForPost.run test step inside glob.pipeline fuel state) := by
  intro ctx returns modifier u condition post body test step inside glob frame checked fuel nps ph state same
  induction fuel generalizing state with
  | zero => exact ⟨same,rfl⟩
  | succ fuel ih =>
    have conditionRun := Solidity.Yul.RawCondition.source_eval test glob frame fuel state same
    cases actual : (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) with
    | mk tag next =>
      rcases next with ⟨locals,world⟩
      rw [actual] at conditionRun
      let nextFrame : Solidity.Yul.RawFrame.State ctx :=
        Solidity.Yul.RawCoherent.capture state (Solidity.Yul.LocalState.ofClean (locals,world))
      have nextSame : Solidity.Yul.RawCoherent.coherent nextFrame = true :=
        Solidity.Yul.RawCoherent.capture_coherent state locals world
      have nextClean : nextFrame.clean = locals := by
        simp only [nextFrame,Solidity.Yul.RawCoherent.capture,Solidity.Yul.LocalState.ofClean,
          Solidity.Yul.LocalValues.clean_ofClean,Option.getD_some]
      cases tag with
      | error halt =>
        change Solidity.Yul.RawCondition.eval test fuel state = (.error halt,nextFrame) at conditionRun
        have sourceCondition :
            (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
              (.error halt,(nextFrame.clean,nextFrame.world)) := by
          rw [nextClean]
          exact actual
        simp only [Solidity.Yul.RawCheckedForPost.run,conditionRun]
        exact ⟨nextSame,Solidity.Yul.RawSourceForPost.source_error condition post body
          glob frame fuel nps ph state nextFrame halt sourceCondition⟩
      | ok value =>
        cases value with
        | val value =>
          cases value with
          | bool choice =>
            have branch := inside.correct glob frame checked fuel nps ph nextFrame nextSame
            have sourceCondition :
                (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                  (.ok (.val (.bool choice)),(nextFrame.clean,nextFrame.world)) := by
              rw [nextClean]
              exact actual
            have selected := Solidity.Yul.RawSourceForPost.source_choice condition post body
              glob frame fuel nps ph state nextFrame choice (inside.run glob.pipeline fuel nextFrame) sourceCondition branch.2
            cases choice with
            | false =>
              change Solidity.Yul.RawCondition.eval test fuel state = (.ok false,nextFrame) at conditionRun
              simp only [Solidity.Yul.RawCheckedForPost.run,conditionRun,Bool.false_eq_true,if_false]
              exact ⟨nextSame,selected⟩
            | true =>
              change Solidity.Yul.RawCondition.eval test fuel state = (.ok true,nextFrame) at conditionRun
              simp only [Solidity.Yul.RawCheckedForPost.run,conditionRun,if_true]
              rw [selected]
              cases bodyTag : (inside.run glob.pipeline fuel nextFrame).1 with
              | error halt => exact ⟨branch.1,rfl⟩
              | ok flow =>
                cases flow with
                | normal =>
                  exact Solidity.Yul.RawSourceForPost.after_correct condition post body step
                    (Solidity.Yul.RawCheckedForPost.run test step inside glob.pipeline fuel)
                    glob frame fuel nps ph ih (inside.run glob.pipeline fuel nextFrame).2 branch.1
                | continue_ h =>
                  exact Solidity.Yul.RawSourceForPost.after_correct condition post body step
                    (Solidity.Yul.RawCheckedForPost.run test step inside glob.pipeline fuel)
                    glob frame fuel nps ph ih (inside.run glob.pipeline fuel nextFrame).2 branch.1
                | break_ h => exact ⟨branch.1,rfl⟩
                | leave_ h => cases h
          | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible

end Solidity.Yul.RawCheckedForPost
