import Solidity.Yul.RawCheckedAdapter
import Solidity.Yul.RawSourceAdapterIfElse

/-! Conditional composition over actual checked executable statement producers.
Nested branches retain exact normal/break/continue/error flow and raw frames.
Source transport keeps actual producer, checked-frame and coherence premises. -/
namespace Solidity.Yul.RawCheckedAdapterIfElse

def run {ctx returns modifier u condition yes no}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawCheckedAdapter.Adapter ctx returns modifier u yes)
    (two : RawCheckedAdapter.Adapter ctx returns modifier u no)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    let first := RawCondition.eval test n state
    match first.1 with
    | .error halt => (.error halt,first.2)
    | .ok choice => if choice then one.run pipeline n first.2
      else two.run pipeline n first.2

end Solidity.Yul.RawCheckedAdapterIfElse

namespace Solidity.Yul.RawCheckedAdapterIfElse
theorem correct : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (yes no : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (one : Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u yes)
 (two : Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u no)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent
   (Solidity.Yul.RawCheckedAdapterIfElse.run test one two glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.ifElse condition yes no) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawLoopBody.represented
   (Solidity.Yul.RawCheckedAdapterIfElse.run test one two glob.pipeline fuel state) := by
  intro ctx returns modifier u condition test yes no one two glob frame checked fuel nps ph state same
  cases fuel with
  | zero => exact ⟨same,rfl⟩
  | succ fuel =>
    have conditionRun := RawCondition.source_eval test glob frame fuel state same
    cases actual : (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) with
    | mk tag next =>
      rcases next with ⟨locals,world⟩
      rw [actual] at conditionRun
      let nextFrame : RawFrame.State ctx :=
        RawCoherent.capture state (LocalState.ofClean (locals,world))
      have nextSame : RawCoherent.coherent nextFrame = true :=
        RawCoherent.capture_coherent state locals world
      have nextClean : nextFrame.clean = locals := by
        simp only [nextFrame, RawCoherent.capture, LocalState.ofClean,
          LocalValues.clean_ofClean, Option.getD_some]
      cases tag with
      | error halt =>
        change RawCondition.eval test fuel state = (.error halt,nextFrame) at conditionRun
        simp only [run, conditionRun]
        exact ⟨nextSame, RawSourceAdapterIfElse.source_error condition yes no glob frame fuel nps ph state locals world halt actual⟩
      | ok value =>
        cases value with
        | val value =>
          cases value with
          | bool choice =>
            cases choice with
            | false =>
              change RawCondition.eval test fuel state = (.ok false,nextFrame) at conditionRun
              have branch := two.correct glob frame checked fuel nps ph nextFrame nextSame
              have sourceCondition :
                  (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                    (.ok (.val (.bool false)),(nextFrame.clean,nextFrame.world)) := by
                rw [nextClean]
                exact actual
              have selected := RawSourceAdapterIfElse.source_selected condition yes no glob frame fuel nps ph
                state nextFrame false (two.run glob.pipeline fuel nextFrame) sourceCondition branch.2
              simp only [run, conditionRun, Bool.false_eq_true, if_false]
              exact ⟨branch.1,selected⟩
            | true =>
              change RawCondition.eval test fuel state = (.ok true,nextFrame) at conditionRun
              have branch := one.correct glob frame checked fuel nps ph nextFrame nextSame
              have sourceCondition :
                  (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                    (.ok (.val (.bool true)),(nextFrame.clean,nextFrame.world)) := by
                rw [nextClean]
                exact actual
              have selected := RawSourceAdapterIfElse.source_selected condition yes no glob frame fuel nps ph
                state nextFrame true (one.run glob.pipeline fuel nextFrame) sourceCondition branch.2
              simp only [run, conditionRun, if_true]
              exact ⟨branch.1,selected⟩
          | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible



def adapter {ctx returns modifier u condition yes no}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawCheckedAdapter.Adapter ctx returns modifier u yes)
    (two : RawCheckedAdapter.Adapter ctx returns modifier u no) :
    RawCheckedAdapter.Adapter ctx returns modifier u (.ifElse condition yes no) where
  run := run test one two
  correct := correct ctx returns modifier u condition test yes no one two

end Solidity.Yul.RawCheckedAdapterIfElse
