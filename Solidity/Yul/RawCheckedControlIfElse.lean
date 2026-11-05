import Solidity.Yul.RawCheckedControlSequence
import Solidity.Yul.RawSourceAdapterIfElse

/-! Mixed checked-word conditional blocks preserve selected normal/break/continue
flow and partial raw frames. Source transport keeps checked/coherent premises. -/
namespace Solidity.Yul.RawCheckedControlIfElse

def run {ctx returns modifier u condition yes no}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawCheckedControlSequence.Supported ctx returns modifier u yes)
    (two : RawCheckedControlSequence.Supported ctx returns modifier u no)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    let first := RawCondition.eval test n state
    match first.1 with
    | .error halt => (.error halt,first.2)
    | .ok choice => if choice then RawCheckedControlSequence.block one pipeline n first.2
      else RawCheckedControlSequence.block two pipeline n first.2

end Solidity.Yul.RawCheckedControlIfElse

namespace Solidity.Yul.RawCheckedControlIfElse
theorem correct : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (yes no : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (one : Solidity.Yul.RawCheckedControlSequence.Supported ctx returns modifier u yes)
 (two : Solidity.Yul.RawCheckedControlSequence.Supported ctx returns modifier u no)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent
   (Solidity.Yul.RawCheckedControlIfElse.run test one two glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.ifElse condition (.block yes) (.block no)) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawLoopBody.represented
   (Solidity.Yul.RawCheckedControlIfElse.run test one two glob.pipeline fuel state) := by
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
        exact ⟨nextSame, RawSourceAdapterIfElse.source_error condition (.block yes) (.block no) glob frame fuel nps ph state locals world halt actual⟩
      | ok value =>
        cases value with
        | val value =>
          cases value with
          | bool choice =>
            cases choice with
            | false =>
              change RawCondition.eval test fuel state = (.ok false,nextFrame) at conditionRun
              have branch := RawCheckedControlSequence.block_correct two glob frame checked fuel nps ph nextFrame nextSame
              have sourceCondition :
                  (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                    (.ok (.val (.bool false)),(nextFrame.clean,nextFrame.world)) := by
                rw [nextClean]
                exact actual
              have selected := RawSourceAdapterIfElse.source_selected condition (.block yes) (.block no) glob frame fuel nps ph
                state nextFrame false (RawCheckedControlSequence.block two glob.pipeline fuel nextFrame) sourceCondition branch.2
              simp only [run, conditionRun, Bool.false_eq_true, if_false]
              exact ⟨branch.1,selected⟩
            | true =>
              change RawCondition.eval test fuel state = (.ok true,nextFrame) at conditionRun
              have branch := RawCheckedControlSequence.block_correct one glob frame checked fuel nps ph nextFrame nextSame
              have sourceCondition :
                  (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                    (.ok (.val (.bool true)),(nextFrame.clean,nextFrame.world)) := by
                rw [nextClean]
                exact actual
              have selected := RawSourceAdapterIfElse.source_selected condition (.block yes) (.block no) glob frame fuel nps ph
                state nextFrame true (RawCheckedControlSequence.block one glob.pipeline fuel nextFrame) sourceCondition branch.2
              simp only [run, conditionRun, if_true]
              exact ⟨branch.1,selected⟩
          | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible


end Solidity.Yul.RawCheckedControlIfElse
