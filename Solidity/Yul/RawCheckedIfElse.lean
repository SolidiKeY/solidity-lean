import Solidity.Yul.RawCheckedSequence
import Solidity.Yul.RawIfElse

/-! Concrete mixed Boolean/checked-uint8 branches over actual intrinsic
Source if/else syntax. Selected partial frames and raw words are retained;
Source agreement requires checked execution and exact coherence. -/
namespace Solidity.Yul.RawCheckedIfElse

def run {ctx returns modifier control condition yes no}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawCheckedSequence.Supported ctx returns modifier control yes)
    (two : RawCheckedSequence.Supported ctx returns modifier control no)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R Unit × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    let first := RawCondition.eval test n state
    match first.1 with
    | .error halt => (.error halt,first.2)
    | .ok choice => if choice then RawCheckedSequence.block one pipeline n first.2
      else RawCheckedSequence.block two pipeline n first.2

theorem correct {ctx returns modifier control condition yes no}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawCheckedSequence.Supported ctx returns modifier control yes)
    (two : RawCheckedSequence.Supported ctx returns modifier control no)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (checked : frame.checked = true)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (same : RawCoherent.coherent state = true) :
    RawCoherent.coherent (run test one two glob.pipeline fuel state).2 = true ∧
      (Solidity.Source.execS glob frame fuel nps ph
        (Solidity.Source.RStmt.ifElse condition (.block yes) (.block no)) state.clean).run
        (Solidity.Source.L0 ctx.env,state.world) =
          RawSequence.represented (run test one two glob.pipeline fuel state) := by
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
        exact ⟨nextSame, RawIfElse.source_error condition yes no glob frame fuel nps ph state locals world halt actual⟩
      | ok value =>
        cases value with
        | val value =>
          cases value with
          | bool choice =>
            cases choice with
            | false =>
              change RawCondition.eval test fuel state = (.ok false,nextFrame) at conditionRun
              have branch := RawCheckedSequence.block_correct ctx returns modifier control no two glob frame checked fuel nps ph nextFrame nextSame
              have sourceCondition :
                  (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                    (.ok (.val (.bool false)),(nextFrame.clean,nextFrame.world)) := by
                rw [nextClean]
                exact actual
              have selected := RawIfElse.source_selected condition yes no glob frame fuel nps ph
                state nextFrame false (RawCheckedSequence.block two glob.pipeline fuel nextFrame) sourceCondition branch.2
              simp only [run, conditionRun, Bool.false_eq_true, if_false]
              exact ⟨branch.1,selected⟩
            | true =>
              change RawCondition.eval test fuel state = (.ok true,nextFrame) at conditionRun
              have branch := RawCheckedSequence.block_correct ctx returns modifier control yes one glob frame checked fuel nps ph nextFrame nextSame
              have sourceCondition :
                  (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                    (.ok (.val (.bool true)),(nextFrame.clean,nextFrame.world)) := by
                rw [nextClean]
                exact actual
              have selected := RawIfElse.source_selected condition yes no glob frame fuel nps ph
                state nextFrame true (RawCheckedSequence.block one glob.pipeline fuel nextFrame) sourceCondition branch.2
              simp only [run, conditionRun, if_true]
              exact ⟨branch.1,selected⟩
          | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible

end Solidity.Yul.RawCheckedIfElse
