import Solidity.Yul.RawCheckedSequence
import Solidity.Yul.RawIfThen

/-! Concrete if-only composition with mixed Boolean/checked-uint8 blocks.
The condition and body use actual intrinsic Source syntax/certificates.
Raw condition effects and partial branch frames are retained; Source agreement
keeps checked-frame and exact coherence premises. No general admission. -/
namespace Solidity.Yul.RawCheckedIf

def run {ctx returns modifier control condition yes}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawCheckedSequence.Supported ctx returns modifier control yes)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R Unit × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | fuel+1 =>
    let first := RawCondition.eval test fuel state
    match first.1 with
    | .error halt => (.error halt,first.2)
    | .ok choice => if choice then RawCheckedSequence.block one pipeline fuel first.2
      else (.ok (),first.2)

theorem correct : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (yes : Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (one : Solidity.Yul.RawCheckedSequence.Supported ctx returns modifier control yes)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedIf.run test one glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.ifThen condition (.block yes)) state.clean).run
     (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedIf.run test one glob.pipeline fuel state) := by
  intro ctx returns modifier control condition yes test one glob frame checked fuel nps ph state same
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
        exact ⟨nextSame, RawIfThen.source_error condition yes glob frame fuel nps ph state locals world halt actual⟩
      | ok value =>
        cases value with
        | val value =>
          cases value with
          | bool choice =>
            cases choice with
            | false =>
              change RawCondition.eval test fuel state = (.ok false,nextFrame) at conditionRun
              have sourceCondition :
                  (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                    (.ok (.val (.bool false)),(nextFrame.clean,nextFrame.world)) := by
                rw [nextClean]
                exact actual
              simp only [run, conditionRun, Bool.false_eq_true, if_false]
              exact ⟨nextSame, RawIfThen.source_false condition yes glob frame fuel nps ph
                state nextFrame sourceCondition⟩
            | true =>
              change RawCondition.eval test fuel state = (.ok true,nextFrame) at conditionRun
              have branch := RawCheckedSequence.block_correct ctx returns modifier control yes one glob frame checked fuel nps ph nextFrame nextSame
              have sourceCondition :
                  (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                    (.ok (.val (.bool true)),(nextFrame.clean,nextFrame.world)) := by
                rw [nextClean]
                exact actual
              have selected := RawIfThen.source_true condition yes glob frame fuel nps ph
                state nextFrame (RawCheckedSequence.block one glob.pipeline fuel nextFrame) sourceCondition branch.2
              simp only [run, conditionRun, if_true]
              exact ⟨branch.1,selected⟩
          | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible



end Solidity.Yul.RawCheckedIf
