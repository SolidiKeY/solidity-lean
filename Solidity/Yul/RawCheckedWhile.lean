import Solidity.Yul.RawCheckedSequence
import Solidity.Yul.RawWhile

/-! Concrete fuelled loops over actual mixed Boolean/checked-uint8 blocks.
Only normal block flow is certified here. Raw partial frames and predecessor
Source horizons are retained; checked/coherent Source premises stay explicit. -/
namespace Solidity.Yul.RawCheckedWhile

def run {ctx returns modifier u condition yes}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawCheckedSequence.Supported ctx returns modifier ⟨true,u⟩ yes)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R Unit × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    let first := RawCondition.eval test n state
    match first.1 with
    | .error halt => (.error halt,first.2)
    | .ok choice => if choice then
      let body := RawCheckedSequence.block one pipeline n first.2
      match body.1 with
      | .error halt => (.error halt,body.2)
      | .ok () => run test one pipeline n body.2
      else (.ok (),first.2)

theorem correct {ctx returns modifier u condition yes} {l : Bool}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawCheckedSequence.Supported ctx returns modifier ⟨true,u⟩ yes)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (checked : frame.checked = true)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (same : RawCoherent.coherent state = true) :
    RawCoherent.coherent (run test one glob.pipeline fuel state).2 = true ∧
      (Solidity.Source.execS glob frame fuel nps ph
        (Solidity.Source.RStmt.whileLoop (l := l) condition (.block yes)) state.clean).run
        (Solidity.Source.L0 ctx.env,state.world) =
          RawSequence.represented (run test one glob.pipeline fuel state) := by
  induction fuel generalizing state with
  | zero => exact ⟨same,rfl⟩
  | succ fuel ih =>
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
        exact ⟨nextSame, RawWhile.source_error condition yes glob frame fuel nps ph state locals world halt actual⟩
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
              exact ⟨nextSame, RawWhile.source_false condition yes glob frame fuel nps ph
                state nextFrame sourceCondition⟩
            | true =>
              change RawCondition.eval test fuel state = (.ok true,nextFrame) at conditionRun
              have branch := RawCheckedSequence.block_correct ctx returns modifier ⟨true,u⟩ yes one glob frame checked fuel nps ph nextFrame nextSame
              have sourceCondition :
                  (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                    (.ok (.val (.bool true)),(nextFrame.clean,nextFrame.world)) := by
                rw [nextClean]
                exact actual
              have selected := RawWhile.source_true (l := l) condition yes glob frame fuel nps ph
                state nextFrame (RawCheckedSequence.block one glob.pipeline fuel nextFrame) sourceCondition branch.2
              simp only [run, conditionRun, if_true]
              rw [selected]
              cases bodyTag : (RawCheckedSequence.block one glob.pipeline fuel nextFrame).1 with
              | error halt =>
                exact ⟨branch.1,rfl⟩
              | ok value =>
                cases value
                exact ih (RawCheckedSequence.block one glob.pipeline fuel nextFrame).2 branch.1
          | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible

end Solidity.Yul.RawCheckedWhile
