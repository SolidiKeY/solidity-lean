import Solidity.Yul.RawControlSequence
import Solidity.Yul.RawControlledWhile

/-! Source while-loop with actual certified boolean condition and same-context
certified Source item sequences with normal/break/continue flow. No replacement AST or generic Source admission.
Horizon and scope-close operations are those of actual Source.execS. -/
namespace Solidity.Yul.RawSequenceWhile

def run {ctx returns modifier u condition yes}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawControlSequence.Supported ctx returns modifier u yes)
    (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R Unit × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    let first := RawCondition.eval test n state
    match first.1 with
    | .error halt => (.error halt,first.2)
    | .ok choice => if choice then
      let body := RawControlSequence.block one n first.2
      match body.1 with
      | .error halt => (.error halt,body.2)
      | .ok flow => match flow with
        | .normal | .continue_ _ => run test one n body.2
        | .break_ _ => (.ok (),body.2)
        | .leave_ impossible => nomatch impossible
      else (.ok (),first.2)

theorem correct {ctx returns modifier u condition yes} {l : Bool}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawControlSequence.Supported ctx returns modifier u yes)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (same : RawCoherent.coherent state = true) :
    RawCoherent.coherent (run test one fuel state).2 = true ∧
      (Solidity.Source.execS glob frame fuel nps ph
        (Solidity.Source.RStmt.whileLoop (l := l) condition (.block yes)) state.clean).run
        (Solidity.Source.L0 ctx.env,state.world) =
          RawSequence.represented (run test one fuel state) := by
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
        exact ⟨nextSame, RawControlledWhile.source_error condition (.block yes) glob frame fuel nps ph state locals world halt actual⟩
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
              exact ⟨nextSame, RawControlledWhile.source_false condition (.block yes) glob frame fuel nps ph
                state nextFrame sourceCondition⟩
            | true =>
              change RawCondition.eval test fuel state = (.ok true,nextFrame) at conditionRun
              have branch := RawControlSequence.block_correct one glob frame fuel nps ph nextFrame nextSame
              have sourceCondition :
                  (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                    (.ok (.val (.bool true)),(nextFrame.clean,nextFrame.world)) := by
                rw [nextClean]
                exact actual
              have selected := RawControlledWhile.source_true (l := l) condition (.block yes) glob frame fuel nps ph
                state nextFrame (RawControlSequence.block one fuel nextFrame) sourceCondition branch.2
              simp only [run, conditionRun, if_true]
              rw [selected]
              cases bodyTag : (RawControlSequence.block one fuel nextFrame).1 with
              | error halt =>
                exact ⟨branch.1,rfl⟩
              | ok flow =>
                cases flow with
                | normal => exact ih (RawControlSequence.block one fuel nextFrame).2 branch.1
                | continue_ h => exact ih (RawControlSequence.block one fuel nextFrame).2 branch.1
                | break_ h => exact ⟨branch.1,rfl⟩
                | leave_ h => cases h
          | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible

theorem source_agrees {ctx returns modifier u condition yes} {l : Bool}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawControlSequence.Supported ctx returns modifier u yes)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (same : RawCoherent.coherent state = true) :
    RawCoherent.observe (run test one fuel state) =
      some ((Solidity.Source.execS glob frame fuel nps ph
        (Solidity.Source.RStmt.whileLoop (l := l) condition (.block yes)) state.clean).run
        (Solidity.Source.L0 ctx.env,state.world)) := by
  have actual := correct (l := l) test one glob frame fuel nps ph state same
  unfold RawCoherent.observe
  rw [if_pos actual.1]
  exact congrArg some actual.2.symm

end Solidity.Yul.RawSequenceWhile
