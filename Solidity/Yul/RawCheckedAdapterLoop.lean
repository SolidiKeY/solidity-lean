import Solidity.Yul.RawCheckedAdapter
import Solidity.Yul.RawControlledWhile

/-! Checked Source while composition over actual executable body producers.
Normal/continue recurse at actual postbody frames; break exits.
Source agreement retains producer, checked-frame and coherence premises. -/
namespace Solidity.Yul.RawCheckedAdapterLoop

def run {ctx returns modifier u condition yes}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawCheckedAdapter.Adapter ctx returns modifier u yes)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R Unit × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    let first := RawCondition.eval test n state
    match first.1 with
    | .error halt => (.error halt,first.2)
    | .ok choice => if choice then
      let body := one.run pipeline n first.2
      match body.1 with
      | .error halt => (.error halt,body.2)
      | .ok flow => match flow with
        | .normal | .continue_ _ => run test one pipeline n body.2
        | .break_ _ => (.ok (),body.2)
        | .leave_ impossible => nomatch impossible
      else (.ok (),first.2)

end Solidity.Yul.RawCheckedAdapterLoop

namespace Solidity.Yul.RawCheckedAdapterLoop
theorem correct : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier l u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (yes : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (one : Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u yes)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent
   (Solidity.Yul.RawCheckedAdapterLoop.run test one glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.whileLoop (l := l) condition yes) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedAdapterLoop.run test one glob.pipeline fuel state) := by
  intro ctx returns modifier l u condition test yes one glob frame checked fuel nps ph state same
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
        exact ⟨nextSame, RawControlledWhile.source_error condition yes glob frame fuel nps ph state locals world halt actual⟩
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
              exact ⟨nextSame, RawControlledWhile.source_false condition yes glob frame fuel nps ph
                state nextFrame sourceCondition⟩
            | true =>
              change RawCondition.eval test fuel state = (.ok true,nextFrame) at conditionRun
              have branch := one.correct glob frame checked fuel nps ph nextFrame nextSame
              have sourceCondition :
                  (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                    (.ok (.val (.bool true)),(nextFrame.clean,nextFrame.world)) := by
                rw [nextClean]
                exact actual
              have selected := RawControlledWhile.source_true (l := l) condition yes glob frame fuel nps ph
                state nextFrame (one.run glob.pipeline fuel nextFrame) sourceCondition branch.2
              simp only [run, conditionRun, if_true]
              rw [selected]
              cases bodyTag : (one.run glob.pipeline fuel nextFrame).1 with
              | error halt =>
                exact ⟨branch.1,rfl⟩
              | ok flow =>
                cases flow with
                | normal => exact ih (one.run glob.pipeline fuel nextFrame).2 branch.1
                | continue_ h => exact ih (one.run glob.pipeline fuel nextFrame).2 branch.1
                | break_ h => exact ⟨branch.1,rfl⟩
                | leave_ h => cases h
          | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible


theorem lift_correct : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (yes : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (one : Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u yes)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent
   (Solidity.Yul.RawCheckedAdapterLoop.run test one glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.whileLoop (l := true) condition yes) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawLoopBody.represented
   ((Solidity.Yul.RawCheckedAdapterLoop.run test one glob.pipeline fuel state).1.map
      (fun _ => (Solidity.Yul.Closed.Flow.normal : Solidity.Yul.RawLoopBody.Flow)),
    (Solidity.Yul.RawCheckedAdapterLoop.run test one glob.pipeline fuel state).2) := by
  intro ctx returns modifier u condition test yes one glob frame checked fuel nps ph state same
  rw [RawLoopBody.plain_represented]
  exact correct ctx returns modifier true u condition test yes one glob frame checked fuel nps ph state same

def loop {ctx returns modifier u condition yes}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawCheckedAdapter.Adapter ctx returns modifier u yes) :
    RawCheckedAdapter.Adapter ctx returns modifier u
      (Solidity.Source.RStmt.whileLoop (l := true) condition yes) where
  run pipeline fuel state :=
    let actual := run test one pipeline fuel state
    (actual.1.map (fun _ => .normal),actual.2)
  correct := lift_correct ctx returns modifier u condition test yes one

end Solidity.Yul.RawCheckedAdapterLoop
