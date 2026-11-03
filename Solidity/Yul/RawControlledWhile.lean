import Solidity.Yul.RawLoopBody

/-! Source while-loop with actual certified boolean condition and same-context
certified Source bodies with normal/break/continue flow. No replacement AST or generic Source admission.
Horizon and scope-close operations are those of actual Source.execS. -/
namespace Solidity.Yul.RawControlledWhile

def run {ctx returns modifier u condition yes}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawLoopBody.Supported ctx returns modifier u yes)
    (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R Unit × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    let first := RawCondition.eval test n state
    match first.1 with
    | .error halt => (.error halt,first.2)
    | .ok choice => if choice then
      let body := RawLoopBody.run one n first.2
      match body.1 with
      | .error halt => (.error halt,body.2)
      | .ok flow => match flow with
        | .normal | .continue_ _ => run test one n body.2
        | .break_ _ => (.ok (),body.2)
        | .leave_ impossible => nomatch impossible
      else (.ok (),first.2)

theorem source_error {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy}
    {modifier : Bool} {l u : Bool}
    (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
    (yes : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (next : Solidity.Source.Locals ctx.env.layout ctx.tys)
    (world : Solidity.Source.St ctx.env) (halt : Solidity.Source.Halt)
    (actual : (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
      (.error halt,(next,world))) :
    (Solidity.Source.execS glob frame (fuel+1) nps ph
      (Solidity.Source.RStmt.whileLoop (l := l) condition yes) state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) =
        (.error halt,(Solidity.Source.L0 ctx.env,world)) := by
  rw [Solidity.Source.execS, Solidity.Source.Hoare.run_bind,
    RawCondition.sub_error condition glob frame fuel state.clean next state.world world halt actual]

theorem source_false {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy}
    {modifier : Bool} {l u : Bool}
    (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
    (yes : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state next : RawFrame.State ctx)
    (actual : (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
      (.ok (.val (.bool false)),(next.clean,next.world))) :
    (Solidity.Source.execS glob frame (fuel+1) nps ph
      (Solidity.Source.RStmt.whileLoop (l := l) condition yes) state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) =
        RawSequence.represented (.ok (),next) := by
  rw [Solidity.Source.execS, Solidity.Source.Hoare.run_bind,
    RawCondition.sub_bool condition glob frame fuel state.clean next.clean
      state.world next.world false actual]
  rfl

theorem source_true {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy}
    {modifier l u : Bool}
    (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
    (yes : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state next : RawFrame.State ctx)
    (result : Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx)
    (actual : (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
      (.ok (.val (.bool true)),(next.clean,next.world)))
    (branch : (Solidity.Source.execS glob frame fuel nps ph
      yes next.clean).run
      (Solidity.Source.L0 ctx.env,next.world) = RawLoopBody.represented result) :
    (Solidity.Source.execS glob frame (fuel+1) nps ph
      (Solidity.Source.RStmt.whileLoop (l := l) condition yes) state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) =
        match result.1 with
        | .error halt => (.error halt,(Solidity.Source.L0 ctx.env,result.2.world))
        | .ok flow => match flow with
          | .normal | .continue_ _ => (Solidity.Source.execS glob frame fuel nps ph
              (Solidity.Source.RStmt.whileLoop (l := l) condition yes)
              result.2.clean).run (Solidity.Source.L0 ctx.env,result.2.world)
          | .break_ _ => RawSequence.represented (.ok (),result.2)
          | .leave_ impossible => nomatch impossible := by
  rw [Solidity.Source.execS, Solidity.Source.Hoare.run_bind,
    RawCondition.sub_bool condition glob frame fuel state.clean next.clean
      state.world next.world true actual]
  dsimp only
  rw [Solidity.Source.Hoare.run_bind]
  have getTrue : (Solidity.Source.getV (E := ctx.env) (Γ := [])
      (Solidity.Source.RVal.val (Solidity.Source.Val.bool true))).run
      (Solidity.Source.L0 ctx.env,next.world) =
        (.ok (.bool true),(Solidity.Source.L0 ctx.env,next.world)) := rfl
  rw [getTrue]
  dsimp only
  rw [Solidity.Source.Hoare.run_bind, branch]
  cases tag : result.1 with
  | error halt => simp only [RawLoopBody.represented,tag,Except.map]
  | ok flow =>
    cases flow with
    | normal =>
      simp only [RawLoopBody.represented,tag,Except.map,RawLoopBody.out,RawSequence.restore_self]
      rfl
    | continue_ h =>
      simp only [RawLoopBody.represented,tag,Except.map,RawLoopBody.out]
    | break_ h =>
      simp only [RawLoopBody.represented,tag,Except.map,RawLoopBody.out,RawSequence.represented]
      rfl
    | leave_ h => cases h

theorem correct {ctx returns modifier u condition yes} {l : Bool}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawLoopBody.Supported ctx returns modifier u yes)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (same : RawCoherent.coherent state = true) :
    RawCoherent.coherent (run test one fuel state).2 = true ∧
      (Solidity.Source.execS glob frame fuel nps ph
        (Solidity.Source.RStmt.whileLoop (l := l) condition yes) state.clean).run
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
        exact ⟨nextSame, source_error condition yes glob frame fuel nps ph state locals world halt actual⟩
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
              exact ⟨nextSame, source_false condition yes glob frame fuel nps ph
                state nextFrame sourceCondition⟩
            | true =>
              change RawCondition.eval test fuel state = (.ok true,nextFrame) at conditionRun
              have branch := RawLoopBody.correct one glob frame fuel nps ph nextFrame nextSame
              have sourceCondition :
                  (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                    (.ok (.val (.bool true)),(nextFrame.clean,nextFrame.world)) := by
                rw [nextClean]
                exact actual
              have selected := source_true (l := l) condition yes glob frame fuel nps ph
                state nextFrame (RawLoopBody.run one fuel nextFrame) sourceCondition branch.2
              simp only [run, conditionRun, if_true]
              rw [selected]
              cases bodyTag : (RawLoopBody.run one fuel nextFrame).1 with
              | error halt =>
                exact ⟨branch.1,rfl⟩
              | ok flow =>
                cases flow with
                | normal => exact ih (RawLoopBody.run one fuel nextFrame).2 branch.1
                | continue_ h => exact ih (RawLoopBody.run one fuel nextFrame).2 branch.1
                | break_ h => exact ⟨branch.1,rfl⟩
                | leave_ h => cases h
          | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible

theorem source_agrees {ctx returns modifier u condition yes} {l : Bool}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawLoopBody.Supported ctx returns modifier u yes)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (same : RawCoherent.coherent state = true) :
    RawCoherent.observe (run test one fuel state) =
      some ((Solidity.Source.execS glob frame fuel nps ph
        (Solidity.Source.RStmt.whileLoop (l := l) condition yes) state.clean).run
        (Solidity.Source.L0 ctx.env,state.world)) := by
  have actual := correct (l := l) test one glob frame fuel nps ph state same
  unfold RawCoherent.observe
  rw [if_pos actual.1]
  exact congrArg some actual.2.symm

end Solidity.Yul.RawControlledWhile
