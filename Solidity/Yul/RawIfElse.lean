import Solidity.Yul.RawCondition

/-! Source if/else with actual certified boolean condition and same-context
certified Source blocks. No replacement AST or generic Source admission.
Horizon and scope-close operations are those of actual Source.execS. -/
namespace Solidity.Yul.RawIfElse

def run {ctx returns modifier control condition yes no}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawSequence.Supported ctx returns modifier control yes)
    (two : RawSequence.Supported ctx returns modifier control no)
    (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R Unit × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    let first := RawCondition.eval test n state
    match first.1 with
    | .error halt => (.error halt,first.2)
    | .ok choice => if choice then RawSequence.block one n first.2
      else RawSequence.block two n first.2

theorem source_error {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy}
    {modifier : Bool} {control : Solidity.Source.SCtx}
    (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
    (yes no : Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (next : Solidity.Source.Locals ctx.env.layout ctx.tys)
    (world : Solidity.Source.St ctx.env) (halt : Solidity.Source.Halt)
    (actual : (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
      (.error halt,(next,world))) :
    (Solidity.Source.execS glob frame (fuel+1) nps ph
      (Solidity.Source.RStmt.ifElse condition (.block yes) (.block no)) state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) =
        (.error halt,(Solidity.Source.L0 ctx.env,world)) := by
  rw [Solidity.Source.execS, Solidity.Source.Hoare.run_bind,
    RawCondition.sub_error condition glob frame fuel state.clean next state.world world halt actual]

theorem source_selected {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy}
    {modifier : Bool} {control : Solidity.Source.SCtx}
    (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
    (yes no : Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state next : RawFrame.State ctx) (choice : Bool)
    (result : Solidity.Source.R Unit × RawFrame.State ctx)
    (actual : (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
      (.ok (.val (.bool choice)),(next.clean,next.world)))
    (branch : (Solidity.Source.execS glob frame fuel nps ph
      (if choice then Solidity.Source.RStmt.block yes else Solidity.Source.RStmt.block no)
      next.clean).run (Solidity.Source.L0 ctx.env,next.world) = RawSequence.represented result) :
    (Solidity.Source.execS glob frame (fuel+1) nps ph
      (Solidity.Source.RStmt.ifElse condition (.block yes) (.block no)) state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) = RawSequence.represented result := by
  cases choice with
  | false =>
    simp only [reduceCtorEq, if_false] at branch
    rw [Solidity.Source.execS, Solidity.Source.Hoare.run_bind,
      RawCondition.sub_bool condition glob frame fuel state.clean next.clean
        state.world next.world false actual]
    change (do
      let out ← Solidity.Source.execS glob frame fuel nps ph
        (Solidity.Source.RStmt.block no) next.clean
      Solidity.Source.EM.lift out.close).run
        (Solidity.Source.L0 ctx.env,next.world) = _
    rw [Solidity.Source.Hoare.run_bind, branch]
    cases tag : result.1 with
    | error halt => simp only [RawSequence.represented, tag, Except.map]
    | ok _value =>
      simp only [RawSequence.represented, tag, Except.map,
        Solidity.Source.Out.close, RawSequence.restore_self]
      rfl
  | true =>
    simp only [if_true] at branch
    rw [Solidity.Source.execS, Solidity.Source.Hoare.run_bind,
      RawCondition.sub_bool condition glob frame fuel state.clean next.clean
        state.world next.world true actual]
    change (do
      let out ← Solidity.Source.execS glob frame fuel nps ph
        (Solidity.Source.RStmt.block yes) next.clean
      Solidity.Source.EM.lift out.close).run
        (Solidity.Source.L0 ctx.env,next.world) = _
    rw [Solidity.Source.Hoare.run_bind, branch]
    cases tag : result.1 with
    | error halt => simp only [RawSequence.represented, tag, Except.map]
    | ok _value =>
      simp only [RawSequence.represented, tag, Except.map,
        Solidity.Source.Out.close, RawSequence.restore_self]
      rfl

theorem correct {ctx returns modifier control condition yes no}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawSequence.Supported ctx returns modifier control yes)
    (two : RawSequence.Supported ctx returns modifier control no)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (same : RawCoherent.coherent state = true) :
    RawCoherent.coherent (run test one two fuel state).2 = true ∧
      (Solidity.Source.execS glob frame fuel nps ph
        (Solidity.Source.RStmt.ifElse condition (.block yes) (.block no)) state.clean).run
        (Solidity.Source.L0 ctx.env,state.world) =
          RawSequence.represented (run test one two fuel state) := by
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
        exact ⟨nextSame, source_error condition yes no glob frame fuel nps ph state locals world halt actual⟩
      | ok value =>
        cases value with
        | val value =>
          cases value with
          | bool choice =>
            cases choice with
            | false =>
              change RawCondition.eval test fuel state = (.ok false,nextFrame) at conditionRun
              have branch := RawSequence.block_correct two glob frame fuel nps ph nextFrame nextSame
              have sourceCondition :
                  (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                    (.ok (.val (.bool false)),(nextFrame.clean,nextFrame.world)) := by
                rw [nextClean]
                exact actual
              have selected := source_selected condition yes no glob frame fuel nps ph
                state nextFrame false (RawSequence.block two fuel nextFrame) sourceCondition branch.2
              simp only [run, conditionRun, Bool.false_eq_true, if_false]
              exact ⟨branch.1,selected⟩
            | true =>
              change RawCondition.eval test fuel state = (.ok true,nextFrame) at conditionRun
              have branch := RawSequence.block_correct one glob frame fuel nps ph nextFrame nextSame
              have sourceCondition :
                  (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                    (.ok (.val (.bool true)),(nextFrame.clean,nextFrame.world)) := by
                rw [nextClean]
                exact actual
              have selected := source_selected condition yes no glob frame fuel nps ph
                state nextFrame true (RawSequence.block one fuel nextFrame) sourceCondition branch.2
              simp only [run, conditionRun, if_true]
              exact ⟨branch.1,selected⟩
          | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible

theorem source_agrees {ctx returns modifier control condition yes no}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawSequence.Supported ctx returns modifier control yes)
    (two : RawSequence.Supported ctx returns modifier control no)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (same : RawCoherent.coherent state = true) :
    RawCoherent.observe (run test one two fuel state) =
      some ((Solidity.Source.execS glob frame fuel nps ph
        (Solidity.Source.RStmt.ifElse condition (.block yes) (.block no)) state.clean).run
        (Solidity.Source.L0 ctx.env,state.world)) := by
  have actual := correct test one two glob frame fuel nps ph state same
  unfold RawCoherent.observe
  rw [if_pos actual.1]
  exact congrArg some actual.2.symm

end Solidity.Yul.RawIfElse
