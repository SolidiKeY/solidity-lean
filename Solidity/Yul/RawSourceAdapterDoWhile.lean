import Solidity.Yul.RawSourceAdapterIfElse

/-! Actual do/while: the body precedes its condition; break skips the condition.
The raw local state and Source syntax remain intrinsic. -/
namespace Solidity.Yul.RawSourceAdapterDoWhile

def after {ctx condition}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (resume : RawFrame.State ctx → Solidity.Source.R Unit × RawFrame.State ctx)
    (fuel : Nat) (state : RawFrame.State ctx) : Solidity.Source.R Unit × RawFrame.State ctx :=
  let next := RawCondition.eval test fuel state
  match next.1 with
  | .error halt => (.error halt,next.2)
  | .ok choice => if choice then resume next.2 else (.ok (),next.2)

def run {ctx returns modifier u condition stmt}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (inside : RawSourceAdapter.Adapter ctx returns modifier u stmt)
    (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R Unit × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    let body := inside.run n state
    match body.1 with
    | .error halt => (.error halt,body.2)
    | .ok flow => match flow with
      | .break_ _ => (.ok (),body.2)
      | .normal | .continue_ _ =>
        after test (run test inside n) n body.2
      | .leave_ impossible => nomatch impossible

/-- The real Source continuation after a normal/continue body result. -/
def sourceAfter {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy}
    {modifier l u : Bool}
    (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
    (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (locals : Solidity.Source.Locals ctx.env.layout ctx.tys) :
    Solidity.Source.EM ctx.env [] (Solidity.Source.Out ctx.env.layout ctx.tys ctx.tys) := do
  let (value,next) ← Solidity.Source.EM.sub locals (Solidity.Source.evalE glob frame fuel condition)
  let clean ← Solidity.Source.getV value
  if LocalBoolControl.truth (LocalValue.clean clean) then
    Solidity.Source.execS glob frame fuel nps ph
      (Solidity.Source.RStmt.doWhile (l := l) stmt condition) next
  else pure (.normal next)

theorem source_body {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy}
    {modifier l u : Bool}
    (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
    (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : Solidity.Yul.RawFrame.State ctx)
    (result : Solidity.Source.R Solidity.Yul.RawLoopBody.Flow × Solidity.Yul.RawFrame.State ctx)
    (actual : (Solidity.Source.execS glob frame fuel nps ph stmt state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) = Solidity.Yul.RawLoopBody.represented result) :
    (Solidity.Source.execS glob frame (fuel+1) nps ph
      (Solidity.Source.RStmt.doWhile (l := l) stmt condition) state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) =
        match result.1 with
        | .error halt => (.error halt,(Solidity.Source.L0 ctx.env,result.2.world))
        | .ok flow => match flow with
          | .break_ _ => Solidity.Yul.RawSequence.represented (.ok (),result.2)
          | .normal | .continue_ _ =>
            (Solidity.Yul.RawSourceAdapterDoWhile.sourceAfter (l := l) condition stmt glob frame
              fuel nps ph result.2.clean).run (Solidity.Source.L0 ctx.env,result.2.world)
          | .leave_ impossible => nomatch impossible := by
  rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,actual]
  cases tag : result.1 with
  | error halt => simp only [Solidity.Yul.RawLoopBody.represented,tag,Except.map]
  | ok flow =>
    cases flow with
    | normal =>
      simp only [Solidity.Yul.RawLoopBody.represented,tag,Except.map,
        Solidity.Yul.RawLoopBody.out,Solidity.Yul.RawSequence.restore_self]
      simp only [Solidity.Yul.RawSourceAdapterDoWhile.sourceAfter,Solidity.Source.EM.lift,pure_bind]
      apply congrArg (fun computation : Solidity.Source.EM ctx.env []
        (Solidity.Source.Out ctx.env.layout ctx.tys ctx.tys) =>
          computation.run (Solidity.Source.L0 ctx.env,result.2.world))
      apply congrArg (fun continuation =>
        Solidity.Source.EM.sub result.2.clean (Solidity.Source.evalE glob frame fuel condition) >>= continuation)
      funext pair
      rcases pair with ⟨value,next⟩
      apply congrArg (fun continuation => Solidity.Source.getV value >>= continuation)
      funext clean
      cases clean with
      | bool b => cases b <;> rfl
      | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible
    | continue_ h =>
      simp only [Solidity.Yul.RawLoopBody.represented,tag,Except.map,Solidity.Yul.RawLoopBody.out]
      simp only [Solidity.Yul.RawSourceAdapterDoWhile.sourceAfter,pure_bind]
      apply congrArg (fun computation : Solidity.Source.EM ctx.env []
        (Solidity.Source.Out ctx.env.layout ctx.tys ctx.tys) =>
          computation.run (Solidity.Source.L0 ctx.env,result.2.world))
      apply congrArg (fun continuation =>
        Solidity.Source.EM.sub result.2.clean (Solidity.Source.evalE glob frame fuel condition) >>= continuation)
      funext pair
      rcases pair with ⟨value,next⟩
      apply congrArg (fun continuation => Solidity.Source.getV value >>= continuation)
      funext clean
      cases clean with
      | bool b => cases b <;> rfl
      | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible
    | break_ h =>
      simp only [Solidity.Yul.RawLoopBody.represented,tag,Except.map,Solidity.Yul.RawLoopBody.out,
        Solidity.Yul.RawSequence.represented]
      rfl
    | leave_ h => cases h

theorem source_after_error {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier l u : Bool}
    (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
    (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : Solidity.Yul.RawFrame.State ctx)
    (next : Solidity.Source.Locals ctx.env.layout ctx.tys) (world : Solidity.Source.St ctx.env)
    (halt : Solidity.Source.Halt)
    (actual : (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
      (.error halt,(next,world))) :
    (Solidity.Yul.RawSourceAdapterDoWhile.sourceAfter (l := l) condition stmt glob frame fuel nps ph
      state.clean).run (Solidity.Source.L0 ctx.env,state.world) =
      (.error halt,(Solidity.Source.L0 ctx.env,world)) := by
  first
  | simp only [Solidity.Yul.RawSourceAdapterDoWhile.sourceAfter,Solidity.Source.Hoare.run_bind,
      Solidity.Yul.RawCondition.sub_error condition glob frame fuel state.clean next state.world world halt actual]
  | decide
  | omega
  | rfl



theorem source_after_choice {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier l u : Bool}
    (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
    (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : Solidity.Yul.RawFrame.State ctx)
    (next : Solidity.Yul.RawFrame.State ctx) (choice : Bool)
    (actual : (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
      (.ok (.val (.bool choice)),(next.clean,next.world))) :
    (Solidity.Yul.RawSourceAdapterDoWhile.sourceAfter (l := l) condition stmt glob frame fuel nps ph
      state.clean).run (Solidity.Source.L0 ctx.env,state.world) =
      if choice then
        (Solidity.Source.execS glob frame fuel nps ph
          (Solidity.Source.RStmt.doWhile (l := l) stmt condition) next.clean).run
          (Solidity.Source.L0 ctx.env,next.world)
      else Solidity.Yul.RawSequence.represented (.ok (),next) := by
  rw [Solidity.Yul.RawSourceAdapterDoWhile.sourceAfter,Solidity.Source.Hoare.run_bind,
    Solidity.Yul.RawCondition.sub_bool condition glob frame fuel state.clean next.clean
      state.world next.world choice actual]
  dsimp only
  rw [Solidity.Source.Hoare.run_bind]
  have getBool : (Solidity.Source.getV (E := ctx.env) (Γ := []) (.val (.bool choice))).run
      (Solidity.Source.L0 ctx.env,next.world) =
      (.ok (.bool choice),(Solidity.Source.L0 ctx.env,next.world)) := by rfl
  rw [getBool]
  simp only [Solidity.Yul.LocalBoolControl.truth_clean]
  cases choice <;> rfl

theorem after_correct {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier l u : Bool}
    (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
    (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
    (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
    (resume : Solidity.Yul.RawFrame.State ctx → Solidity.Source.R Unit × Solidity.Yul.RawFrame.State ctx)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (law : ∀ next : Solidity.Yul.RawFrame.State ctx, Solidity.Yul.RawCoherent.coherent next = true →
      Solidity.Yul.RawCoherent.coherent (resume next).2 = true ∧
        (Solidity.Source.execS glob frame fuel nps ph
          (Solidity.Source.RStmt.doWhile (l := l) stmt condition) next.clean).run
          (Solidity.Source.L0 ctx.env,next.world) = Solidity.Yul.RawSequence.represented (resume next))
    (state : Solidity.Yul.RawFrame.State ctx) (same : Solidity.Yul.RawCoherent.coherent state = true) :
    Solidity.Yul.RawCoherent.coherent
        (Solidity.Yul.RawSourceAdapterDoWhile.after test resume fuel state).2 = true ∧
      (Solidity.Yul.RawSourceAdapterDoWhile.sourceAfter (l := l) condition stmt glob frame fuel nps ph
        state.clean).run (Solidity.Source.L0 ctx.env,state.world) =
          Solidity.Yul.RawSequence.represented (Solidity.Yul.RawSourceAdapterDoWhile.after test resume fuel state) := by
  have conditionRun := RawCondition.source_eval test glob frame fuel state same
  cases actual : (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) with
  | mk tag next =>
    rcases next with ⟨locals,world⟩
    rw [actual] at conditionRun
    let nextFrame : RawFrame.State ctx := RawCoherent.capture state (LocalState.ofClean (locals,world))
    have nextSame : RawCoherent.coherent nextFrame = true :=
      RawCoherent.capture_coherent state locals world
    have nextClean : nextFrame.clean = locals := by
      simp only [nextFrame,RawCoherent.capture,LocalState.ofClean,LocalValues.clean_ofClean,Option.getD_some]
    cases tag with
    | error halt =>
      change RawCondition.eval test fuel state = (.error halt,nextFrame) at conditionRun
      simp only [after,conditionRun]
      exact ⟨nextSame,source_after_error condition stmt glob frame fuel nps ph state locals world halt actual⟩
    | ok value =>
      cases value with
      | val value =>
        cases value with
        | bool choice =>
          cases choice with
          | false =>
            change RawCondition.eval test fuel state = (.ok false,nextFrame) at conditionRun
            have conditionActual :
                (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                  (.ok (.val (.bool false)),(nextFrame.clean,nextFrame.world)) := by
              rw [nextClean]
              exact actual
            have selected := source_after_choice (l := l) condition stmt glob frame fuel nps ph
              state nextFrame false conditionActual
            simp only [after,conditionRun,Bool.false_eq_true,if_false]
            exact ⟨nextSame,selected⟩
          | true =>
            change RawCondition.eval test fuel state = (.ok true,nextFrame) at conditionRun
            have conditionActual :
                (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                  (.ok (.val (.bool true)),(nextFrame.clean,nextFrame.world)) := by
              rw [nextClean]
              exact actual
            have selected := source_after_choice (l := l) condition stmt glob frame fuel nps ph
              state nextFrame true conditionActual
            have recursive := law nextFrame nextSame
            simp only [after,conditionRun,if_true]
            rw [selected]
            exact recursive
        | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible

theorem correct {ctx returns modifier u condition stmt} {l : Bool}
    (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
    (inside : Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u stmt)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : Solidity.Yul.RawFrame.State ctx) (same : Solidity.Yul.RawCoherent.coherent state = true) :
    Solidity.Yul.RawCoherent.coherent
        (Solidity.Yul.RawSourceAdapterDoWhile.run test inside fuel state).2 = true ∧
      (Solidity.Source.execS glob frame fuel nps ph
        (Solidity.Source.RStmt.doWhile (l := l) stmt condition) state.clean).run
        (Solidity.Source.L0 ctx.env,state.world) =
          Solidity.Yul.RawSequence.represented (Solidity.Yul.RawSourceAdapterDoWhile.run test inside fuel state) := by
  induction fuel generalizing state with
  | zero => exact ⟨same,rfl⟩
  | succ fuel ih =>
    have body := inside.correct glob frame fuel nps ph state same
    have actual := source_body (l := l) condition stmt glob frame fuel nps ph state
      (inside.run fuel state) body.2
    cases tag : (inside.run fuel state).1 with
    | error halt =>
      simp only [run,tag]
      simp only [tag] at actual
      exact ⟨body.1,actual⟩
    | ok flow =>
      cases flow with
      | break_ h =>
        simp only [run,tag]
        simp only [tag] at actual
        exact ⟨body.1,actual⟩
      | normal =>
        have tail := after_correct (l := l) condition stmt test (run test inside fuel)
          glob frame fuel nps ph ih (inside.run fuel state).2 body.1
        simp only [run,tag]
        simp only [tag] at actual
        rw [actual]
        exact tail
      | continue_ h =>
        have tail := after_correct (l := l) condition stmt test (run test inside fuel)
          glob frame fuel nps ph ih (inside.run fuel state).2 body.1
        simp only [run,tag]
        simp only [tag] at actual
        rw [actual]
        exact tail
      | leave_ h => cases h

theorem source_agrees {ctx returns modifier u condition stmt} {l : Bool}
    (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
    (inside : Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u stmt)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : Solidity.Yul.RawFrame.State ctx) (same : Solidity.Yul.RawCoherent.coherent state = true) :
    Solidity.Yul.RawCoherent.observe (Solidity.Yul.RawSourceAdapterDoWhile.run test inside fuel state) =
      some ((Solidity.Source.execS glob frame fuel nps ph
        (Solidity.Source.RStmt.doWhile (l := l) stmt condition) state.clean).run
        (Solidity.Source.L0 ctx.env,state.world)) := by
  simp only [RawCoherent.observe, (correct (l := l) test inside glob frame fuel nps ph state same).1,
    RawSequence.represented, if_true, (correct (l := l) test inside glob frame fuel nps ph state same).2]

/-- Package the proved body-first loop for concrete recursive composition. -/
def adapter {ctx returns modifier u condition stmt}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (inside : RawSourceAdapter.Adapter ctx returns modifier u stmt) :
    RawSourceAdapter.Adapter ctx returns modifier u
      (Solidity.Source.RStmt.doWhile (l := true) stmt condition) where
  run fuel state :=
    let actual := run test inside fuel state
    (actual.1.map (fun _ => .normal),actual.2)
  correct glob frame fuel nps ph state same := by
    simp only [RawLoopBody.plain_represented, and_self,
        (correct (l := true) test inside glob frame fuel nps ph state same).1,
        (correct (l := true) test inside glob frame fuel nps ph state same).2]

end Solidity.Yul.RawSourceAdapterDoWhile
