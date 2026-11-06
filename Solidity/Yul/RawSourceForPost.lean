import Solidity.Yul.RawSourceAdapterFor

/-! Same-context Source for iterations with a present condition and a boolean post.
Post values are discarded; errors/partial state are retained. The Source expression
statement wrapper uses fuel+1 precisely to evaluate its expression at fuel. -/
namespace Solidity.Yul.RawSourceForPost

def discard {ctx post}
    (step : LocalBoolControl.Supported ctx.env ctx.tys post)
    (fuel : Nat) (state : RawFrame.State ctx) : Solidity.Source.R Unit × RawFrame.State ctx :=
  RawCoherent.execS (returns := []) (modifier := false) (control := Solidity.Source.SCtx.body)
    (.expression step) (fuel+1) state

def after {ctx post}
    (step : LocalBoolControl.Supported ctx.env ctx.tys post)
    (resume : RawFrame.State ctx → Solidity.Source.R Unit × RawFrame.State ctx)
    (fuel : Nat) (state : RawFrame.State ctx) : Solidity.Source.R Unit × RawFrame.State ctx :=
  let next := discard step fuel state
  match next.1 with
  | .error halt => (.error halt,next.2)
  | .ok _ => resume next.2

def run {ctx returns modifier u condition post body}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (step : LocalBoolControl.Supported ctx.env ctx.tys post)
    (inside : RawSourceAdapter.Adapter ctx returns modifier u body)
    (fuel : Nat) (state : RawFrame.State ctx) : Solidity.Source.R Unit × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    let guard := RawCondition.eval test n state
    match guard.1 with
    | .error halt => (.error halt,guard.2)
    | .ok choice => if choice then
      let branch := inside.run n guard.2
      match branch.1 with
      | .error halt => (.error halt,branch.2)
      | .ok flow => match flow with
        | .normal | .continue_ _ => after step (run test step inside n) n branch.2
        | .break_ _ => (.ok (),branch.2)
        | .leave_ impossible => nomatch impossible
      else (.ok (),guard.2)

def sourceTail {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier u : Bool}
    (condition post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
    (body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (locals : Solidity.Source.Locals ctx.env.layout ctx.tys) :
    Solidity.Source.EM ctx.env [] (Solidity.Source.Out ctx.env.layout ctx.tys ctx.tys) := do
  let (_,next) ← Solidity.Source.EM.sub locals (Solidity.Source.evalE glob frame fuel post)
  Solidity.Source.forIter glob frame fuel nps ph (.some condition) (.some post) body next

theorem discard_correct : ∀ {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier u : Bool}
  {post : Solidity.Source.RExpr ctx.env ctx.tys .bool}
  (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
  (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
  (ph : Option (Solidity.Source.Ph ctx.env)) (state : Solidity.Yul.RawFrame.State ctx)
  (_same : Solidity.Yul.RawCoherent.coherent state = true),
  Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawSourceForPost.discard step fuel state).2 = true ∧
    (Solidity.Source.execS glob frame (fuel+1) nps ph
      (Solidity.Source.RStmt.expr (R := returns) (M := modifier) (k := ⟨true,u⟩) post) state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) =
        Solidity.Yul.RawSequence.represented (Solidity.Yul.RawSourceForPost.discard step fuel state) := by
  intro ctx returns modifier u post step glob frame fuel nps ph state same
  exact ⟨Solidity.Yul.RawCoherent.invariant (returns := returns) (modifier := modifier) (control := ⟨true,u⟩)
    (.expression step) glob frame (fuel+1) state same,
    Solidity.Yul.RawCoherent.source_run (returns := returns) (modifier := modifier) (control := ⟨true,u⟩)
      (.expression step) glob frame (fuel+1) nps ph state same⟩

theorem source_tail_step : ∀ {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier u : Bool}
  (condition post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
  (body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
  (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
  (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
  (state : Solidity.Yul.RawFrame.State ctx)
  (result : Solidity.Source.R Unit × Solidity.Yul.RawFrame.State ctx)
  (_actual : (Solidity.Source.execS glob frame (fuel+1) nps ph
    (Solidity.Source.RStmt.expr (R := returns) (M := modifier) (k := ⟨true,u⟩) post) state.clean).run
    (Solidity.Source.L0 ctx.env,state.world) = Solidity.Yul.RawSequence.represented result),
  (Solidity.Yul.RawSourceForPost.sourceTail condition post body glob frame fuel nps ph state.clean).run
    (Solidity.Source.L0 ctx.env,state.world) =
      match result.1 with
      | .error halt => Solidity.Yul.RawSequence.represented (.error halt,result.2)
      | .ok _ => (Solidity.Source.forIter glob frame fuel nps ph (.some condition) (.some post) body result.2.clean).run
          (Solidity.Source.L0 ctx.env,result.2.world) := by
  intro ctx returns modifier u condition post body glob frame fuel nps ph state result actual
  have shape : Solidity.Yul.RawSourceForPost.sourceTail condition post body glob frame fuel nps ph state.clean =
      (do
        let out ← Solidity.Source.execS glob frame (fuel+1) nps ph
          (Solidity.Source.RStmt.expr (R := returns) (M := modifier) (k := ⟨true,u⟩) post) state.clean
        match out with
        | .normal next => Solidity.Source.forIter glob frame fuel nps ph (.some condition) (.some post) body next
        | _ => Solidity.Source.EM.halt (.stuck "post flow")) := by
    simp only [Solidity.Yul.RawSourceForPost.sourceTail,Solidity.Source.execS,bind_assoc,pure_bind]
  rw [shape,Solidity.Source.Hoare.run_bind,actual]
  cases tag : result.1 with
  | error halt => simp only [Solidity.Yul.RawSequence.represented,tag,Except.map]
  | ok value =>
    simp only [Solidity.Yul.RawSequence.represented,tag,Except.map]

theorem source_error : ∀ {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier u : Bool}
  (condition post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
  (body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
  (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
  (ph : Option (Solidity.Source.Ph ctx.env))
  (state next : Solidity.Yul.RawFrame.State ctx) (halt : Solidity.Source.Halt)
  (_actual : (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
    (.error halt,(next.clean,next.world))),
  (Solidity.Source.forIter glob frame (fuel+1) nps ph (.some condition) (.some post) body state.clean).run
    (Solidity.Source.L0 ctx.env,state.world) =
      Solidity.Yul.RawSequence.represented (.error halt,next) := by
  intro ctx returns modifier u condition post body glob frame fuel nps ph state next halt actual
  rw [Solidity.Source.forIter]
  simp only [pure_bind]
  rw [Solidity.Source.Hoare.run_bind,
    Solidity.Yul.RawCondition.sub_error condition glob frame fuel state.clean next.clean state.world next.world halt actual]
  rfl

theorem source_choice : ∀ {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier u : Bool}
  (condition post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
  (body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
  (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
  (ph : Option (Solidity.Source.Ph ctx.env))
  (state next : Solidity.Yul.RawFrame.State ctx) (choice : Bool)
  (result : Solidity.Source.R Solidity.Yul.RawLoopBody.Flow × Solidity.Yul.RawFrame.State ctx)
  (_conditionRun : (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
    (.ok (.val (.bool choice)),(next.clean,next.world)))
  (_bodyRun : (Solidity.Source.execS glob frame fuel nps ph body next.clean).run
    (Solidity.Source.L0 ctx.env,next.world) = Solidity.Yul.RawLoopBody.represented result),
  (Solidity.Source.forIter glob frame (fuel+1) nps ph (.some condition) (.some post) body state.clean).run
    (Solidity.Source.L0 ctx.env,state.world) =
      if choice then
        match result.1 with
        | .error halt => Solidity.Yul.RawSequence.represented (.error halt,result.2)
        | .ok flow => match flow with
          | .normal | .continue_ _ =>
            (Solidity.Yul.RawSourceForPost.sourceTail condition post body glob frame fuel nps ph result.2.clean).run
              (Solidity.Source.L0 ctx.env,result.2.world)
          | .break_ _ => Solidity.Yul.RawSequence.represented (.ok (),result.2)
          | .leave_ impossible => nomatch impossible
      else Solidity.Yul.RawSequence.represented (.ok (),next) := by
  intro ctx returns modifier u condition post body glob frame fuel nps ph state next choice result conditionRun bodyRun
  rw [Solidity.Source.forIter]
  simp only [pure_bind]
  rw [Solidity.Source.Hoare.run_bind,
    Solidity.Yul.RawCondition.sub_bool condition glob frame fuel state.clean next.clean state.world next.world choice conditionRun]
  dsimp only
  rw [Solidity.Source.Hoare.run_bind]
  have getBool : (Solidity.Source.getV (E := ctx.env) (Γ := []) (.val (.bool choice))).run
      (Solidity.Source.L0 ctx.env,next.world) =
      (.ok (.bool choice),(Solidity.Source.L0 ctx.env,next.world)) := by rfl
  rw [getBool]
  cases choice with
  | false => rfl
  | true =>
    simp only [Bool.not_true,Bool.false_eq_true,if_false,if_true]
    rw [Solidity.Source.Hoare.run_bind,bodyRun]
    cases tag : result.1 with
    | error halt => simp only [Solidity.Yul.RawLoopBody.represented,Solidity.Yul.RawSequence.represented,tag,Except.map]
    | ok flow =>
      cases flow with
      | normal =>
        simp only [Solidity.Yul.RawLoopBody.represented,tag,Except.map,Solidity.Yul.RawLoopBody.out,
          Solidity.Yul.RawSequence.restore_self,Solidity.Source.EM.lift,pure_bind]
        rfl
      | continue_ h =>
        simp only [Solidity.Yul.RawLoopBody.represented,tag,Except.map,Solidity.Yul.RawLoopBody.out]
        rfl
      | break_ h =>
        simp only [Solidity.Yul.RawLoopBody.represented,tag,Except.map,Solidity.Yul.RawLoopBody.out,
          Solidity.Yul.RawSequence.represented]
        rfl
      | leave_ h => cases h

theorem after_correct : ∀ {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier u : Bool}
  (condition post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
  (body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
  (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
  (resume : Solidity.Yul.RawFrame.State ctx → Solidity.Source.R Unit × Solidity.Yul.RawFrame.State ctx)
  (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
  (ph : Option (Solidity.Source.Ph ctx.env))
  (_law : ∀ next : Solidity.Yul.RawFrame.State ctx, Solidity.Yul.RawCoherent.coherent next = true →
    Solidity.Yul.RawCoherent.coherent (resume next).2 = true ∧
      (Solidity.Source.forIter glob frame fuel nps ph (.some condition) (.some post) body next.clean).run
        (Solidity.Source.L0 ctx.env,next.world) = Solidity.Yul.RawSequence.represented (resume next))
  (state : Solidity.Yul.RawFrame.State ctx) (_same : Solidity.Yul.RawCoherent.coherent state = true),
  Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawSourceForPost.after step resume fuel state).2 = true ∧
    (Solidity.Yul.RawSourceForPost.sourceTail condition post body glob frame fuel nps ph state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) =
        Solidity.Yul.RawSequence.represented (Solidity.Yul.RawSourceForPost.after step resume fuel state) := by
  intro ctx returns modifier u condition post body step resume glob frame fuel nps ph law state same
  have part := Solidity.Yul.RawSourceForPost.discard_correct (returns := returns) (modifier := modifier) (u := u)
    step glob frame fuel nps ph state same
  have actual := Solidity.Yul.RawSourceForPost.source_tail_step condition post body glob frame fuel nps ph
    state (Solidity.Yul.RawSourceForPost.discard step fuel state) part.2
  cases tag : (Solidity.Yul.RawSourceForPost.discard step fuel state).1 with
  | error halt =>
    simp only [Solidity.Yul.RawSourceForPost.after,tag] at actual ⊢
    exact ⟨part.1,actual⟩
  | ok value =>
    have done := law (Solidity.Yul.RawSourceForPost.discard step fuel state).2 part.1
    simp only [Solidity.Yul.RawSourceForPost.after,tag]
    simp only [tag] at actual
    rw [actual]
    exact done

theorem correct : ∀ {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier u : Bool}
  {condition post : Solidity.Source.RExpr ctx.env ctx.tys .bool}
  {body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys}
  (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
  (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
  (inside : Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u body)
  (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
  (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
  (state : Solidity.Yul.RawFrame.State ctx) (_same : Solidity.Yul.RawCoherent.coherent state = true),
  Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawSourceForPost.run test step inside fuel state).2 = true ∧
    (Solidity.Source.forIter glob frame fuel nps ph (.some condition) (.some post) body state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) =
        Solidity.Yul.RawSequence.represented (Solidity.Yul.RawSourceForPost.run test step inside fuel state) := by
  intro ctx returns modifier u condition post body test step inside glob frame fuel nps ph state same
  induction fuel generalizing state with
  | zero => exact ⟨same,rfl⟩
  | succ fuel ih =>
    have conditionRun := Solidity.Yul.RawCondition.source_eval test glob frame fuel state same
    cases actual : (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) with
    | mk tag next =>
      rcases next with ⟨locals,world⟩
      rw [actual] at conditionRun
      let nextFrame : Solidity.Yul.RawFrame.State ctx :=
        Solidity.Yul.RawCoherent.capture state (Solidity.Yul.LocalState.ofClean (locals,world))
      have nextSame : Solidity.Yul.RawCoherent.coherent nextFrame = true :=
        Solidity.Yul.RawCoherent.capture_coherent state locals world
      have nextClean : nextFrame.clean = locals := by
        simp only [nextFrame,Solidity.Yul.RawCoherent.capture,Solidity.Yul.LocalState.ofClean,
          Solidity.Yul.LocalValues.clean_ofClean,Option.getD_some]
      cases tag with
      | error halt =>
        change Solidity.Yul.RawCondition.eval test fuel state = (.error halt,nextFrame) at conditionRun
        have sourceCondition :
            (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
              (.error halt,(nextFrame.clean,nextFrame.world)) := by
          rw [nextClean]
          exact actual
        simp only [Solidity.Yul.RawSourceForPost.run,conditionRun]
        exact ⟨nextSame,Solidity.Yul.RawSourceForPost.source_error condition post body
          glob frame fuel nps ph state nextFrame halt sourceCondition⟩
      | ok value =>
        cases value with
        | val value =>
          cases value with
          | bool choice =>
            have branch := inside.correct glob frame fuel nps ph nextFrame nextSame
            have sourceCondition :
                (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                  (.ok (.val (.bool choice)),(nextFrame.clean,nextFrame.world)) := by
              rw [nextClean]
              exact actual
            have selected := Solidity.Yul.RawSourceForPost.source_choice condition post body
              glob frame fuel nps ph state nextFrame choice (inside.run fuel nextFrame) sourceCondition branch.2
            cases choice with
            | false =>
              change Solidity.Yul.RawCondition.eval test fuel state = (.ok false,nextFrame) at conditionRun
              simp only [Solidity.Yul.RawSourceForPost.run,conditionRun,Bool.false_eq_true,if_false]
              exact ⟨nextSame,selected⟩
            | true =>
              change Solidity.Yul.RawCondition.eval test fuel state = (.ok true,nextFrame) at conditionRun
              simp only [Solidity.Yul.RawSourceForPost.run,conditionRun,if_true]
              rw [selected]
              cases bodyTag : (inside.run fuel nextFrame).1 with
              | error halt => exact ⟨branch.1,rfl⟩
              | ok flow =>
                cases flow with
                | normal =>
                  exact Solidity.Yul.RawSourceForPost.after_correct condition post body step
                    (Solidity.Yul.RawSourceForPost.run test step inside fuel)
                    glob frame fuel nps ph ih (inside.run fuel nextFrame).2 branch.1
                | continue_ h =>
                  exact Solidity.Yul.RawSourceForPost.after_correct condition post body step
                    (Solidity.Yul.RawSourceForPost.run test step inside fuel)
                    glob frame fuel nps ph ih (inside.run fuel nextFrame).2 branch.1
                | break_ h => exact ⟨branch.1,rfl⟩
                | leave_ h => cases h
          | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible

end Solidity.Yul.RawSourceForPost

/-! Initialized same-context forLoop with a present Boolean post. -/

namespace Solidity.Yul.RawSourceForPost.Initialized

def run {ctx returns modifier u initial condition post body}
    (initializer : RawSourceAdapter.Adapter ctx returns modifier u initial)
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (step : LocalBoolControl.Supported ctx.env ctx.tys post)
    (inside : RawSourceAdapter.Adapter ctx returns modifier u body)
    (fuel : Nat) (state : RawFrame.State ctx) : Solidity.Source.R Unit × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    let first := initializer.run n state
    match first.1 with
    | .error halt => (.error halt,first.2)
    | .ok flow => match flow with
      | .normal => RawSourceForPost.run test step inside n first.2
      | .break_ _ | .continue_ _ => (.error (.stuck "for initializer"),first.2)
      | .leave_ impossible => nomatch impossible

theorem source_step : ∀ {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier u l : Bool}
  {init body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys}
  (condition post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
  (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
  (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env)) (state : Solidity.Yul.RawFrame.State ctx)
  (first : Solidity.Source.R Solidity.Yul.RawLoopBody.Flow × Solidity.Yul.RawFrame.State ctx)
  (second : Solidity.Source.R Unit × Solidity.Yul.RawFrame.State ctx)
  (_initRun : (Solidity.Source.execS glob frame fuel nps ph init state.clean).run
    (Solidity.Source.L0 ctx.env,state.world) = Solidity.Yul.RawLoopBody.represented first)
  (_iterRun : (Solidity.Source.forIter glob frame fuel nps ph (.some condition) (.some post) body first.2.clean).run
    (Solidity.Source.L0 ctx.env,first.2.world) = Solidity.Yul.RawSequence.represented second),
  (Solidity.Source.execS glob frame (fuel+1) nps ph
    (Solidity.Source.RStmt.forLoop (l := l) init (.some condition) (.some post) body) state.clean).run
    (Solidity.Source.L0 ctx.env,state.world) =
      match first.1 with
      | .error halt => Solidity.Yul.RawSequence.represented (.error halt,first.2)
      | .ok flow => match flow with
        | .normal => Solidity.Yul.RawSequence.represented second
        | .break_ _ | .continue_ _ =>
          Solidity.Yul.RawSequence.represented (.error (.stuck "for initializer"),first.2)
        | .leave_ impossible => nomatch impossible := by
  intro ctx returns modifier u l init body condition post glob frame fuel nps ph state first second initRun iterRun
  rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,initRun]
  cases tag : first.1 with
  | error halt =>
    simp only [Solidity.Yul.RawLoopBody.represented,Solidity.Yul.RawSequence.represented,tag,Except.map]
  | ok flow =>
    cases flow with
    | normal =>
      simp only [Solidity.Yul.RawLoopBody.represented,tag,Except.map,Solidity.Yul.RawLoopBody.out]
      rw [Solidity.Source.Hoare.run_bind,iterRun]
      cases doneTag : second.1 with
      | error halt => simp only [Solidity.Yul.RawSequence.represented,doneTag,Except.map]
      | ok value =>
        simp only [Solidity.Yul.RawSequence.represented,doneTag,Except.map,
          Solidity.Yul.RawSequence.restore_self,Solidity.Source.EM.lift,pure_bind]
        rfl
    | break_ h | continue_ h =>
      simp only [Solidity.Yul.RawLoopBody.represented,tag,Except.map,Solidity.Yul.RawLoopBody.out,
        Solidity.Yul.RawSequence.represented]
      rfl
    | leave_ h => cases h

/-- Final Source correspondence; both step premises come from actual producers. -/
theorem correct : ∀ {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier u l : Bool}
  {initial body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys}
  {condition post : Solidity.Source.RExpr ctx.env ctx.tys .bool}
  (initializer : Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u initial)
  (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
  (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
  (inside : Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u body)
  (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
  (ph : Option (Solidity.Source.Ph ctx.env)) (state : Solidity.Yul.RawFrame.State ctx)
  (_same : Solidity.Yul.RawCoherent.coherent state = true),
  Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawSourceForPost.Initialized.run initializer test step inside fuel state).2 = true ∧
    (Solidity.Source.execS glob frame fuel nps ph
      (Solidity.Source.RStmt.forLoop (l := l) initial (.some condition) (.some post) body) state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) =
        Solidity.Yul.RawSequence.represented (Solidity.Yul.RawSourceForPost.Initialized.run initializer test step inside fuel state) := by
  intro ctx returns modifier u l initial body condition post initializer test step inside glob frame fuel nps ph state same
  cases fuel with
  | zero => exact ⟨same,rfl⟩
  | succ fuel =>
    have first := initializer.correct glob frame fuel nps ph state same
    have second := Solidity.Yul.RawSourceForPost.correct test step inside glob frame fuel nps ph
      (initializer.run fuel state).2 first.1
    have actual := Solidity.Yul.RawSourceForPost.Initialized.source_step (l := l) condition post glob frame fuel nps ph state
      (initializer.run fuel state) (Solidity.Yul.RawSourceForPost.run test step inside fuel (initializer.run fuel state).2)
      first.2 second.2
    cases tag : (initializer.run fuel state).1 with
    | error halt =>
      simp only [Solidity.Yul.RawSourceForPost.Initialized.run,tag] at actual ⊢
      exact ⟨first.1,actual⟩
    | ok flow =>
      cases flow with
      | normal =>
        simp only [Solidity.Yul.RawSourceForPost.Initialized.run,tag] at actual ⊢
        exact ⟨second.1,actual⟩
      | break_ h | continue_ h =>
        simp only [Solidity.Yul.RawSourceForPost.Initialized.run,tag] at actual ⊢
        exact ⟨first.1,actual⟩
      | leave_ h => cases h

/-- Package the actual checked forLoop for further intrinsic Source composition. -/
def adapter : ∀ {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier u : Bool}
  {initial body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys}
  {condition post : Solidity.Source.RExpr ctx.env ctx.tys .bool}
  (_initializer : Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u initial)
  (_test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
  (_step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
  (_inside : Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u body),
  Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u
    (Solidity.Source.RStmt.forLoop (l := true) initial (.some condition) (.some post) body) := by
  intro ctx returns modifier u initial body condition post initializer test step inside
  exact {
    run := fun fuel state =>
      let actual := Solidity.Yul.RawSourceForPost.Initialized.run initializer test step inside fuel state
      (actual.1.map (fun _ => .normal),actual.2)
    correct := fun glob frame fuel nps ph state same => by
      simp only [Solidity.Yul.RawLoopBody.plain_represented,and_self,
        (Solidity.Yul.RawSourceForPost.Initialized.correct (l := true) initializer test step inside
          glob frame fuel nps ph state same).1,
        (Solidity.Yul.RawSourceForPost.Initialized.correct (l := true) initializer test step inside
          glob frame fuel nps ph state same).2]
  }

end Solidity.Yul.RawSourceForPost.Initialized

/-! Absent-condition transport at the exact Source horizon. -/
namespace Solidity.Yul.RawSourceForPost.Absent

theorem source_true : ∀ {env : Solidity.Source.Env} {returns : List Solidity.Source.STy} {modifier u : Bool}
 {ctx after : Solidity.Source.RCtx}
 (post : Solidity.Source.ROptExpr env ctx)
 (body : Solidity.Source.RStmt env returns modifier ⟨true,u⟩ ctx after)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph env)) (locals : Solidity.Source.Locals env.layout ctx),
 Solidity.Source.forIter glob frame fuel nps ph .none post body locals =
 Solidity.Source.forIter glob frame fuel nps ph (.some (.bool true)) post body locals := by
  intro env returns modifier u ctx after post body glob frame fuel nps ph locals
  induction fuel generalizing locals with
  | zero => rfl
  | succ fuel ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      conv => lhs; rw [Solidity.Source.forIter]
      conv => rhs; rw [Solidity.Source.forIter]
      change (Solidity.Source.execS glob frame (fuel+1) nps ph body locals >>= _) =
        (Solidity.Source.execS glob frame (fuel+1) nps ph body locals >>= _)
      apply congrArg (fun cont : Solidity.Source.Out env.layout ctx after →
        Solidity.Source.EM env [] (Solidity.Source.Out env.layout ctx ctx) =>
        Solidity.Source.execS glob frame (fuel+1) nps ph body locals >>= cont)
      funext outcome
      cases outcome <;> simp only [pure_bind,ih]

end Solidity.Yul.RawSourceForPost.Absent

namespace Solidity.Yul.RawSourceForPost.Absent

theorem source_initialized : ∀ {env : Solidity.Source.Env} {returns : List Solidity.Source.STy} {modifier u l : Bool}
 {ctx mid after : Solidity.Source.RCtx}
 (initial : Solidity.Source.RStmt env returns modifier ⟨true,u⟩ ctx mid)
 (post : Solidity.Source.ROptExpr env mid)
 (body : Solidity.Source.RStmt env returns modifier ⟨true,u⟩ mid after)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph env)) (locals : Solidity.Source.Locals env.layout ctx),
 Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.forLoop (l := l) initial .none post body) locals =
 Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.forLoop (l := l) initial (.some (.bool true)) post body) locals := by
  intro env returns modifier u l ctx mid after initial post body glob frame fuel nps ph locals
  cases fuel with
  | zero => rfl
  | succ fuel =>
    conv => lhs; rw [Solidity.Source.execS]
    conv => rhs; rw [Solidity.Source.execS]
    simp only [Solidity.Yul.RawSourceForPost.Absent.source_true]

end Solidity.Yul.RawSourceForPost.Absent

namespace Solidity.Yul.RawSourceForPost.Absent

/-- Reuse an actual literal-true producer; runtime and coherence are unchanged. -/
def adapter : ∀ {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier u : Bool}
 {initial body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys}
 {post : Solidity.Source.ROptExpr ctx.env ctx.tys},
 Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u
   (Solidity.Source.RStmt.forLoop (l := true) initial (.some (.bool true)) post body) →
 Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u
   (Solidity.Source.RStmt.forLoop (l := true) initial .none post body) := by
  intro ctx returns modifier u initial body post producer
  exact {
    run := producer.run
    correct := fun glob frame fuel nps ph state same => by
      simpa only [Solidity.Yul.RawSourceForPost.Absent.source_initialized] using
        producer.correct glob frame fuel nps ph state same
  }

end Solidity.Yul.RawSourceForPost.Absent
