import Solidity.Yul.RawSourceForIter

/-! Actual Source forLoop with a same-context initializer, present condition and no post.
Initializer errors retain partial state; control exits are refused as Source specifies.
This extends the local raw adapter without changing Source types or evaluation. -/
namespace Solidity.Yul.RawSourceAdapterFor

def run {ctx returns modifier u initial condition body}
    (initializer : RawSourceAdapter.Adapter ctx returns modifier u initial)
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (inside : RawSourceAdapter.Adapter ctx returns modifier u body)
    (fuel : Nat) (state : RawFrame.State ctx) : Solidity.Source.R Unit × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    let first := initializer.run n state
    match first.1 with
    | .error halt => (.error halt,first.2)
    | .ok flow => match flow with
      | .normal => RawSourceAdapterLoop.run test inside n first.2
      | .break_ _ | .continue_ _ => (.error (.stuck "for initializer"),first.2)
      | .leave_ impossible => nomatch impossible

theorem source_step : ∀ {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier u l : Bool}
  {init body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys}
  (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
  (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
  (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env)) (state : Solidity.Yul.RawFrame.State ctx)
  (first : Solidity.Source.R Solidity.Yul.RawLoopBody.Flow × Solidity.Yul.RawFrame.State ctx)
  (second : Solidity.Source.R Unit × Solidity.Yul.RawFrame.State ctx)
  (_initRun : (Solidity.Source.execS glob frame fuel nps ph init state.clean).run
    (Solidity.Source.L0 ctx.env,state.world) = Solidity.Yul.RawLoopBody.represented first)
  (_iterRun : (Solidity.Source.forIter glob frame fuel nps ph (.some condition) .none body first.2.clean).run
    (Solidity.Source.L0 ctx.env,first.2.world) = Solidity.Yul.RawSequence.represented second),
  (Solidity.Source.execS glob frame (fuel+1) nps ph
    (Solidity.Source.RStmt.forLoop (l := l) init (.some condition) .none body) state.clean).run
    (Solidity.Source.L0 ctx.env,state.world) =
      match first.1 with
      | .error halt => Solidity.Yul.RawSequence.represented (.error halt,first.2)
      | .ok flow => match flow with
        | .normal => Solidity.Yul.RawSequence.represented second
        | .break_ _ | .continue_ _ =>
          Solidity.Yul.RawSequence.represented (.error (.stuck "for initializer"),first.2)
        | .leave_ impossible => nomatch impossible := by
  intro ctx returns modifier u l init body condition glob frame fuel nps ph state first second initRun iterRun
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
  {condition : Solidity.Source.RExpr ctx.env ctx.tys .bool}
  (initializer : Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u initial)
  (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
  (inside : Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u body)
  (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
  (ph : Option (Solidity.Source.Ph ctx.env)) (state : Solidity.Yul.RawFrame.State ctx)
  (_same : Solidity.Yul.RawCoherent.coherent state = true),
  Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawSourceAdapterFor.run initializer test inside fuel state).2 = true ∧
    (Solidity.Source.execS glob frame fuel nps ph
      (Solidity.Source.RStmt.forLoop (l := l) initial (.some condition) .none body) state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) =
        Solidity.Yul.RawSequence.represented (Solidity.Yul.RawSourceAdapterFor.run initializer test inside fuel state) := by
  intro ctx returns modifier u l initial body condition initializer test inside glob frame fuel nps ph state same
  cases fuel with
  | zero => exact ⟨same,rfl⟩
  | succ fuel =>
    have first := initializer.correct glob frame fuel nps ph state same
    have second := Solidity.Yul.RawSourceForIter.correct test inside glob frame fuel nps ph
      (initializer.run fuel state).2 first.1
    have actual := Solidity.Yul.RawSourceAdapterFor.source_step (l := l) condition glob frame fuel nps ph state
      (initializer.run fuel state) (Solidity.Yul.RawSourceAdapterLoop.run test inside fuel (initializer.run fuel state).2)
      first.2 second.2
    cases tag : (initializer.run fuel state).1 with
    | error halt =>
      simp only [Solidity.Yul.RawSourceAdapterFor.run,tag] at actual ⊢
      exact ⟨first.1,actual⟩
    | ok flow =>
      cases flow with
      | normal =>
        simp only [Solidity.Yul.RawSourceAdapterFor.run,tag] at actual ⊢
        exact ⟨second.1,actual⟩
      | break_ h | continue_ h =>
        simp only [Solidity.Yul.RawSourceAdapterFor.run,tag] at actual ⊢
        exact ⟨first.1,actual⟩
      | leave_ h => cases h

/-- Package the actual checked forLoop for further intrinsic Source composition. -/
def adapter : ∀ {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier u : Bool}
  {initial body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys}
  {condition : Solidity.Source.RExpr ctx.env ctx.tys .bool}
  (_initializer : Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u initial)
  (_test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
  (_inside : Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u body),
  Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u
    (Solidity.Source.RStmt.forLoop (l := true) initial (.some condition) .none body) := by
  intro ctx returns modifier u initial body condition initializer test inside
  exact {
    run := fun fuel state =>
      let actual := Solidity.Yul.RawSourceAdapterFor.run initializer test inside fuel state
      (actual.1.map (fun _ => .normal),actual.2)
    correct := fun glob frame fuel nps ph state same => by
      simp only [Solidity.Yul.RawLoopBody.plain_represented,and_self,
        (Solidity.Yul.RawSourceAdapterFor.correct (l := true) initializer test inside
          glob frame fuel nps ph state same).1,
        (Solidity.Yul.RawSourceAdapterFor.correct (l := true) initializer test inside
          glob frame fuel nps ph state same).2]
  }

end Solidity.Yul.RawSourceAdapterFor
