import Solidity.Yul.RawCheckedForPost

/-! Same-context checked initializer plus present-condition/boolean-post Source
for composition. Control errors retain actual initializer frames. This does
not supply context-growing declarations or general assembly admission. -/
namespace Solidity.Yul.RawCheckedInitializedForPost

def run {ctx returns modifier u initial condition post body}
    (initializer : RawCheckedAdapter.Adapter ctx returns modifier u initial)
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (step : LocalBoolControl.Supported ctx.env ctx.tys post)
    (inside : RawCheckedAdapter.Adapter ctx returns modifier u body)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) : Solidity.Source.R Unit × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    let first := initializer.run pipeline n state
    match first.1 with
    | .error halt => (.error halt,first.2)
    | .ok flow => match flow with
      | .normal => RawCheckedForPost.run test step inside pipeline n first.2
      | .break_ _ | .continue_ _ => (.error (.stuck "for initializer"),first.2)
      | .leave_ impossible => nomatch impossible

end Solidity.Yul.RawCheckedInitializedForPost

namespace Solidity.Yul.RawCheckedInitializedForPost
theorem correct : ∀ {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier u l : Bool}
  {initial body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys}
  {condition post : Solidity.Source.RExpr ctx.env ctx.tys .bool}
  (initializer : Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u initial)
  (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
  (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
  (inside : Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u body)
  (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (checked : frame.checked = true) (fuel nps : Nat)
  (ph : Option (Solidity.Source.Ph ctx.env)) (state : Solidity.Yul.RawFrame.State ctx)
  (_same : Solidity.Yul.RawCoherent.coherent state = true),
  Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedInitializedForPost.run initializer test step inside glob.pipeline fuel state).2 = true ∧
    (Solidity.Source.execS glob frame fuel nps ph
      (Solidity.Source.RStmt.forLoop (l := l) initial (.some condition) (.some post) body) state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) =
        Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedInitializedForPost.run initializer test step inside glob.pipeline fuel state) := by
  intro ctx returns modifier u l initial body condition post initializer test step inside glob frame checked fuel nps ph state same
  cases fuel with
  | zero => exact ⟨same,rfl⟩
  | succ fuel =>
    have first := initializer.correct glob frame checked fuel nps ph state same
    have second := Solidity.Yul.RawCheckedForPost.correct test step inside glob frame checked fuel nps ph
      (initializer.run glob.pipeline fuel state).2 first.1
    have actual := Solidity.Yul.RawSourceForPost.Initialized.source_step (l := l) condition post glob frame fuel nps ph state
      (initializer.run glob.pipeline fuel state) (Solidity.Yul.RawCheckedForPost.run test step inside glob.pipeline fuel (initializer.run glob.pipeline fuel state).2)
      first.2 second.2
    cases tag : (initializer.run glob.pipeline fuel state).1 with
    | error halt =>
      simp only [Solidity.Yul.RawCheckedInitializedForPost.run,tag] at actual ⊢
      exact ⟨first.1,actual⟩
    | ok flow =>
      cases flow with
      | normal =>
        simp only [Solidity.Yul.RawCheckedInitializedForPost.run,tag] at actual ⊢
        exact ⟨second.1,actual⟩
      | break_ h | continue_ h =>
        simp only [Solidity.Yul.RawCheckedInitializedForPost.run,tag] at actual ⊢
        exact ⟨first.1,actual⟩
      | leave_ h => cases h
end Solidity.Yul.RawCheckedInitializedForPost

namespace Solidity.Yul.RawCheckedInitializedForPost
def adapter : ∀ {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier u : Bool}
  {initial body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys}
  {condition post : Solidity.Source.RExpr ctx.env ctx.tys .bool}
  (_initializer : Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u initial)
  (_test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
  (_step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
  (_inside : Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u body),
  Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u
    (Solidity.Source.RStmt.forLoop (l := true) initial (.some condition) (.some post) body) := by
  intro ctx returns modifier u initial body condition post initializer test step inside
  exact {
    run := fun pipeline fuel state =>
      let actual := run initializer test step inside pipeline fuel state
      (actual.1.map (fun _ => .normal),actual.2)
    correct := fun glob frame checked fuel nps ph state same => by
      simpa only [RawLoopBody.plain_represented] using
        (correct (l := true) initializer test step inside glob frame checked fuel nps ph state same)
  }
end Solidity.Yul.RawCheckedInitializedForPost
