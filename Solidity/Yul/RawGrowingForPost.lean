import Solidity.Yul.RawGrowingBlock
import Solidity.Yul.RawCheckedForPost

/-! Checked Source for execution with one growing Boolean literal initializer
and present Boolean condition/post. Iteration uses the existing concrete
producer; scope exit removes only that binder. No general initializer,
declaration-group or frontend admission claim. -/
namespace Solidity.Yul.RawGrowingForPost

def run {ctx returns modifier u name condition post body} (value : Bool)
    (test : LocalBoolControl.Supported ctx.env (ctx.push name .bool).tys condition)
    (step : LocalBoolControl.Supported ctx.env (ctx.push name .bool).tys post)
    (inside : RawCheckedAdapter.Adapter (ctx.push name .bool) returns modifier u body)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R Unit × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    match RawPreparedDeclaration.run name value n state with
    | .inl failure => (.error failure.1,failure.2)
    | .inr next =>
      let result := RawCheckedForPost.run test step inside pipeline n next
      (result.1,RawGrowingBlock.drop result.2)

end Solidity.Yul.RawGrowingForPost

namespace Solidity.Yul.RawGrowingForPost
theorem correct : ∀ (ctx : Solidity.Source.Ctx) (name : String) (value : Bool)
 (returns : List Solidity.Source.STy) (modifier u l : Bool)
 (condition post : Solidity.Source.RExpr ctx.env (ctx.push name .bool).tys .bool)
 (body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩
   (ctx.push name .bool).tys (ctx.push name .bool).tys)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env (ctx.push name .bool).tys condition)
 (step : Solidity.Yul.LocalBoolControl.Supported ctx.env (ctx.push name .bool).tys post)
 (inside : Solidity.Yul.RawCheckedAdapter.Adapter (ctx.push name .bool) returns modifier u body)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent
   (Solidity.Yul.RawGrowingForPost.run value test step inside glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.forLoop (l := l)
     (Solidity.Source.RStmt.declInit (E := ctx.env) (R := returns) (M := modifier)
       (k := ⟨true,u⟩) (Γ := ctx.tys) (τ := .bool) (.bool value) (by rfl))
     (.some condition) (.some post) body) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawSequence.represented
   (Solidity.Yul.RawGrowingForPost.run value test step inside glob.pipeline fuel state) := by
  intro ctx name value returns modifier u l condition post body test step inside glob frame checked fuel nps ph state same
  cases fuel with
  | zero => exact ⟨same,rfl⟩
  | succ fuel =>
    have first := RawPreparedDeclaration.source_correct ctx name value returns modifier
      ⟨true,u⟩ glob frame fuel nps ph state
    have coherent := RawPreparedDeclaration.coherent_result ctx name value fuel state same
    cases actual : RawPreparedDeclaration.run name value fuel state with
    | inl failure =>
      rcases failure with ⟨halt,next⟩
      rw [actual] at first coherent
      simp only [run,actual]
      constructor
      · exact coherent
      · rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,first]
        rfl
    | inr next =>
      rw [actual] at first coherent
      have second := RawCheckedForPost.correct test step inside glob frame checked fuel nps ph next coherent
      simp only [run,actual]
      generalize iterationEq : RawCheckedForPost.run test step inside glob.pipeline fuel next = iteration at second ⊢
      constructor
      · exact RawGrowingBlock.drop_coherent ctx name iteration.2 second.1
      · rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,first]
        dsimp only [RawDeclarationFrame.project]
        rw [Solidity.Source.Hoare.run_bind,second.2]
        cases tag : iteration.1 with
        | error halt =>
          simp only [RawSequence.represented,tag,Except.map]
          rfl
        | ok _value =>
          simp only [RawSequence.represented,tag,Except.map]
          rw [Solidity.Source.Hoare.run_bind,RawGrowingSequence.lift_run,
            RawGrowingBlock.restore_drop ctx name]
          rfl
end Solidity.Yul.RawGrowingForPost

namespace Solidity.Yul.RawGrowingForPost
def adapter : ∀ (ctx : Solidity.Source.Ctx) (name : String) (value : Bool)
 (returns : List Solidity.Source.STy) (modifier u : Bool)
 (condition post : Solidity.Source.RExpr ctx.env (ctx.push name .bool).tys .bool)
 (body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩
   (ctx.push name .bool).tys (ctx.push name .bool).tys)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env (ctx.push name .bool).tys condition)
 (step : Solidity.Yul.LocalBoolControl.Supported ctx.env (ctx.push name .bool).tys post)
 (inside : Solidity.Yul.RawCheckedAdapter.Adapter (ctx.push name .bool) returns modifier u body),
 Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u
 (Solidity.Source.RStmt.forLoop (l := true)
     (Solidity.Source.RStmt.declInit (E := ctx.env) (R := returns) (M := modifier)
       (k := ⟨true,u⟩) (Γ := ctx.tys) (τ := .bool) (.bool value) (by rfl))
     (.some condition) (.some post) body) := by
  intro ctx name value returns modifier u condition post body test step inside
  exact {
    run := fun pipeline fuel state =>
      let actual := run value test step inside pipeline fuel state
      (actual.1.map (fun _ => .normal),actual.2)
    correct := fun glob frame checked fuel nps ph state same => by
      simpa only [RawLoopBody.plain_represented] using
        (correct ctx name value returns modifier u true condition post body test step inside
          glob frame checked fuel nps ph state same)
  }
end Solidity.Yul.RawGrowingForPost
