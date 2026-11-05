import Solidity.Yul.RawGrowingBlock
import Solidity.Yul.RawControlDeclaration
import Solidity.Yul.RawCheckedForPost

/-! Growing checked for/post composition with an actual supported Boolean
initializer expression. The initializer's partial state, iteration and scope
restoration are joined concretely; Source agreement retains checked/coherent
premises. This does not cover arbitrary initializer types or admission. -/
namespace Solidity.Yul.RawControlForPost

def run {ctx returns modifier u name initializer condition post body}
    (initial : LocalBoolControl.Supported ctx.env ctx.tys initializer)
    (test : LocalBoolControl.Supported ctx.env (ctx.push name .bool).tys condition)
    (step : LocalBoolControl.Supported ctx.env (ctx.push name .bool).tys post)
    (inside : RawCheckedAdapter.Adapter (ctx.push name .bool) returns modifier u body)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R Unit × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    match RawControlDeclaration.run name initial n state with
    | .inl failure => (.error failure.1,failure.2)
    | .inr next =>
      let result := RawCheckedForPost.run test step inside pipeline n next
      (result.1,RawGrowingBlock.drop result.2)

end Solidity.Yul.RawControlForPost

namespace Solidity.Yul.RawControlForPost
theorem correct : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (returns : List Solidity.Source.STy) (modifier u l : Bool)
 (initializer : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (initial : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys initializer)
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
   (Solidity.Yul.RawControlForPost.run initial test step inside glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.forLoop (l := l)
     (Solidity.Source.RStmt.declInit (E := ctx.env) (R := returns) (M := modifier)
       (k := ⟨true,u⟩) (Γ := ctx.tys) (τ := .bool) initializer (by rfl))
     (.some condition) (.some post) body) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawSequence.represented
   (Solidity.Yul.RawControlForPost.run initial test step inside glob.pipeline fuel state) := by
  intro ctx name returns modifier u l initializer initial condition post body test step inside glob frame checked fuel nps ph state same
  cases fuel with
  | zero => exact ⟨same,rfl⟩
  | succ fuel =>
    have first := RawControlDeclaration.correct ctx name initializer initial returns modifier
      ⟨true,u⟩ glob frame fuel nps ph state same
    cases actual : RawControlDeclaration.run name initial fuel state with
    | inl failure =>
      rcases failure with ⟨halt,next⟩
      rw [actual] at first
      simp only [run,actual]
      constructor
      · exact first.1
      · rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,first.2]
        rfl
    | inr next =>
      rw [actual] at first
      have second := RawCheckedForPost.correct test step inside glob frame checked fuel nps ph next first.1
      simp only [run,actual]
      generalize iterationEq : RawCheckedForPost.run test step inside glob.pipeline fuel next = iteration at second ⊢
      constructor
      · exact RawGrowingBlock.drop_coherent ctx name iteration.2 second.1
      · rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,first.2]
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
end Solidity.Yul.RawControlForPost

namespace Solidity.Yul.RawControlForPost
def adapter : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (returns : List Solidity.Source.STy) (modifier u : Bool)
 (initializer : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (_initial : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys initializer)
 (condition post : Solidity.Source.RExpr ctx.env (ctx.push name .bool).tys .bool)
 (body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩
   (ctx.push name .bool).tys (ctx.push name .bool).tys)
 (_test : Solidity.Yul.LocalBoolControl.Supported ctx.env (ctx.push name .bool).tys condition)
 (_step : Solidity.Yul.LocalBoolControl.Supported ctx.env (ctx.push name .bool).tys post)
 (_inside : Solidity.Yul.RawCheckedAdapter.Adapter (ctx.push name .bool) returns modifier u body),
 Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u
 (Solidity.Source.RStmt.forLoop (l := true)
     (Solidity.Source.RStmt.declInit (E := ctx.env) (R := returns) (M := modifier)
       (k := ⟨true,u⟩) (Γ := ctx.tys) (τ := .bool) initializer (by rfl))
     (.some condition) (.some post) body) := by
  intro ctx name returns modifier u initializer initial condition post body test step inside
  exact {
    run := fun pipeline fuel state =>
      let actual := run initial test step inside pipeline fuel state
      (actual.1.map (fun _ => .normal),actual.2)
    correct := fun glob frame checked fuel nps ph state same => by
      simpa only [RawLoopBody.plain_represented] using
        (correct ctx name returns modifier u true initializer initial condition post body test step inside
          glob frame checked fuel nps ph state same)
  }
end Solidity.Yul.RawControlForPost
