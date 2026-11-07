import Solidity.Yul.RawTypedScope
import Solidity.Yul.RawU8Declaration
import Solidity.Yul.RawCheckedAdapterLoop
import Solidity.Yul.RawSourceForIter

/-! Growing checked no-post for composition with an actual supported uint8
initializer expression. The initializer's partial state, no-post iteration and scope
restoration are joined concretely; Source agreement retains checked/coherent
premises. This does not cover arbitrary initializer types or admission. -/
namespace Solidity.Yul.RawU8For

def run {ctx returns modifier u name initializer condition body}
    (initial : LocalU8Expr.Supported ctx.env ctx.tys initializer)
    (test : LocalBoolControl.Supported ctx.env (ctx.push name LocalU8Expr.Ty).tys condition)
    (inside : RawCheckedAdapter.Adapter (ctx.push name LocalU8Expr.Ty) returns modifier u body)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R Unit × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    match RawU8Declaration.run name initial pipeline n state with
    | .inl failure => (.error failure.1,failure.2)
    | .inr next =>
      let result := RawCheckedAdapterLoop.run test inside pipeline n next
      (result.1,RawTypedScope.drop result.2)

end Solidity.Yul.RawU8For

namespace Solidity.Yul.RawU8For
theorem correct : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (returns : List Solidity.Source.STy) (modifier u l : Bool)
 (initializer : Solidity.Source.RExpr ctx.env ctx.tys Solidity.Yul.LocalU8Expr.Ty)
 (initial : Solidity.Yul.LocalU8Expr.Supported ctx.env ctx.tys initializer)
 (condition : Solidity.Source.RExpr ctx.env (ctx.push name LocalU8Expr.Ty).tys .bool)
 (body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩
   (ctx.push name LocalU8Expr.Ty).tys (ctx.push name LocalU8Expr.Ty).tys)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env (ctx.push name LocalU8Expr.Ty).tys condition)
 (inside : Solidity.Yul.RawCheckedAdapter.Adapter (ctx.push name LocalU8Expr.Ty) returns modifier u body)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent
   (Solidity.Yul.RawU8For.run initial test inside glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.forLoop (l := l)
     (Solidity.Source.RStmt.declInit (E := ctx.env) (R := returns) (M := modifier)
       (k := ⟨true,u⟩) (Γ := ctx.tys) (τ := Solidity.Yul.LocalU8Expr.Ty) initializer (by rfl))
     (.some condition) .none body) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawSequence.represented
   (Solidity.Yul.RawU8For.run initial test inside glob.pipeline fuel state) := by
  intro ctx name returns modifier u l initializer initial condition body test inside glob frame checked fuel nps ph state same
  cases fuel with
  | zero => exact ⟨same,rfl⟩
  | succ fuel =>
    have first := RawU8Declaration.correct ctx name initializer initial returns modifier
      ⟨true,u⟩ glob frame checked fuel nps ph state same
    cases actual : RawU8Declaration.run name initial glob.pipeline fuel state with
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
      have loop := RawCheckedAdapterLoop.correct (ctx.push name LocalU8Expr.Ty) returns modifier true u
        condition test body inside glob frame checked fuel nps ph next first.1
      have second : RawCoherent.coherent
          (RawCheckedAdapterLoop.run test inside glob.pipeline fuel next).2 = true ∧
          (Solidity.Source.forIter glob frame fuel nps ph (.some condition) .none body next.clean).run
            (Solidity.Source.L0 ctx.env,next.world) =
          RawSequence.represented (RawCheckedAdapterLoop.run test inside glob.pipeline fuel next) := by
        simpa only [RawSourceForIter.source_while] using loop
      simp only [run,actual]
      generalize iterationEq : RawCheckedAdapterLoop.run test inside glob.pipeline fuel next = iteration at second ⊢
      constructor
      · exact RawTypedScope.drop_coherent ctx name LocalU8Expr.Ty iteration.2 second.1
      · rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,first.2]
        dsimp only [RawPreparedInteger.project]
        rw [Solidity.Source.Hoare.run_bind,second.2]
        cases tag : iteration.1 with
        | error halt =>
          simp only [RawSequence.represented,tag,Except.map]
          rfl
        | ok _value =>
          simp only [RawSequence.represented,tag,Except.map]
          rw [Solidity.Source.Hoare.run_bind,RawGrowingSequence.lift_run,
            RawTypedScope.restore_drop ctx name LocalU8Expr.Ty]
          rfl
end Solidity.Yul.RawU8For

namespace Solidity.Yul.RawU8For
def adapter : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (returns : List Solidity.Source.STy) (modifier u : Bool)
 (initializer : Solidity.Source.RExpr ctx.env ctx.tys Solidity.Yul.LocalU8Expr.Ty)
 (_initial : Solidity.Yul.LocalU8Expr.Supported ctx.env ctx.tys initializer)
 (condition : Solidity.Source.RExpr ctx.env (ctx.push name LocalU8Expr.Ty).tys .bool)
 (body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩
   (ctx.push name LocalU8Expr.Ty).tys (ctx.push name LocalU8Expr.Ty).tys)
 (_test : Solidity.Yul.LocalBoolControl.Supported ctx.env (ctx.push name LocalU8Expr.Ty).tys condition)
 (_inside : Solidity.Yul.RawCheckedAdapter.Adapter (ctx.push name LocalU8Expr.Ty) returns modifier u body),
 Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u
 (Solidity.Source.RStmt.forLoop (l := true)
     (Solidity.Source.RStmt.declInit (E := ctx.env) (R := returns) (M := modifier)
       (k := ⟨true,u⟩) (Γ := ctx.tys) (τ := Solidity.Yul.LocalU8Expr.Ty) initializer (by rfl))
     (.some condition) .none body) := by
  intro ctx name returns modifier u initializer initial condition body test inside
  exact {
    run := fun pipeline fuel state =>
      let actual := run initial test inside pipeline fuel state
      (actual.1.map (fun _ => .normal),actual.2)
    correct := fun glob frame checked fuel nps ph state same => by
      simpa only [RawLoopBody.plain_represented] using
        (correct ctx name returns modifier u true initializer initial condition body test inside
          glob frame checked fuel nps ph state same)
  }
end Solidity.Yul.RawU8For
