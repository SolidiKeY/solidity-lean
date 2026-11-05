import Solidity.Yul.RawPreparedDeclaration
import Solidity.Yul.RawCheckedAdapterSequence

/-! Concrete checked Source item sequencing across a Boolean literal binder.
Pre-declaration errors retain the old context; reached tail frames retain the
grown context. Projection uses actual Source.Out.up for enclosing control.
This is item sequencing, not final block scope closure or admission. -/
namespace Solidity.Yul.RawGrowingSequence

abbrev Result (ctx : Solidity.Source.Ctx) (name : String) :=
  Sum (Solidity.Source.Halt × RawFrame.State ctx)
    (Solidity.Source.R RawLoopBody.Flow × RawFrame.State (ctx.push name .bool))

def run {ctx returns modifier u name items}
    (value : Bool)
    (tail : RawCheckedAdapterSequence.Items (ctx.push name .bool) returns modifier u items)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Result ctx name :=
  match fuel with
  | 0 => .inl (.timeout,state)
  | n+1 =>
    match RawPreparedDeclaration.run name value n state with
    | .inl failure => .inl failure
    | .inr next => .inr (tail.run pipeline n next)

def project {ctx name} (result : Result ctx name) :
    Solidity.Source.R (Solidity.Source.Out ctx.env.layout ctx.tys ((ctx.push name .bool).tys)) ×
      (Solidity.Source.Locals ctx.env.layout [] × Solidity.Source.St ctx.env) :=
  match result with
  | .inl failure => (.error failure.1,(Solidity.Source.L0 ctx.env,failure.2.world))
  | .inr next =>
    let actual := RawLoopBody.represented next
    (actual.1.bind (fun out => out.up ctx.tys),actual.2)

def Coherent {ctx name} (result : Result ctx name) : Prop :=
  match result with
  | .inl failure => RawCoherent.coherent failure.2 = true
  | .inr next => RawCoherent.coherent next.2 = true

end Solidity.Yul.RawGrowingSequence

namespace Solidity.Yul.RawGrowingSequence
theorem lift_run : ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx) (α : Type)
 (result : Solidity.Source.R α) (state : Solidity.Source.EMState env types),
 (Solidity.Source.EM.lift result).run state = (result,state) := by
  intro env types α result state
  cases result <;> rfl
end Solidity.Yul.RawGrowingSequence

namespace Solidity.Yul.RawGrowingSequence
theorem correct : ∀ (ctx : Solidity.Source.Ctx) (name : String) (value : Bool)
 (returns : List Solidity.Source.STy) (modifier u : Bool)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩
   (ctx.push name .bool).tys (ctx.push name .bool).tys)
 (tail : Solidity.Yul.RawCheckedAdapterSequence.Items (ctx.push name .bool) returns modifier u items)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawGrowingSequence.Coherent
   (Solidity.Yul.RawGrowingSequence.run value tail glob.pipeline fuel state) ∧
 (Solidity.Source.execItems glob frame fuel nps ph
   (Solidity.Source.RItems.stmt
     (Solidity.Source.RStmt.declInit (E := ctx.env) (R := returns) (M := modifier)
       (k := ⟨true,u⟩) (Γ := ctx.tys) (τ := .bool) (.bool value) (by rfl)) items)
   state.clean).run (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawGrowingSequence.project
   (Solidity.Yul.RawGrowingSequence.run value tail glob.pipeline fuel state) := by
  intro ctx name value returns modifier u items tail glob frame checked fuel nps ph state same
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
      simp only [run,actual,Coherent]
      constructor
      · exact coherent
      · rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,first]
        rfl
    | inr next =>
      rw [actual] at first coherent
      have second := tail.correct glob frame checked fuel nps ph next coherent
      simp only [run,actual,Coherent]
      constructor
      · exact second.1
      · rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,first]
        change ((do
          let out ← Solidity.Source.execItems glob frame fuel nps ph items next.clean
          Solidity.Source.EM.lift (out.up ctx.tys))).run
            (Solidity.Source.L0 ctx.env,next.world) =
          project (.inr (tail.run glob.pipeline fuel next))
        rw [Solidity.Source.Hoare.run_bind,second.2]
        cases tag : (tail.run glob.pipeline fuel next).1 with
        | error halt => simp only [RawLoopBody.represented,tag,Except.map,project]; rfl
        | ok flow =>
          cases flow with
          | normal => simp only [RawLoopBody.represented,tag,Except.map,RawLoopBody.out,project]; rfl
          | break_ h =>
            simp only [RawLoopBody.represented,tag,Except.map,RawLoopBody.out,project]
            apply lift_run
          | continue_ h =>
            simp only [RawLoopBody.represented,tag,Except.map,RawLoopBody.out,project]
            apply lift_run
          | leave_ h => cases h
end Solidity.Yul.RawGrowingSequence
