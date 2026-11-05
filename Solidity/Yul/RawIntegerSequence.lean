import Solidity.Yul.RawPreparedInteger
import Solidity.Yul.RawGrowingSequence
import Solidity.Yul.RawCheckedAdapterSequence

/-! Concrete checked Source item sequencing across an in-range integer literal binder.
Pre-declaration errors retain the old context; reached tail frames retain the
grown context. Projection uses actual Source.Out.up for enclosing control.
This is item sequencing, not final block scope closure or admission. -/
namespace Solidity.Yul.RawIntegerSequence

abbrev Result (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.IntTy) :=
  Sum (Solidity.Source.Halt × RawFrame.State ctx)
    (Solidity.Source.R RawLoopBody.Flow × RawFrame.State (ctx.push name (.int ty)))

def run {ctx returns modifier u name}
    (ty : Solidity.Source.IntTy) (value : Int) (inRange : ty.lo ≤ value ∧ value ≤ ty.hi)
    {items} (tail : RawCheckedAdapterSequence.Items (ctx.push name (.int ty)) returns modifier u items)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Result ctx name ty :=
  match fuel with
  | 0 => .inl (.timeout,state)
  | n+1 =>
    match RawPreparedInteger.run name ty value inRange n state with
    | .inl failure => .inl failure
    | .inr next => .inr (tail.run pipeline n next)

def project {ctx name ty} (result : Result ctx name ty) :
    Solidity.Source.R (Solidity.Source.Out ctx.env.layout ctx.tys ((ctx.push name (.int ty)).tys)) ×
      (Solidity.Source.Locals ctx.env.layout [] × Solidity.Source.St ctx.env) :=
  match result with
  | .inl failure => (.error failure.1,(Solidity.Source.L0 ctx.env,failure.2.world))
  | .inr next =>
    let actual := RawLoopBody.represented next
    (actual.1.bind (fun out => out.up ctx.tys),actual.2)

def Coherent {ctx name ty} (result : Result ctx name ty) : Prop :=
  match result with
  | .inl failure => RawCoherent.coherent failure.2 = true
  | .inr next => RawCoherent.coherent next.2 = true

end Solidity.Yul.RawIntegerSequence

namespace Solidity.Yul.RawIntegerSequence
theorem correct : ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.IntTy) (value : Int) (inRange : ty.lo ≤ value ∧ value ≤ ty.hi)
 (returns : List Solidity.Source.STy) (modifier u : Bool)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩
   (ctx.push name (.int ty)).tys (ctx.push name (.int ty)).tys)
 (tail : Solidity.Yul.RawCheckedAdapterSequence.Items (ctx.push name (.int ty)) returns modifier u items)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawIntegerSequence.Coherent
   (Solidity.Yul.RawIntegerSequence.run ty value inRange tail glob.pipeline fuel state) ∧
 (Solidity.Source.execItems glob frame fuel nps ph
   (Solidity.Source.RItems.stmt
     (Solidity.Source.RStmt.declInit (E := ctx.env) (R := returns) (M := modifier)
       (k := ⟨true,u⟩) (Γ := ctx.tys) (τ := .int ty) (.const (Solidity.Source.Q.ofInt value))
       (RawIntegerInitialization.admissible ctx.env ty value inRange)) items)
   state.clean).run (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawIntegerSequence.project
   (Solidity.Yul.RawIntegerSequence.run ty value inRange tail glob.pipeline fuel state) := by
  intro ctx name ty value inRange returns modifier u items tail glob frame checked fuel nps ph state same
  cases fuel with
  | zero => exact ⟨same,rfl⟩
  | succ fuel =>
    have first := RawPreparedInteger.source_correct ctx name ty value inRange returns modifier
      ⟨true,u⟩ glob frame fuel nps ph state
    have coherent := RawPreparedInteger.coherent_result ctx name ty value inRange fuel state same
    cases actual : RawPreparedInteger.run name ty value inRange fuel state with
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
            apply RawGrowingSequence.lift_run
          | continue_ h =>
            simp only [RawLoopBody.represented,tag,Except.map,RawLoopBody.out,project]
            apply RawGrowingSequence.lift_run
          | leave_ h => cases h
end Solidity.Yul.RawIntegerSequence
