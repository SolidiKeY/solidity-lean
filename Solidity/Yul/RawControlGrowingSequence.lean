import Solidity.Yul.RawGrowingSequence
import Solidity.Yul.RawControlDeclaration

/-! Concrete item sequencing after a supported Boolean initializer expression.
Reuses the existing typed old-error/grown-tail result and Source.Out.up projection.
This does not close a block scope or admit general declarations. -/
namespace Solidity.Yul.RawControlGrowingSequence
def run {ctx returns modifier u name initializer items}
    (initial : LocalBoolControl.Supported ctx.env ctx.tys initializer)
    (tail : RawCheckedAdapterSequence.Items (ctx.push name .bool) returns modifier u items)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    RawGrowingSequence.Result ctx name :=
  match fuel with
  | 0 => .inl (.timeout,state)
  | n+1 =>
    match RawControlDeclaration.run name initial n state with
    | .inl failure => .inl failure
    | .inr next => .inr (tail.run pipeline n next)
end Solidity.Yul.RawControlGrowingSequence

namespace Solidity.Yul.RawControlGrowingSequence
theorem correct : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (returns : List Solidity.Source.STy) (modifier u : Bool)
 (initializer : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (initial : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys initializer)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩
   (ctx.push name .bool).tys (ctx.push name .bool).tys)
 (tail : Solidity.Yul.RawCheckedAdapterSequence.Items (ctx.push name .bool) returns modifier u items)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawGrowingSequence.Coherent
   (Solidity.Yul.RawControlGrowingSequence.run initial tail glob.pipeline fuel state) ∧
 (Solidity.Source.execItems glob frame fuel nps ph
   (Solidity.Source.RItems.stmt
     (Solidity.Source.RStmt.declInit (E := ctx.env) (R := returns) (M := modifier)
       (k := ⟨true,u⟩) (Γ := ctx.tys) (τ := .bool) initializer (by rfl)) items)
   state.clean).run (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawGrowingSequence.project
   (Solidity.Yul.RawControlGrowingSequence.run initial tail glob.pipeline fuel state) := by
  intro ctx name returns modifier u initializer initial items tail glob frame checked fuel nps ph state same
  cases fuel with
  | zero => exact ⟨same,rfl⟩
  | succ fuel =>
    have first := RawControlDeclaration.correct ctx name initializer initial returns modifier
      ⟨true,u⟩ glob frame fuel nps ph state same
    cases actual : RawControlDeclaration.run name initial fuel state with
    | inl failure =>
      rcases failure with ⟨halt,next⟩
      rw [actual] at first
      simp only [run,actual,RawGrowingSequence.Coherent]
      constructor
      · exact first.1
      · rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,first.2]
        rfl
    | inr next =>
      rw [actual] at first
      have second := tail.correct glob frame checked fuel nps ph next first.1
      simp only [run,actual,RawGrowingSequence.Coherent]
      constructor
      · exact second.1
      · rw [Solidity.Source.execItems,Solidity.Source.Hoare.run_bind,first.2]
        change ((do
          let out ← Solidity.Source.execItems glob frame fuel nps ph items next.clean
          Solidity.Source.EM.lift (out.up ctx.tys))).run
            (Solidity.Source.L0 ctx.env,next.world) =
          RawGrowingSequence.project (.inr (tail.run glob.pipeline fuel next))
        rw [Solidity.Source.Hoare.run_bind,second.2]
        cases tag : (tail.run glob.pipeline fuel next).1 with
        | error halt => simp only [RawLoopBody.represented,tag,Except.map,RawGrowingSequence.project]; rfl
        | ok flow =>
          cases flow with
          | normal => simp only [RawLoopBody.represented,tag,Except.map,RawLoopBody.out,RawGrowingSequence.project]; rfl
          | break_ h =>
            simp only [RawLoopBody.represented,tag,Except.map,RawLoopBody.out,RawGrowingSequence.project]
            apply RawGrowingSequence.lift_run
          | continue_ h =>
            simp only [RawLoopBody.represented,tag,Except.map,RawLoopBody.out,RawGrowingSequence.project]
            apply RawGrowingSequence.lift_run
          | leave_ h => cases h
end Solidity.Yul.RawControlGrowingSequence
