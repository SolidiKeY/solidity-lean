import Solidity.Yul.RawIntegerSequence
import Solidity.Yul.RawTypedScope

/-! Integer literal declaration blocks reuse the existing generic LOCAL scope
closure. Source execution and older raw mutations are composed concretely;
arbitrary initializers and frontend admission remain separate. -/
namespace Solidity.Yul.RawIntegerBlock
def close {ctx name ty} (result : RawIntegerSequence.Result ctx name ty) :
    Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx :=
  match result with
  | .inl failure => (.error failure.1,failure.2)
  | .inr next => RawTypedScope.close next
def run {ctx returns modifier u name}
    (ty : Solidity.Source.IntTy) (value : Int) (inRange : ty.lo ≤ value ∧ value ≤ ty.hi)
    {items} (tail : RawCheckedAdapterSequence.Items (ctx.push name (.int ty)) returns modifier u items)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 => close (RawIntegerSequence.run ty value inRange tail pipeline n state)
end Solidity.Yul.RawIntegerBlock

namespace Solidity.Yul.RawIntegerBlock
theorem close_correct : ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.IntTy)
 (result : Solidity.Yul.RawIntegerSequence.Result ctx name ty),
 Solidity.Yul.RawIntegerSequence.Coherent result →
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawIntegerBlock.close result).2 = true ∧
 (let actual := Solidity.Yul.RawIntegerSequence.project result
  (actual.1.bind Solidity.Source.Out.close,actual.2)) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.RawIntegerBlock.close result) := by
  intro ctx name ty result same
  cases result with
  | inl failure => exact ⟨same,rfl⟩
  | inr next => exact RawTypedScope.close_correct ctx name (.int ty) next same

theorem correct : ∀ (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.IntTy) (value : Int) (inRange : ty.lo ≤ value ∧ value ≤ ty.hi)
 (returns : List Solidity.Source.STy) (modifier u : Bool)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩
   (ctx.push name (.int ty)).tys (ctx.push name (.int ty)).tys)
 (tail : Solidity.Yul.RawCheckedAdapterSequence.Items (ctx.push name (.int ty)) returns modifier u items)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawIntegerBlock.run ty value inRange tail glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.block
    (Solidity.Source.RItems.stmt
     (Solidity.Source.RStmt.declInit (E := ctx.env) (R := returns) (M := modifier)
       (k := ⟨true,u⟩) (Γ := ctx.tys) (τ := .int ty) (.const (Solidity.Source.Q.ofInt value))
       (RawIntegerInitialization.admissible ctx.env ty value inRange)) items))
   state.clean).run (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.RawIntegerBlock.run ty value inRange tail glob.pipeline fuel state) := by
  intro ctx name ty value inRange returns modifier u items tail glob frame checked fuel nps ph state same
  cases fuel with
  | zero => exact ⟨same,rfl⟩
  | succ fuel =>
    have part := RawIntegerSequence.correct ctx name ty value inRange returns modifier u items tail
      glob frame checked fuel nps ph state same
    have closed := close_correct ctx name ty (RawIntegerSequence.run ty value inRange tail glob.pipeline fuel state) part.1
    constructor
    · exact closed.1
    · rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,part.2]
      cases pairEq : RawIntegerSequence.project (RawIntegerSequence.run ty value inRange tail glob.pipeline fuel state) with
      | mk tag post =>
        cases tag with
        | error halt =>
          simpa only [pairEq,Except.bind] using closed.2
        | ok out =>
          change (Solidity.Source.EM.lift out.close).run post = _
          rw [RawGrowingSequence.lift_run]
          simpa only [pairEq,Except.bind] using closed.2

end Solidity.Yul.RawIntegerBlock

namespace Solidity.Yul.RawIntegerBlock
def adapter (ctx : Solidity.Source.Ctx) (name : String) (ty : Solidity.Source.IntTy)
    (value : Int) (inRange : ty.lo ≤ value ∧ value ≤ ty.hi)
    (returns : List Solidity.Source.STy) (modifier u : Bool)
    (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩
      (ctx.push name (.int ty)).tys (ctx.push name (.int ty)).tys)
    (tail : RawCheckedAdapterSequence.Items (ctx.push name (.int ty)) returns modifier u items) :
    RawCheckedAdapter.Adapter ctx returns modifier u
      (.block (.stmt (.declInit (τ := .int ty) (.const (Solidity.Source.Q.ofInt value))
        (RawIntegerInitialization.admissible ctx.env ty value inRange)) items)) where
  run := run ty value inRange tail
  correct := correct ctx name ty value inRange returns modifier u items tail
end Solidity.Yul.RawIntegerBlock
