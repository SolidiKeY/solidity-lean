import Solidity.Yul.RawU8GrowingSequence
import Solidity.Yul.RawIntegerBlock

/-! Concrete block closure after a supported uint8 initializer and checked
grown tail. Existing close/drop/restoration are reused, with actual Source
composition. Other declaration types/groups and admission remain separate. -/
namespace Solidity.Yul.RawU8GrowingBlock
def run {ctx returns modifier u name initializer items}
    (initial : LocalU8Expr.Supported ctx.env ctx.tys initializer)
    (tail : RawCheckedAdapterSequence.Items (ctx.push name LocalU8Expr.Ty) returns modifier u items)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 => RawIntegerBlock.close (RawU8GrowingSequence.run initial tail pipeline n state)
end Solidity.Yul.RawU8GrowingBlock

namespace Solidity.Yul.RawU8GrowingBlock
theorem correct : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (returns : List Solidity.Source.STy) (modifier u : Bool)
 (initializer : Solidity.Source.RExpr ctx.env ctx.tys Solidity.Yul.LocalU8Expr.Ty)
 (initial : Solidity.Yul.LocalU8Expr.Supported ctx.env ctx.tys initializer)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩
   (ctx.push name LocalU8Expr.Ty).tys (ctx.push name LocalU8Expr.Ty).tys)
 (tail : Solidity.Yul.RawCheckedAdapterSequence.Items (ctx.push name LocalU8Expr.Ty) returns modifier u items)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawU8GrowingBlock.run initial tail glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.block
    (Solidity.Source.RItems.stmt
     (Solidity.Source.RStmt.declInit (E := ctx.env) (R := returns) (M := modifier)
       (k := ⟨true,u⟩) (Γ := ctx.tys) (τ := Solidity.Yul.LocalU8Expr.Ty) initializer (by rfl)) items))
   state.clean).run (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.RawU8GrowingBlock.run initial tail glob.pipeline fuel state) := by
  intro ctx name returns modifier u initializer initial items tail glob frame checked fuel nps ph state same
  cases fuel with
  | zero => exact ⟨same,rfl⟩
  | succ fuel =>
    have part := RawU8GrowingSequence.correct ctx name returns modifier u initializer initial items tail
      glob frame checked fuel nps ph state same
    have closed := RawIntegerBlock.close_correct ctx name Solidity.Source.IntTy.u8 (RawU8GrowingSequence.run initial tail glob.pipeline fuel state) part.1
    constructor
    · exact closed.1
    · rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,part.2]
      cases pairEq : RawIntegerSequence.project (RawU8GrowingSequence.run initial tail glob.pipeline fuel state) with
      | mk tag post =>
        cases tag with
        | error halt =>
          simpa only [pairEq,Except.bind] using closed.2
        | ok out =>
          change (Solidity.Source.EM.lift out.close).run post = _
          rw [RawGrowingSequence.lift_run]
          simpa only [pairEq,Except.bind] using closed.2

end Solidity.Yul.RawU8GrowingBlock

namespace Solidity.Yul.RawU8GrowingBlock
def adapter : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (returns : List Solidity.Source.STy) (modifier u : Bool)
 (initializer : Solidity.Source.RExpr ctx.env ctx.tys Solidity.Yul.LocalU8Expr.Ty)
 (_initial : Solidity.Yul.LocalU8Expr.Supported ctx.env ctx.tys initializer)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩
   (ctx.push name LocalU8Expr.Ty).tys (ctx.push name LocalU8Expr.Ty).tys)
 (_tail : Solidity.Yul.RawCheckedAdapterSequence.Items (ctx.push name LocalU8Expr.Ty) returns modifier u items),
 Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u
 (Solidity.Source.RStmt.block
    (Solidity.Source.RItems.stmt
     (Solidity.Source.RStmt.declInit (E := ctx.env) (R := returns) (M := modifier)
       (k := ⟨true,u⟩) (Γ := ctx.tys) (τ := Solidity.Yul.LocalU8Expr.Ty) initializer (by rfl)) items)) := by
  intro ctx name returns modifier u initializer initial items tail
  exact {
    run := run initial tail
    correct := correct ctx name returns modifier u initializer initial items tail
  }
end Solidity.Yul.RawU8GrowingBlock
