import Solidity.Yul.RawCheckedSequence
import Solidity.Yul.RawSourceAdapterDoWhile

/-! Concrete body-first mixed Boolean/checked-uint8 loops over actual Source
syntax. Normal body flow only; checked/coherent Source premises explicit. -/
namespace Solidity.Yul.RawCheckedDoWhile

def run {ctx returns modifier u condition items}
 (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
 (body : RawCheckedSequence.Supported ctx returns modifier ⟨true,u⟩ items)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
 Solidity.Source.R Unit × RawFrame.State ctx :=
 match fuel with
 | 0 => (.error .timeout,state)
 | fuel+1 =>
   let first := RawCheckedSequence.block body pipeline fuel state
   match first.1 with
   | .error halt => (.error halt,first.2)
   | .ok () => RawSourceAdapterDoWhile.after test (run test body pipeline fuel) fuel first.2

theorem correct : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier l u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawCheckedSequence.Supported ctx returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent
   (Solidity.Yul.RawCheckedDoWhile.run test body glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.doWhile (l := l) (.block items) condition) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedDoWhile.run test body glob.pipeline fuel state) := by
  intro ctx returns modifier l u condition test items body glob frame checked fuel nps ph state same
  induction fuel generalizing state with
  | zero => exact ⟨same,rfl⟩
  | succ fuel ih =>
    have first := RawCheckedSequence.block_correct ctx returns modifier ⟨true,u⟩ items body glob frame checked fuel nps ph state same
    have asFlow := first.2.trans
      (RawLoopBody.plain_represented (RawCheckedSequence.block body glob.pipeline fuel state)).symm
    have actual := RawSourceAdapterDoWhile.source_body (l := l) condition (.block items) glob frame fuel nps ph
      state ((RawCheckedSequence.block body glob.pipeline fuel state).1.map
        (fun _ => (Closed.Flow.normal : RawLoopBody.Flow)),
        (RawCheckedSequence.block body glob.pipeline fuel state).2) asFlow
    cases tag : (RawCheckedSequence.block body glob.pipeline fuel state).1 with
    | error halt =>
      simp only [run,tag]
      simp only [tag,Except.map] at actual
      exact ⟨first.1,actual⟩
    | ok value =>
      cases value
      have tail := RawSourceAdapterDoWhile.after_correct (l := l) condition (.block items) test
        (run test body glob.pipeline fuel) glob frame fuel nps ph ih
        (RawCheckedSequence.block body glob.pipeline fuel state).2 first.1
      simp only [run,tag]
      simp only [tag,Except.map] at actual
      rw [actual]
      exact tail

end Solidity.Yul.RawCheckedDoWhile
