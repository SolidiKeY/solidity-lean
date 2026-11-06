import Solidity.Yul.RawCheckedControlSequence
import Solidity.Yul.RawSourceAdapterDoWhile

/-! Body-first mixed checked-word/control loops. Break skips the guard;
normal and continue evaluate it at the actual postbody state.
Source agreement retains checked/coherent premises. -/
namespace Solidity.Yul.RawCheckedControlDoWhile

def run {ctx returns modifier u condition stmt}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (inside : RawCheckedControlSequence.Supported ctx returns modifier u stmt)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R Unit × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    let body := RawCheckedControlSequence.block inside pipeline n state
    match body.1 with
    | .error halt => (.error halt,body.2)
    | .ok flow => match flow with
      | .break_ _ => (.ok (),body.2)
      | .normal | .continue_ _ =>
        RawSourceAdapterDoWhile.after test (run test inside pipeline n) n body.2
      | .leave_ impossible => nomatch impossible

end Solidity.Yul.RawCheckedControlDoWhile

namespace Solidity.Yul.RawCheckedControlDoWhile
theorem correct : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier l u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawCheckedControlSequence.Supported ctx returns modifier u items)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent
   (Solidity.Yul.RawCheckedControlDoWhile.run test body glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.doWhile (l := l) (.block items) condition) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedControlDoWhile.run test body glob.pipeline fuel state) := by
  intro ctx returns modifier l u condition test items inside glob frame checked fuel nps ph state same
  induction fuel generalizing state with
  | zero => exact ⟨same,rfl⟩
  | succ fuel ih =>
    have body := RawCheckedControlSequence.block_correct inside glob frame checked fuel nps ph state same
    have actual := RawSourceAdapterDoWhile.source_body (l := l) condition (.block items) glob frame fuel nps ph state
      (RawCheckedControlSequence.block inside glob.pipeline fuel state) body.2
    cases tag : (RawCheckedControlSequence.block inside glob.pipeline fuel state).1 with
    | error halt =>
      simp only [run,tag]
      simp only [tag] at actual
      exact ⟨body.1,actual⟩
    | ok flow =>
      cases flow with
      | break_ h =>
        simp only [run,tag]
        simp only [tag] at actual
        exact ⟨body.1,actual⟩
      | normal =>
        have tail := RawSourceAdapterDoWhile.after_correct (l := l) condition (.block items) test (run test inside glob.pipeline fuel)
          glob frame fuel nps ph ih (RawCheckedControlSequence.block inside glob.pipeline fuel state).2 body.1
        simp only [run,tag]
        simp only [tag] at actual
        rw [actual]
        exact tail
      | continue_ h =>
        have tail := RawSourceAdapterDoWhile.after_correct (l := l) condition (.block items) test (run test inside glob.pipeline fuel)
          glob frame fuel nps ph ih (RawCheckedControlSequence.block inside glob.pipeline fuel state).2 body.1
        simp only [run,tag]
        simp only [tag] at actual
        rw [actual]
        exact tail
      | leave_ h => cases h


end Solidity.Yul.RawCheckedControlDoWhile
