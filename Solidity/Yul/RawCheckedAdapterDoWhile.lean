import Solidity.Yul.RawCheckedAdapter
import Solidity.Yul.RawSourceAdapterDoWhile

/-! Body-first loop composition over checked executable statement producers.
Break skips the guard; normal/continue evaluate it on the exact postbody frame.
Source agreement uses the real fuel induction and checked/coherent premises. -/
namespace Solidity.Yul.RawCheckedAdapterDoWhile

def run {ctx returns modifier u condition stmt}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (inside : RawCheckedAdapter.Adapter ctx returns modifier u stmt)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R Unit × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    let body := inside.run pipeline n state
    match body.1 with
    | .error halt => (.error halt,body.2)
    | .ok flow => match flow with
      | .break_ _ => (.ok (),body.2)
      | .normal | .continue_ _ =>
        RawSourceAdapterDoWhile.after test (run test inside pipeline n) n body.2
      | .leave_ impossible => nomatch impossible

end Solidity.Yul.RawCheckedAdapterDoWhile

namespace Solidity.Yul.RawCheckedAdapterDoWhile
theorem correct : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier l u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (items : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u items)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent
   (Solidity.Yul.RawCheckedAdapterDoWhile.run test body glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.doWhile (l := l) items condition) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedAdapterDoWhile.run test body glob.pipeline fuel state) := by
  intro ctx returns modifier l u condition test items inside glob frame checked fuel nps ph state same
  induction fuel generalizing state with
  | zero => exact ⟨same,rfl⟩
  | succ fuel ih =>
    have body := inside.correct glob frame checked fuel nps ph state same
    have actual := RawSourceAdapterDoWhile.source_body (l := l) condition items glob frame fuel nps ph state
      (inside.run glob.pipeline fuel state) body.2
    cases tag : (inside.run glob.pipeline fuel state).1 with
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
        have tail := RawSourceAdapterDoWhile.after_correct (l := l) condition items test (run test inside glob.pipeline fuel)
          glob frame fuel nps ph ih (inside.run glob.pipeline fuel state).2 body.1
        simp only [run,tag]
        simp only [tag] at actual
        rw [actual]
        exact tail
      | continue_ h =>
        have tail := RawSourceAdapterDoWhile.after_correct (l := l) condition items test (run test inside glob.pipeline fuel)
          glob frame fuel nps ph ih (inside.run glob.pipeline fuel state).2 body.1
        simp only [run,tag]
        simp only [tag] at actual
        rw [actual]
        exact tail
      | leave_ h => cases h



theorem lift_correct : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (items : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u items)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent
   (Solidity.Yul.RawCheckedAdapterDoWhile.run test body glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.doWhile (l := true) items condition) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawLoopBody.represented
   ((Solidity.Yul.RawCheckedAdapterDoWhile.run test body glob.pipeline fuel state).1.map
      (fun _ => (Solidity.Yul.Closed.Flow.normal : Solidity.Yul.RawLoopBody.Flow)),
    (Solidity.Yul.RawCheckedAdapterDoWhile.run test body glob.pipeline fuel state).2) := by
  intro ctx returns modifier u condition test items body glob frame checked fuel nps ph state same
  rw [RawLoopBody.plain_represented]
  exact correct ctx returns modifier true u condition test items body glob frame checked fuel nps ph state same

def adapter {ctx returns modifier u condition stmt}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (inside : RawCheckedAdapter.Adapter ctx returns modifier u stmt) :
    RawCheckedAdapter.Adapter ctx returns modifier u
      (Solidity.Source.RStmt.doWhile (l := true) stmt condition) where
  run pipeline fuel state :=
    let actual := run test inside pipeline fuel state
    (actual.1.map (fun _ => .normal),actual.2)
  correct := lift_correct ctx returns modifier u condition test stmt inside

end Solidity.Yul.RawCheckedAdapterDoWhile
