import Solidity.Yul.RawCheckedDoWhile
import Solidity.Yul.RawCheckedSequenceHorizon
import Solidity.Yul.RawLoopBodyHorizon

/-! Completed body-first mixed loops preserve the entire raw result/frame.
Timeout prefixes are excluded; Source transport keeps checked/coherent premises. -/
namespace Solidity.Yul.RawCheckedDoWhileHorizon

theorem successor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawCheckedSequence.Supported ctx returns modifier ⟨true,u⟩ items)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawCheckedDoWhile.run test body pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawCheckedDoWhile.run test body pipeline (fuel+1) state =
 Solidity.Yul.RawCheckedDoWhile.run test body pipeline fuel state := by
  intro ctx returns modifier u condition test items body pipeline fuel
  induction fuel with
  | zero => intro state terminal; exact False.elim (terminal rfl)
  | succ fuel ih =>
    intro state terminal
    have tail : ∀ next : RawFrame.State ctx,
        (RawSourceAdapterDoWhile.after test (RawCheckedDoWhile.run test body pipeline fuel) fuel next).1 ≠ .error .timeout →
        RawSourceAdapterDoWhile.after test (RawCheckedDoWhile.run test body pipeline (fuel+1)) (fuel+1) next =
        RawSourceAdapterDoWhile.after test (RawCheckedDoWhile.run test body pipeline fuel) fuel next := by
      intro next ready
      have conditionReady : (RawCondition.eval test fuel next).1 ≠ .error .timeout := by
        intro bad
        apply ready
        simp only [RawSourceAdapterDoWhile.after,bad]
      have same := RawLoopBodyHorizon.conditionSuccessor ctx condition test fuel next conditionReady
      unfold RawSourceAdapterDoWhile.after
      rw [same]
      cases actual : RawCondition.eval test fuel next with
      | mk tag after =>
        cases tag with
        | error halt => rfl
        | ok choice =>
          cases choice with
          | false => rfl
          | true =>
            apply ih after
            simp only [RawSourceAdapterDoWhile.after,actual,if_true] at ready
            exact ready
    have bodyReady : (RawCheckedSequence.block body pipeline fuel state).1 ≠ .error .timeout := by
      intro bad
      apply terminal
      rw [RawCheckedDoWhile.run,bad]
    have same := RawCheckedSequenceHorizon.blockExtension ctx returns modifier ⟨true,u⟩ items body pipeline fuel 1 state bodyReady
    conv => lhs; rw [RawCheckedDoWhile.run]
    conv => rhs; rw [RawCheckedDoWhile.run]
    rw [same]
    cases actual : RawCheckedSequence.block body pipeline fuel state with
    | mk tag next =>
      cases tag with
      | error halt => rfl
      | ok value =>
        cases value
        apply tail next
        rw [RawCheckedDoWhile.run,actual] at terminal
        exact terminal

theorem extension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawCheckedSequence.Supported ctx returns modifier ⟨true,u⟩ items)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawCheckedDoWhile.run test body pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawCheckedDoWhile.run test body pipeline (fuel+extra) state =
 Solidity.Yul.RawCheckedDoWhile.run test body pipeline fuel state := by
  intro ctx returns modifier u condition test items body pipeline fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : (RawCheckedDoWhile.run test body pipeline (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (successor ctx returns modifier u condition test items body pipeline (fuel+extra) state ready).trans ih

theorem sourceExtension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier l u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawCheckedSequence.Supported ctx returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel extra nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 (Solidity.Yul.RawCheckedDoWhile.run test body glob.pipeline fuel state).1 ≠ .error .timeout →
 (Solidity.Source.execS glob frame (fuel+extra) nps ph
   (Solidity.Source.RStmt.doWhile (l := l) (.block items) condition) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.doWhile (l := l) (.block items) condition) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) := by
  intro ctx returns modifier l u condition test items body glob frame checked fuel extra nps ph state same terminal
  have first := RawCheckedDoWhile.correct ctx returns modifier l u condition test items body glob frame checked fuel nps ph state same
  have later := RawCheckedDoWhile.correct ctx returns modifier l u condition test items body glob frame checked (fuel+extra) nps ph state same
  rw [extension ctx returns modifier u condition test items body glob.pipeline fuel extra state terminal] at later
  exact later.2.trans first.2.symm

end Solidity.Yul.RawCheckedDoWhileHorizon
