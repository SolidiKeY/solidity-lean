import Solidity.Yul.RawCheckedWhile
import Solidity.Yul.RawCheckedSequenceHorizon
import Solidity.Yul.RawLoopBodyHorizon

/-! Completed mixed-loop horizons preserve the entire raw result/frame.
Timeout prefixes remain distinct. Source transport retains checked/coherence premises. -/
namespace Solidity.Yul.RawCheckedWhileHorizon

theorem successor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawCheckedSequence.Supported ctx returns modifier ⟨true,u⟩ items)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawCheckedWhile.run test body pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawCheckedWhile.run test body pipeline (fuel+1) state =
 Solidity.Yul.RawCheckedWhile.run test body pipeline fuel state := by
  intro ctx returns modifier u condition test items body pipeline fuel
  induction fuel with
  | zero => intro state terminal; exact False.elim (terminal rfl)
  | succ fuel ih =>
    intro state terminal
    have conditionReady : (RawCondition.eval test fuel state).1 ≠ .error .timeout := by
      intro bad
      apply terminal
      rw [RawCheckedWhile.run]
      dsimp only
      rw [bad]
    have conditionSame := RawLoopBodyHorizon.conditionSuccessor ctx condition test fuel state conditionReady
    conv => lhs; rw [RawCheckedWhile.run]
    conv => rhs; rw [RawCheckedWhile.run]
    rw [conditionSame]
    cases actual : RawCondition.eval test fuel state with
    | mk result next =>
      cases result with
      | error halt => rfl
      | ok choice =>
        cases choice with
        | false => rfl
        | true =>
          have bodyReady : (RawCheckedSequence.block body pipeline fuel next).1 ≠ .error .timeout := by
            intro bad
            apply terminal
            rw [RawCheckedWhile.run,actual]
            dsimp only
            rw [bad]
            rfl
          have bodySame := RawCheckedSequenceHorizon.blockExtension ctx returns modifier ⟨true,u⟩ items body pipeline fuel 1 next bodyReady
          rw [bodySame]
          cases bodyActual : RawCheckedSequence.block body pipeline fuel next with
          | mk tag after =>
            cases tag with
            | error halt => rfl
            | ok value =>
              cases value
              apply ih after
              rw [RawCheckedWhile.run,actual,bodyActual] at terminal
              exact terminal

theorem extension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawCheckedSequence.Supported ctx returns modifier ⟨true,u⟩ items)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawCheckedWhile.run test body pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawCheckedWhile.run test body pipeline (fuel+extra) state =
 Solidity.Yul.RawCheckedWhile.run test body pipeline fuel state := by
  intro ctx returns modifier u condition test items body pipeline fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : (RawCheckedWhile.run test body pipeline (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (successor ctx returns modifier u condition test items body pipeline (fuel+extra) state ready).trans ih

theorem sourceExtension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier l u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawCheckedSequence.Supported ctx returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel extra nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 (Solidity.Yul.RawCheckedWhile.run test body glob.pipeline fuel state).1 ≠ .error .timeout →
 (Solidity.Source.execS glob frame (fuel+extra) nps ph
   (Solidity.Source.RStmt.whileLoop (l := l) condition (.block items)) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.whileLoop (l := l) condition (.block items)) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) := by
  intro ctx returns modifier l u condition test items body glob frame checked fuel extra nps ph state same terminal
  have first := RawCheckedWhile.correct (l := l) test body glob frame checked fuel nps ph state same
  have later := RawCheckedWhile.correct (l := l) test body glob frame checked (fuel+extra) nps ph state same
  rw [extension ctx returns modifier u condition test items body glob.pipeline fuel extra state terminal] at later
  exact later.2.trans first.2.symm

end Solidity.Yul.RawCheckedWhileHorizon
