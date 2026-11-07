import Solidity.Yul.RawCheckedControlWhile
import Solidity.Yul.RawCheckedControlSequenceHorizon
import Solidity.Yul.RawLoopBodyHorizon

/-! Mixed checked-word/control while horizons preserve complete results and raw frames.
Normal and continue recurse; break exits. Source agreement keeps checked/coherent premises. -/
namespace Solidity.Yul.RawCheckedControlWhileHorizon

theorem successor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (stmt : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawCheckedControlSequence.Supported ctx returns modifier u stmt)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawCheckedControlWhile.run test body pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawCheckedControlWhile.run test body pipeline (fuel+1) state =
 Solidity.Yul.RawCheckedControlWhile.run test body pipeline fuel state := by
  intro ctx returns modifier u condition test stmt body pipeline fuel
  induction fuel with
  | zero => intro state terminal; exact False.elim (terminal rfl)
  | succ fuel ih =>
    intro state terminal
    have conditionReady : (Solidity.Yul.RawCondition.eval test fuel state).1 ≠ .error .timeout := by
      intro bad
      apply terminal
      rw [Solidity.Yul.RawCheckedControlWhile.run]
      dsimp only
      rw [bad]
    have conditionSame := Solidity.Yul.RawLoopBodyHorizon.conditionSuccessor ctx condition test fuel state conditionReady
    conv => lhs; rw [Solidity.Yul.RawCheckedControlWhile.run]
    conv => rhs; rw [Solidity.Yul.RawCheckedControlWhile.run]
    rw [conditionSame]
    cases actual : Solidity.Yul.RawCondition.eval test fuel state with
    | mk result next =>
      cases result with
      | error halt => rfl
      | ok choice =>
        cases choice with
        | false => rfl
        | true =>
          have bodyReady : (Solidity.Yul.RawCheckedControlSequence.block body pipeline fuel next).1 ≠ .error .timeout := by
            intro bad
            apply terminal
            rw [Solidity.Yul.RawCheckedControlWhile.run,actual]
            dsimp only
            rw [bad]
            rfl
          have bodySame := Solidity.Yul.RawCheckedControlSequenceHorizon.blockSuccessor ctx returns modifier u stmt body pipeline fuel next bodyReady
          rw [bodySame]
          cases bodyActual : Solidity.Yul.RawCheckedControlSequence.block body pipeline fuel next with
          | mk tag after =>
            cases tag with
            | error halt => rfl
            | ok flow =>
              cases flow with
              | normal =>
                apply ih after
                rw [Solidity.Yul.RawCheckedControlWhile.run,actual,bodyActual] at terminal
                exact terminal
              | continue_ h =>
                apply ih after
                rw [Solidity.Yul.RawCheckedControlWhile.run,actual,bodyActual] at terminal
                exact terminal
              | break_ h => rfl
              | leave_ impossible => cases impossible

theorem extension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (stmt : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawCheckedControlSequence.Supported ctx returns modifier u stmt)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawCheckedControlWhile.run test body pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawCheckedControlWhile.run test body pipeline (fuel+extra) state =
 Solidity.Yul.RawCheckedControlWhile.run test body pipeline fuel state := by
  intro ctx returns modifier u condition test stmt body pipeline fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : (Solidity.Yul.RawCheckedControlWhile.run test body pipeline (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (Solidity.Yul.RawCheckedControlWhileHorizon.successor ctx returns modifier u condition test stmt body pipeline (fuel+extra) state ready).trans ih

theorem sourceExtension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier l u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawCheckedControlSequence.Supported ctx returns modifier u items)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel extra nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 (Solidity.Yul.RawCheckedControlWhile.run test body glob.pipeline fuel state).1 ≠ .error .timeout →
 (Solidity.Source.execS glob frame (fuel+extra) nps ph
   (Solidity.Source.RStmt.whileLoop (l := l) condition (.block items)) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.whileLoop (l := l) condition (.block items)) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) := by
  intro ctx returns modifier l u condition test items body glob frame checked fuel extra nps ph state same terminal
  have first := RawCheckedControlWhile.correct (l := l) test body glob frame checked fuel nps ph state same
  have later := RawCheckedControlWhile.correct (l := l) test body glob frame checked (fuel+extra) nps ph state same
  rw [extension ctx returns modifier u condition test items body glob.pipeline fuel extra state terminal] at later
  exact later.2.trans first.2.symm

end Solidity.Yul.RawCheckedControlWhileHorizon
