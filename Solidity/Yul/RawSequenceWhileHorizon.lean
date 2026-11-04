import Solidity.Yul.RawSequenceWhile
import Solidity.Yul.RawControlSequenceHorizon

/-! Concrete sequence-bodied while completed horizons preserve entire raw frames.
Normal/continue recurse on actual states; break exits without an assumed child law. -/
namespace Solidity.Yul.RawSequenceWhileHorizon

theorem successor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (stmt : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawControlSequence.Supported ctx returns modifier u stmt)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSequenceWhile.run test body fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawSequenceWhile.run test body (fuel+1) state =
 Solidity.Yul.RawSequenceWhile.run test body fuel state := by
  intro ctx returns modifier u condition test stmt body fuel
  induction fuel with
  | zero => intro state terminal; exact False.elim (terminal rfl)
  | succ fuel ih =>
    intro state terminal
    have conditionReady : (Solidity.Yul.RawCondition.eval test fuel state).1 ≠ .error .timeout := by
      intro bad
      apply terminal
      rw [Solidity.Yul.RawSequenceWhile.run]
      dsimp only
      rw [bad]
    have conditionSame := Solidity.Yul.RawLoopBodyHorizon.conditionSuccessor ctx condition test fuel state conditionReady
    conv => lhs; rw [Solidity.Yul.RawSequenceWhile.run]
    conv => rhs; rw [Solidity.Yul.RawSequenceWhile.run]
    rw [conditionSame]
    cases actual : Solidity.Yul.RawCondition.eval test fuel state with
    | mk result next =>
      cases result with
      | error halt => rfl
      | ok choice =>
        cases choice with
        | false => rfl
        | true =>
          have bodyReady : (Solidity.Yul.RawControlSequence.block body fuel next).1 ≠ .error .timeout := by
            intro bad
            apply terminal
            rw [Solidity.Yul.RawSequenceWhile.run,actual]
            dsimp only
            rw [bad]
            rfl
          have bodySame := Solidity.Yul.RawControlSequenceHorizon.blockSuccessor ctx returns modifier u stmt body fuel next bodyReady
          rw [bodySame]
          cases bodyActual : Solidity.Yul.RawControlSequence.block body fuel next with
          | mk tag after =>
            cases tag with
            | error halt => rfl
            | ok flow =>
              cases flow with
              | normal =>
                apply ih after
                rw [Solidity.Yul.RawSequenceWhile.run,actual,bodyActual] at terminal
                exact terminal
              | continue_ h =>
                apply ih after
                rw [Solidity.Yul.RawSequenceWhile.run,actual,bodyActual] at terminal
                exact terminal
              | break_ h => rfl
              | leave_ impossible => cases impossible

theorem extension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (stmt : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawControlSequence.Supported ctx returns modifier u stmt)
 (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSequenceWhile.run test body fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawSequenceWhile.run test body (fuel+extra) state =
 Solidity.Yul.RawSequenceWhile.run test body fuel state := by
  intro ctx returns modifier u condition test stmt body fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : (Solidity.Yul.RawSequenceWhile.run test body (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (Solidity.Yul.RawSequenceWhileHorizon.successor ctx returns modifier u condition test stmt body (fuel+extra) state ready).trans ih

end Solidity.Yul.RawSequenceWhileHorizon
