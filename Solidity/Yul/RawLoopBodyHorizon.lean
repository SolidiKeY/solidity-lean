import Solidity.Yul.RawLoopBody
import Solidity.Yul.RawSequenceHorizon

/-! Concrete raw condition and control-body horizons preserve full results and frames.
Break/continue are completed flows; no coherence or supplied child law is required. -/
namespace Solidity.Yul.RawLoopBodyHorizon

theorem conditionSuccessor : ∀ (ctx : Solidity.Source.Ctx)
 (expr : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (proof : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys expr)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawCondition.eval proof fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawCondition.eval proof (fuel+1) state = Solidity.Yul.RawCondition.eval proof fuel state := by
  intro ctx expr proof fuel state terminal
  have ready : (Solidity.Yul.LocalBoolControl.eval proof fuel (Solidity.Yul.RawCoherent.prepare state)).1 ≠ .error .timeout := by
    intro bad
    apply terminal
    simp only [Solidity.Yul.RawCondition.eval,bad,Except.map]
  have same := Solidity.Yul.LocalBoolHorizon.successor ctx.env ctx.tys expr proof fuel (Solidity.Yul.RawCoherent.prepare state) ready
  unfold Solidity.Yul.RawCondition.eval
  rw [same]

theorem successor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawLoopBody.run proof fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawLoopBody.run proof (fuel+1) state = Solidity.Yul.RawLoopBody.run proof fuel state := by
  intro ctx returns modifier u stmt proof
  induction proof with
  | plain inside =>
    intro fuel state terminal
    have ready : (Solidity.Yul.RawSequence.block inside fuel state).1 ≠ .error .timeout := by
      intro bad
      apply terminal
      simp only [Solidity.Yul.RawLoopBody.run,bad,Except.map]
    have same := Solidity.Yul.RawSequenceHorizon.blockSuccessor ctx returns modifier ⟨true,u⟩ _ inside fuel state ready
    simp only [Solidity.Yul.RawLoopBody.run,same]
  | skip =>
    intro fuel state terminal
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel => rfl
  | break_ =>
    intro fuel state terminal
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel => rfl
  | continue_ =>
    intro fuel state terminal
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel => rfl
  | ifThen test inside ih =>
    intro fuel state terminal
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel =>
      have ready : (Solidity.Yul.RawCondition.eval test fuel state).1 ≠ .error .timeout := by
        intro bad
        apply terminal
        rw [Solidity.Yul.RawLoopBody.run_ifThen]
        dsimp only
        rw [bad]
      have same := Solidity.Yul.RawLoopBodyHorizon.conditionSuccessor ctx _ test fuel state ready
      rw [Solidity.Yul.RawLoopBody.run_ifThen,Solidity.Yul.RawLoopBody.run_ifThen,same]
      cases actual : Solidity.Yul.RawCondition.eval test fuel state with
      | mk result next =>
        cases result with
        | error halt => rfl
        | ok choice =>
          cases choice with
          | false => rfl
          | true =>
            apply ih fuel next
            rw [Solidity.Yul.RawLoopBody.run_ifThen,actual] at terminal
            exact terminal

theorem conditionExtension : ∀ (ctx : Solidity.Source.Ctx)
 (expr : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (proof : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys expr)
 (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawCondition.eval proof fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawCondition.eval proof (fuel+extra) state = Solidity.Yul.RawCondition.eval proof fuel state := by
  intro ctx expr proof fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : (Solidity.Yul.RawCondition.eval proof (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (Solidity.Yul.RawLoopBodyHorizon.conditionSuccessor ctx expr proof (fuel+extra) state ready).trans ih

theorem extension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawLoopBody.run proof fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawLoopBody.run proof (fuel+extra) state = Solidity.Yul.RawLoopBody.run proof fuel state := by
  intro ctx returns modifier u stmt proof fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : (Solidity.Yul.RawLoopBody.run proof (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (Solidity.Yul.RawLoopBodyHorizon.successor ctx returns modifier u stmt proof (fuel+extra) state ready).trans ih

end Solidity.Yul.RawLoopBodyHorizon
