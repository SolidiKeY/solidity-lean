import Solidity.Yul.RawSourceAdapterLoop
import Solidity.Yul.RawControlledWhileHorizon

/-! Exact concrete body-adapter/driver agreement and completed P16 adapter horizons.
No claim of raw stability for arbitrary adapters follows from clean Source correctness. -/
namespace Solidity.Yul.RawAdapterLoopHorizon

theorem body_agrees : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawSourceAdapterLoop.run test (Solidity.Yul.RawSourceAdapter.body body) fuel state =
 Solidity.Yul.RawControlledWhile.run test body fuel state := by
  intro ctx returns modifier u condition test stmt body fuel
  induction fuel with
  | zero => intro state; rfl
  | succ fuel ih =>
    intro state
    conv => lhs; rw [Solidity.Yul.RawSourceAdapterLoop.run]
    conv => rhs; rw [Solidity.Yul.RawControlledWhile.run]
    cases actual : Solidity.Yul.RawCondition.eval test fuel state with
    | mk result next =>
      cases result with
      | error halt => rfl
      | ok choice =>
        cases choice with
        | false => rfl
        | true =>
          dsimp only [Solidity.Yul.RawSourceAdapter.body]
          cases bodyActual : Solidity.Yul.RawLoopBody.run body fuel next with
          | mk tag after =>
            cases tag with
            | error halt => rfl
            | ok flow =>
              cases flow with
              | normal => exact ih after
              | continue_ h => exact ih after
              | break_ h => rfl
              | leave_ impossible => cases impossible

theorem successor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 ((Solidity.Yul.RawSourceAdapterLoop.loop test (Solidity.Yul.RawSourceAdapter.body body)).run fuel state).1 ≠ .error .timeout →
 (Solidity.Yul.RawSourceAdapterLoop.loop test (Solidity.Yul.RawSourceAdapter.body body)).run (fuel+1) state = (Solidity.Yul.RawSourceAdapterLoop.loop test (Solidity.Yul.RawSourceAdapter.body body)).run fuel state := by
  intro ctx returns modifier u condition test stmt body fuel state terminal
  have ready : (Solidity.Yul.RawControlledWhile.run test body fuel state).1 ≠ .error .timeout := by
    intro bad
    apply terminal
    change (Solidity.Yul.RawSourceAdapterLoop.run test (Solidity.Yul.RawSourceAdapter.body body) fuel state).1.map
      (fun _ => (Solidity.Yul.Closed.Flow.normal : Solidity.Yul.RawLoopBody.Flow)) = .error .timeout
    rw [Solidity.Yul.RawAdapterLoopHorizon.body_agrees,bad]
    rfl
  have same := Solidity.Yul.RawControlledWhileHorizon.successor ctx returns modifier u condition test stmt body fuel state ready
  change (let actual := Solidity.Yul.RawSourceAdapterLoop.run test (Solidity.Yul.RawSourceAdapter.body body) (fuel+1) state
          (actual.1.map (fun _ => (Solidity.Yul.Closed.Flow.normal : Solidity.Yul.RawLoopBody.Flow)),actual.2)) =
    (let actual := Solidity.Yul.RawSourceAdapterLoop.run test (Solidity.Yul.RawSourceAdapter.body body) fuel state
     (actual.1.map (fun _ => (Solidity.Yul.Closed.Flow.normal : Solidity.Yul.RawLoopBody.Flow)),actual.2))
  simp only [Solidity.Yul.RawAdapterLoopHorizon.body_agrees,same]

theorem extension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 ((Solidity.Yul.RawSourceAdapterLoop.loop test (Solidity.Yul.RawSourceAdapter.body body)).run fuel state).1 ≠ .error .timeout →
 (Solidity.Yul.RawSourceAdapterLoop.loop test (Solidity.Yul.RawSourceAdapter.body body)).run (fuel+extra) state = (Solidity.Yul.RawSourceAdapterLoop.loop test (Solidity.Yul.RawSourceAdapter.body body)).run fuel state := by
  intro ctx returns modifier u condition test stmt body fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : ((Solidity.Yul.RawSourceAdapterLoop.loop test (Solidity.Yul.RawSourceAdapter.body body)).run (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (Solidity.Yul.RawAdapterLoopHorizon.successor ctx returns modifier u condition test stmt body (fuel+extra) state ready).trans ih

end Solidity.Yul.RawAdapterLoopHorizon
