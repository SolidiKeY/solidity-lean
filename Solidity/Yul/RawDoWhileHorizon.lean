import Solidity.Yul.RawSourceAdapterDoWhile
import Solidity.Yul.RawLoopBodyHorizon

/-! Completed concrete body-first loop horizons preserve full raw frames.
Break skips the condition; no raw stability is inferred for arbitrary adapters. -/
namespace Solidity.Yul.RawDoWhileHorizon

theorem successor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.body body) (fuel+1) state = Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.body body) fuel state := by
  intro ctx returns modifier u condition test stmt body fuel
  induction fuel with
  | zero => intro state terminal; exact False.elim (terminal rfl)
  | succ fuel ih =>
    intro state terminal
    have tail : ∀ next : Solidity.Yul.RawFrame.State ctx,
        (Solidity.Yul.RawSourceAdapterDoWhile.after test
          (Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.body body) fuel) fuel next).1 ≠ .error .timeout →
        Solidity.Yul.RawSourceAdapterDoWhile.after test
          (Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.body body) (fuel+1)) (fuel+1) next =
        Solidity.Yul.RawSourceAdapterDoWhile.after test
          (Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.body body) fuel) fuel next := by
      intro next ready
      have conditionReady : (Solidity.Yul.RawCondition.eval test fuel next).1 ≠ .error .timeout := by
        intro bad
        apply ready
        simp only [Solidity.Yul.RawSourceAdapterDoWhile.after,bad]
      have same := Solidity.Yul.RawLoopBodyHorizon.conditionSuccessor ctx condition test fuel next conditionReady
      unfold Solidity.Yul.RawSourceAdapterDoWhile.after
      rw [same]
      cases actual : Solidity.Yul.RawCondition.eval test fuel next with
      | mk tag after =>
        cases tag with
        | error halt => rfl
        | ok choice =>
          cases choice with
          | false => rfl
          | true =>
            apply ih after
            simp only [Solidity.Yul.RawSourceAdapterDoWhile.after,actual,if_true] at ready
            exact ready
    have bodyReady : (Solidity.Yul.RawLoopBody.run body fuel state).1 ≠ .error .timeout := by
      intro bad
      apply terminal
      rw [Solidity.Yul.RawSourceAdapterDoWhile.run]
      dsimp only [Solidity.Yul.RawSourceAdapter.body]
      rw [bad]
    have same := Solidity.Yul.RawLoopBodyHorizon.successor ctx returns modifier u stmt body fuel state bodyReady
    conv => lhs; rw [Solidity.Yul.RawSourceAdapterDoWhile.run]
    conv => rhs; rw [Solidity.Yul.RawSourceAdapterDoWhile.run]
    dsimp only [Solidity.Yul.RawSourceAdapter.body]
    rw [same]
    cases actual : Solidity.Yul.RawLoopBody.run body fuel state with
    | mk tag next =>
      cases tag with
      | error halt => rfl
      | ok flow =>
        cases flow with
        | normal | continue_ _ =>
          apply tail next
          rw [Solidity.Yul.RawSourceAdapterDoWhile.run] at terminal
          dsimp only [Solidity.Yul.RawSourceAdapter.body] at terminal
          rw [actual] at terminal
          exact terminal
        | break_ _ => rfl
        | leave_ impossible => cases impossible

theorem extension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.body body) (fuel+extra) state = Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.body body) fuel state := by
  intro ctx returns modifier u condition test stmt body fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : (Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.body body) (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (successor ctx returns modifier u condition test stmt body (fuel+extra) state ready).trans ih

theorem adapterSuccessor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 ((Solidity.Yul.RawSourceAdapterDoWhile.adapter test (Solidity.Yul.RawSourceAdapter.body body)).run fuel state).1 ≠ .error .timeout →
 (Solidity.Yul.RawSourceAdapterDoWhile.adapter test (Solidity.Yul.RawSourceAdapter.body body)).run (fuel+1) state = (Solidity.Yul.RawSourceAdapterDoWhile.adapter test (Solidity.Yul.RawSourceAdapter.body body)).run fuel state := by
  intro ctx returns modifier u condition test stmt body fuel state terminal
  have ready : (Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 ≠ .error .timeout := by
    intro bad
    apply terminal
    change (Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.body body) fuel state).1.map
      (fun _ => (Solidity.Yul.Closed.Flow.normal : Solidity.Yul.RawLoopBody.Flow)) = .error .timeout
    rw [bad]
    rfl
  have same := successor ctx returns modifier u condition test stmt body fuel state ready
  simp only [Solidity.Yul.RawSourceAdapterDoWhile.adapter,same]

theorem adapterExtension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 ((Solidity.Yul.RawSourceAdapterDoWhile.adapter test (Solidity.Yul.RawSourceAdapter.body body)).run fuel state).1 ≠ .error .timeout →
 (Solidity.Yul.RawSourceAdapterDoWhile.adapter test (Solidity.Yul.RawSourceAdapter.body body)).run (fuel+extra) state = (Solidity.Yul.RawSourceAdapterDoWhile.adapter test (Solidity.Yul.RawSourceAdapter.body body)).run fuel state := by
  intro ctx returns modifier u condition test stmt body fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : ((Solidity.Yul.RawSourceAdapterDoWhile.adapter test (Solidity.Yul.RawSourceAdapter.body body)).run (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (adapterSuccessor ctx returns modifier u condition test stmt body (fuel+extra) state ready).trans ih

end Solidity.Yul.RawDoWhileHorizon
