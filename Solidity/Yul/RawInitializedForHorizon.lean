import Solidity.Yul.RawSourceAdapterFor
import Solidity.Yul.RawAdapterLoopHorizon

/-! Completed actual same-context initialized no-post for-loop driver and adapter horizons.
Concrete initializer/body certificates preserve full raw frames; clean Source
correctness remains separate. Initializer break/continue stay stuck. -/
namespace Solidity.Yul.RawInitializedForHorizon

theorem successor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (initial : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (initProof : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u initial)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSourceAdapterFor.run (Solidity.Yul.RawSourceAdapter.body initProof) test (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawSourceAdapterFor.run (Solidity.Yul.RawSourceAdapter.body initProof) test (Solidity.Yul.RawSourceAdapter.body body) (fuel+1) state = Solidity.Yul.RawSourceAdapterFor.run (Solidity.Yul.RawSourceAdapter.body initProof) test (Solidity.Yul.RawSourceAdapter.body body) fuel state := by
  intro ctx returns modifier u initial initProof condition test stmt body fuel state terminal
  cases fuel with
  | zero => exact False.elim (terminal rfl)
  | succ fuel =>
    have ready : (Solidity.Yul.RawLoopBody.run initProof fuel state).1 ≠ .error .timeout := by
      intro bad
      apply terminal
      rw [Solidity.Yul.RawSourceAdapterFor.run]
      dsimp only [Solidity.Yul.RawSourceAdapter.body]
      rw [bad]
    have same := Solidity.Yul.RawLoopBodyHorizon.successor ctx returns modifier u initial initProof fuel state ready
    conv => lhs; rw [Solidity.Yul.RawSourceAdapterFor.run]
    conv => rhs; rw [Solidity.Yul.RawSourceAdapterFor.run]
    dsimp only [Solidity.Yul.RawSourceAdapter.body]
    rw [same]
    cases actual : Solidity.Yul.RawLoopBody.run initProof fuel state with
    | mk tag next =>
      cases tag with
      | error halt => rfl
      | ok flow =>
        cases flow with
        | normal =>
          have ready : (Solidity.Yul.RawControlledWhile.run test body fuel next).1 ≠ .error .timeout := by
            rw [Solidity.Yul.RawSourceAdapterFor.run] at terminal
            dsimp only [Solidity.Yul.RawSourceAdapter.body] at terminal
            rw [actual] at terminal
            change (Solidity.Yul.RawSourceAdapterLoop.run test (Solidity.Yul.RawSourceAdapter.body body) fuel next).1 ≠ .error .timeout at terminal
            rw [Solidity.Yul.RawAdapterLoopHorizon.body_agrees] at terminal
            exact terminal
          change Solidity.Yul.RawSourceAdapterLoop.run test (Solidity.Yul.RawSourceAdapter.body body) (fuel+1) next =
            Solidity.Yul.RawSourceAdapterLoop.run test (Solidity.Yul.RawSourceAdapter.body body) fuel next
          simp only [Solidity.Yul.RawAdapterLoopHorizon.body_agrees]
          exact Solidity.Yul.RawControlledWhileHorizon.successor ctx returns modifier u condition test stmt body fuel next ready
        | break_ _ | continue_ _ => rfl
        | leave_ impossible => cases impossible

theorem extension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (initial : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (initProof : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u initial)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSourceAdapterFor.run (Solidity.Yul.RawSourceAdapter.body initProof) test (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawSourceAdapterFor.run (Solidity.Yul.RawSourceAdapter.body initProof) test (Solidity.Yul.RawSourceAdapter.body body) (fuel+extra) state = Solidity.Yul.RawSourceAdapterFor.run (Solidity.Yul.RawSourceAdapter.body initProof) test (Solidity.Yul.RawSourceAdapter.body body) fuel state := by
  intro ctx returns modifier u initial initProof condition test stmt body fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : (Solidity.Yul.RawSourceAdapterFor.run (Solidity.Yul.RawSourceAdapter.body initProof) test (Solidity.Yul.RawSourceAdapter.body body) (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (successor ctx returns modifier u initial initProof condition test stmt body (fuel+extra) state ready).trans ih

theorem adapterSuccessor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (initial : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (initProof : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u initial)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 ((Solidity.Yul.RawSourceAdapterFor.adapter (Solidity.Yul.RawSourceAdapter.body initProof) test (Solidity.Yul.RawSourceAdapter.body body)).run fuel state).1 ≠ .error .timeout →
 (Solidity.Yul.RawSourceAdapterFor.adapter (Solidity.Yul.RawSourceAdapter.body initProof) test (Solidity.Yul.RawSourceAdapter.body body)).run (fuel+1) state = (Solidity.Yul.RawSourceAdapterFor.adapter (Solidity.Yul.RawSourceAdapter.body initProof) test (Solidity.Yul.RawSourceAdapter.body body)).run fuel state := by
  intro ctx returns modifier u initial initProof condition test stmt body fuel state terminal
  have ready : (Solidity.Yul.RawSourceAdapterFor.run (Solidity.Yul.RawSourceAdapter.body initProof) test (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 ≠ .error .timeout := by
    intro bad
    apply terminal
    change (Solidity.Yul.RawSourceAdapterFor.run (Solidity.Yul.RawSourceAdapter.body initProof) test (Solidity.Yul.RawSourceAdapter.body body) fuel state).1.map
      (fun _ => (Solidity.Yul.Closed.Flow.normal : Solidity.Yul.RawLoopBody.Flow)) = .error .timeout
    rw [bad]
    rfl
  have same := successor ctx returns modifier u initial initProof condition test stmt body fuel state ready
  simp only [Solidity.Yul.RawSourceAdapterFor.adapter,same]

theorem adapterExtension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (initial : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (initProof : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u initial)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 ((Solidity.Yul.RawSourceAdapterFor.adapter (Solidity.Yul.RawSourceAdapter.body initProof) test (Solidity.Yul.RawSourceAdapter.body body)).run fuel state).1 ≠ .error .timeout →
 (Solidity.Yul.RawSourceAdapterFor.adapter (Solidity.Yul.RawSourceAdapter.body initProof) test (Solidity.Yul.RawSourceAdapter.body body)).run (fuel+extra) state = (Solidity.Yul.RawSourceAdapterFor.adapter (Solidity.Yul.RawSourceAdapter.body initProof) test (Solidity.Yul.RawSourceAdapter.body body)).run fuel state := by
  intro ctx returns modifier u initial initProof condition test stmt body fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : ((Solidity.Yul.RawSourceAdapterFor.adapter (Solidity.Yul.RawSourceAdapter.body initProof) test (Solidity.Yul.RawSourceAdapter.body body)).run (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (adapterSuccessor ctx returns modifier u initial initProof condition test stmt body (fuel+extra) state ready).trans ih

end Solidity.Yul.RawInitializedForHorizon
