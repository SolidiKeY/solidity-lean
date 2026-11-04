import Solidity.Yul.RawForPostHorizon

/-! Completed actual same-context initialized for-post driver and adapter horizons.
Concrete initializer/body certificates preserve full raw frames; clean Source
correctness remains separate. Initializer break/continue stay stuck. -/
namespace Solidity.Yul.RawInitializedForPostHorizon

theorem successor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (initial : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (initProof : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u initial)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSourceForPost.Initialized.run (Solidity.Yul.RawSourceAdapter.body initProof) test step (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawSourceForPost.Initialized.run (Solidity.Yul.RawSourceAdapter.body initProof) test step (Solidity.Yul.RawSourceAdapter.body body) (fuel+1) state = Solidity.Yul.RawSourceForPost.Initialized.run (Solidity.Yul.RawSourceAdapter.body initProof) test step (Solidity.Yul.RawSourceAdapter.body body) fuel state := by
  intro ctx returns modifier u initial initProof condition test post step stmt body fuel state terminal
  cases fuel with
  | zero => exact False.elim (terminal rfl)
  | succ fuel =>
    have ready : (Solidity.Yul.RawLoopBody.run initProof fuel state).1 ≠ .error .timeout := by
      intro bad
      apply terminal
      rw [Solidity.Yul.RawSourceForPost.Initialized.run]
      dsimp only [Solidity.Yul.RawSourceAdapter.body]
      rw [bad]
    have same := Solidity.Yul.RawLoopBodyHorizon.successor ctx returns modifier u initial initProof fuel state ready
    conv => lhs; rw [Solidity.Yul.RawSourceForPost.Initialized.run]
    conv => rhs; rw [Solidity.Yul.RawSourceForPost.Initialized.run]
    dsimp only [Solidity.Yul.RawSourceAdapter.body]
    rw [same]
    cases actual : Solidity.Yul.RawLoopBody.run initProof fuel state with
    | mk tag next =>
      cases tag with
      | error halt => rfl
      | ok flow =>
        cases flow with
        | normal =>
          apply Solidity.Yul.RawForPostHorizon.successor ctx returns modifier u condition test post step stmt body fuel next
          rw [Solidity.Yul.RawSourceForPost.Initialized.run] at terminal
          dsimp only [Solidity.Yul.RawSourceAdapter.body] at terminal
          rw [actual] at terminal
          exact terminal
        | break_ _ | continue_ _ => rfl
        | leave_ impossible => cases impossible

theorem extension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (initial : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (initProof : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u initial)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSourceForPost.Initialized.run (Solidity.Yul.RawSourceAdapter.body initProof) test step (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawSourceForPost.Initialized.run (Solidity.Yul.RawSourceAdapter.body initProof) test step (Solidity.Yul.RawSourceAdapter.body body) (fuel+extra) state = Solidity.Yul.RawSourceForPost.Initialized.run (Solidity.Yul.RawSourceAdapter.body initProof) test step (Solidity.Yul.RawSourceAdapter.body body) fuel state := by
  intro ctx returns modifier u initial initProof condition test post step stmt body fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : (Solidity.Yul.RawSourceForPost.Initialized.run (Solidity.Yul.RawSourceAdapter.body initProof) test step (Solidity.Yul.RawSourceAdapter.body body) (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (successor ctx returns modifier u initial initProof condition test post step stmt body (fuel+extra) state ready).trans ih

theorem adapterSuccessor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (initial : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (initProof : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u initial)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 ((Solidity.Yul.RawSourceForPost.Initialized.adapter (Solidity.Yul.RawSourceAdapter.body initProof) test step (Solidity.Yul.RawSourceAdapter.body body)).run fuel state).1 ≠ .error .timeout →
 (Solidity.Yul.RawSourceForPost.Initialized.adapter (Solidity.Yul.RawSourceAdapter.body initProof) test step (Solidity.Yul.RawSourceAdapter.body body)).run (fuel+1) state = (Solidity.Yul.RawSourceForPost.Initialized.adapter (Solidity.Yul.RawSourceAdapter.body initProof) test step (Solidity.Yul.RawSourceAdapter.body body)).run fuel state := by
  intro ctx returns modifier u initial initProof condition test post step stmt body fuel state terminal
  have ready : (Solidity.Yul.RawSourceForPost.Initialized.run (Solidity.Yul.RawSourceAdapter.body initProof) test step (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 ≠ .error .timeout := by
    intro bad
    apply terminal
    change (Solidity.Yul.RawSourceForPost.Initialized.run (Solidity.Yul.RawSourceAdapter.body initProof) test step (Solidity.Yul.RawSourceAdapter.body body) fuel state).1.map
      (fun _ => (Solidity.Yul.Closed.Flow.normal : Solidity.Yul.RawLoopBody.Flow)) = .error .timeout
    rw [bad]
    rfl
  have same := successor ctx returns modifier u initial initProof condition test post step stmt body fuel state ready
  simp only [Solidity.Yul.RawSourceForPost.Initialized.adapter,same]

theorem adapterExtension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (initial : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (initProof : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u initial)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 ((Solidity.Yul.RawSourceForPost.Initialized.adapter (Solidity.Yul.RawSourceAdapter.body initProof) test step (Solidity.Yul.RawSourceAdapter.body body)).run fuel state).1 ≠ .error .timeout →
 (Solidity.Yul.RawSourceForPost.Initialized.adapter (Solidity.Yul.RawSourceAdapter.body initProof) test step (Solidity.Yul.RawSourceAdapter.body body)).run (fuel+extra) state = (Solidity.Yul.RawSourceForPost.Initialized.adapter (Solidity.Yul.RawSourceAdapter.body initProof) test step (Solidity.Yul.RawSourceAdapter.body body)).run fuel state := by
  intro ctx returns modifier u initial initProof condition test post step stmt body fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : ((Solidity.Yul.RawSourceForPost.Initialized.adapter (Solidity.Yul.RawSourceAdapter.body initProof) test step (Solidity.Yul.RawSourceAdapter.body body)).run (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (adapterSuccessor ctx returns modifier u initial initProof condition test post step stmt body (fuel+extra) state ready).trans ih

end Solidity.Yul.RawInitializedForPostHorizon
