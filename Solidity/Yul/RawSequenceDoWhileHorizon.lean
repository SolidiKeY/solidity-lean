import Solidity.Yul.RawSourceAdapterDoWhile
import Solidity.Yul.RawAdapterSequenceLoopHorizon

/-! Completed concrete sequence/block body-first horizons preserve full raw frames.
Break skips the condition; no raw stability is inferred for arbitrary adapters. -/
namespace Solidity.Yul.RawSequenceDoWhileHorizon

theorem successor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawControlSequence.Supported ctx returns modifier u items)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body)) fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body)) (fuel+1) state = Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body)) fuel state := by
  intro ctx returns modifier u condition test items body fuel
  induction fuel with
  | zero => intro state terminal; exact False.elim (terminal rfl)
  | succ fuel ih =>
    intro state terminal
    have tail : ∀ next : Solidity.Yul.RawFrame.State ctx,
        (Solidity.Yul.RawSourceAdapterDoWhile.after test
          (Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body)) fuel) fuel next).1 ≠ .error .timeout →
        Solidity.Yul.RawSourceAdapterDoWhile.after test
          (Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body)) (fuel+1)) (fuel+1) next =
        Solidity.Yul.RawSourceAdapterDoWhile.after test
          (Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body)) fuel) fuel next := by
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
    have bodyReady : (Solidity.Yul.RawControlSequence.block body fuel state).1 ≠ .error .timeout := by
      intro bad
      apply terminal
      rw [Solidity.Yul.RawSourceAdapterDoWhile.run]
      simp only [Solidity.Yul.RawAdapterSequenceLoopHorizon.block_agrees]
      rw [bad]
    have same := Solidity.Yul.RawControlSequenceHorizon.blockSuccessor ctx returns modifier u items body fuel state bodyReady
    conv => lhs; rw [Solidity.Yul.RawSourceAdapterDoWhile.run]
    conv => rhs; rw [Solidity.Yul.RawSourceAdapterDoWhile.run]
    simp only [Solidity.Yul.RawAdapterSequenceLoopHorizon.block_agrees]
    rw [same]
    cases actual : Solidity.Yul.RawControlSequence.block body fuel state with
    | mk tag next =>
      cases tag with
      | error halt => rfl
      | ok flow =>
        cases flow with
        | normal | continue_ _ =>
          apply tail next
          rw [Solidity.Yul.RawSourceAdapterDoWhile.run] at terminal
          rw [Solidity.Yul.RawAdapterSequenceLoopHorizon.block_agrees] at terminal
          rw [actual] at terminal
          exact terminal
        | break_ _ => rfl
        | leave_ impossible => cases impossible

theorem extension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawControlSequence.Supported ctx returns modifier u items)
 (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body)) fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body)) (fuel+extra) state = Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body)) fuel state := by
  intro ctx returns modifier u condition test items body fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : (Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body)) (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (successor ctx returns modifier u condition test items body (fuel+extra) state ready).trans ih

theorem adapterSuccessor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawControlSequence.Supported ctx returns modifier u items)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 ((Solidity.Yul.RawSourceAdapterDoWhile.adapter test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body))).run fuel state).1 ≠ .error .timeout →
 (Solidity.Yul.RawSourceAdapterDoWhile.adapter test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body))).run (fuel+1) state = (Solidity.Yul.RawSourceAdapterDoWhile.adapter test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body))).run fuel state := by
  intro ctx returns modifier u condition test items body fuel state terminal
  have ready : (Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body)) fuel state).1 ≠ .error .timeout := by
    intro bad
    apply terminal
    change (Solidity.Yul.RawSourceAdapterDoWhile.run test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body)) fuel state).1.map
      (fun _ => (Solidity.Yul.Closed.Flow.normal : Solidity.Yul.RawLoopBody.Flow)) = .error .timeout
    rw [bad]
    rfl
  have same := successor ctx returns modifier u condition test items body fuel state ready
  simp only [Solidity.Yul.RawSourceAdapterDoWhile.adapter,same]

theorem adapterExtension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawControlSequence.Supported ctx returns modifier u items)
 (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 ((Solidity.Yul.RawSourceAdapterDoWhile.adapter test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body))).run fuel state).1 ≠ .error .timeout →
 (Solidity.Yul.RawSourceAdapterDoWhile.adapter test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body))).run (fuel+extra) state = (Solidity.Yul.RawSourceAdapterDoWhile.adapter test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body))).run fuel state := by
  intro ctx returns modifier u condition test items body fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : ((Solidity.Yul.RawSourceAdapterDoWhile.adapter test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body))).run (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (adapterSuccessor ctx returns modifier u condition test items body (fuel+extra) state ready).trans ih

end Solidity.Yul.RawSequenceDoWhileHorizon
