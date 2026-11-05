import Solidity.Yul.RawSourceAdapterLoop
import Solidity.Yul.RawSequenceWhileHorizon

/-! Concrete sequence/block P16 adapter agreement and completed whole-frame horizons.
No stability inference for arbitrary adapters from clean Source correctness. -/
namespace Solidity.Yul.RawAdapterSequenceLoopHorizon

theorem block_agrees : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawControlSequence.Supported ctx returns modifier u items)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body)).run fuel state = Solidity.Yul.RawControlSequence.block body fuel state := by
  intro ctx returns modifier u items body fuel state
  cases fuel <;> rfl

theorem body_agrees : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawControlSequence.Supported ctx returns modifier u items)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawSourceAdapterLoop.run test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body)) fuel state =
 Solidity.Yul.RawSequenceWhile.run test body fuel state := by
  intro ctx returns modifier u items body condition test fuel
  induction fuel with
  | zero => intro state; rfl
  | succ fuel ih =>
    intro state
    conv => lhs; rw [Solidity.Yul.RawSourceAdapterLoop.run]
    conv => rhs; rw [Solidity.Yul.RawSequenceWhile.run]
    cases actual : Solidity.Yul.RawCondition.eval test fuel state with
    | mk result next =>
      cases result with
      | error halt => rfl
      | ok choice =>
        cases choice with
        | false => rfl
        | true =>
          rw [Solidity.Yul.RawAdapterSequenceLoopHorizon.block_agrees]
          cases bodyActual : Solidity.Yul.RawControlSequence.block body fuel next with
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
 (modifier u : Bool)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawControlSequence.Supported ctx returns modifier u items)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 ((Solidity.Yul.RawSourceAdapterLoop.loop test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body))).run fuel state).1 ≠ .error .timeout →
 (Solidity.Yul.RawSourceAdapterLoop.loop test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body))).run (fuel+1) state = (Solidity.Yul.RawSourceAdapterLoop.loop test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body))).run fuel state := by
  intro ctx returns modifier u items body condition test fuel state terminal
  have ready : (Solidity.Yul.RawSequenceWhile.run test body fuel state).1 ≠ .error .timeout := by
    intro bad
    apply terminal
    change (Solidity.Yul.RawSourceAdapterLoop.run test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body)) fuel state).1.map
      (fun _ => (Solidity.Yul.Closed.Flow.normal : Solidity.Yul.RawLoopBody.Flow)) = .error .timeout
    rw [Solidity.Yul.RawAdapterSequenceLoopHorizon.body_agrees,bad]
    rfl
  have same := Solidity.Yul.RawSequenceWhileHorizon.successor ctx returns modifier u condition test items body fuel state ready
  change (let actual := Solidity.Yul.RawSourceAdapterLoop.run test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body)) (fuel+1) state
          (actual.1.map (fun _ => (Solidity.Yul.Closed.Flow.normal : Solidity.Yul.RawLoopBody.Flow)),actual.2)) =
    (let actual := Solidity.Yul.RawSourceAdapterLoop.run test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body)) fuel state
     (actual.1.map (fun _ => (Solidity.Yul.Closed.Flow.normal : Solidity.Yul.RawLoopBody.Flow)),actual.2))
  simp only [Solidity.Yul.RawAdapterSequenceLoopHorizon.body_agrees,same]

theorem extension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawControlSequence.Supported ctx returns modifier u items)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 ((Solidity.Yul.RawSourceAdapterLoop.loop test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body))).run fuel state).1 ≠ .error .timeout →
 (Solidity.Yul.RawSourceAdapterLoop.loop test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body))).run (fuel+extra) state = (Solidity.Yul.RawSourceAdapterLoop.loop test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body))).run fuel state := by
  intro ctx returns modifier u items body condition test fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : ((Solidity.Yul.RawSourceAdapterLoop.loop test (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence body))).run (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (Solidity.Yul.RawAdapterSequenceLoopHorizon.successor ctx returns modifier u items body condition test (fuel+extra) state ready).trans ih

end Solidity.Yul.RawAdapterSequenceLoopHorizon
