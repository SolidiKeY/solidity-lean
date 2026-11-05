import Solidity.Yul.RawControlledWhile

/-! Exact word-view preservation for actual read-only condition/continue execution.
Raw capture metadata may change; these laws do not claim whole-frame identity. -/
namespace Solidity.Yul.RawReadOnlyViews

theorem condition : ∀ (ctx : Solidity.Source.Ctx) (index : Solidity.Source.Idx ctx.tys .bool)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.view (Solidity.Yul.RawCondition.eval (.base (.local index)) fuel state).2 =
 Solidity.Yul.RawFrame.view state := by
  intro ctx index fuel state
  have actual := (Solidity.Yul.RawCondition.full_state (.base (.local index)) fuel state).1
  cases fuel <;> exact actual.trans (Solidity.Yul.RawCoherent.prepare_view state)

theorem continueBody : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (index : Solidity.Source.Idx ctx.tys .bool)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.view (Solidity.Yul.RawLoopBody.run (ctx := ctx) (returns := returns) (modifier := modifier) (u := u) (.ifThen (.base (.local index)) .continue_) fuel state).2 = Solidity.Yul.RawFrame.view state := by
  intro ctx returns modifier u index fuel state
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [Solidity.Yul.RawLoopBody.run_ifThen]
    have preserved := Solidity.Yul.RawReadOnlyViews.condition ctx index fuel state
    cases actual : Solidity.Yul.RawCondition.eval (.base (.local index)) fuel state with
    | mk result next =>
      rw [actual] at preserved
      cases result with
      | error halt => exact preserved
      | ok choice =>
        cases choice with
        | false => exact preserved
        | true => cases fuel <;> exact preserved

theorem loop : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (index : Solidity.Source.Idx ctx.tys .bool)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlledWhile.run (ctx := ctx) (returns := returns) (modifier := modifier) (u := u) (.base (.local index)) (.ifThen (.base (.local index)) .continue_) fuel state).2 = Solidity.Yul.RawFrame.view state := by
  intro ctx returns modifier u index fuel
  induction fuel with
  | zero => intro state; rfl
  | succ fuel ih =>
    intro state
    rw [Solidity.Yul.RawControlledWhile.run]
    have conditionView := Solidity.Yul.RawReadOnlyViews.condition ctx index fuel state
    cases actual : Solidity.Yul.RawCondition.eval (.base (.local index)) fuel state with
    | mk result next =>
      rw [actual] at conditionView
      cases result with
      | error halt => exact conditionView
      | ok choice =>
        cases choice with
        | false => exact conditionView
        | true =>
          have bodyView := Solidity.Yul.RawReadOnlyViews.continueBody ctx returns modifier u index fuel next
          cases bodyActual : Solidity.Yul.RawLoopBody.run (ctx := ctx) (returns := returns) (modifier := modifier) (u := u)
              (.ifThen (.base (.local index)) .continue_) fuel next with
          | mk tag after =>
            rw [bodyActual] at bodyView
            cases tag with
            | error halt => exact bodyView.trans conditionView
            | ok flow =>
              cases flow with
              | normal => exact (ih after).trans (bodyView.trans conditionView)
              | continue_ h => exact (ih after).trans (bodyView.trans conditionView)
              | break_ h => exact bodyView.trans conditionView
              | leave_ impossible => cases impossible

end Solidity.Yul.RawReadOnlyViews
