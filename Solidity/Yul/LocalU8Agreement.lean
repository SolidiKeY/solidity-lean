import Solidity.Yul.LocalU8Source

/-! Concrete composition with actual Source.evalE for checked frames.
The helper's real child agreements are discharged by the final structural
induction; they are not a replacement for that final theorem. -/
namespace Solidity.Yul.LocalU8Expr

theorem add_agrees {env ctx left right} (one : Supported env ctx left) (two : Supported env ctx right)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (checked : frame.checked = true)
    (leftAgreement : ∀ state, eval one glob.pipeline fuel (LocalState.ofClean state) =
      cleanOutcome ((Solidity.Source.evalE glob frame fuel left).run state))
    (rightAgreement : ∀ state, eval two glob.pipeline fuel (LocalState.ofClean state) =
      cleanOutcome ((Solidity.Source.evalE glob frame fuel right).run state))
    (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env) :
    eval (.add one two) glob.pipeline (fuel+2) (LocalState.ofClean state) =
      cleanOutcome ((Solidity.Source.evalE glob frame (fuel+2) (.binary .add left right)).run state) := by
  cases pipeline : glob.pipeline with
  | legacy =>
      have first := rightAgreement state
      rw [pipeline] at first
      cases rightRun : (Solidity.Source.evalE glob frame fuel right).run state with
      | mk rightResult middle =>
          rw [rightRun] at first
          cases rightResult with
          | error halt =>
              change eval two .legacy fuel (LocalState.ofClean state) =
                (.error halt,LocalState.ofClean middle) at first
              have pairRun : (Solidity.Source.evalPair glob frame (fuel+1) left right).run state =
                  (.error halt,middle) := by
                rw [source_pair_legacy left right glob frame fuel state pipeline,rightRun]
              rw [add_legacy,first,source_add_error left right glob frame (fuel+1) state middle halt pairRun]
              rfl
          | ok rightValue =>
              cases rightValue with
              | val rightValue =>
                  change eval two .legacy fuel (LocalState.ofClean state) =
                    (.ok (.clean rightValue),LocalState.ofClean middle) at first
                  have second := leftAgreement middle
                  rw [pipeline] at second
                  cases leftRun : (Solidity.Source.evalE glob frame fuel left).run middle with
                  | mk leftResult next =>
                      rw [leftRun] at second
                      cases leftResult with
                      | error halt =>
                          change eval one .legacy fuel (LocalState.ofClean middle) =
                            (.error halt,LocalState.ofClean next) at second
                          have pairRun : (Solidity.Source.evalPair glob frame (fuel+1) left right).run state =
                              (.error halt,next) := by
                            rw [source_pair_legacy left right glob frame fuel state pipeline,rightRun]
                            dsimp only
                            rw [leftRun]
                          rw [add_legacy,first]
                          dsimp only
                          rw [second,source_add_error left right glob frame (fuel+1) state next halt pairRun]
                          rfl
                      | ok leftValue =>
                          cases leftValue with
                          | val leftValue =>
                              change eval one .legacy fuel (LocalState.ofClean middle) =
                                (.ok (.clean leftValue),LocalState.ofClean next) at second
                              have pairRun : (Solidity.Source.evalPair glob frame (fuel+1) left right).run state =
                                  (.ok (.val leftValue,.val rightValue),next) := by
                                rw [source_pair_legacy left right glob frame fuel state pipeline,rightRun]
                                dsimp only
                                rw [leftRun]
                              rw [add_legacy,first]
                              dsimp only
                              rw [second,source_add_values left right glob frame (fuel+1) state next
                                leftValue rightValue checked pairRun]
                              simp only [Except.bind,LocalOperations.u8Binary_clean]
                              cases operation : Solidity.Source.binVal true .add leftValue rightValue <;> rfl
  | viaIR =>
      have first := leftAgreement state
      rw [pipeline] at first
      cases leftRun : (Solidity.Source.evalE glob frame fuel left).run state with
      | mk leftResult middle =>
          rw [leftRun] at first
          cases leftResult with
          | error halt =>
              change eval one .viaIR fuel (LocalState.ofClean state) =
                (.error halt,LocalState.ofClean middle) at first
              have pairRun : (Solidity.Source.evalPair glob frame (fuel+1) left right).run state =
                  (.error halt,middle) := by
                rw [source_pair_viaIR left right glob frame fuel state pipeline,leftRun]
              rw [add_viaIR,first,source_add_error left right glob frame (fuel+1) state middle halt pairRun]
              rfl
          | ok leftValue =>
              cases leftValue with
              | val leftValue =>
                  change eval one .viaIR fuel (LocalState.ofClean state) =
                    (.ok (.clean leftValue),LocalState.ofClean middle) at first
                  have second := rightAgreement middle
                  rw [pipeline] at second
                  cases rightRun : (Solidity.Source.evalE glob frame fuel right).run middle with
                  | mk rightResult next =>
                      rw [rightRun] at second
                      cases rightResult with
                      | error halt =>
                          change eval two .viaIR fuel (LocalState.ofClean middle) =
                            (.error halt,LocalState.ofClean next) at second
                          have pairRun : (Solidity.Source.evalPair glob frame (fuel+1) left right).run state =
                              (.error halt,next) := by
                            rw [source_pair_viaIR left right glob frame fuel state pipeline,leftRun]
                            dsimp only
                            rw [rightRun]
                          rw [add_viaIR,first]
                          dsimp only
                          rw [second,source_add_error left right glob frame (fuel+1) state next halt pairRun]
                          rfl
                      | ok rightValue =>
                          cases rightValue with
                          | val rightValue =>
                              change eval two .viaIR fuel (LocalState.ofClean middle) =
                                (.ok (.clean rightValue),LocalState.ofClean next) at second
                              have pairRun : (Solidity.Source.evalPair glob frame (fuel+1) left right).run state =
                                  (.ok (.val leftValue,.val rightValue),next) := by
                                rw [source_pair_viaIR left right glob frame fuel state pipeline,leftRun]
                                dsimp only
                                rw [rightRun]
                              rw [add_viaIR,first]
                              dsimp only
                              rw [second,source_add_values left right glob frame (fuel+1) state next
                                leftValue rightValue checked pairRun]
                              simp only [Except.bind,LocalOperations.u8Binary_clean]
                              cases operation : Solidity.Source.binVal true .add leftValue rightValue <;> rfl

/-- Actual Source checked-frame agreement for every certified tree/horizon.
The only frame restriction is explicit, not an assumed operation/child law. -/
theorem source_agrees {env ctx expr} (proof : Supported env ctx expr)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (checked : frame.checked = true)
    (fuel : Nat) (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env) :
    eval proof glob.pipeline fuel (LocalState.ofClean state) =
      cleanOutcome ((Solidity.Source.evalE glob frame fuel expr).run state) := by
  induction proof generalizing fuel state with
  | «local» index =>
      cases fuel with
      | zero => exact source_zero _ glob frame state
      | succ fuel => exact source_local index fuel glob frame state
  | @assign inner target child ih =>
      cases fuel with
      | zero => exact source_zero _ glob frame state
      | succ fuel =>
          have induct := ih fuel state
          cases actual : (Solidity.Source.evalE glob frame fuel inner).run state with
          | mk result next =>
              rw [actual] at induct
              cases result with
              | error halt =>
                  change eval child glob.pipeline fuel (LocalState.ofClean state) =
                    (.error halt,LocalState.ofClean next) at induct
                  rw [assign_step,induct,source_assign_error target inner glob frame fuel state next halt actual]
                  rfl
              | ok value =>
                  cases value with
                  | val value =>
                      change eval child glob.pipeline fuel (LocalState.ofClean state) =
                        (.ok (.clean value),LocalState.ofClean next) at induct
                      cases fuel with
                      | zero => cases actual
                      | succ fuel =>
                          rw [assign_step,induct,
                            source_assign_value target inner glob frame fuel state next value actual]
                          simp only [cleanOutcome,LocalState.ofClean,LocalBoolExpr.ofClean_set]
                          rfl
  | @add left right one two ihOne ihTwo =>
      cases fuel with
      | zero => exact source_zero _ glob frame state
      | succ fuel =>
          cases fuel with
          | zero =>
              have pairRun : (Solidity.Source.evalPair glob frame 0 left right).run state =
                  (.error .timeout,state) := rfl
              rw [add_one,source_add_error left right glob frame 0 state state .timeout pairRun]
              rfl
          | succ fuel => exact add_agrees one two glob frame fuel checked (ihOne fuel) (ihTwo fuel) state

end Solidity.Yul.LocalU8Expr
