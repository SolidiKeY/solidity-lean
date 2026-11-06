import Solidity.Yul.LocalBoolControlSource

/-! Concrete clean agreement for all trees of the control extension.
The final theorem discharges every source-step premise using actual source
execution and induction, and keeps the complete returned partial state. -/
namespace Solidity.Yul.LocalBoolControl
open LocalBoolExpr (cleanOutcome)

theorem source_agrees {env ctx expr} (proof : Supported env ctx expr)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env) :
    eval proof fuel (LocalState.ofClean state) =
      cleanOutcome ((Solidity.Source.evalE glob frame fuel expr).run state) := by
  induction proof generalizing fuel state with
  | base proof => exact LocalBoolExpr.source_agrees proof glob frame fuel state
  | @and left right one two ihOne ihTwo =>
      cases fuel with
      | zero => rw [zero]; rfl
      | succ fuel =>
          have induct := ihOne fuel state
          cases actual : (Solidity.Source.evalE glob frame fuel left).run state with
          | mk result next =>
              rw [actual] at induct
              cases result with
              | error halt =>
                  change eval one fuel (LocalState.ofClean state) =
                    (.error halt,LocalState.ofClean next) at induct
                  rw [and_step,induct,source_and_error left right glob frame fuel state next halt actual]
                  rfl
              | ok value =>
                  cases value with
                  | val value =>
                      cases value with
                      | bool value =>
                          change eval one fuel (LocalState.ofClean state) =
                            (.ok (.clean (.bool value)),LocalState.ofClean next) at induct
                          cases value with
                          | false =>
                              rw [and_step,induct,source_and_false left right glob frame fuel state next actual]
                              simp only [truth_clean,Bool.false_eq_true,if_false]
                              rfl
                          | true =>
                              rw [and_step,induct,source_and_true left right glob frame fuel state next actual]
                              simp only [truth_clean,if_true]
                              exact ihTwo fuel next
                      | memRef impossible _ => cases impossible
                      | storRef impossible _ => cases impossible
                      | cdRef impossible _ => cases impossible
  | @or left right one two ihOne ihTwo =>
      cases fuel with
      | zero => rw [zero]; rfl
      | succ fuel =>
          have induct := ihOne fuel state
          cases actual : (Solidity.Source.evalE glob frame fuel left).run state with
          | mk result next =>
              rw [actual] at induct
              cases result with
              | error halt =>
                  change eval one fuel (LocalState.ofClean state) =
                    (.error halt,LocalState.ofClean next) at induct
                  rw [or_step,induct,source_or_error left right glob frame fuel state next halt actual]
                  rfl
              | ok value =>
                  cases value with
                  | val value =>
                      cases value with
                      | bool value =>
                          change eval one fuel (LocalState.ofClean state) =
                            (.ok (.clean (.bool value)),LocalState.ofClean next) at induct
                          cases value with
                          | false =>
                              rw [or_step,induct,source_or_false left right glob frame fuel state next actual]
                              simp only [truth_clean,Bool.false_eq_true,if_false]
                              exact ihTwo fuel next
                          | true =>
                              rw [or_step,induct,source_or_true left right glob frame fuel state next actual]
                              simp only [truth_clean,if_true]
                              rfl
                      | memRef impossible _ => cases impossible
                      | storRef impossible _ => cases impossible
                      | cdRef impossible _ => cases impossible
  | @cond condition yes no test one two ihTest ihOne ihTwo =>
      cases fuel with
      | zero => rw [zero]; rfl
      | succ fuel =>
          have induct := ihTest fuel state
          cases actual : (Solidity.Source.evalE glob frame fuel condition).run state with
          | mk result next =>
              rw [actual] at induct
              cases result with
              | error halt =>
                  change eval test fuel (LocalState.ofClean state) =
                    (.error halt,LocalState.ofClean next) at induct
                  rw [cond_step,induct,source_cond_error condition yes no glob frame fuel state next halt actual]
                  rfl
              | ok value =>
                  cases value with
                  | val value =>
                      cases value with
                      | bool value =>
                          change eval test fuel (LocalState.ofClean state) =
                            (.ok (.clean (.bool value)),LocalState.ofClean next) at induct
                          cases value with
                          | false =>
                              rw [cond_step,induct,source_cond_false condition yes no glob frame fuel state next actual]
                              simp only [truth_clean,Bool.false_eq_true,if_false]
                              exact ihTwo fuel next
                          | true =>
                              rw [cond_step,induct,source_cond_true condition yes no glob frame fuel state next actual]
                              simp only [truth_clean,if_true]
                              exact ihOne fuel next
                      | memRef impossible _ => cases impossible
                      | storRef impossible _ => cases impossible
                      | cdRef impossible _ => cases impossible
  | @not inner child ih =>
      cases fuel with
      | zero => rw [zero]; rfl
      | succ fuel =>
          have induct := ih fuel state
          cases actual : (Solidity.Source.evalE glob frame fuel inner).run state with
          | mk result next =>
              rw [actual] at induct
              cases result with
              | error halt =>
                  change eval child fuel (LocalState.ofClean state) =
                    (.error halt,LocalState.ofClean next) at induct
                  rw [not_step,induct,LocalBoolExpr.source_not_error inner glob frame fuel state next halt actual]
                  rfl
              | ok value =>
                  cases value with
                  | val value =>
                      cases value with
                      | bool value =>
                          change eval child fuel (LocalState.ofClean state) =
                            (.ok (.clean (.bool value)),LocalState.ofClean next) at induct
                          rw [not_step,induct,LocalBoolExpr.source_not_bool inner glob frame fuel state next value actual]
                          simp only [Except.bind]
                          rw [LocalOperations.boolNot_clean]
                          rfl
                      | memRef impossible _ => cases impossible
                      | storRef impossible _ => cases impossible
                      | cdRef impossible _ => cases impossible
  | @assign inner target child ih =>
      cases fuel with
      | zero => rw [zero]; rfl
      | succ fuel =>
          have induct := ih fuel state
          cases actual : (Solidity.Source.evalE glob frame fuel inner).run state with
          | mk result next =>
              rw [actual] at induct
              cases result with
              | error halt =>
                  change eval child fuel (LocalState.ofClean state) =
                    (.error halt,LocalState.ofClean next) at induct
                  rw [assign_step,induct,LocalBoolExpr.source_assign_error target inner glob frame fuel state next halt actual]
                  rfl
              | ok value =>
                  cases value with
                  | val value =>
                      change eval child fuel (LocalState.ofClean state) =
                        (.ok (.clean value),LocalState.ofClean next) at induct
                      cases fuel with
                      | zero => cases actual
                      | succ fuel =>
                          rw [assign_step,induct,
                            LocalBoolExpr.source_assign_value target inner glob frame fuel state next value actual]
                          simp only [cleanOutcome,LocalState.ofClean,LocalBoolExpr.ofClean_set]
                          rfl

end Solidity.Yul.LocalBoolControl
