import Solidity.Lowering.Readonly.CaptureFailureControls

/-! Guard separate phase assumptions being mistaken for jointly feasible actual
external-call failures. Closed input conjunctions include the declaration signature
and every phase run at the same typed state sequence. Clients apply unchanged
capture laws; later phases cannot erase timeout or post-argument rejection.
These are source-model witnesses, not compiler/EVM/gas/fork or frame adequacy. -/
namespace Solidity.H62.ReadonlyBind.CaptureJointControls
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Lowering.Readonly
open Solidity.Backend.Passes.SourceCallControls (dCallOut)
open ReceiverControls (target arguments before after signature)

/-- The receiver itself exhausts the evaluator before any argument mutation. -/
theorem target_inputs :
    dCallOut.fnSig EB = some ([.address false], []) ∧
    (evalE (GB answerOnly) FC 0 target).run before = (.error .timeout, before) :=
  ⟨signature, rfl⟩

/-- Successful receiver and exhausted value runs use exactly the same state. -/
theorem value_inputs :
    dCallOut.fnSig EB = some ([.address false], []) ∧
    (evalE (Γ := [.address false]) (GB answerOnly) FC 1 (.this "C")).run before =
      (.ok (.val (.contract FC.this)), before) ∧
    (evalE (GB answerOnly) FC 1 (lit 0)).run before = (.error .timeout, before) :=
  ⟨signature, rfl, rfl⟩

/-- The integer bound and all three actual evaluation hypotheses hold together. -/
theorem arguments_inputs :
    dCallOut.fnSig EB = some ([.address false], []) ∧
    (IntTy.u256.lo ≤ 0 ∧ 0 ≤ IntTy.u256.hi) ∧
    (evalE (Γ := [.address false]) (GB answerOnly) FC 2 (.this "C")).run before =
      (.ok (.val (.contract FC.this)), before) ∧
    (evalE (GB answerOnly) FC 2 (lit 0)).run before =
      (.ok (.val (.int 0 (by decide))), before) ∧
    (evalConvArgs (GB answerOnly) FC 2 arguments).run before =
      (.error .timeout, before) :=
  ⟨signature, by decide, rfl, rfl, rfl⟩

/-- Rejection occurs only after the actual argument mutation, encoding and lookup. -/
theorem rejection_inputs :
    dCallOut.fnSig EB = some ([.address false], []) ∧
    (IntTy.u256.lo ≤ 0 ∧ 0 ≤ IntTy.u256.hi) ∧
    (evalE CaptureFailureControls.noCode FC 6 target).run before =
      (.ok (.val (.contract ext)), before) ∧
    (evalE CaptureFailureControls.noCode FC 6 (lit 0)).run before =
      (.ok (.val (.int 0 (by decide))), before) ∧
    (evalConvArgs CaptureFailureControls.noCode FC 6 arguments).run before =
      (.ok (.cons (.address (addr 4)) .nil), after) ∧
    (encodeVals FC 6 false ((.cons (.address (addr 4)) .nil : Vals EB.layout [.address false]).toR)).run after =
      (.ok (wordBytes (toWord 4)), after) ∧
    (instanceAt CaptureFailureControls.noCode ext : EM EB [.address false] _).run after =
      (.ok none, after) ∧
    ((none : Option String).isNone && !CaptureFailureControls.noCode.hasCode after.2.events ext) = true :=
  ⟨signature, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem target_failure :
    (evalE (GB answerOnly) FC 1
      (.extCall target dCallOut target_inputs.1 (lit 0) arguments)).run before =
      (.error .timeout, before) := by
  exact CaptureFailures.target_failed (GB answerOnly) FC 0 dCallOut target_inputs.1
    target (lit 0) arguments before before .timeout target_inputs.2

theorem value_failure :
    (evalE (GB answerOnly) FC 2
      (.extCall (.this "C") dCallOut value_inputs.1 (lit 0) arguments)).run before =
      (.error .timeout, before) := by
  exact CaptureFailures.value_failed (GB answerOnly) FC 1 dCallOut value_inputs.1
    (.this "C") (lit 0) arguments FC.this before before before .timeout
    value_inputs.2.1 value_inputs.2.2

theorem arguments_failure :
    (evalE (GB answerOnly) FC 3
      (.extCall (.this "C") dCallOut arguments_inputs.1 (lit 0) arguments)).run before =
      (.error .timeout, before) := by
  exact CaptureFailures.arguments_failed (GB answerOnly) FC 2 dCallOut arguments_inputs.1
    (.this "C") (lit 0) arguments FC.this 0 arguments_inputs.2.1
    before before before before .timeout
    arguments_inputs.2.2.1 arguments_inputs.2.2.2.1 arguments_inputs.2.2.2.2

theorem code_rejection :
    (evalE CaptureFailureControls.noCode FC 7
      (.extCall target dCallOut rejection_inputs.1 (lit 0) arguments)).run before =
      (.error (.revert []), after) := by
  exact CaptureFailures.code_rejected CaptureFailureControls.noCode FC 6 dCallOut rejection_inputs.1
    target (lit 0) arguments ext 0 rejection_inputs.2.1 (.cons (.address (addr 4)) .nil)
    (wordBytes (toWord 4)) none before before before after after after
    rejection_inputs.2.2.1 rejection_inputs.2.2.2.1 rejection_inputs.2.2.2.2.1
    rejection_inputs.2.2.2.2.2.1 rejection_inputs.2.2.2.2.2.2.1 rejection_inputs.2.2.2.2.2.2.2

/-- The rejection client preserves the visible mutation and never enters a callee. -/
theorem rejection_effect_boundary :
    after.1 ≠ before.1 ∧ after.2.events = before.2.events :=
  ⟨CaptureFailureControls.effect_not_rolled_back.2, rfl⟩

end Solidity.H62.ReadonlyBind.CaptureJointControls
