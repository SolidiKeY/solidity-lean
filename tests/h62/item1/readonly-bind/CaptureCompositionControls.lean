import Solidity.Lowering.Readonly.CaptureFailureControls
import EncodingFailureControls

/-! Guard partial phase witnesses being reported as complete encoding-failure or
successful-capture feasibility. Each conjunction includes signature, integer
validity and all original run hypotheses at one state sequence. The encoding
case uses a real allocated typed array; successful capture retains argument
mutation without retargeting the previously evaluated receiver. These are source
capture facts, not callee/compiler success, EVM/gas/fork or frame adequacy. -/
namespace Solidity.H62.ReadonlyBind.CaptureCompositionControls
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Lowering.Readonly
open Solidity.Backend.Passes.SourceTypedCall
open Solidity.Backend.Passes.SourceCallControls (dCallOut)
open ReceiverControls (target arguments before after signature captured)

/-- Signature and bounds belong to the same actual array-encoding failure. -/
theorem encoding_inputs :
    EncodingFailureControls.declaration.fnSig EB = some ([EncodingFailureControls.arrayTy], []) ∧
    (IntTy.u256.lo ≤ 0 ∧ 0 ≤ IntTy.u256.hi) ∧
    (evalE (Γ := [EncodingFailureControls.arrayTy]) (GB answerOnly) FC 6 (.this "C")).run EncodingFailureControls.before =
      (.ok (.val (.contract FC.this)), EncodingFailureControls.before) ∧
    (evalE (Γ := [EncodingFailureControls.arrayTy]) (GB answerOnly) FC 6 (lit 0)).run EncodingFailureControls.before =
      (.ok (.val (.int 0 (by decide))), EncodingFailureControls.before) ∧
    (evalConvArgs (GB answerOnly) FC 6 EncodingFailureControls.arguments).run EncodingFailureControls.before =
      (.ok EncodingFailureControls.values, EncodingFailureControls.before) ∧
    (encodeVals FC 6 false EncodingFailureControls.values.toR).run EncodingFailureControls.before =
      (.error (.stuck "not ABI-encodable"), EncodingFailureControls.before) :=
  ⟨EncodingFailureControls.signature, by decide, EncodingFailureControls.joint_capture⟩

theorem allocated_argument :
    EncodingFailureControls.before.2.heap.get sB.heap.next = some
      ⟨EncodingFailureControls.arrayTy, .array 1 (fun _ h => nomatch h) (fun _ => .val (.bool true))⟩ :=
  EncodingFailureControls.allocated

theorem encoding_failure :
    (evalE (GB answerOnly) FC 7
      (.extCall (.this "C") EncodingFailureControls.declaration encoding_inputs.1 (lit 0) EncodingFailureControls.arguments)).run EncodingFailureControls.before =
      (.error (.stuck "not ABI-encodable"), EncodingFailureControls.before) := by
  exact CaptureFailures.encoding_failed (GB answerOnly) FC 6 EncodingFailureControls.declaration encoding_inputs.1
    (.this "C") (lit 0) EncodingFailureControls.arguments FC.this 0 encoding_inputs.2.1 EncodingFailureControls.values
    EncodingFailureControls.before EncodingFailureControls.before EncodingFailureControls.before EncodingFailureControls.before EncodingFailureControls.before (.stuck "not ABI-encodable")
    encoding_inputs.2.2.1 encoding_inputs.2.2.2.1 encoding_inputs.2.2.2.2.1 encoding_inputs.2.2.2.2.2

/-- The six hypotheses follow one before-to-after sequence; encoding, lookup
and admission use the post-argument state. -/
theorem compose_inputs :
    dCallOut.fnSig EB = some ([.address false], []) ∧
    (IntTy.u256.lo ≤ 0 ∧ 0 ≤ IntTy.u256.hi) ∧
    (evalE (GB answerOnly) FC 6 target).run before = (.ok (.val (.contract ext)), before) ∧
    (evalE (GB answerOnly) FC 6 (lit 0)).run before =
      (.ok (.val (.int 0 (by decide))), before) ∧
    (evalConvArgs (GB answerOnly) FC 6 arguments).run before =
      (.ok (.cons (.address (addr 4)) .nil), after) ∧
    (encodeVals FC 6 false ((.cons (.address (addr 4)) .nil : Vals EB.layout [.address false]).toR)).run after =
      (.ok (wordBytes (toWord 4)), after) ∧
    (instanceAt (GB answerOnly) ext : EM EB [.address false] _).run after = (.ok none, after) ∧
    ((none : Option String).isNone && !(GB answerOnly).hasCode after.2.events ext) = false :=
  ⟨signature, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem capture_success :
    CapturedAt (GB answerOnly) FC 6 target dCallOut compose_inputs.1 (lit 0) arguments
      before after captured := by
  exact CapturePhases.compose (GB answerOnly) FC 6 dCallOut compose_inputs.1
    target (lit 0) arguments ext 0 compose_inputs.2.1 (.cons (.address (addr 4)) .nil)
    (wordBytes (toWord 4)) none before before before after after after
    compose_inputs.2.2.1 compose_inputs.2.2.2.1 compose_inputs.2.2.2.2.1
    compose_inputs.2.2.2.2.2.1 compose_inputs.2.2.2.2.2.2.1 compose_inputs.2.2.2.2.2.2.2

/-- Successful capture resumes at after, without reevaluating the receiver. -/
theorem resume_boundary :
    (evalE (GB answerOnly) FC 7
      (.extCall target dCallOut compose_inputs.1 (lit 0) arguments)).run before =
      (resume (GB answerOnly) FC 6 dCallOut [] captured).run after :=
  external_captured _ _ _ _ _ _ _ _ _ _ _ capture_success

theorem capture_observations :
    after.1 ≠ before.1 ∧ captured.receiver ≠ addr 4 ∧ after.2.events = before.2.events :=
  ⟨CaptureFailureControls.effect_not_rolled_back.2, ReceiverControls.receiver_not_retargeted, rfl⟩

end Solidity.H62.ReadonlyBind.CaptureCompositionControls
