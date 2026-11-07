import Solidity.Backend.WorldCalls.SourceBridgeControls
import Solidity.Backend.Passes.SourceCallBoundary

/-! Ordinary frozen consumers applied with every premise supplied together.
These are concrete paired/source fixtures, not compiler-success replacements.
No global record inhabitance is substituted for the actual per-input runs. -/
namespace Solidity.H62.ReadonlyAudit.JointClients
open Solidity.Source Solidity.Source.SemanticsExamples Solidity.Roadmap
open Solidity.Backend.WorldCalls Solidity.Lowering.Readonly

theorem restore_client : PaymentControl.view PaymentControl.final = PaymentControl.view PaymentControl.initial :=
  Callbacks.restore PaymentControl.frame

theorem suffix_client :
    Evm.run (PaymentControl.code.full ++ [.revert]) PaymentControl.initial =
      Evm.run [.revert] PaymentControl.final :=
  Callbacks.suffix PaymentControl.premises (identity PaymentControl.origin)
    PaymentControl.initial PaymentControl.final (.ok (.success [])) PaymentControl.sourceFinal
    [.revert] PaymentControl.inhabited

theorem deterministic_client :
    identity PaymentControl.origin = identity PaymentControl.origin ∧
    (.ok (.success []) : Except Halt Outcome) = .ok (.success []) ∧
    PaymentControl.sourceFinal = PaymentControl.sourceFinal ∧
    (Evm.Out.ok PaymentControl.final 0) = .ok PaymentControl.final 0 :=
  Callbacks.deterministic PaymentControl.premises (identity PaymentControl.origin) (identity PaymentControl.origin)
    PaymentControl.initial (.ok (.success [])) (.ok (.success [])) PaymentControl.sourceFinal PaymentControl.sourceFinal
    (.ok PaymentControl.final 0) (.ok PaymentControl.final 0) PaymentControl.inhabited PaymentControl.inhabited

theorem target_unique_client : PaymentControl.final = PaymentControl.final :=
  Callbacks.target_unique PaymentControl.premises (identity PaymentControl.origin)
    PaymentControl.initial PaymentControl.final PaymentControl.final (.ok (.success [])) PaymentControl.sourceFinal
    PaymentControl.inhabited PaymentControl.executed

theorem captured_client :
    (Solidity.Lowering.V08.SourceCallPhase.capture Controls.origin.global Controls.origin.frame Controls.origin.horizon
      (SourceBridge.request Controls.origin)).run Controls.origin.after =
      (.ok (.success [7], Controls.final), (Controls.origin.after.1, Controls.final)) :=
  SourceBridge.captured Controls.origin (.success [7]) Controls.final SourceBridgeControls.nonself_raw

theorem bridge_storage_client : Controls.typedThree = Controls.typedThree :=
  SourceBridge.static_storage Controls.origin (.ok (.success [7])) Controls.final
    SourceBridgeControls.nonself_raw Controls.runtime Controls.representation
    Controls.typedThree Controls.typedThree Controls.entry_representation Controls.exit_representation

theorem storage_client :
    (Controls.final.ex.world.accounts Controls.origin.frame.this).storage =
      (Controls.origin.after.2.ex.world.accounts Controls.origin.frame.this).storage :=
  InvocationFrame.Invocation.storage Controls.origin (.ok (.success [7])) Controls.final Controls.raw Controls.runtime

theorem typed_storage_client : Controls.typedThree = Controls.typedThree :=
  InvocationFrame.typed_storage Controls.origin (.ok (.success [7])) Controls.final Controls.raw Controls.runtime
    Controls.representation Controls.typedThree Controls.typedThree Controls.entry_representation Controls.exit_representation

theorem typed_resume_client :
    (Solidity.State.ofStorage Controls.typedThree : Solidity.State Controls.Cell []).withStorage Controls.typedThree =
      (Solidity.State.ofStorage Controls.typedThree : Solidity.State Controls.Cell []).withStorage Controls.typedThree :=
  InvocationFrame.typed_resume Controls.origin (.ok (.success [7])) Controls.final Controls.raw Controls.runtime
    Controls.representation Controls.typedThree Controls.typedThree Controls.entry_representation Controls.exit_representation
    (Solidity.State.ofStorage Controls.typedThree)

theorem raw_unique_client :
    (.ok (.success [7]) : Except Halt Outcome) = .ok (.success [7]) ∧ Controls.final = Controls.final :=
  InvocationFrame.Invocation.raw_unique Controls.origin (.ok (.success [7])) (.ok (.success [7]))
    Controls.final Controls.final Controls.raw Controls.raw

theorem depth_client :
    callAddr (GB answerOnly) {FC with depth := 1024} 1 ext (word 0) [] false =
      (pure (.revert []) : EM EB [] Outcome) :=
  Solidity.Backend.Passes.SourceCallBoundary.call_depth (GB answerOnly) {FC with depth := 1024}
    0 ext (word 0) [] false (by decide)

theorem static_value_client :
    callAddr (GB answerOnly) {FC with static := true} 1 ext (word 1) [] false =
      (EM.halt (.revert []) : EM EB [] Outcome) :=
  Solidity.Backend.Passes.SourceCallBoundary.call_static_value (GB answerOnly) {FC with static := true}
    0 ext (word 1) [] false (by decide) rfl (by decide)

#print axioms restore_client
#print axioms suffix_client
#print axioms deterministic_client
#print axioms target_unique_client
#print axioms captured_client
#print axioms bridge_storage_client
#print axioms storage_client
#print axioms typed_storage_client
#print axioms typed_resume_client
#print axioms raw_unique_client
#print axioms depth_client
#print axioms static_value_client
end Solidity.H62.ReadonlyAudit.JointClients
