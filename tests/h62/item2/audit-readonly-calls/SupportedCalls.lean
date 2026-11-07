import Solidity.Backend.WorldCalls.ExternalControls
import Solidity.Lowering.Readonly.SourceReadBuiltinControls

/-! Positive Source success and joint conditional-client witnesses. These
are isolated actual fixtures, not general compiler totality or P10 adequacy.
Failure, zero-horizon timeout and unsupported gas observations stay distinct. -/
namespace Solidity.H62.ReadonlyAudit.SupportedCalls
open Solidity.Source Solidity.Source.SemanticsExamples Solidity.Roadmap
open Solidity.Backend.WorldCalls
open Solidity.Lowering.Readonly

/-- All hypotheses of Callbacks.returned are supplied together at one input. -/
theorem returned_joint :
    ∃ (i : InvocationFrame.Invocation EB [.address false] ⟨none, "I"⟩ [] [])
      (p : Premises i) (key : Identity) (initial machine : Evm.Machine)
      (raw : Except Halt Outcome) (final : St EB),
      p.Step key initial raw final (.ok machine 0) :=
  ⟨PaymentControl.origin, PaymentControl.premises, identity PaymentControl.origin,
    PaymentControl.initial, PaymentControl.final, .ok (.success []),
    PaymentControl.sourceFinal, PaymentControl.inhabited⟩

/-- A nonempty exact declared uint result rules out source reject-all behavior. -/
theorem supported_uint :
    (evalE (ResumeControls.global (.success (wordBytes (word 1)))) FC 7
      (.extCall ReceiverControls.target ResumeControls.dG ResumeControls.signature (lit 0) .nil)).run
      FullCaptureControls.before =
      (.ok (.val (.int 1 (by decide))),
        (FullCaptureControls.before.1, ResumeControls.final (.success (wordBytes (word 1))))) :=
  ExternalControls.canonical_uint

theorem supported_uint_not_revert :
    (evalE (ResumeControls.global (.success (wordBytes (word 1)))) FC 7
      (.extCall ReceiverControls.target ResumeControls.dG ResumeControls.signature (lit 0) .nil)).run
      FullCaptureControls.before ≠
      (.error (.revert []),
        (FullCaptureControls.before.1, ResumeControls.final (.success (wordBytes (word 1))))) := by
  rw [supported_uint]
  intro impossible
  cases impossible

/-- Source success with malformed bytes really fails at the caller decoder. -/
theorem malformed_observable :
    (evalE (ResumeControls.global (.success [1])) FC 7
      (.extCall ReceiverControls.target ResumeControls.dG ResumeControls.signature (lit 0) .nil)).run
      FullCaptureControls.before =
      (.error (.revert []), (FullCaptureControls.before.1, ResumeControls.final (.success [1]))) :=
  ExternalControls.malformed_one_byte

/-- Zero Source horizon is timeout; it is not EVM gas exhaustion. -/
theorem timeout_observable :
    (Solidity.Backend.Passes.SourceTypedCall.resume (ResumeControls.global (.success [1])) FC 0
      ResumeControls.dG [uint] ResumeControls.captured).run
      (Solidity.Backend.Passes.SourceCallControls.before.1, sB) =
      (.error .timeout, (Solidity.Backend.Passes.SourceCallControls.before.1, sB)) :=
  ResumeControls.exhaustion

/-- The current Source builtin explicitly refuses gasleft. No gas or fork
adequacy is inferred from the payment-only EVM contract. -/
theorem gas_refusal_observable (pipeline : Pipeline) :
    (SourceReadBuiltinControls.builtin pipeline .gasleft
      (RArgs.nil : RArgs EB [] []) uint).1 = .error (.stuck "builtin") := by
  cases pipeline <;> rfl

#print axioms returned_joint
#print axioms supported_uint
#print axioms supported_uint_not_revert
#print axioms malformed_observable
#print axioms timeout_observable
#print axioms gas_refusal_observable
end Solidity.H62.ReadonlyAudit.SupportedCalls
