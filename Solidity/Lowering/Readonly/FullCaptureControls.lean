import Solidity.Lowering.Readonly.CapturePhases
import Solidity.Lowering.Readonly.ResumeControls
import Solidity.Lowering.Readonly.ReceiverControls

/-! Discharged capture for the actual declared-return g control. Each source
phase is kernel-checked separately, then composed; no broader call/history
producer is inferred from this single inhabited source fixture. -/
namespace Solidity.Lowering.Readonly.FullCaptureControls
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Backend.Passes.SourceTypedCall
open ResumeControls

def before : Locals EB.layout [.address false] × St EB :=
  Solidity.Backend.Passes.SourceCallControls.before

theorem receiver_phase (out : Solidity.Roadmap.Outcome) :
    (evalE (global out) FC 6 ReceiverControls.target).run before =
      (.ok (.val (.contract ext)), before) := by rfl

theorem value_phase (out : Solidity.Roadmap.Outcome) :
    (evalE (global out) FC 6 (lit 0 : RExpr EB [.address false] uint)).run before =
      (.ok (.val (.int 0 (by decide))), before) := by rfl

theorem capture_fact (out : Solidity.Roadmap.Outcome) :
    CapturedAt (global out) FC 6 ReceiverControls.target dG signature (lit 0) .nil
      before before captured := by
  have phases := CapturePhases.compose (global out) FC 6 dG signature
    ReceiverControls.target (lit 0) .nil ext 0 (by decide) .nil [] none
    before before before before before before
    (receiver_phase out) (value_phase out) (by rfl) (by rfl) (by rfl) (by rfl)
  simpa only [List.append_nil] using phases

/-- Declared uint decoding fails after a genuine capture and successful
unknown-callee one-byte result, rather than suppressing that raw success. -/
theorem full_malformed_expression :
    (evalE (global (.success [1])) FC 7
      (.extCall ReceiverControls.target dG signature (lit 0) .nil)).run before =
      (.error (.revert []), (before.1, final (.success [1]))) := by
  rw [external_captured _ _ _ _ _ _ _ _ _ _ _ (capture_fact (.success [1]))]
  exact malformed_success

/-- An actual callee revert keeps its distinct bytes through capture/resume. -/
theorem full_callee_revert :
    (evalE (global (.revert [7])) FC 7
      (.extCall ReceiverControls.target dG signature (lit 0) .nil)).run before =
      (.error (.revert [7]), (before.1, final (.revert [7]))) := by
  rw [external_captured _ _ _ _ _ _ _ _ _ _ _ (capture_fact (.revert [7]))]
  exact callee_revert

/-- A canonical uint word really returns its typed value after the same
source capture; the malformed controls do not arise from universal refusal. -/
theorem full_canonical_return :
    (evalE (global (.success (wordBytes (word 1)))) FC 7
      (.extCall ReceiverControls.target dG signature (lit 0) .nil)).run before =
      (.ok (.val (.int 1 (by decide))), (before.1, final (.success (wordBytes (word 1))))) := by
  rw [external_captured _ _ _ _ _ _ _ _ _ _ _ (capture_fact (.success (wordBytes (word 1))))]
  change (resume (global (.success (wordBytes (word 1)))) FC 6 dG [uint] captured).run (before.1, sB) = _
  rw [CallerResume.success _ _ _ _ _ _ _ _ _ _ (actual_raw (.success (wordBytes (word 1))))]
  rfl

theorem full_empty_return :
    (evalE (global (.success [])) FC 7
      (.extCall ReceiverControls.target dG signature (lit 0) .nil)).run before =
      (.error (.revert []), (before.1, final (.success []))) := by
  rw [external_captured _ _ _ _ _ _ _ _ _ _ _ (capture_fact (.success []))]
  change (resume (global (.success [])) FC 6 dG [uint] captured).run (before.1, sB) = _
  rw [CallerResume.success _ _ _ _ _ _ _ _ _ _ (actual_raw (.success []))]
  rfl

end Solidity.Lowering.Readonly.FullCaptureControls
