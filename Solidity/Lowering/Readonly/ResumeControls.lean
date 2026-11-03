import Solidity.Lowering.Readonly.CallerResume
import Solidity.Lowering.Readonly.Controls

/-! Actual raw call/decoder boundary executions. These do not assert a source
capture for the g control; full capture-to-decoder composition is proved
conditionally in CallerResume and instantiated below for the existing ping.
No runtime-history or arbitrary-call raw producer is invented. -/
namespace Solidity.Lowering.Readonly.ResumeControls
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Backend.Passes.SourceTypedCall

def dG : Decl := ⟨.function, "g", some "C", false, fn "g" .nil pUint⟩
theorem declared : EB.declOf .function ⟨some "C", "g"⟩ = some dG := by rfl
theorem signature : dG.fnSig EB = some ([], [uint]) := by rfl

def captured : Captured EB [] := ⟨ext, word 0, .nil,
  (GB answerOnly).selector (sigOf EB.layout dG.name [])⟩
def global (out : Solidity.Roadmap.Outcome) : Glob EB := GB (fun _ => .answer out)
def final (out : Solidity.Roadmap.Outcome) : St EB :=
  { sB with events := [.call ext (word 0) captured.input false, .answer out none] }

theorem actual_raw (out : Solidity.Roadmap.Outcome) :
    (callAddr (global out) FC 6 captured.receiver captured.value captured.input
      (dG.fnMut == some .view || dG.fnMut == some .pure)).run (L0 EB, sB) =
      (.ok out, (L0 EB, final out)) := by
  cases out <;> rfl

theorem malformed_success :
    (resume (global (.success [1])) FC 6 dG [uint] captured).run
      (Solidity.Backend.Passes.SourceCallControls.before.1, sB) =
      (.error (.revert []), (Solidity.Backend.Passes.SourceCallControls.before.1, final (.success [1]))) := by
  rw [CallerResume.success _ _ _ _ _ _ _ _ _ _ (actual_raw (.success [1]))]
  rfl

theorem callee_revert :
    (resume (global (.revert [7])) FC 6 dG [uint] captured).run
      (Solidity.Backend.Passes.SourceCallControls.before.1, sB) =
      (.error (.revert [7]), (Solidity.Backend.Passes.SourceCallControls.before.1, final (.revert [7]))) := by
  rw [CallerResume.success _ _ _ _ _ _ _ _ _ _ (actual_raw (.revert [7]))]
  rfl

theorem exhaustion :
    (resume (global (.success [1])) FC 0 dG [uint] captured).run
      (Solidity.Backend.Passes.SourceCallControls.before.1, sB) =
      (.error .timeout, (Solidity.Backend.Passes.SourceCallControls.before.1, sB)) :=
  CallerResume.halted _ _ _ _ _ _ _ _ _ _ rfl

theorem no_declared_returns :
    (evalE Controls.origin.global Controls.origin.frame (Controls.origin.horizon + 1)
      (.extCall Controls.origin.target Controls.origin.declaration Controls.origin.signature
        Controls.origin.value Controls.origin.arguments)).run Controls.origin.before =
      (.ok RVal.unit, (Controls.origin.after.1, Controls.final)) := by
  rw [CallerResume.invocation Controls.origin _ _ Controls.raw]
  rfl

end Solidity.Lowering.Readonly.ResumeControls
