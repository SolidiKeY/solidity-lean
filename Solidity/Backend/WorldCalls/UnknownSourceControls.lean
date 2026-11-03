import Solidity.Backend.WorldCalls.UnknownSourceCall
import Solidity.Backend.WorldCalls.SourceBridgeControls
import Solidity.Lowering.Readonly.EnvironmentHistoryControls

namespace Solidity.Backend.WorldCalls.UnknownSourceControls
open Solidity.Source Solidity.Source.SemanticsExamples Solidity.Roadmap
open Solidity.Lowering.Readonly
open Solidity.Backend.Passes.SourceCallControls
open UnknownSourceCall

def global : Glob EB := GB (fun _ => .answer (.success [7]))
def frame : Fr := {FC with static := true}
def finished : St EB := {sB with events := sB.events ++
  [.call ext (word 0) [] true, .answer (.success [7]) none]}

theorem actual_loop : (envLoop global 1 (frame.depth + 1) true).run
    (L0 EB, entered sB frame ext [] false) = (.ok (.success [7]), (L0 EB, finished)) := by rfl

theorem children : EnvironmentHistory.CallbackHistories global true 1 := by
  intro n bound depth state target sender value input requested code credited choice
  cases choice

theorem actual_call : (callAddr global frame 2 ext (word 0) [] false).run (L0 EB, sB) =
    (.ok (.success [7]), (L0 EB, finished)) :=
  success global frame 1 ext [] [7] false sB finished (by decide) (by rfl) actual_loop

theorem history : StaticJournal.History sB.ex true finished.ex :=
  success_history global frame 1 ext [] [7] false sB finished children actual_loop

theorem storage : StaticJournal.SameStorage finished.ex sB.ex := history.storage rfl

/-- An actual nonself read-only callback remains among the transported outcomes. -/
theorem reentry :
    (callAddr Controls.readOrigin.global Controls.readOrigin.frame Controls.readOrigin.horizon ext (word 0)
      (selOf "ping()") false).run (L0 EB, sB) =
        (.ok (.success []), (L0 EB, Controls.readFinal)) := by
  exact Controls.read_reentry_raw

theorem reentry_event : Controls.readFinal.events.contains (.reentered (.success [])) = true :=
  Controls.callback_not_suppressed

theorem false_bytes : ¬ (callAddr global frame 2 ext (word 0) [] false).run (L0 EB, sB) =
    (.ok (.success [9]), (L0 EB, finished)) := by
  rw [actual_call]
  intro h
  cases h

/-- An inherited-static value attempt still halts; it is not a successful call. -/
theorem value_refusal : (callAddr global frame 2 ext (word 1) [] false).run (L0 EB, sB) =
    (.error (.revert []), (L0 EB, sB)) := by rfl
def revertGlobal : Glob EB := GB (fun _ => .answer (.revert [1, 0, 255]))
def revertFinal : St EB := {sB with events := sB.events ++
  [.call ext (word 0) [] true, .answer (.revert [1, 0, 255]) none]}

/-- Complete ordered revert bytes cross the actual live-mark rollback branch. -/
theorem raw_revert : (callAddr revertGlobal frame 2 ext (word 0) [] false).run (L0 EB, sB) =
    (.ok (.revert [1, 0, 255]), (L0 EB, revertFinal)) := by
  exact (transport revertGlobal frame 1 ext [] false sB (by decide) (by rfl)).trans (by rfl)

/-- Environment exhaustion is a halt, retaining the actual emitted-call state. -/
theorem environment_timeout : (callAddr global frame 1 ext (word 0) [] false).run (L0 EB, sB) =
    (.error .timeout, (L0 EB, entered sB frame ext [] false)) := by
  exact (transport global frame 0 ext [] false sB (by decide) (by rfl)).trans (by rfl)
def origin : InvocationFrame.Invocation EB [.address false] ⟨none, "I"⟩ [] [] :=
  {Controls.origin with global := global, horizon := 2, execution := by rfl}
def invocationFinal : St EB := {sB with events := sB.events ++
  [.call ext (word 0) (selOf "ping()") true, .answer (.success [7]) none]}

theorem joint : origin.RawAt (.ok (.success [7])) invocationFinal ∧ origin.RuntimeFrames invocationFinal :=
  invocation_success origin 1 [7] invocationFinal rfl rfl (by decide) rfl
    (by rfl) children (by rfl)
end Solidity.Backend.WorldCalls.UnknownSourceControls
