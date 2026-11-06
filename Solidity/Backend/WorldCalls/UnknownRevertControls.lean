import Solidity.Backend.WorldCalls.UnknownSourceCall
import Solidity.Lowering.Readonly.HistoryRollbackControls

/-! Actual static unknown-call credit/revert at a post-effect caller mark.
No target/EVM or general callback-history producer is inferred. -/
namespace Solidity.Backend.WorldCalls.UnknownRevertControls
open Solidity.Source Solidity.Source.SemanticsExamples Solidity.Roadmap
open Solidity.Lowering.Readonly

def strategy (events : List Event) : Move :=
  if events.any (fun event => match event with | .credit _ _ => true | _ => false)
  then .answer (.revert [1, 0, 255]) else .credit thisC (word 5)
def global : Glob EB := GB strategy

def origin : InvocationFrame.Invocation EB [.address false] ⟨none, "I"⟩ [] [] :=
  {Controls.origin with
    global := global
    horizon := 3
    before := (Controls.origin.before.1, HistoryRollbackControls.entry)
    after := (Controls.origin.after.1, HistoryRollbackControls.entry)
    execution := by rfl}

def result := SourceBridge.evaluated origin

theorem children : EnvironmentHistory.CallbackHistories global true 2 := by
  intro n bound depth state target sender value input requested code credited choice
  simp only [global, GB, strategy] at choice
  split at choice <;> cases choice

/-- Actual ordered revert, retained supplied prior caller effect, balance rollback,
and observable nonempty credit: no endpoint frame is supplied as a premise. -/
theorem observations :
Solidity.Backend.WorldCalls.UnknownRevertControls.result.1 = .ok (.revert [1, 0, 255]) ∧
 Solidity.Source.SemanticsExamples.readX Solidity.Backend.WorldCalls.UnknownRevertControls.result.2 = some 4 ∧
 (Solidity.Backend.WorldCalls.UnknownRevertControls.result.2.ex.world.accounts Solidity.Source.SemanticsExamples.thisC).balance = 0 ∧
 Solidity.Backend.WorldCalls.UnknownRevertControls.result.2.events.contains (.credit Solidity.Source.SemanticsExamples.thisC (Solidity.Source.SemanticsExamples.word 5)) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- Nonempty source execution instantiates the all-outcome producer. The
prior caller write is supplied in the input, not executed by these nil arguments. -/
theorem frame : origin.RawAt result.1 result.2 ∧ origin.RuntimeFrames result.2 :=
  UnknownSourceCall.evaluated_frame origin 2 rfl rfl (by decide) rfl (by rfl) children

end Solidity.Backend.WorldCalls.UnknownRevertControls
