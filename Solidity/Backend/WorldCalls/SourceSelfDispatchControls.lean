import Solidity.Backend.WorldCalls.SourceSelfDispatch
import Solidity.Backend.WorldCalls.SelfControls

/-! Actual Source self-dispatch witnesses, not internal-call or target CALL
substitutes. Ordinary mutation, static refusal, raw revert and timeout stay distinct. -/
namespace Solidity.Backend.WorldCalls.SourceSelfDispatchControls
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Roadmap
open Solidity.Backend.Passes.SourceCallFrame
def global := GB answerOnly
def child (mode : Bool) := childFrame thisC thisC (word 0) (selOf "cb()") mode "C" (FC.depth+1)
def dispatched (mode : Bool) (n : Nat := 28) :=
  (dispatch global (child mode) n (selOf "cb()")).run (L0 EB,{sB with heap := Source.Heap.empty})
def called (mode : Bool) (n : Nat := 30) :=
  (callAddr global FC n thisC (word 0) (selOf "cb()") mode).run (L0 EB,sB)

theorem child_success : (dispatched false).1 = .ok [] := by rfl
theorem actual_success_path :
    called false = (.ok (.success []),((dispatched false).2.1,
      {(dispatched false).2.2 with heap := sB.heap})) :=
  SourceSelfDispatch.success global FC 28 (word 0) (selOf "cb()") [] false "C"
    sB (dispatched false).2.2 (dispatched false).2.1
    (by decide) rfl (by rfl) (by decide) (Prod.ext child_success rfl)

theorem actual_mutation : readX (called false).2.2 = some 4 := by decide
theorem static_child_refused : (dispatched true).1 = .error (.revert []) := by rfl
theorem actual_revert_path :
    called true = (.ok (.revert []),((dispatched true).2.1,
      rolledBack (dispatched true).2.2 (SourceSelfDispatch.checkpoint sB))) :=
  SourceSelfDispatch.reverted global FC 28 (word 0) (selOf "cb()") [] true "C"
    sB (dispatched true).2.2 (dispatched true).2.1
    (by decide) rfl (by rfl) (by decide) (Prod.ext static_child_refused rfl)
theorem static_storage_kept : readX (called true).2.2 = some 3 := by decide

theorem actual_timeout_path :
    called false 2 = (.error .timeout,((dispatched false 0).2.1,
      {(dispatched false 0).2.2 with heap := sB.heap})) :=
  SourceSelfDispatch.halted global FC 0 (word 0) (selOf "cb()") false "C"
    sB (dispatched false 0).2.2 (dispatched false 0).2.1 .timeout
    (fun bytes h => by cases h) (by decide) rfl (by rfl) (by decide) rfl

theorem insufficient_self_value :
    ((callAddr global FC 30 thisC (word 1) (selOf "cb()") false).run (L0 EB,sB)).1 =
      .ok (.revert []) := by rfl
theorem depth_before_self_entry :
    ((callAddr global {FC with depth := 1024} 30 thisC (word 0)
      (selOf "cb()") false).run (L0 EB,sB)).1 = .ok (.revert []) := by rfl
end Solidity.Backend.WorldCalls.SourceSelfDispatchControls
