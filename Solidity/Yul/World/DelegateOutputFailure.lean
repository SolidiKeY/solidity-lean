import Solidity.Yul.World.DelegateOutput
namespace Solidity.Yul.World.DelegateOutputFailure
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.DelegatePhysical
open Solidity.Yul.World.DelegatePort
open Solidity.Yul.World.StateCallChecks (caller residual observed memory heap placement byteEntry)

def completed (G : Glob env) : Result env [.bytes .memory] := reverted (caller G) residual before observed (errorData G)
theorem heap_eq (G : Glob env) : heap G=(completed G).1.1.1.2.heap := rfl
theorem shared (G : Glob env) : (completed G).2.effects.execution=(completed G).1.1.1.2.ex := rfl

def called (G : Glob env) :=
  call (CallerFrame.liftInvoke (invoke true G 0)) (caller G) residual before observed rfl (memory G)
    (parent (caller G) DelegateChecks.sender DelegateChecks.value false) .delegatecall DelegateChecks.target 10000 0 160 4

theorem called_exact (G : Glob env) : called G=some (.ok (.revert (errorData G)),completed G) := DelegateChecks.reverted_call G

def runWindow (G : Glob env) (source size : Word) := HeapOutputTransport.sequenceWindow (called G)
  (.revert (errorData G),completed G) (called_exact G) (shared G)
  (heap G) (heap_eq G) (placement G) (byteEntry G) (memory G) 0 source size

def expected (G : Glob env) (bytes : Bytes) := HeapOutputTransport.image (completed G)
  (heap G) (heap_eq G) (placement G) (byteEntry G) (memory G) 0 bytes

theorem inside (G : Glob env) : (0 : Word).val+([0x11,0x22] : Bytes).length≤(byteEntry G).bytes.length := by
  simp only [StateCallChecks.byteEntry,input_length,List.length_cons,List.length_nil]
  decide

/-- Actual ordinary custom-error rollback, then copy its two argument bytes.
The full failure buffer and all caller/physical prefixes remain in the result. -/
theorem argument_copy (G : Glob env) :
    runWindow G 4 2=some (.ok (.revert (errorData G)),expected G [0x11,0x22]) := by
  rw [runWindow,HeapOutputTransport.sequenceWindow_exact]
  have actual:=HeapOutputTransport.window_exact (completed G) (shared G) (heap G) (heap_eq G)
    (placement G) (byteEntry G) (memory G) 0 4 2 [0x11,0x22] (StateCallExtra.error_window G)
    (inside G) (DelegateOutput.reads G).1 (DelegateOutput.reads G).2
  exact congrArg (fun x=>some ((Except.ok (Outcome.revert (errorData G)) : Except Halt Outcome),x)) actual

theorem exact_end_window (G : Glob env) : returnWindow (completed G).2.effects.returndata 36 0=some [] := by
  change returnWindow (errorData G) 36 0=some []
  simp only [returnWindow,StateCallExtra.error_length,Nat.add_zero,Nat.le_refl,if_true,List.take_zero]

theorem zero_inside (G : Glob env) : (0 : Word).val+([] : Bytes).length≤(byteEntry G).bytes.length := by
  simp only [StateCallChecks.byteEntry,input_length,List.length_nil]
  decide

theorem exact_end_zero (G : Glob env) :
    runWindow G 36 0=some (.ok (.revert (errorData G)),expected G []) := by
  rw [runWindow,HeapOutputTransport.sequenceWindow_exact]
  have actual:=HeapOutputTransport.window_exact (completed G) (shared G) (heap G) (heap_eq G)
    (placement G) (byteEntry G) (memory G) 0 36 0 [] (exact_end_window G)
    (zero_inside G) (DelegateOutput.reads G).1 (DelegateOutput.reads G).2
  exact congrArg (fun x=>some ((Except.ok (Outcome.revert (errorData G)) : Except Halt Outcome),x)) actual

/-- Failure remains a completed Source revert; ownership/bounds refusal is
None on the copy, never a recoding of the callee outcome. -/
theorem out_of_source_zero (G : Glob env) :
    runWindow G 37 0=some (.ok (.revert (errorData G)),(completed G,none)) := by
  rw [runWindow,HeapOutputTransport.sequenceWindow_exact]
  have bad : (completed G).2.effects.returndata.length<(37 : Word).val+(0 : Word).val := by
    change (errorData G).length<37+0
    rw [StateCallExtra.error_length]
    decide
  rw [HeapOutputTransport.window_bad_source (completed G) (shared G) (heap G) (heap_eq G) (placement G) (byteEntry G) (memory G) 0 37 0 bad]
end Solidity.Yul.World.DelegateOutputFailure
