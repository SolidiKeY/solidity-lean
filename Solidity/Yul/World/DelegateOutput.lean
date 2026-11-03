import Solidity.Yul.World.DelegateExtra
import Solidity.Yul.World.HeapOutputTransport

namespace Solidity.Yul.World.DelegateOutput
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.DelegatePhysical
open Solidity.Yul.World.DelegatePort
open Solidity.Yul.World.StateCallChecks (caller residual observed memory heap placement byteEntry)

def completed (G : Glob env) : Result env [.bytes .memory] := successful (caller G) residual observed

/-- Only the heap projection is reduced; no supplied frame adequacy premise. -/
theorem heap_eq (G : Glob env) : heap G=(completed G).1.1.1.2.heap := rfl

theorem shared (G : Glob env) : (completed G).2.effects.execution=(completed G).1.1.1.2.ex := rfl

theorem reads (G : Glob env) : (byteEntry G).Reads (placement G) (memory G) :=
  encodeByteHeap_reads (D:=env.layout) (h:=heap G) (placement G) [byteEntry G]
    (by simp only [List.map_cons,List.map_nil,List.nodup_cons,List.not_mem_nil,List.nodup_nil,not_false_eq_true,and_self])
    (mstore (mstore (fun _=>0xa5) 64 192) 96 0) (byteEntry G) List.mem_cons_self

theorem data (G : Glob env) : (completed G).2.effects.returndata=ReturningCall.output := rfl

theorem inside (G : Glob env) : (0 : Word).val+min (2 : Word).val (completed G).2.effects.returndata.length≤(byteEntry G).bytes.length := by
  simp only [data,ReturningCall.output_exact,StateCallChecks.byteEntry,input_length,List.length_append,List.length_cons,List.length_nil,List.length_replicate]
  decide

def copy (G : Glob env) := HeapOutputTransport.copy (completed G) (shared G)
  (heap G) (heap_eq G) (placement G) (byteEntry G) (memory G) 0 2

def expected (G : Glob env) := HeapOutputTransport.image (completed G)
  (heap G) (heap_eq G) (placement G) (byteEntry G) (memory G) 0 [0x11,0x22]

/-- Specialized actual completion and real copy, retaining the entire result. -/
theorem copy_exact (G : Glob env) : copy G=expected G := by
  have actual:=HeapOutputTransport.exact_copy (completed G) (shared G) (heap G) (heap_eq G)
    (placement G) (byteEntry G) (memory G) 0 2 (inside G) (reads G).1 (reads G).2
  rw [show callOutput (completed G).2.effects.returndata (2 : Word).val=[0x11,0x22] from DelegateExtra.output_prefix G] at actual
  exact actual

def called (G : Glob env) :=
  call (CallerFrame.liftInvoke (invoke false G 0)) (caller G) residual before observed rfl (memory G)
    (parent (caller G) DelegateChecks.sender DelegateChecks.value false) .delegatecall DelegateChecks.target 10000 0 160 4

theorem called_exact (G : Glob env) : called G=some (.ok (.success ReturningCall.output),completed G) := DelegateChecks.success G

def runAndCopy (G : Glob env) := HeapOutputTransport.sequence (called G)
  (.success ReturningCall.output,completed G) (called_exact G) (shared G)
  (heap G) (heap_eq G) (placement G) (byteEntry G) (memory G) 0 2

/-- Actual registered delegate execution followed by the real bounded copy.
No final outcome/run/equality premise is supplied by the theorem's caller. -/
theorem runAndCopy_exact (G : Glob env) :
    runAndCopy G=some (.ok (.success ReturningCall.output),expected G) := by
  rw [runAndCopy,HeapOutputTransport.sequence_exact]
  exact congrArg (fun x=>some ((Except.ok (Outcome.success ReturningCall.output) : Except Halt Outcome),x)) (copy_exact G)

theorem exact_destination (G : Glob env) :
    (placement G).address (byteEntry G).id+32+(0 : Word).val=160 := rfl

theorem untouched_tail (G : Glob env) :
    (HeapWindow.splice (input G) 0 [0x11,0x22]).drop 2=(input G).drop 2 :=
  HeapWindow.splice_suffix (input G) [0x11,0x22] 0 (by rw [input_length]; decide)
end Solidity.Yul.World.DelegateOutput
