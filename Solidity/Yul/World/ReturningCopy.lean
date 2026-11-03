import Solidity.Yul.World.ReturningPort
import Solidity.Yul.World.ReturnSize

namespace Solidity.Yul.World.ReturningCall
open Solidity.Source
open Solidity.Roadmap (Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Backend.Environment (writeBytes)

def copiedBytes : Bytes := [0xa1,0x11,0x22,0xd4,0xe5,0xf6]
def copiedHeap (G : Glob env) := (heap G).write 1 (.bytes copiedBytes) rfl
def copiedState (G : Glob env) := withSourceHeap (after (caller G)) (copiedHeap G)
def copiedMemory (G : Glob env) := writeBytes (memory G) 289 [0x11,0x22]

theorem output_length : output.length=32 := wordBytes_length _
theorem output_prefix : callOutput output 2=[0x11,0x22] := by rw [output_exact]; decide

theorem copy_output (G : Glob env) :
    copyOutput (result G) rfl (placement G) 1 false old rfl (memory G) 1 2=
      (result G,some ((copiedMemory G,copiedState G),
        (CallerFrameChecks.residual,CallerFrameChecks.encoding),(result G).2)) := by
  have actual := copyOutput_exact (result G) rfl (placement G) 1 false old rfl (memory G) 1 2
    (by change 1+min 2 output.length≤old.length; rw [output_length]; decide) (output_reads G).1 (output_reads G).2
  simpa only [output_prefix] using actual

theorem copy_heap (G : Glob env) :
    HeapWindow.copyHeapWindow (result G).2.effects (heap G) (placement G) 1 false old rfl (memory G) 1 0 2=
      some (copiedMemory G,copiedHeap G) :=
  HeapWindow.copyHeapWindow_exact _ _ _ _ _ _ [0x11,0x22] rfl _ 1 0 2 (by change returnWindow output 0 2=some [0x11,0x22]; rw [output_exact]; decide) (by decide)
    (output_reads G).1 (output_reads G).2

theorem copy_state (G : Glob env) :
    HeapWindow.copyStateWindow (result G).2.effects (after (caller G)) (placement G) 1 false old rfl (memory G) 1 0 2=
      some (copiedMemory G,copiedState G) :=
  HeapWindow.copyStateWindow_exact _ _ _ _ _ _ [0x11,0x22] rfl _ 1 0 2 (by change returnWindow output 0 2=some [0x11,0x22]; rw [output_exact]; decide) (by decide)
    (output_reads G).1 (output_reads G).2

theorem copied_payload (G : Glob env) : readBytes (copiedMemory G) 288 6=copiedBytes :=
  HeapWindow.read_splice (memory G) 288 old [0x11,0x22] 1 (output_reads G).2 (by decide)

theorem copied_header (G : Glob env) : (mload (copiedMemory G) 256).val=6 := by
  exact (congrArg Fin.val (HeapWindow.window_header (memory G) 256 1 [0x11,0x22])).trans (output_reads G).1

theorem outside_bytes (G : Glob env) (a : Nat) (outside : a<289 ∨ 291≤a) :
    copiedMemory G a=memory G a :=
  Solidity.Backend.Environment.writeBytes_frame _ _ _ _ outside

theorem exact_untouched_suffix : copiedBytes.drop 3=old.drop 3 ∧ copiedBytes.take 1=old.take 1 := ⟨rfl,rfl⟩

theorem input_image_preserved (G : Glob env) {τ : Source.STy} {d : Source.Data env.layout τ}
    (image : MemoryImage (placement G) d) (found : (heap G).get 0=some ⟨τ,d⟩)
    (reads : image.Reads (memory G) 128) : image.Reads (copiedMemory G) 128 :=
  HeapWindow.window_other_image (result G).2.effects (heap G) (placement G) 1 0 false old [0x11,0x22] rfl
    (memory G) 1 0 2 (by change returnWindow output 0 2=some [0x11,0x22]; rw [output_exact]; decide) (by decide)
    (output_reads G).1 (output_reads G).2 (copiedMemory G) (copiedHeap G) (copy_heap G) image found (by decide) reads

theorem heap_types (G : Glob env) : (copiedHeap G).ty=(heap G).ty :=
  funext (fun a=>Source.Heap.write_ty _ _ a _ _)

theorem heap_next (G : Glob env) : (copiedHeap G).next=(heap G).next := rfl

theorem input_cell_preserved (G : Glob env) : (copiedHeap G).get 0=(heap G).get 0 :=
  Source.Heap.write_other _ (by decide) _ _

theorem copied_aliases (G : Glob env) :
    (Source.bytesOfRV (E:=env) parentFrame 1 (.val ((copiedState G).1.get .here))).run (copiedState G)=
      (.ok copiedBytes,copiedState G) ∧
    (Source.bytesOfRV (E:=env) parentFrame 1 (.val ((copiedState G).2.fnLocals.2.get .here))).run (copiedState G)=
      (.ok copiedBytes,copiedState G) ∧
    (Source.bytesOfRV (E:=env) parentFrame 1 (.val ((copiedState G).1.get (.there .here)))).run (copiedState G)=
      (.ok (input G),copiedState G) := ⟨rfl,rfl,rfl⟩

theorem full_copy_frame (G : Glob env) :
    (copiedState G).1=(caller G).1 ∧ (copiedState G).2.fnLocals=(caller G).2.fnLocals ∧
    (copiedState G).2.ex=moved ∧ (copiedState G).2.events=(caller G).2.events ∧
    (copiedState G).2.logs=(caller G).2.logs ∧ (result G).2.effects.returndata=output ∧
    (result G).2.trace=(observed G).trace := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem tail_window : returnWindow output 30 2=some [0,0x55] := by rw [output_exact]; decide

theorem exact_end_zero : returnWindow output 32 0=some [] := by rw [output_exact]; decide

theorem invalid_zero : returnWindow output 33 0=none := by rw [output_exact]; decide

theorem full_buffer_unchanged (G : Glob env) : (result G).2.effects.returndata.length=32 := output_length

theorem wrong_extent (G : Glob env) : copyOutput (result G) rfl (placement G) 1 false old rfl (memory G) 5 2=
    (result G,none) := copyOutput_refusal _ rfl _ 1 false old rfl _ 5 2 (by change ¬(5+min 2 output.length≤old.length); rw [output_length]; decide)

theorem invalid_zero_copy (G : Glob env) : copyAfter (result G) rfl (placement G) 1 false old rfl (memory G) 1 33 0=
    (result G,none) := copyAfter_bad_source _ rfl _ 1 false old rfl _ 1 33 0 (by change output.length<33+0; rw [output_length]; decide)

theorem owner_memOK (G : Glob env) : Source.MemOK env (heap G).ty (after (caller G)) := by
  have first : HeapOK (E:=env) (Source.Heap.empty.alloc ⟨.bytes .memory,.bytes (input G)⟩).1 :=
    HeapOK.alloc HeapOK.empty (.bytes (input G))
  have ok : HeapOK (E:=env) (heap G) := HeapOK.alloc first (.bytes old)
  have top : HeapShaped (E:=env) (heap G) := HeapShaped.alloc (E:=env)
    (x:=⟨.bytes .memory,.bytes old⟩)
    (HeapShaped.alloc (E:=env) (x:=⟨.bytes .memory,.bytes (input G)⟩) HeapShaped.empty trivial) trivial
  have inner : HeapInner (E:=env) (heap G) := HeapInner.alloc (E:=env)
    (x:=⟨.bytes .memory,.bytes old⟩)
    (HeapInner.alloc (E:=env) (x:=⟨.bytes .memory,.bytes (input G)⟩) HeapInner.empty trivial) trivial
  exact ⟨⟨⟨ok,HeapTy.Le.refl _⟩,⟨⟨.bytes .memory,rfl,rfl⟩,⟨⟨.bytes .memory,rfl,rfl⟩,trivial⟩⟩⟩,top,inner⟩

theorem copied_memOK (G : Glob env) : Source.MemOK env (heap G).ty (copiedState G) :=
  HeapWindow.copyStateWindow_memOK _ _ _ _ _ _ _ _ _ _ _ _ _ _ (copy_state G) (owner_memOK G)

theorem read_before_write (m : ByteView) (destination : Nat) (bytes : Bytes) (base count : Nat)
    (before : base+count≤destination) :
    readBytes (writeBytes m destination bytes) base count=readBytes m base count := by
  apply List.ext_getElem
  · simp only [readBytes,List.length_map,List.length_range]
  · intro i hi hj
    have bound : i<count := by simpa only [readBytes,List.length_map,List.length_range] using hi
    simp only [readBytes,List.getElem_map,List.getElem_range]
    exact Solidity.Backend.Environment.writeBytes_frame _ _ _ _ (Or.inl (by omega))

theorem input_entry_after_copy (G : Glob env) : (inputEntry G).Reads (placement G) (copiedMemory G) := by
  have head : mload (copiedMemory G) 128=mload (memory G) 128 :=
    mload_congr _ _ _ (fun i=>Solidity.Backend.Environment.writeBytes_frame _ _ _ _
      (Or.inl (by have bound:=i.isLt; omega)))
  constructor
  · exact (congrArg Fin.val head).trans (input_reads G).1
  · have before : readBytes (memory G) 160 4=input G := by
      simpa only [inputEntry,input_length] using (input_reads G).2
    have after : readBytes (copiedMemory G) 160 4=input G :=
      (read_before_write (memory G) 289 [0x11,0x22] 160 4 (by decide)).trans before
    simpa only [inputEntry,input_length] using after

theorem return_size (G : Glob env) : returndataSize (result G).2.effects=some 32 := by
  have exactSize := checkedReturnSize_exact output (by rw [output_length]; decide)
  simpa only [output_length] using exactSize

theorem no_stale_buffer (G : Glob env) : (result G).2.effects.returndata≠[9,8,7,6] := by
  intro stale
  have length : (32 : Nat)=4 := output_length.symm.trans (congrArg List.length stale)
  exact (by decide : (32 : Nat)≠4) length

theorem wrong_bytes_rejected : copiedBytes≠[0xa1,9,8,0xd4,0xe5,0xf6] ∧
    copiedBytes≠[0x11,0x22,0xc3,0xd4,0xe5,0xf6] := by decide

theorem end_zero_copy (G : Glob env) : copyAfter (result G) rfl (placement G) 1 false old rfl (memory G) 6 32 0=
    (result G,some ((memory G,after (caller G)),(CallerFrameChecks.residual,CallerFrameChecks.encoding),(result G).2)) := by
  have zero : HeapWindow.copyHeapWindow (result G).2.effects (result G).1.1.1.2.heap
      (placement G) 1 false old rfl (memory G) 6 32 0=some (memory G,(result G).1.1.1.2.heap) :=
    HeapWindow.copyHeapWindow_zero (result G).2.effects (result G).1.1.1.2.heap (placement G) 1 false old rfl (memory G) 6 32
      (by change 32≤output.length; rw [output_length]; exact Nat.le_refl _) (by decide) (output_reads G).1 (output_reads G).2
  unfold copyAfter HeapWindow.copyCoupledWindow
  rw [HeapWindow.copyStateWindow_heap,zero]
  simp only [Option.map_some,withSourceHeap_unchanged]
  rfl

theorem enclosing_revert_keeps_copied_heap (G : Glob env) :
    finish (caller G) CallerFrameChecks.encoding (observed G)
      (enter (caller G) CallerFrameChecks.residual (parent (caller G)) .call CallerFrameChecks.receiver 7 (input G))
      ⟨⟨copiedState G,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ [] (.revert [0xee])=
      (⟨⟨withSourceHeap (caller G) (copiedHeap G),CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩,
        ⟨⟨entryExecution,committedLogs (observed G).trace,[0xee]⟩,(observed G).trace,rfl⟩) := by
  have rollback := finish_runs_revert (withSourceHeap (caller G) (copiedHeap G)) CallerFrameChecks.residual
    CallerFrameChecks.encoding (observed G)
    [.account CallerFrameChecks.owner (fun a=>a.withBalance 4),.account CallerFrameChecks.receiver (fun a=>a.withBalance 30)]
    [] [] CallerFrameChecks.receiver CallerFrameChecks.owner 7 (input G) false [] [0xee]
  simpa only [Source.ExecState.run,rollbackTrace,discardLogs,List.append_nil] using rollback

theorem static_kind_refusal (G : Glob env) (failed : Bool) : invokeTemplateAt 10 failed G (observed G)
    (enter (caller G) CallerFrameChecks.residual (parent (caller G)) .staticcall CallerFrameChecks.receiver 7 (input G))
    .staticcall CallerFrameChecks.receiver 10000 (input G)
    ⟨⟨⟨Source.L0 env,(caller G).2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=none := rfl

theorem wrong_context_refusal (G : Glob env) (failed : Bool) : invokeTemplateAt 10 failed G (observed G)
    (enter (caller G) CallerFrameChecks.residual {parent (caller G) with this:=CallerFrameChecks.target} .call CallerFrameChecks.receiver 7 (input G))
    .call CallerFrameChecks.receiver 10000 (input G)
    ⟨⟨⟨Source.L0 env,(caller G).2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=none := rfl

theorem wrong_value_refusal (G : Glob env) (failed : Bool) : invokeTemplateAt 10 failed G (observed G)
    (enter (caller G) CallerFrameChecks.residual (parent (caller G)) .call CallerFrameChecks.receiver 6 (input G))
    .call CallerFrameChecks.receiver 10000 (input G)
    ⟨⟨⟨Source.L0 env,(caller G).2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=none := rfl

theorem precompile_refusal (G : Glob env) (failed : Bool) : invokeTemplateAt 10 failed G (observed G)
    (enter (caller G) CallerFrameChecks.residual (parent (caller G)) .call ⟨1,by decide⟩ 7 (input G))
    .call ⟨1,by decide⟩ 10000 (input G)
    ⟨⟨⟨Source.L0 env,(caller G).2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=none := rfl

def unregistered (G : Glob env) : Source.EMState env [] :=
  ⟨Source.L0 env,{(caller G).2 with ex:=entryExecution.apply (.account CallerFrameChecks.receiver (fun a=>{a with code:=none}))}⟩

theorem registration_refusal (G : Glob env) (failed : Bool) : invokeTemplateAt 10 failed G (observed G)
    (enter (unregistered G) CallerFrameChecks.residual (parent (unregistered G)) .call CallerFrameChecks.receiver 7 (input G))
    .call CallerFrameChecks.receiver 10000 (input G)
    ⟨⟨unregistered G,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=none := rfl

end Solidity.Yul.World.ReturningCall
