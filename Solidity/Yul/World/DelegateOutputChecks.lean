import Solidity.Yul.World.DelegateOutputFailure
namespace Solidity.Yul.World.DelegateOutputChecks
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.DelegatePhysical
open Solidity.Yul.World.DelegatePort
open Solidity.Yul.World.StateCallChecks (caller residual observed memory heap placement byteEntry)

/-- Exact destination and strict region:160/161change, every other raw byte
is preserved. This uses the full image from the actual runAndCopy theorem. -/
theorem outside_bytes (G : Glob env) (i : Nat) (outside : i<160 ∨ 162≤i) :
    Solidity.Backend.Environment.writeBytes (memory G) 160 [0x11,0x22] i=memory G i :=
  Solidity.Backend.Environment.writeBytes_frame [0x11,0x22] 160 i (memory G) outside

theorem header_preserved (G : Glob env) :
    mload (Solidity.Backend.Environment.writeBytes (memory G) 160 [0x11,0x22]) 128=mload (memory G) 128 := by
  apply mload_congr
  intro i
  apply outside_bytes
  left
  have bound:=i.isLt
  omega

theorem full_state (G : Glob env) :
    ∃ m' s', DelegateOutput.expected G=(DelegateOutput.completed G,
      some ((m',s'),((DelegateOutput.completed G).1.1.2,(DelegateOutput.completed G).1.2),(DelegateOutput.completed G).2)) ∧
      s'.1=(caller G).1 ∧ s'.2.ex=(changed (caller G) account).2.ex ∧ s'.2.events=(caller G).2.events ∧
      s'.2.logs=(caller G).2.logs ∧ s'.2.fnLocals=(caller G).2.fnLocals ∧
      s'.2.heap.ty=(heap G).ty ∧ s'.2.heap.next=(heap G).next :=
  HeapOutputTransport.image_frame (DelegateOutput.completed G) (heap G) (DelegateOutput.heap_eq G)
    (placement G) (byteEntry G) (memory G) 0 [0x11,0x22]

theorem destination_refusal (G : Glob env) :
    HeapOutputTransport.copy (DelegateOutput.completed G) (DelegateOutput.shared G)
      (heap G) (DelegateOutput.heap_eq G) (placement G) (byteEntry G) (memory G) 3 2=
      (DelegateOutput.completed G,none) := by
  apply HeapOutputTransport.destination_refused
  simp only [DelegateOutput.data,ReturningCall.output_exact,StateCallChecks.byteEntry,input_length,
    List.length_append,List.length_cons,List.length_nil,List.length_replicate]
  decide

theorem stale_refusal : returnWindow observed.effects.returndata 4 2=none := rfl

theorem actual_buffer (G : Glob env) :
    (DelegateOutput.completed G).2.effects.returndata.length=32 ∧
    (DelegateOutputFailure.completed G).2.effects.returndata.length=36 ∧ observed.effects.returndata.length=4 := by
  constructor
  · rw [DelegateOutput.data]
    simp only [ReturningCall.output_exact,List.length_append,List.length_cons,List.length_nil,List.length_replicate]
  · exact ⟨StateCallExtra.error_length G,rfl⟩

theorem full_prefix (G : Glob env) :
    let c:=DelegateOutput.completed G
    c.2.trace=observed.trace ∧ c.1.1.1.2.ex.journal.length=5 ∧ c.1.1.2.journal.length=2 ∧ c.1.2.journal.length=2 ∧
    c.2.effects.returndata=ReturningCall.output ∧ (caller G).2.ex.journal.length=4 ∧ residual.journal.length=1 ∧ before.journal.length=1 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem completed_memOK (G : Glob env) : Source.MemOK env (heap G).ty (DelegateOutput.completed G).1.1.1 := by
  have actual:=representedSourceStep_MemOK (heap G).ty
    (DelegateBody.frame account DelegateChecks.sender DelegateChecks.value 1) plan (caller G) residual
    (StateCallChecks.caller_memOK G)
  rw [representedSourceStep_nonstatic _ _ _ _ rfl,DelegatePhysical.source_op] at actual
  exact actual

theorem copied_memOK (G : Glob env) :
    ∃ m' s', DelegateOutput.expected G=(DelegateOutput.completed G,
      some ((m',s'),((DelegateOutput.completed G).1.1.2,(DelegateOutput.completed G).1.2),(DelegateOutput.completed G).2)) ∧
      Source.MemOK env (heap G).ty s' :=
  HeapOutputTransport.image_memOK (DelegateOutput.completed G) (heap G) (DelegateOutput.heap_eq G)
    (placement G) (byteEntry G) (memory G) 0 [0x11,0x22] (heap G).ty (completed_memOK G)
end Solidity.Yul.World.DelegateOutputChecks
