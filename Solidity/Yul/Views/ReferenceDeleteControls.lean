import Solidity.Yul.Views.ReferenceDelete
import Solidity.Yul.Views.MemoryDeleteControls

/-! Actual reference deletion allocates empty bytes, updates one of two aliases,
and retains the old object and dirty padding. The source and physical states
use computed packing coordinates, not the unrelated spaced mixed-heap seed. -/
namespace Solidity.Yul.Views.ReferenceDelete.Controls
open Solidity.Yul.Views.Controls
open MemoryDelete.Controls

def p : Placement mixedHeap := ComputedPlacement.build mixedHeap rfl (by decide)
def words : List Roadmap.Word := [1,7,128,128,480]

def fields : MemoryFields p mixedFields words :=
  .cons (.bool true) 1 (.scalar _ _ (by decide)) _ _
    (.cons mixedSeven 7 (.scalar _ _ (by decide)) _ _
    (.cons (.memRef rfl 0) 128 (.pointer rfl 0 (.bytes .memory) rfl rfl) _ _
    (.cons (.memRef rfl 0) 128 (.pointer rfl 0 (.bytes .memory) rfl rfl) _ _
    (.cons (.memRef rfl 4) 480 (.pointer rfl 4 mixedArrayTy rfl rfl) _ _ .nil))))

def entry0 : MixedHeapEntry p := ⟨0,_,.bytes mixedChild,rfl,.bytes _ (by decide)⟩
def entry1 : MixedHeapEntry p := ⟨1,_,.string mixedString,rfl,.string _ (by decide)⟩
def entry2 : MixedHeapEntry p := ⟨2,_,mixedStatic,rfl,
  memoryArrayImage p 2 (n:=some 2) 2 (fun _ eq => (Option.some.inj eq).symm) mixedStaticVals
    (fun i => if i.val=0 then 7 else 9) (by
      intro i
      dsimp only
      by_cases zero : i.val=0
      · simp only [mixedStaticVals,if_pos zero]
        exact .scalar mixedSeven 7 (by decide)
      · simp only [mixedStaticVals,if_neg zero]
        exact .scalar mixedNine 9 (by decide)) rfl⟩
def entry3 : MixedHeapEntry p := ⟨3,_,.struct mixedFields,rfl,.words _ words (.strct _ _ fields)⟩
def entry4 : MixedHeapEntry p := ⟨4,_,mixedDynamic,rfl,
  memoryArrayImage p 4 (n:=none) 2 (fun _ eq => nomatch eq) (fun _ => .memRef rfl 0) (fun _ => 128)
    (fun _ => .pointer rfl 0 (.bytes .memory) rfl rfl) rfl⟩
def entry5 : MixedHeapEntry p := ⟨5,_,.bytes mixedOther,rfl,.bytes _ (by decide)⟩
def entries := [entry0,entry1,entry2,entry3,entry4,entry5]
def seed : ByteView := mstore (fun i => if 96≤i ∧ i<128 then 0 else 0xa5) 64 p.free
def memory := encodeMixedHeap p entries seed

theorem coverage : CoversMixedHeap entries := by
  intro a present
  have small := mixed_present_lt a present
  have choices : a=0 ∨ a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨entry0,List.mem_cons_self,rfl⟩
  · exact ⟨entry1,List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩
  · exact ⟨entry2,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),rfl⟩
  · exact ⟨entry3,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),rfl⟩
  · exact ⟨entry4,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))),rfl⟩
  · exact ⟨entry5,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))),rfl⟩

def raw := (ComputedAllocationWrite.prepare mixedHeap p rfl (Source.Data.bytes (l:=.memory) [])
  (.bytes 0) rfl (by decide) memory).getD memory
def patch := mstore raw 384 640

theorem allocation_step : ComputedAllocationWrite.prepare mixedHeap p rfl (Source.Data.bytes (l:=.memory) [])
    (.bytes 0) rfl (by decide) memory=some raw := rfl

theorem oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id) := by
  intro e _
  exact mixedImage_reads_of_coverage p entries coverage memory (encodeMixedHeap_reads p entries (by decide) seed) e

theorem reserved : ReservedOK memory p.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  apply encodeMixedHeap_reserved
  constructor
  · exact congrArg Fin.val (mload_mstore _ 64 p.free)
  · intro byte
    rw [seed,mstore_outside _ _ _ _ (by have small:=byte.isLt;omega)]
    have small := byte.isLt
    exact if_pos (by omega)

theorem source_and_physical :
    (Source.deleteLoc mixedReadFrame 2 (.mem (τ:=.bytes .memory) 3 2)).run mixedState=(.ok (),referenceAfter) ∧
    ∃ q : Placement referenceAfter.2.heap,
      q.address=(fun id => if id=6 then 640 else p.address id) ∧ q.free.val=672 ∧
      Source.MemOK mixedEnv mixedHeap.ty referenceAfter ∧
      encodeMixedHeap q (generatedHeapEntries q) patch=patch ∧
      ∃ snapshot : Placement MemoryDelete.Controls.allocated.2.heap, ∃ history : RetainedAllocation snapshot q,
        enumeratedMemoryWriteback referenceAfter snapshot q history patch=.ok (some (.ok (),referenceAfter)) ∧
        ReservedOK patch q.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  obtain ⟨r,after,q,step,addresses,free,run,safe,whole,origin,history,writeback,reservedAfter⟩ :=
    strct mixedHeap.ty mixedState p rfl mixed_actual_MemOK StructWordHeap.Controls.support mixedReadFrame 0 3 mixedName false
      mixedFields refFields words fields rfl ⟨2,by decide⟩ rfl (by decide) memory oldReads reserved
  have rawEq : r=raw := Option.some.inj (step.symm.trans allocation_step)
  subst r
  have actual : (Source.deleteLoc mixedReadFrame 2 (.mem (τ:=.bytes .memory) 3 2)).run mixedState=(.ok (),referenceAfter) := rfl
  have stateEq : after=referenceAfter := (congrArg Prod.snd run).symm.trans (congrArg Prod.snd actual)
  subst after
  exact ⟨actual,q,addresses,free,safe,whole,origin,history,writeback,reservedAfter⟩

theorem exact_raw : (mload patch 64).val=672 ∧ (mload patch 640).val=0 ∧
    (mload patch 384).val=640 ∧ (mload patch 416).val=128 ∧ (mload patch 128).val=3 ∧
    patch 160=0x11 ∧ patch 162=0x33 ∧ patch 163=0xa5 ∧ patch 672=0xa5 := by decide

theorem actual_aliases :
    (Source.readLoc (E:=mixedEnv) mixedReadFrame (.mem (τ:=.bytes .memory) 3 2)).run referenceAfter=
      (.ok (.memRef rfl 6),referenceAfter) ∧
    (Source.readLoc (E:=mixedEnv) mixedReadFrame (.mem (τ:=.bytes .memory) 3 3)).run referenceAfter=
      (.ok (.memRef rfl 0),referenceAfter) ∧
    (Source.heapBytes (E:=mixedEnv) (Γ:=_) 6).run referenceAfter=(.ok [],referenceAfter) ∧
    (Source.heapBytes (E:=mixedEnv) (Γ:=_) 0).run referenceAfter=(.ok mixedChild,referenceAfter) := ⟨rfl,rfl,rfl,rfl⟩

theorem allocation_before_type_failure :
    (Source.deleteLoc mixedReadFrame 2 (.mem (τ:=.bytes .memory) 3 0)).run mixedState=
      (.error (.stuck "field type"),allocated) := rfl

def allocationPlacement := ComputedAllocationWrite.placement mixedHeap p rfl (Source.Data.bytes (l:=.memory) [])
  (.bytes 0) rfl (by decide)

theorem allocation_failure_and_map :
    (Source.deleteLoc mixedReadFrame 2 (.mem (τ:=.bytes .memory) 3 0)).run mixedState=
      (.error (.stuck "field type"),allocated) ∧
    Source.MemOK mixedEnv mixedHeap.ty allocated ∧
    encodeMixedHeap allocationPlacement (generatedHeapEntries allocationPlacement) raw=raw ∧
    enumeratedMemoryWriteback allocated allocationPlacement allocationPlacement (retainInitial _ _) raw=
      .ok (some (.ok (),allocated)) := by
  first | (simp only;done) | decide | omega | rfl | skip
  have physical := ComputedAllocationWrite.sound mixedHeap.ty mixedState p rfl
    (Source.Data.bytes (l:=.memory) []) (.bytes 0) rfl (by decide) memory raw allocation_step mixed_actual_MemOK
    trivial (.bytes _) trivial StructWordHeap.Controls.support oldReads
  exact ⟨rfl,physical.2.1,physical.2.2.2.1,physical.2.2.2.2⟩

theorem missing_allocation_negative : (mload patch 384).val≠(mload memory 384).val ∧
    (mload patch 64).val≠(mload memory 64).val := by decide

theorem false_zero_pointer_negative : (mload patch 384).val≠0 := by decide
end Solidity.Yul.Views.ReferenceDelete.Controls
