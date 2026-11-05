import Solidity.Yul.Views.ReferenceDeleteRetained
import Solidity.Yul.Views.RetainedMemberControls
import Solidity.Yul.Views.MemoryDeleteControls

/-! A real retained history shrinks an array2->0 before allocating reference
deletion elsewhere. Original array capacity and dormant pointer words survive
in the extended origin; the new empty child does not replace that provenance. -/
namespace Solidity.Yul.Views.ReferenceDeleteRetained.Controls
open Solidity.Yul.Views.Controls

def p := retainedRefZeroPlacement

theorem types : retainedRefZeroHeap.ty=mixedHeap.ty :=
  funext (fun a => Source.Heap.write_ty mixedHeap 4 a _ (by rfl))

def fields : MemoryFields p mixedFields mixedStructWords :=
  StructWordStore.Controls.fields.transport p types rfl

def entry0 : MixedHeapEntry p := ⟨0,_,.bytes mixedChild,rfl,.bytes _ (by decide)⟩
def entry1 : MixedHeapEntry p := ⟨1,_,.string mixedString,rfl,.string _ (by decide)⟩
def entry2 : MixedHeapEntry p := ⟨2,_,mixedStatic,rfl,
  memoryArrayImage p 2 (n:=some 2) 2 (fun _ eq => (Option.some.inj eq).symm) mixedStaticVals
    (fun i => if i.val=0 then 7 else 9) (fun i => (mixed_static_element i).transport p types rfl) rfl⟩
def entry3 : MixedHeapEntry p := ⟨3,_,.struct mixedFields,rfl,.words _ mixedStructWords (.strct _ _ fields)⟩
def entry4 : MixedHeapEntry p := ⟨4,_,dynamicMemberData mixedLayout (.bytes .memory) 0 Fin.elim0,rfl,
  memoryArrayImage p 4 (n:=none) 0 (fun _ eq => nomatch eq) Fin.elim0 Fin.elim0 (fun i=>nomatch i) rfl⟩
def entry5 : MixedHeapEntry p := ⟨5,_,.bytes mixedOther,rfl,.bytes _ (by decide)⟩
def entries := [entry0,entry1,entry2,entry3,entry4,entry5]
def memory := encodeMixedHeap p entries mixedPhysical

theorem coverage : CoversMixedHeap entries := by
  intro a present
  have small : a<6 := by
    rw [retainedRefZeroHistory.occupancy a] at present
    exact mixed_present_lt a present
  have choices : a=0 ∨ a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨entry0,List.mem_cons_self,rfl⟩
  · exact ⟨entry1,List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩
  · exact ⟨entry2,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),rfl⟩
  · exact ⟨entry3,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),rfl⟩
  · exact ⟨entry4,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))),rfl⟩
  · exact ⟨entry5,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))),rfl⟩

theorem oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id) := by
  intro e _
  exact mixedImage_reads_of_coverage p entries coverage memory (encodeMixedHeap_reads p entries (by decide) mixedPhysical) e

theorem initial_safe : Source.MemOK mixedEnv mixedHeap.ty retainedRefZeroState :=
  retainedMemberArray_MemOK mixedEnv mixedHeap.ty mixedState mixedPlacement mixedPlacement (retainInitial _ _)
    mixedEntries 4 (.bytes .memory) retainedRefZeroPhysical _ retained_ref_source_zero mixed_actual_MemOK

theorem support : ∀ a τ d,retainedRefZeroHeap.get a=some ⟨τ,d⟩ → InventoryTypeSupported mixedEnv τ :=
  heapWrite_inventory_supported mixedHeap 4 (dynamicMemberData mixedLayout (.bytes .memory) 0 Fin.elim0)
    (by rfl) StructWordHeap.Controls.support

theorem fresh : ∀ a,(mixedHeap.cells a).isSome → mixedPlacement.address a≠1664 := by
  intro a present
  have small := mixed_present_lt a present
  change 128+a*256≠1664
  omega

theorem currentFresh : ∀ a,(retainedRefZeroHeap.cells a).isSome → p.address a≠1664 := by
  intro a present
  apply fresh
  rw [←retainedRefZeroHistory.occupancy a]
  exact present

def snapshot := heapAllocPlacement mixedHeap mixedPlacement (Source.Data.bytes (l:=.memory) []) (.bytes 0) (.bytes _)
  1664 1696 (by decide) fresh (by decide)
def allocated := objectAllocatedState retainedRefZeroState (Source.Data.bytes (l:=.memory) [])
def post := withSourceHeap allocated (allocated.2.heap.write 3 (.struct MemoryDelete.Controls.refFields) (by rfl))
def raw := (objectAllocationView retainedRefZeroHeap p (Source.Data.bytes (l:=.memory) []) rfl (.bytes 0) (.bytes _)
  1664 1696 (by decide) currentFresh (by decide) memory).getD memory
def patch := mstore raw 960 1664

theorem allocation_step : objectAllocationView retainedRefZeroHeap p (Source.Data.bytes (l:=.memory) []) rfl (.bytes 0) (.bytes _)
    1664 1696 (by decide) currentFresh (by decide) memory=some raw := rfl

theorem source_and_retained :
    (Source.deleteLoc mixedReadFrame 2 (.mem (τ:=.bytes .memory) 3 2)).run retainedRefZeroState=(.ok (),post) ∧
    ∃ q : Placement post.2.heap,
      q.address=(fun id => if id=6 then 1664 else p.address id) ∧ q.free=1696 ∧
      Source.MemOK mixedEnv mixedHeap.ty post ∧ encodeMixedHeap q (generatedHeapEntries q) patch=patch ∧
      ∃ history : RetainedAllocation snapshot q,
        enumeratedMemoryWriteback post snapshot q history patch=.ok (some (.ok (),post)) ∧ ReservedOK patch q.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  have reserved : ReservedOK memory p.free := encodeMixedHeap_reserved p entries mixedPhysical mixed_reserved
  obtain ⟨r,out,q,step,addresses,free,run,safe,full,history,wb,reservedOut⟩ :=
    strct mixedHeap.ty retainedRefZeroState mixedPlacement p retainedRefZeroHistory initial_safe support mixedReadFrame 0 3 mixedName false
      mixedFields MemoryDelete.Controls.refFields mixedStructWords fields rfl ⟨2,by decide⟩ rfl
      1664 1696 (by decide) fresh (by decide) memory oldReads reserved
  have rawEq : r=raw := Option.some.inj (step.symm.trans allocation_step)
  subst r
  have actual : (Source.deleteLoc mixedReadFrame 2 (.mem (τ:=.bytes .memory) 3 2)).run retainedRefZeroState=(.ok (),post) := rfl
  have stateEq : out=post := (congrArg Prod.snd run).symm.trans (congrArg Prod.snd actual)
  subst out
  exact ⟨actual,q,addresses,free,safe,full,history,wb,reservedOut⟩

theorem original_capacity_and_dormant_words : (snapshot.shape 4).size=96 ∧ (p.shape 4).size=32 ∧
    (mload patch 1152).val=0 ∧ (mload patch 1184).val=128 ∧ (mload patch 1216).val=128 ∧
    (mload patch 960).val=1664 ∧ (mload patch 992).val=128 ∧ (mload patch 1664).val=0 ∧
    (mload patch 64).val=1696 ∧ patch 163=0xa5 ∧ patch 1696=0xa5 := by decide

theorem actual_aliases :
    post.2.heap.get 4=some ⟨_,dynamicMemberData mixedLayout (.bytes .memory) 0 Fin.elim0⟩ ∧
    (Source.readLoc (E:=mixedEnv) mixedReadFrame (.mem (τ:=.bytes .memory) 3 2)).run post=(.ok (.memRef rfl 6),post) ∧
    (Source.readLoc (E:=mixedEnv) mixedReadFrame (.mem (τ:=.bytes .memory) 3 3)).run post=(.ok (.memRef rfl 0),post) ∧
    post.2.heap.get 0=mixedHeap.get 0 := ⟨rfl,rfl,rfl,rfl⟩

theorem replaced_history_negative : (snapshot.shape 4).size≠(p.shape 4).size := by decide

def regrow := mstore patch 1152 2
def regrown := withSourceHeap post (post.2.heap.write 4 (dynamicMemberData mixedLayout (.bytes .memory) 2 retainedRefOld) (by rfl))

theorem regrowth_recovers_dormant_aliases :
    ∃ (q : Placement post.2.heap) (history : RetainedAllocation snapshot q),
      retainedMemberArrayState post snapshot q history (generatedHeapEntries q) 4 (.bytes .memory) regrow=
        some (.ok (),regrown) := by
  first | (simp only;done) | decide | omega | rfl | skip
  obtain ⟨_,q,addresses,free,safe,full,history,wb,reservedOut⟩ := source_and_retained
  have supportAllocated := heapAlloc_inventory_supported retainedRefZeroHeap (Source.Data.bytes (l:=.memory) []) trivial support
  have supportOut := heapWrite_inventory_supported allocated.2.heap 3 (.struct MemoryDelete.Controls.refFields) (by rfl) supportAllocated
  have coverage := (prepareHeapInventory_ok q _ (ownerMemOK_prepares_inventory mixedHeap.ty post q safe supportOut)).2.1
  have address0 : q.address 0=128 := by rw [addresses];rfl
  have address4 : q.address 4=1152 := by rw [addresses];rfl
  have childType : post.2.heap.ty 0=some (.bytes .memory) := rfl
  have word : ownedPointerWord q 0 (.bytes .memory) childType=128 := Fin.ext address0
  have element : MemoryElement q (Source.Val.memRef (τ:=.bytes .memory) rfl 0) 128 := by
    rw [←word]
    exact .pointer rfl 0 (.bytes .memory) childType rfl
  have decode0 := decodeMemoryMember_encode q _ coverage (.bytes .memory) (Or.inr (Or.inr rfl))
    (Source.Val.memRef (τ:=.bytes .memory) rfl 0) 128 element
  have tail : ∀ i : Fin 2,mload regrow (1184+i.val*32)=128 := by
    intro i
    have choices : i=0 ∨ i=1 := by have small:=i.isLt;apply Or.imp Fin.ext Fin.ext;omega
    rcases choices with rfl | rfl <;> decide
  have decoded : decodeArrayMembers q (generatedHeapEntries q) (.bytes .memory) 2 regrow 1184=some retainedRefOld := by
    apply decodeArrayMembers_of_decodes
    intro i
    rw [tail i]
    exact decode0
  refine ⟨q,history,?_⟩
  unfold retainedMemberArrayState
  rw [address4,show mload regrow 1152=2 from mload_mstore _ _ _,if_pos (by decide)]
  change (decodeArrayMembers q (generatedHeapEntries q) (.bytes .memory) 2 regrow 1184).map _=some _
  rw [decoded]
  rfl
end Solidity.Yul.Views.ReferenceDeleteRetained.Controls
