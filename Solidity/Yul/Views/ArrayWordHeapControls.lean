import Solidity.Yul.Views.ArrayWordHeap
import Solidity.Yul.Views.ArrayWordStoreControls

/-! Whole generated heap reconstruction after the actual new-pointer consumer.
All four objects and unknown tail bytes participate; the post-write Source
state is the same one reached by the actual new/getV/writeLoc computation. -/
namespace Solidity.Yul.Views.ArrayWordHeap.Controls
open ArrayWordStore
open AllocationPointer.Controls
open ArrayWordStore.Controls

def seed : ByteView := mstore (fun i=>if i=383 then 99 else 0) 64 q.free
def memory := encodeMixedHeap q (generatedHeapEntries q) seed
def patched := mstore memory 256 288
def values := replace old ⟨0,by decide⟩ (Source.Val.memRef (τ:=.bytes .memory) rfl 3)
def next := withSourceHeap after (after.2.heap.write 2
  (memberArrayData E.layout (.bytes .memory) (some 1) 1 (fun _ eq => (Option.some.inj eq).symm) values) (by rfl))
def placement := memberArrayWrittenPlacement after.2.heap q 2 (.bytes .memory) (some 1) 1
  (fun _ eq => (Option.some.inj eq).symm) old values rfl

theorem old_safe : Source.MemOK E initial.2.heap.ty after :=
  (objectAllocRef_MemOK initial.2.heap.ty initial data rfl trivial trivial (.bytes _) initial_safe).1

theorem source_and_whole :
    (Source.writeLoc F 0 (.mem 2 0) (Source.Val.memRef (τ:=.bytes .memory) rfl 3)).run after=(.ok (),next) ∧
    Source.MemOK E initial.2.heap.ty next ∧ CoversMixedHeap (generatedHeapEntries placement) ∧
    encodeMixedHeap placement (generatedHeapEntries placement) patched=patched ∧
    enumeratedMemoryWriteback next placement placement (retainInitial _ _) patched=.ok (some (.ok (),next)) ∧
    ReservedOK patched placement.free := by
  have support : ∀ a τ d,after.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ := by
    intro a τ d found
    have small : a<4 := by
      by_cases small : a<4
      · exact small
      · have missing := after.2.heap.bounded a (by change 4≤a;omega)
        change after.2.heap.cells a=some ⟨τ,d⟩ at found
        rw [missing] at found
        cases found
    have choices : a=0 ∨ a=1 ∨ a=2 ∨ a=3 := by omega
    rcases choices with rfl | rfl | rfl | rfl <;> cases found
    · trivial
    · trivial
    · exact Or.inl (Or.inr (Or.inr rfl))
    · trivial
  have oldRead : ∀ e∈generatedHeapEntries q,e.image.Reads memory (q.address e.id) :=
    encodeMixedHeap_reads q _ (prepareHeapInventory_ok q _ rfl).2.2 seed
  have start : ReservedOK seed q.free := by
    constructor
    · exact congrArg Fin.val (mload_mstore (fun i=>if i=383 then 99 else 0) 64 q.free)
    · intro i
      rw [seed,mstore_outside _ _ _ _ (by have small:=i.isLt;omega)]
      have small:=i.isLt
      rw [if_neg (by omega)]
  exact whole initial.2.heap.ty after q old_safe support F 0 2 (.bytes .memory) (some 1) 1
    (fun _ eq => (Option.some.inj eq).symm) old words old_encoded rfl ⟨0,by decide⟩
    (.memRef rfl 3) 288 next_encoded memory oldRead (encodeMixedHeap_reserved q _ seed start)

theorem actual_consumer (G : Source.Glob E) (n : Nat) :
    (AllocationPointer.writeNew G F (n+1) 0 (τ:=.bytes .memory) rfl (.local .here) rfl 2 0).run initial=(.ok (),next) := by
  have actual : (Source.writeLoc F 0 (.mem 2 0) (Source.Val.memRef (τ:=.bytes .memory) rfl 3)).run after=(.ok (),written) := rfl
  have same : written=next := congrArg Prod.snd (actual.symm.trans source_and_whole.1)
  rw [AllocationPointer.Controls.actual_success G n,same]

theorem unknown_tail : patched 383=99 := by
  rw [patched,mstore_outside _ _ _ _ (by decide)]
  rw [memory,encodeMixedHeap_residual q _ seed 383]
  · rw [seed,mstore_outside _ _ _ _ (by decide)]
    rfl
  · intro e member
    have present : (after.2.heap.cells e.id).isSome := by
      change (after.2.heap.get e.id).isSome=true
      rw [e.found]
      rfl
    have bound := q.ends e.id present
    have fits := e.image.fits q e.id e.found
    have free : q.free.val=352 := rfl
    exact Or.inr (by omega)
theorem old_parent : mload memory 256=128 := by
  have original := encodeMixedHeap_reads q (generatedHeapEntries q)
    (prepareHeapInventory_ok q _ rfl).2.2 seed
  let image := memoryArrayImage q 2 1 (fun _ eq => (Option.some.inj eq).symm) old words old_encoded rfl
  have read := mixedImage_reads_of_coverage q _ (prepareHeapInventory_ok q _ rfl).2.1 memory original
    (⟨2,_,_,rfl,image⟩ : MixedHeapEntry q)
  have parts := inventory_array_reads (some 1) 1 (fun _ eq => (Option.some.inj eq).symm) (by decide)
    words memory 256 read
  exact parts.2 ⟨0,by decide⟩

theorem nontrivial_change : patched≠memory := by
  intro same
  have impossible : (288 : Roadmap.Word)=128 :=
    (mload_mstore memory 256 288).symm.trans ((congrArg (fun m => mload m 256) same).trans old_parent)
  exact (by decide : (288 : Roadmap.Word)≠128) impossible
end Solidity.Yul.Views.ArrayWordHeap.Controls
