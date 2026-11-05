import Solidity.Yul.Views.StructWordHeap
import Solidity.Yul.Views.StructWordStoreControls

/-! Six heterogeneous objects inhabit the whole-heap struct update theorem.
The pointer field changes its child while the sibling alias, other objects,
reserved bytes and unknown padding survive. Wrong words cannot represent the
changed field; preparation failure remains separate from Source errors. -/
namespace Solidity.Yul.Views.StructWordHeap.Controls
open Solidity.Yul.Views.Controls
open StructWordStore.Controls

def next := withSourceHeap mixedState (mixedHeap.write 3 (.struct pointerFields) (by rfl))
def placement := structWrittenPlacement mixedHeap mixedPlacement 3 mixedName mixedFields pointerFields rfl

theorem support : ∀ a τ d,mixedHeap.get a=some ⟨τ,d⟩ → InventoryTypeSupported mixedEnv τ := by
  first | (simp only;done) | decide | omega | rfl | skip
  intro a τ d found
  have present : (mixedHeap.cells a).isSome := by change (mixedHeap.get a).isSome=true;rw [found];rfl
  have small := mixed_present_lt a present
  have choices : a=0 ∨ a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl <;> cases found
  · trivial
  · trivial
  · exact Or.inl (Or.inr (Or.inl rfl))
  · exact supported
  · exact Or.inl (Or.inr (Or.inr rfl))
  · trivial

theorem source_and_whole :
    (Source.writeLoc mixedReadFrame 0 (.mem 3 2) (Source.Val.memRef (τ:=.bytes .memory) rfl 5)).run mixedState=(.ok (),next) ∧
    Source.MemOK mixedEnv mixedHeap.ty next ∧ CoversMixedHeap (generatedHeapEntries placement) ∧
    encodeMixedHeap placement (generatedHeapEntries placement) pointerPatch=pointerPatch ∧
    enumeratedMemoryWriteback next placement placement (retainInitial _ _) pointerPatch=.ok (some (.ok (),next)) ∧
    ReservedOK pointerPatch placement.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  have beforeReads : ∀ e∈generatedHeapEntries mixedPlacement,e.image.Reads mixedPhysical (mixedPlacement.address e.id) := by
    intro e _
    exact mixedImage_reads_of_coverage mixedPlacement mixedEntries mixed_coverage mixedPhysical mixed_all_reads e
  exact whole mixedHeap.ty mixedState mixedPlacement mixed_actual_MemOK support mixedReadFrame 0 3 mixedName
    mixedFields pointerFields mixedStructWords fields rfl ⟨2,by decide⟩ (.memRef rfl 5) 1408
    (.pointer rfl 5 (.bytes .memory) rfl rfl) rfl mixedPhysical beforeReads mixed_reserved

theorem every_H (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H mixedState) : Source.MemOK mixedEnv H next := by
  first | (simp only;done) | decide | omega | rfl | skip
  have beforeReads : ∀ e∈generatedHeapEntries mixedPlacement,e.image.Reads mixedPhysical (mixedPlacement.address e.id) := by
    intro e _
    exact mixedImage_reads_of_coverage mixedPlacement mixedEntries mixed_coverage mixedPhysical mixed_all_reads e
  exact (whole H mixedState mixedPlacement ok support mixedReadFrame 0 3 mixedName
    mixedFields pointerFields mixedStructWords fields rfl ⟨2,by decide⟩ (.memRef rfl 5) 1408
    (.pointer rfl 5 (.bytes .memory) rfl rfl) rfl mixedPhysical beforeReads mixed_reserved).2.1

theorem aliases_and_other_objects :
    (Source.readLoc (E:=mixedEnv) mixedReadFrame (.mem (τ:=.bytes .memory) 3 2)).run next=(.ok (.memRef rfl 5),next) ∧
    (Source.readLoc (E:=mixedEnv) mixedReadFrame (.mem (τ:=.bytes .memory) 3 3)).run next=(.ok (.memRef rfl 0),next) ∧
    next.2.heap.get 0=mixedHeap.get 0 ∧ next.2.heap.get 5=mixedHeap.get 5 := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem raw_boundaries : (mload pointerPatch 960).val=1408 ∧ (mload pointerPatch 992).val=128 ∧
    (mload pointerPatch 128).val=3 ∧ (mload pointerPatch 1408).val=3 ∧ pointerPatch 1443=0xa5 ∧
    pointerPatch 1056=0xa5 := by decide

theorem stale_word_negative : mload mixedPhysical 960≠mload pointerPatch 960 := by decide

theorem wrong_child_negative : (Source.readLoc (E:=mixedEnv) mixedReadFrame
    (.mem (τ:=.bytes .memory) 3 2)).run next≠(.ok (.memRef rfl 0),next) := by
  first | (simp only;done) | decide | omega | rfl | skip
  intro bad
  have values := congrArg Prod.fst bad
  cases values

theorem malformed_preparation : canonicalStructState mixedState mixedPlacement mixedEntries 3 mixedName
    (mstore mixedPhysical 896 2)=none := noncanonical_bool_preparation

theorem wrong_type_preserves_source :
    (Source.writeLoc mixedReadFrame 0 (.mem 3 0) (uintValueOfWord mixedLayout 0)).run mixedState=
      (.error (.stuck "field type"),mixedState) := wrong_field_type
end Solidity.Yul.Views.StructWordHeap.Controls
