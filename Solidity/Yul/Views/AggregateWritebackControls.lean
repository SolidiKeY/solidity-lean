import Solidity.Yul.Views.AggregateWriteback
import Solidity.Yul.Views.DynamicUintControls

namespace Solidity.Yul.Views.Controls

theorem mixed_member_support (τ : Source.STy) (member : τ ∈ mixedLayout.fields mixedName) : OrdinaryMemberType τ := by
  change τ ∈ mixedTypes at member
  simp only [mixedTypes, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with eq | eq | eq | eq | eq
  · exact Or.inl eq
  · exact Or.inr (Or.inl eq)
  · subst τ; exact Or.inr (Or.inr rfl)
  · subst τ; exact Or.inr (Or.inr rfl)
  · subst τ; exact Or.inr (Or.inr rfl)

def allChangedFields : Source.DataList mixedLayout (mixedLayout.fields mixedName) :=
  .cons (.val (.bool false)) (.cons (.val (uintValueOfWord mixedLayout highestUint))
    (.cons (.val (.memRef rfl 1)) (.cons (.val (.memRef rfl 1)) (.cons (.val (.memRef rfl 4)) .nil))))
def allChangedWords : List Roadmap.Word := [0, highestUint, 384, 384, 1152]

theorem all_changed_fields_encoded : MemoryFields mixedPlacement allChangedFields allChangedWords :=
  .cons (.bool false) 0 (.scalar _ _ rfl) _ _
  (.cons (uintValueOfWord mixedLayout highestUint) highestUint (.scalar _ _ (uintValueOfWord_word _ _)) _ _
  (.cons (.memRef rfl 1) 384 (.pointer (p := mixedPlacement) (τ := .bytes .memory) rfl 1 (.string .memory) rfl rfl) _ _
  (.cons (.memRef rfl 1) 384 (.pointer (p := mixedPlacement) (τ := .bytes .memory) rfl 1 (.string .memory) rfl rfl) _ _
  (.cons (.memRef rfl 4) 1152 (.pointer rfl 4 mixedArrayTy rfl rfl) _ _ .nil))))

def allChangedPhysical := wordListView allChangedWords mixedPhysical 896
def allChangedHeap := mixedHeap.write 3 (.struct allChangedFields) (by rfl)
def allChangedState := withSourceHeap mixedState allChangedHeap

theorem all_changed_decode : decodeMemoryFields mixedPlacement mixedEntries (mixedLayout.fields mixedName) allChangedPhysical 896 = some allChangedFields :=
  decodeMemoryFields_encode mixedPlacement mixedEntries mixed_coverage all_changed_fields_encoded mixed_member_support _ _

theorem all_changed_heap_step : structHeapWriteback mixedHeap mixedPlacement mixedEntries 3 mixedName mixedFields rfl allChangedPhysical = some allChangedHeap :=
  structHeapWriteback_encode mixedHeap mixedPlacement mixedEntries mixed_coverage 3 mixedName mixedFields allChangedFields rfl allChangedWords
    all_changed_fields_encoded mixed_member_support mixedPhysical

theorem all_changed_source_step : structStateWriteback mixedState mixedPlacement mixedEntries 3 mixedName allChangedPhysical = some (.ok (), allChangedState) := by
  unfold structStateWriteback
  change (decodeMemoryFields mixedPlacement mixedEntries (mixedLayout.fields mixedName) allChangedPhysical 896).map _ = _
  rw [all_changed_decode]
  rfl

theorem all_changed_MemOK (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H mixedState) : Source.MemOK mixedEnv H allChangedState :=
  structStateWriteback_MemOK mixedEnv H mixedState mixedPlacement mixedEntries 3 mixedName allChangedPhysical _ all_changed_source_step ok

def allChangedPlacement := structWrittenPlacement mixedHeap mixedPlacement 3 mixedName mixedFields allChangedFields rfl

theorem all_changed_placement : allChangedPlacement.address = mixedPlacement.address ∧ allChangedPlacement.shape = mixedPlacement.shape ∧ allChangedPlacement.free = mixedPlacement.free := ⟨rfl, rfl, rfl⟩

theorem all_changed_other_objects : allChangedHeap.get 0 = mixedHeap.get 0 ∧ allChangedHeap.get 1 = mixedHeap.get 1 ∧
    allChangedHeap.get 2 = mixedHeap.get 2 ∧ allChangedHeap.get 4 = mixedHeap.get 4 ∧ allChangedHeap.get 5 = mixedHeap.get 5 ∧
    allChangedHeap.next = mixedHeap.next := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem all_changed_aliases (horizon : Nat) :
    (readMixedMemberBytes 2 horizon).run allChangedState = (.ok mixedString, allChangedState) ∧
    (readMixedMemberBytes 3 horizon).run allChangedState = (.ok mixedString, allChangedState) ∧
    (Source.readLoc (E := mixedEnv) mixedReadFrame (τ := .bool) (.mem 3 0)).run allChangedState = (.ok (.bool false), allChangedState) ∧
    (Source.readLoc (E := mixedEnv) mixedReadFrame (τ := .int Source.IntTy.u256) (.mem 3 1)).run allChangedState =
      (.ok (uintValueOfWord mixedLayout highestUint), allChangedState) := ⟨rfl, rfl, rfl, rfl⟩

theorem all_changed_raw_reencode : ∃ ws, MemoryFields mixedPlacement allChangedFields ws ∧ wordListView ws allChangedPhysical 896 = allChangedPhysical :=
  decodedStruct_raw_reencode mixedPlacement mixedEntries mixedName allChangedPhysical 896 allChangedFields all_changed_decode

theorem all_changed_residual : allChangedPhysical 64 = mixedPhysical 64 ∧ allChangedPhysical 96 = mixedPhysical 96 ∧
    allChangedPhysical 1056 = mixedPhysical 1056 ∧ allChangedPhysical 163 = mixedPhysical 163 :=
  ⟨wordList_residual _ _ _ _ (Or.inl (by decide)), wordList_residual _ _ _ _ (Or.inl (by decide)),
    wordList_residual _ _ _ _ (Or.inr (by decide)), wordList_residual _ _ _ _ (Or.inl (by decide))⟩

theorem mixed_original_fields : MemoryFields mixedPlacement mixedFields mixedStructWords :=
  .cons (.bool true) 1 (.scalar _ _ rfl) _ _
  (.cons mixedSeven 7 (.scalar _ _ (by decide)) _ _
  (.cons (.memRef rfl 0) mixedPointer (.pointer rfl 0 (.bytes .memory) rfl rfl) _ _
  (.cons (.memRef rfl 0) mixedPointer (.pointer rfl 0 (.bytes .memory) rfl rfl) _ _
  (.cons (.memRef rfl 4) mixedArrayPointer (.pointer rfl 4 mixedArrayTy rfl rfl) _ _ .nil))))

theorem aggregate_unchanged_whole_heap : structHeapWriteback mixedHeap mixedPlacement mixedEntries 3 mixedName mixedFields rfl mixedPhysical = some mixedHeap := by
  apply structHeapWriteback_unchanged _ _ _ mixed_coverage _ _ _ rfl mixedStructWords mixed_original_fields mixed_member_support
  intro i w found
  have reads := (mixed_all_reads mixedEntry3 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) )
  exact reads i w found

theorem dirty_bool_is_not_supported_preparation : decodeMemoryMember mixedPlacement mixedEntries .bool 2 = none := rfl

theorem invalid_pointer_is_not_supported_preparation : decodeMemoryFields mixedPlacement mixedEntries (mixedLayout.fields mixedName)
    (wordListView [0, highestUint, 129, 384, 1152] mixedPhysical 896) 896 = none := by
  let m := wordListView [0, highestUint, 129, 384, 1152] mixedPhysical 896
  have h0 : mload m 896 = 0 := wordList_read _ _ _ 0 _ rfl
  have h1 : mload m 928 = highestUint := wordList_read _ _ _ 1 _ rfl
  have h2 : mload m 960 = 129 := wordList_read _ _ _ 2 _ rfl
  change decodeMemoryFields mixedPlacement mixedEntries mixedTypes m 896 = none
  simp only [mixedTypes, decodeMemoryFields, h0, h1, h2]
  rfl

theorem missing_owned_candidates : decodeMemoryFields mixedPlacement [] (mixedLayout.fields mixedName) allChangedPhysical 896 = none := by
  have h0 : mload allChangedPhysical 896 = 0 := wordList_read _ _ _ 0 _ rfl
  have h1 : mload allChangedPhysical 928 = highestUint := wordList_read _ _ _ 1 _ rfl
  have h2 : mload allChangedPhysical 960 = 384 := wordList_read _ _ _ 2 _ rfl
  change decodeMemoryFields mixedPlacement [] mixedTypes allChangedPhysical 896 = none
  simp only [mixedTypes, decodeMemoryFields, h0, h1, h2]
  rfl

theorem actual_source_error_preserved : structStateWriteback mixedState mixedPlacement mixedEntries 0 mixedName
    (wordListView allChangedWords mixedPhysical 128) = some (.error (.stuck "memory write type"), mixedState) := by
  unfold structStateWriteback
  change (decodeMemoryFields mixedPlacement mixedEntries (mixedLayout.fields mixedName) (wordListView allChangedWords mixedPhysical 128) 128).map _ = _
  rw [decodeMemoryFields_encode mixedPlacement mixedEntries mixed_coverage all_changed_fields_encoded mixed_member_support]
  rfl

theorem aggregate_unchanged_whole_state : structStateWriteback mixedState mixedPlacement mixedEntries 3 mixedName mixedPhysical = some (.ok (), mixedState) := by
  apply structStateWriteback_unchanged mixedState mixedPlacement mixedEntries mixed_coverage 3 mixedName mixedFields rfl mixedStructWords mixed_original_fields mixed_member_support
  exact mixed_all_reads mixedEntry3 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

def aggregateChildHeap := allChangedHeap.write 1 (.string [0xab, 0x61]) (by rfl)
def aggregateChildState := withSourceHeap allChangedState aggregateChildHeap

theorem aggregate_shared_child_MemOK (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H mixedState) : Source.MemOK mixedEnv H aggregateChildState :=
  heapByte_write_MemOK mixedEnv H allChangedState 1 true [0xab, 0x61] rfl (all_changed_MemOK H ok)

theorem aggregate_shared_child_aliases (horizon : Nat) :
    (readMixedMemberBytes 2 horizon).run aggregateChildState = (.ok [0xab, 0x61], aggregateChildState) ∧
    (readMixedMemberBytes 3 horizon).run aggregateChildState = (.ok [0xab, 0x61], aggregateChildState) ∧
    aggregateChildHeap.get 0 = mixedHeap.get 0 ∧ aggregateChildHeap.get 4 = mixedHeap.get 4 := ⟨rfl, rfl, rfl, rfl⟩

end Solidity.Yul.Views.Controls
