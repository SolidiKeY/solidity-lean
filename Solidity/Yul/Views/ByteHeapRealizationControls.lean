import Solidity.Yul.Views.ByteHeapRealization
import Solidity.Yul.Views.RetainedByteControls

namespace Solidity.Yul.Views.Controls

def actualByteEntries : List (HeapByteEntry byteHeap) :=
  [⟨0, false, byteOld, rfl⟩, ⟨1, true, stringOld, rfl⟩, ⟨2, false, byteOther, rfl⟩]

theorem actual_entries_distinct : (actualByteEntries.map HeapByteEntry.id).Nodup := by decide

theorem actual_entries_cover : CoversByteHeap actualByteEntries := by
  intro a ha
  have bound := byteHeap_present_lt a ha
  have cases : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases cases with eq | eq | eq
  · subst a; exact ⟨⟨0, false, byteOld, rfl⟩, List.mem_cons_self, rfl⟩
  · subst a; exact ⟨⟨1, true, stringOld, rfl⟩, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
  · subst a; exact ⟨⟨2, false, byteOther, rfl⟩, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩

theorem actual_heap_constructed : encodeByteHeap (bytePlacement 0) actualByteEntries heapByteResidual = bytePhysical := rfl

theorem actual_heap_reads : ∀ e ∈ actualByteEntries, e.Reads (bytePlacement 0) bytePhysical := by
  rw [← actual_heap_constructed]
  exact encodeByteHeap_reads _ _ actual_entries_distinct _

theorem actual_heap_realizes : ReservedOK bytePhysical (bytePlacement 0).free ∧
    ∀ a, (byteHeap.cells a).isSome → ∃ e ∈ actualByteEntries, e.id = a ∧ e.Reads (bytePlacement 0) bytePhysical := by
  rw [← actual_heap_constructed]
  exact encodeByteHeap_realizes _ _ actual_entries_distinct actual_entries_cover _ reserved_before

theorem actual_heap_unchanged : encodeByteHeap (bytePlacement 0) actualByteEntries bytePhysical = bytePhysical :=
  encodeByteHeap_unchanged _ _ _ actual_heap_reads

theorem actual_heap_residual_padding : bytePhysical 191 = 0xa5 ∧ bytePhysical 200 = 0xa5 ∧
    bytePhysical 321 = 0xa5 ∧ bytePhysical 419 = 0xa5 := by decide

def missingStringEntries : List (HeapByteEntry byteHeap) :=
  [⟨0, false, byteOld, rfl⟩, ⟨2, false, byteOther, rfl⟩]

theorem missing_entry_not_coverage : ¬ CoversByteHeap missingStringEntries := by
  intro coverage
  obtain ⟨e, member, same⟩ := coverage 1 (by rfl)
  have ids : e.id ∈ [0, 2] := List.mem_map.mpr ⟨e, member, rfl⟩
  rw [same] at ids
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ids
  omega

theorem wrong_entry_type_impossible : ¬ ∃ e : HeapByteEntry byteHeap, e.id = 1 ∧ e.string = false := by
  rintro ⟨e, id, string⟩
  have found := e.found
  rw [id, string] at found
  change some (⟨.string .memory, Source.Data.string stringOld⟩ : Σ τ, Source.Data heapByteEnv.layout τ) =
    some ⟨.bytes .memory, Source.Data.bytes e.bytes⟩ at found
  have types := congrArg (fun x => x.map Sigma.fst) found
  cases types

def realizedRetainedPlacement : Placement retainedBothHeap := retainedWritePlacement (bytePlacement 0) retainedBothAPlacement
  retainedBothA 1 (.string retainedString64Bytes) (by rfl) (.bytes 64) (.string _) (by decide)
def realizedRetainedHistory : RetainedAllocation (bytePlacement 0) realizedRetainedPlacement :=
  retainWritten _ _ retainedBothA 1 (.string retainedString64Bytes) (by rfl) (.bytes 64) (.string _) (by decide)
def realizedRetainedEntries : List (HeapByteEntry retainedBothHeap) :=
  [⟨0, false, growBytes, rfl⟩, ⟨1, true, retainedString64Bytes, rfl⟩, ⟨2, false, byteOther, rfl⟩]
def realizedRetainedPhysical := encodeByteHeap realizedRetainedPlacement realizedRetainedEntries bytePhysical

theorem realized_retained_distinct : (realizedRetainedEntries.map HeapByteEntry.id).Nodup := by decide

theorem realized_retained_coverage : CoversByteHeap realizedRetainedEntries := by
  intro a ha
  have old : (byteHeap.cells a).isSome := by rw [realizedRetainedHistory.occupancy a] at ha; exact ha
  have bound := byteHeap_present_lt a old
  have cases : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases cases with eq | eq | eq
  · subst a; exact ⟨⟨0, false, growBytes, rfl⟩, List.mem_cons_self, rfl⟩
  · subst a; exact ⟨⟨1, true, retainedString64Bytes, rfl⟩, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
  · subst a; exact ⟨⟨2, false, byteOther, rfl⟩, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩

theorem realized_retained_reads : ∀ e ∈ realizedRetainedEntries, e.Reads realizedRetainedPlacement realizedRetainedPhysical :=
  encodeByteHeap_reads _ _ realized_retained_distinct _

theorem realized_retained_reserved : ReservedOK realizedRetainedPhysical 512 :=
  encodeByteHeap_reserved _ _ _ resize_initial_reserved

theorem realized_retained_unchanged : encodeByteHeap realizedRetainedPlacement realizedRetainedEntries realizedRetainedPhysical = realizedRetainedPhysical :=
  encodeByteHeap_unchanged _ _ _ realized_retained_reads

theorem realized_retained_padding : realizedRetainedPhysical 191 = 0xa5 ∧ realizedRetainedPhysical 200 = 0xa5 ∧
    realizedRetainedPhysical 384 = 0 ∧ realizedRetainedPhysical 419 = 0xa5 := by decide

/-- A source-model representability control, not a new refusal or exclusion.
MemOK alone does not promise ordinary EVM-sized placement capacity. -/
def oversizedBytes : List UInt8 := List.replicate (2 ^ 256) 0
def oversizedHeap : Source.Heap heapByteEnv.layout :=
  (Source.Heap.empty.alloc ⟨.bytes .memory, .bytes oversizedBytes⟩).1
def oversizedState := withSourceHeap byteState oversizedHeap

theorem oversized_actual_MemOK : Source.MemOK heapByteEnv oversizedHeap.ty oversizedState := by
  have heap : Source.HeapOK (E := heapByteEnv) oversizedHeap := Source.HeapOK.alloc Source.HeapOK.empty (.bytes oversizedBytes)
  have top : Source.HeapShaped (E := heapByteEnv) oversizedHeap :=
    Source.HeapShaped.alloc (E := heapByteEnv) (x := ⟨.bytes .memory, .bytes oversizedBytes⟩) Source.HeapShaped.empty trivial
  have inner : Source.HeapInner (E := heapByteEnv) oversizedHeap :=
    Source.HeapInner.alloc (E := heapByteEnv) (x := ⟨.bytes .memory, .bytes oversizedBytes⟩) Source.HeapInner.empty trivial
  refine ⟨⟨⟨heap, Source.HeapTy.Le.refl _⟩, ?_⟩, top, inner⟩
  exact ⟨⟨.bytes .memory, rfl, rfl⟩, ⟨⟨.bytes .memory, rfl, rfl⟩, trivial⟩⟩

theorem oversized_no_ordinary_placement : ¬ Nonempty (Placement oversizedHeap) := by
  rintro ⟨p⟩
  have bound := heapByte_length_bound oversizedHeap p 0 false oversizedBytes (by rfl)
  simp only [oversizedBytes, List.length_replicate, Nat.lt_irrefl] at bound

#print axioms oversized_actual_MemOK
#print axioms oversized_no_ordinary_placement
#print axioms actual_heap_constructed
#print axioms actual_heap_realizes
#print axioms actual_heap_unchanged
end Solidity.Yul.Views.Controls
