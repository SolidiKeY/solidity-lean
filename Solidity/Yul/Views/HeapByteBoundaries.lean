import Solidity.Yul.Views.HeapByteStateControls

/-! Finite witnesses, NOT a decoder size cap. Ordinary empty,31/32/33-byte
objects use actual allocation and valid placement; unsupported header changes
remain an explicit open integration case, never a Yul refusal/no-op. -/
namespace Solidity.Yul.Views.Controls

def boundaryBytes (n : Fin 34) : List UInt8 := List.replicate n.val 0x11
def boundaryHeap (n : Fin 34) : Source.Heap heapByteEnv.layout :=
  (Source.Heap.empty.alloc ⟨.bytes .memory, .bytes (boundaryBytes n)⟩).1

theorem boundary_present_zero (n : Fin 34) (a : Nat) (h : ((boundaryHeap n).cells a).isSome) : a = 0 := by
  by_cases he : a = 0
  · exact he
  · simp only [boundaryHeap, Source.Heap.alloc, Source.Heap.empty, if_neg he,
      Option.isSome_none, Bool.false_eq_true] at h

def boundaryPlacement (n : Fin 34) : Placement (boundaryHeap n) where
  address _ := 128
  shape _ := .bytes n.val
  free := ⟨128 + (MemoryShape.bytes n.val).size, by
    change 128 + (32 + (n.val + 31) / 32 * 32) < 2 ^ 256
    have hn := n.isLt
    omega⟩
  free_start := by change 128 ≤ 128 + (MemoryShape.bytes n.val).size; omega
  distinct a b ha hb _ := (boundary_present_zero n a ha).trans (boundary_present_zero n b hb).symm
  typed a τ d h := by
    by_cases he : a = 0
    · subst a
      change some (⟨.bytes .memory, .bytes (boundaryBytes n)⟩ : Σ σ, Source.Data heapByteEnv.layout σ) = some ⟨τ, d⟩ at h
      cases h
      have hs := HasMemoryShape.bytes (D := heapByteEnv.layout) (l := .memory) (boundaryBytes n)
      simpa only [boundaryBytes, List.length_replicate] using hs
    · simp only [boundaryHeap, Source.Heap.alloc, Source.Heap.empty, if_neg he] at h
      cases h
  starts _ _ := by decide
  ends _ _ := Nat.le_refl _
  separate a b ha hb hn := False.elim (hn ((boundary_present_zero n a ha).trans (boundary_present_zero n b hb).symm))

def boundaryResidual (n : Fin 34) : ByteView := mstore (mstore (fun _ => 0xa5) 64 (boundaryPlacement n).free) 96 0

def boundaryPhysical (n : Fin 34) := bytesObjectView (boundaryBytes n)
  (by simp only [boundaryBytes, List.length_replicate]; have hn := n.isLt; omega) (boundaryResidual n) 128
def boundaryChanged (n : Fin 34) := bytesObjectView (List.replicate n.val 0xff)
  (by rw [List.length_replicate]; have hn := n.isLt; omega) (boundaryPhysical n) 128

theorem boundary_whole_unchanged (n : Fin 34) : heapByteWriteback (boundaryHeap n) (boundaryPlacement n)
    0 false (boundaryBytes n) rfl (boundaryPhysical n) = some (boundaryHeap n) :=
  heapByteWriteback_unchanged _ _ _ _ _ rfl (boundaryPhysical n)
    (congrArg Fin.val (bytesObject_header _ _ _ 128)) (bytesObject_payload_list _ _ _ 128)

theorem boundary_changed_result (n : Fin 34) : heapByteWriteback (boundaryHeap n) (boundaryPlacement n)
    0 false (boundaryBytes n) rfl (boundaryChanged n) =
    some ((boundaryHeap n).write 0 (.bytes (List.replicate n.val 0xff)) (by rfl)) :=
  heapByteWriteback_encode _ _ _ _ _ _ rfl (by rw [List.length_replicate]; have hn := n.isLt; omega)
    (by simp only [boundaryBytes, List.length_replicate]) (boundaryPhysical n)

theorem empty_is_allocated : (boundaryHeap 0).get 0 = some ⟨.bytes .memory, .bytes []⟩ ∧
    (boundaryPlacement 0).address 0 = 128 ∧ (boundaryPlacement 0).free.val = 160 ∧
    (boundaryHeap 0).next = 1 := ⟨rfl, rfl, rfl, rfl⟩

theorem boundary_exact_free : (boundaryPlacement 31).free.val = 192 ∧
    (boundaryPlacement 32).free.val = 192 ∧ (boundaryPlacement 33).free.val = 224 := ⟨rfl, rfl, rfl⟩

theorem boundary_payload_padding : boundaryChanged 31 190 = 0xff ∧ boundaryChanged 31 191 = 0xa5 ∧
    boundaryChanged 32 191 = 0xff ∧ boundaryChanged 32 192 = 0xa5 ∧
    boundaryChanged 33 192 = 0xff ∧ boundaryChanged 33 193 = 0xa5 := by decide

theorem header_change_even_same_extent_is_open : heapByteWriteback (boundaryHeap 31) (boundaryPlacement 31)
    0 false (boundaryBytes 31) rfl (mstore (boundaryPhysical 31) 128 32) = none := by
  apply heapByteWriteback_bad_header
  change (mload (mstore (boundaryPhysical 31) 128 32) 128).val ≠ 31
  rw [mload_mstore]
  decide

#print axioms boundary_whole_unchanged
#print axioms boundary_changed_result
#print axioms boundary_payload_padding
end Solidity.Yul.Views.Controls
