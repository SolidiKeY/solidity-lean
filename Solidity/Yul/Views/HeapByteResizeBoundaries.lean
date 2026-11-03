import Solidity.Yul.Views.HeapByteResizeControls

/-! Finite boundary witnesses, not model caps. All changes use actual input
Placement footprints; shrink leaves formerly live tails in physical residual. -/
namespace Solidity.Yul.Views.Controls

def resizeBoundaryState (n : Fin 34) := withSourceHeap byteState (boundaryHeap n)
def resizeBoundaryHeap (n : Fin 34) (bs : List UInt8) := (boundaryHeap n).write 0 (Source.Data.bytes bs) (by rfl)
def resizeBoundaryAfter (n : Fin 34) (bs : List UInt8) := withSourceHeap (resizeBoundaryState n) (resizeBoundaryHeap n bs)
def resizeBoundaryPhysical (n : Fin 34) (bs : List UInt8) (hl : bs.length < 2 ^ 256) := bytesObjectView bs hl (boundaryPhysical n) 128

theorem resizeBoundary_initial_MemOK (n : Fin 34) : Source.MemOK heapByteEnv (boundaryHeap n).ty (resizeBoundaryState n) := by
  have heap : Source.HeapOK (E := heapByteEnv) (boundaryHeap n) := Source.HeapOK.alloc Source.HeapOK.empty (.bytes (boundaryBytes n))
  have top : Source.HeapShaped (E := heapByteEnv) (boundaryHeap n) :=
    Source.HeapShaped.alloc (E := heapByteEnv) (x := ⟨.bytes .memory, .bytes (boundaryBytes n)⟩) Source.HeapShaped.empty trivial
  have inner : Source.HeapInner (E := heapByteEnv) (boundaryHeap n) :=
    Source.HeapInner.alloc (E := heapByteEnv) (x := ⟨.bytes .memory, .bytes (boundaryBytes n)⟩) Source.HeapInner.empty trivial
  refine ⟨⟨⟨heap, Source.HeapTy.Le.refl _⟩, ?_⟩, top, inner⟩
  exact ⟨⟨.bytes .memory, rfl, rfl⟩, ⟨⟨.bytes .memory, rfl, rfl⟩, trivial⟩⟩

theorem resizeBoundary_heap_result (n : Fin 34) (bs : List UInt8) (hl : bs.length < 2 ^ 256)
    (capacity : (MemoryShape.bytes bs.length).size ≤ (MemoryShape.bytes n.val).size) :
    heapByteResizeWriteback (boundaryHeap n) (boundaryPlacement n) 0 false (boundaryBytes n) rfl (resizeBoundaryPhysical n bs hl) = some (resizeBoundaryHeap n bs) :=
  heapByteResize_encode _ _ _ _ _ _ rfl hl capacity (boundaryPhysical n)

theorem resizeBoundary_state_result (n : Fin 34) (bs : List UInt8) (hl : bs.length < 2 ^ 256)
    (capacity : (MemoryShape.bytes bs.length).size ≤ (MemoryShape.bytes n.val).size) :
    heapByteResizeStateWriteback (resizeBoundaryState n) (boundaryPlacement n) 0 false (boundaryBytes n) rfl (resizeBoundaryPhysical n bs hl) = some (resizeBoundaryAfter n bs) := by
  change (heapByteResizeWriteback (boundaryHeap n) (boundaryPlacement n) 0 false (boundaryBytes n) rfl _).map (withSourceHeap (resizeBoundaryState n)) = some _
  rw [resizeBoundary_heap_result n bs hl capacity]
  rfl

theorem resizeBoundary_after_MemOK (n : Fin 34) (bs : List UInt8) (hl : bs.length < 2 ^ 256)
    (capacity : (MemoryShape.bytes bs.length).size ≤ (MemoryShape.bytes n.val).size) :
    Source.MemOK heapByteEnv (boundaryHeap n).ty (resizeBoundaryAfter n bs) :=
  heapByteResizeState_MemOK heapByteEnv (boundaryHeap n).ty (resizeBoundaryState n) (resizeBoundaryAfter n bs) (boundaryPlacement n)
    0 false (boundaryBytes n) rfl (resizeBoundaryPhysical n bs hl) (resizeBoundary_state_result n bs hl capacity) (resizeBoundary_initial_MemOK n)

theorem resizeBoundary_alias_reads (n : Fin 34) (bs : List UInt8) (horizon : Nat) :
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame horizon (.val ((resizeBoundaryAfter n bs).1.get (.here)))).run (resizeBoundaryAfter n bs) = (.ok bs, resizeBoundaryAfter n bs) ∧
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame horizon (.val ((resizeBoundaryAfter n bs).1.get (.there .here)))).run (resizeBoundaryAfter n bs) = (.ok bs, resizeBoundaryAfter n bs) := ⟨rfl, rfl⟩

def grow31Bytes : List UInt8 := List.replicate 31 0x11 ++ [0xa5]
def grow31Physical := mstore (boundaryPhysical 31) 128 32

theorem raw_31to32_result : heapByteResizeWriteback (boundaryHeap 31) (boundaryPlacement 31) 0 false (boundaryBytes 31) rfl grow31Physical = some (resizeBoundaryHeap 31 grow31Bytes) := by
  simp only [heapByteResizeWriteback, grow31Physical, show (boundaryPlacement 31).address 0 = 128 from rfl, mload_mstore]
  rw [if_pos (by decide), decodeHeapByte_data, mload_mstore]
  simp only [show (32 : Roadmap.Word).val = 32 by decide, show (128 + 32 : Nat) = 160 from rfl]
  have payload : readBytes (mstore (boundaryPhysical 31) 128 32) 160 32 = grow31Bytes := by decide
  rw [payload]
  rfl

theorem shrink33to32_result : heapByteResizeWriteback (boundaryHeap 33) (boundaryPlacement 33) 0 false (boundaryBytes 33) rfl
    (resizeBoundaryPhysical 33 (List.replicate 32 0xff) (by decide)) = some (resizeBoundaryHeap 33 (List.replicate 32 0xff)) :=
  resizeBoundary_heap_result 33 _ (by decide) (by decide)

theorem grow33to64_result : heapByteResizeWriteback (boundaryHeap 33) (boundaryPlacement 33) 0 false (boundaryBytes 33) rfl
    (resizeBoundaryPhysical 33 (List.replicate 64 0xff) (by decide)) = some (resizeBoundaryHeap 33 (List.replicate 64 0xff)) :=
  resizeBoundary_heap_result 33 _ (by decide) (by decide)

theorem resize_over_capacity_None : heapByteResizeWriteback (boundaryHeap 32) (boundaryPlacement 32) 0 false (boundaryBytes 32) rfl
    (mstore (boundaryPhysical 32) 128 33) = none := by
  apply heapByteResize_over_capacity
  change ¬(MemoryShape.bytes (mload (mstore (boundaryPhysical 32) 128 33) 128).val).size ≤ (MemoryShape.bytes 32).size
  rw [mload_mstore]
  decide

theorem shrink_padding_live_tail : resizeBoundaryPhysical 33 (List.replicate 32 0xff) (by decide) 192 = 0x11 ∧
    resizeBoundaryPhysical 33 (List.replicate 32 0xff) (by decide) 193 = 0xa5 ∧
    grow31Physical 191 = 0xa5 := by decide

theorem old_fixed_header_controls_retained : heapByteWriteback (boundaryHeap 31) (boundaryPlacement 31)
    0 false (boundaryBytes 31) rfl grow31Physical = none := header_change_even_same_extent_is_open

#print axioms raw_31to32_result
#print axioms resizeBoundary_after_MemOK
#print axioms grow33to64_result
end Solidity.Yul.Views.Controls
