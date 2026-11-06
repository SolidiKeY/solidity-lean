import Solidity.Yul.Views.HeapByteResizeComposition
import Solidity.Yul.Views.HeapByteBoundaries

/-! Actual size-changing heaps/states/aliases. Fixed-length mismatch controls are
retained. Historical capacity after shrink is not inferred from the new shape. -/
namespace Solidity.Yul.Views.Controls

def growBytes : List UInt8 := [0x11, 0x22, 0x33, 0xa5]
def growPhysical := mstore bytePhysical 128 4
def growHeap := byteHeap.write 0 (Source.Data.bytes growBytes) (by rfl)
def shrinkPhysical := mstore bytePhysical 128 1
def shrinkHeap := byteHeap.write 0 (Source.Data.bytes [0x11]) (by rfl)
def emptyPhysical := mstore bytePhysical 128 0
def emptyHeap := byteHeap.write 0 (Source.Data.bytes []) (by rfl)

theorem raw_grow_result : heapByteResizeWriteback byteHeap (bytePlacement 0) 0 false byteOld rfl growPhysical = some growHeap := by
  simp only [heapByteResizeWriteback, growPhysical, show (bytePlacement 0).address 0 = 128 from rfl, mload_mstore]
  rw [if_pos (by decide), decodeHeapByte_data, mload_mstore]
  have bytes : readBytes (mstore bytePhysical 128 4) 160 4 = growBytes := by decide
  simp only [show (4 : Roadmap.Word).val = 4 by decide, show (128 + 32 : Nat) = 160 from rfl]
  rw [bytes]
  rfl

theorem raw_shrink_result : heapByteResizeWriteback byteHeap (bytePlacement 0) 0 false byteOld rfl shrinkPhysical = some shrinkHeap := by
  simp only [heapByteResizeWriteback, shrinkPhysical, show (bytePlacement 0).address 0 = 128 from rfl, mload_mstore]
  rw [if_pos (by decide), decodeHeapByte_data, mload_mstore]
  rfl

theorem raw_empty_result : heapByteResizeWriteback byteHeap (bytePlacement 0) 0 false byteOld rfl emptyPhysical = some emptyHeap := by
  simp only [heapByteResizeWriteback, emptyPhysical, show (bytePlacement 0).address 0 = 128 from rfl, mload_mstore]
  rw [if_pos (by decide), decodeHeapByte_data, mload_mstore]
  rfl

theorem fixed_guard_still_rejects_grow : heapByteWriteback byteHeap (bytePlacement 0) 0 false byteOld rfl growPhysical = none := rfl

def growPlacement : Placement growHeap := heapResizePlacement byteHeap (bytePlacement 0) 0
  (.bytes growBytes) (by rfl) (.bytes 4) (.bytes _) (by decide)
def emptyPlacement : Placement emptyHeap := heapResizePlacement byteHeap (bytePlacement 0) 0
  (.bytes []) (by rfl) (.bytes 0) (.bytes _) (by decide)

theorem actual_grow_placement : growPlacement.address 0 = 128 ∧ growPlacement.free.val = 512 ∧
    growPlacement.shape 0 = .bytes 4 ∧ growPlacement.shape 1 = .bytes 33 := ⟨rfl, rfl, rfl, rfl⟩

theorem actual_empty_placement : emptyPlacement.address 0 = 128 ∧ emptyPlacement.free.val = 512 ∧ emptyPlacement.shape 0 = .bytes 0 := ⟨rfl, rfl, rfl⟩

theorem shrink_keeps_old_live_tail : shrinkPhysical 161 = 0x22 ∧ shrinkPhysical 162 = 0x33 ∧ shrinkPhysical 163 = 0xa5 ∧
    emptyPhysical 160 = 0x11 ∧ emptyPhysical 161 = 0x22 ∧ emptyPhysical 162 = 0x33 := by decide

theorem grow_shrink_types_other_next : growHeap.get 1 = byteHeap.get 1 ∧ growHeap.next = byteHeap.next ∧
    growHeap.ty = byteHeap.ty ∧ emptyHeap.get 2 = byteHeap.get 2 := by
  exact ⟨rfl, rfl, (heapByteResize_types_next byteHeap (bytePlacement 0) 0 false byteOld rfl growPhysical growHeap raw_grow_result).1, rfl⟩

def growState := withSourceHeap byteState growHeap
def shrinkState := withSourceHeap byteState shrinkHeap
def emptyState := withSourceHeap byteState emptyHeap

theorem grow_state_result : heapByteResizeStateWriteback byteState (bytePlacement 0) 0 false byteOld rfl growPhysical = some growState := by
  change (heapByteResizeWriteback byteHeap (bytePlacement 0) 0 false byteOld rfl growPhysical).map (withSourceHeap byteState) = some growState
  rw [raw_grow_result]
  rfl

theorem shrink_state_result : heapByteResizeStateWriteback byteState (bytePlacement 0) 0 false byteOld rfl shrinkPhysical = some shrinkState := by
  change (heapByteResizeWriteback byteHeap (bytePlacement 0) 0 false byteOld rfl shrinkPhysical).map (withSourceHeap byteState) = some shrinkState
  rw [raw_shrink_result]
  rfl

theorem empty_state_result : heapByteResizeStateWriteback byteState (bytePlacement 0) 0 false byteOld rfl emptyPhysical = some emptyState := by
  change (heapByteResizeWriteback byteHeap (bytePlacement 0) 0 false byteOld rfl emptyPhysical).map (withSourceHeap byteState) = some emptyState
  rw [raw_empty_result]
  rfl

theorem actual_resize_MemOK : Source.MemOK heapByteEnv byteHeap.ty growState ∧
    Source.MemOK heapByteEnv byteHeap.ty shrinkState ∧ Source.MemOK heapByteEnv byteHeap.ty emptyState :=
  ⟨heapByteResizeState_MemOK heapByteEnv byteHeap.ty byteState growState (bytePlacement 0) 0 false byteOld rfl growPhysical grow_state_result actual_initial_MemOK,
    heapByteResizeState_MemOK heapByteEnv byteHeap.ty byteState shrinkState (bytePlacement 0) 0 false byteOld rfl shrinkPhysical shrink_state_result actual_initial_MemOK,
    heapByteResizeState_MemOK heapByteEnv byteHeap.ty byteState emptyState (bytePlacement 0) 0 false byteOld rfl emptyPhysical empty_state_result actual_initial_MemOK⟩

theorem both_aliases_grow_read (n : Nat) :
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame n (.val (growState.1.get (.here)))).run growState = (.ok growBytes, growState) ∧
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame n (.val (growState.1.get (.there .here)))).run growState = (.ok growBytes, growState) ∧
    growBytes.length = 4 := ⟨rfl, rfl, rfl⟩

theorem both_aliases_empty_read (n : Nat) :
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame n (.val (emptyState.1.get (.here)))).run emptyState = (.ok [], emptyState) ∧
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame n (.val (emptyState.1.get (.there .here)))).run emptyState = (.ok [], emptyState) := ⟨rfl, rfl⟩

theorem both_aliases_shrink_read (n : Nat) :
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame n (.val (shrinkState.1.get (.here)))).run shrinkState = (.ok [0x11], shrinkState) ∧
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame n (.val (shrinkState.1.get (.there .here)))).run shrinkState = (.ok [0x11], shrinkState) := ⟨rfl, rfl⟩

theorem resize_initial_reserved : ReservedOK bytePhysical 512 := by
  apply bytesObject_reserved _ _ _ 128 _ (by decide)
  apply bytesObject_reserved _ _ _ 256 _ (by decide)
  exact bytesObject_reserved _ _ _ 384 _ (by decide) reserved_before

theorem raw_resize_reserved : ReservedOK growPhysical 512 ∧ ReservedOK shrinkPhysical 512 ∧ ReservedOK emptyPhysical 512 :=
  ⟨mstore_object_header_reserved bytePhysical 128 4 512 (by decide) resize_initial_reserved,
    mstore_object_header_reserved bytePhysical 128 1 512 (by decide) resize_initial_reserved,
    mstore_object_header_reserved bytePhysical 128 0 512 (by decide) resize_initial_reserved⟩

def resizedString : List UInt8 := 0xff :: List.replicate 31 0x62
def resizedStringPhysical := bytesObjectView resizedString (by decide) bytePhysical 256
def resizedStringHeap := byteHeap.write 1 (Source.Data.string resizedString) (by rfl)
def stringAliasState : Source.EMState heapByteEnv [.bytes .memory, .string .memory] :=
  ⟨.cons (.memRef rfl 1) (.cons (.memRef rfl 1) .nil), byteState.2⟩
def resizedStringState := withSourceHeap stringAliasState resizedStringHeap

theorem string_alias_initial_MemOK : Source.MemOK heapByteEnv byteHeap.ty stringAliasState := by
  refine ⟨⟨actual_initial_MemOK.1.1, ?_⟩, actual_initial_MemOK.2⟩
  exact ⟨⟨.string .memory, rfl, rfl⟩, ⟨⟨.string .memory, rfl, rfl⟩, trivial⟩⟩

theorem string_resize_result : heapByteResizeWriteback byteHeap (bytePlacement 0) 1 true stringOld rfl resizedStringPhysical = some resizedStringHeap :=
  heapByteResize_encode byteHeap (bytePlacement 0) 1 true stringOld resizedString rfl (by decide) (by decide) bytePhysical

theorem string_resize_state_result : heapByteResizeStateWriteback stringAliasState (bytePlacement 0) 1 true stringOld rfl resizedStringPhysical = some resizedStringState := by
  change (heapByteResizeWriteback byteHeap (bytePlacement 0) 1 true stringOld rfl resizedStringPhysical).map (withSourceHeap stringAliasState) = some resizedStringState
  rw [string_resize_result]
  rfl

theorem resized_string_MemOK : Source.MemOK heapByteEnv byteHeap.ty resizedStringState :=
  heapByteResizeState_MemOK heapByteEnv byteHeap.ty stringAliasState resizedStringState (bytePlacement 0) 1 true stringOld rfl resizedStringPhysical string_resize_state_result string_alias_initial_MemOK

theorem both_string_alias_reads (n : Nat) :
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame n (.val (resizedStringState.1.get (.here)))).run resizedStringState = (.ok resizedString, resizedStringState) ∧
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame n (.val (resizedStringState.1.get (.there .here)))).run resizedStringState = (.ok resizedString, resizedStringState) ∧
    resizedString.length = 32 ∧ resizedStringPhysical 320 = 0x61 ∧ resizedStringPhysical 321 = 0xa5 := by
  exact ⟨rfl, rfl, rfl, by decide, by decide⟩

def resizedStringPlacement : Placement resizedStringHeap := heapResizePlacement byteHeap (bytePlacement 0) 1
  (.string resizedString) (by rfl) (.bytes 32) (.string _) (by decide)
def combinedResizeHeap := growHeap.write 1 (Source.Data.string resizedString) (by rfl)
def combinedResizePhysical := bytesObjectView resizedString (by decide) growPhysical 256
def reverseResizePhysical := bytesObjectView growBytes (by decide) resizedStringPhysical 128

theorem combined_resize_result : heapByteResizeWriteback growHeap growPlacement 1 true stringOld rfl combinedResizePhysical = some combinedResizeHeap :=
  heapByteResize_encode growHeap growPlacement 1 true stringOld resizedString rfl (by decide) (by decide) growPhysical

theorem combined_resize_reverse : combinedResizeHeap = resizedStringHeap.write 0 (.bytes growBytes) (by rfl) :=
  heap_writes_commute byteHeap 0 1 (.bytes growBytes) (.string resizedString) rfl rfl (by decide)

theorem reverse_resize_result : heapByteResizeWriteback resizedStringHeap resizedStringPlacement 0 false byteOld rfl reverseResizePhysical = some combinedResizeHeap := by
  rw [combined_resize_reverse]
  exact heapByteResize_encode resizedStringHeap resizedStringPlacement 0 false byteOld growBytes rfl (by decide) (by decide) resizedStringPhysical

def combinedResizeState := withSourceHeap byteState combinedResizeHeap

theorem combined_resize_state_result : heapByteResizeStateWriteback growState growPlacement 1 true stringOld rfl combinedResizePhysical = some combinedResizeState := by
  change (heapByteResizeWriteback growHeap growPlacement 1 true stringOld rfl combinedResizePhysical).map (withSourceHeap growState) = some combinedResizeState
  rw [combined_resize_result]
  rfl

theorem combined_resize_MemOK : Source.MemOK heapByteEnv byteHeap.ty combinedResizeState :=
  heapByteResizeState_MemOK heapByteEnv byteHeap.ty growState combinedResizeState growPlacement 1 true stringOld rfl combinedResizePhysical
    combined_resize_state_result actual_resize_MemOK.1

theorem historical_capacity_not_recovered : heapByteResizeWriteback emptyHeap emptyPlacement 0 false [] rfl
    (mstore emptyPhysical 128 4) = none := by
  apply heapByteResize_over_capacity
  change ¬(MemoryShape.bytes (mload (mstore emptyPhysical 128 4) 128).val).size ≤ (MemoryShape.bytes 0).size
  rw [mload_mstore]
  decide

#print axioms raw_grow_result
#print axioms actual_resize_MemOK
#print axioms both_string_alias_reads
end Solidity.Yul.Views.Controls
