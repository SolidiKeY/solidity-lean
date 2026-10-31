import Solidity.Yul.Views.RetainedAllocation
import Solidity.Yul.Views.HeapByteResizeBoundaries

/-! Real original64/96-byte allocations survive shrink. The finite controls
instantiate unbounded universal operations; no length/fuel cap is added. -/
namespace Solidity.Yul.Views.Controls

def retainedInitial : RetainedAllocation (bytePlacement 0) (bytePlacement 0) := retainInitial _ _
def retainedEmptyPlacement : Placement emptyHeap := retainedWritePlacement (bytePlacement 0) (bytePlacement 0)
  retainedInitial 0 (.bytes []) (by rfl) (.bytes 0) (.bytes _) (by decide)
def retainedEmpty : RetainedAllocation (bytePlacement 0) retainedEmptyPlacement :=
  retainWritten _ _ retainedInitial 0 (.bytes []) (by rfl) (.bytes 0) (.bytes _) (by decide)

theorem retained_empty_result : retainedByteWriteback byteHeap (bytePlacement 0) (bytePlacement 0) retainedInitial
    0 false byteOld rfl emptyPhysical = some emptyHeap :=
  retainedByte_compat _ _ _ retainedInitial _ _ _ rfl _ _ raw_empty_result

def retainedRegrowPhysical := mstore emptyPhysical 128 4
def retainedRegrowHeap := emptyHeap.write 0 (.bytes growBytes) (by rfl)
def retainedRegrowPlacement : Placement retainedRegrowHeap := retainedWritePlacement (bytePlacement 0) retainedEmptyPlacement
  retainedEmpty 0 (.bytes growBytes) (by rfl) (.bytes 4) (.bytes _) (by decide)
def retainedRegrown : RetainedAllocation (bytePlacement 0) retainedRegrowPlacement :=
  retainWritten _ _ retainedEmpty 0 (.bytes growBytes) (by rfl) (.bytes 4) (.bytes _) (by decide)

theorem retained_3_zero_4 : retainedByteWriteback emptyHeap (bytePlacement 0) retainedEmptyPlacement retainedEmpty
    0 false [] rfl retainedRegrowPhysical = some retainedRegrowHeap := by
  simp only [retainedByteWriteback, retainedRegrowPhysical,
    show retainedEmptyPlacement.address 0 = 128 from rfl, mload_mstore]
  rw [if_pos (by decide), decodeHeapByte_data, mload_mstore]
  simp only [show (4 : Roadmap.Word).val = 4 by decide, show (128 + 32 : Nat) = 160 from rfl]
  have payload : readBytes (mstore emptyPhysical 128 4) 160 4 = growBytes := by decide
  rw [payload]
  rfl

theorem retained_choices_and_tail : retainedEmptyPlacement.shape 0 = .bytes 0 ∧
    retainedRegrowPlacement.shape 0 = .bytes 4 ∧ retainedRegrowPlacement.address = (bytePlacement 0).address ∧
    retainedRegrowPlacement.free = (bytePlacement 0).free ∧
    retainedRegrowPhysical 160 = 0x11 ∧ retainedRegrowPhysical 161 = 0x22 ∧
    retainedRegrowPhysical 162 = 0x33 ∧ retainedRegrowPhysical 163 = 0xa5 ∧
    retainedRegrowPhysical 191 = 0xa5 ∧ retainedRegrowPhysical 200 = 0xa5 := by
  exact ⟨rfl, rfl, rfl, rfl, by decide, by decide, by decide, by decide, by decide, by decide⟩

def retainedRegrowState := withSourceHeap emptyState retainedRegrowHeap

theorem retained_regrow_state_result : retainedByteStateWriteback emptyState (bytePlacement 0) retainedEmptyPlacement retainedEmpty
    0 false [] rfl retainedRegrowPhysical = some retainedRegrowState := by
  change (retainedByteWriteback emptyHeap _ _ _ _ _ _ rfl _).map (withSourceHeap emptyState) = some _
  rw [retained_3_zero_4]
  rfl

theorem retained_regrow_MemOK (H : Source.HeapTy) (ok : Source.MemOK heapByteEnv H emptyState) :
    Source.MemOK heapByteEnv H retainedRegrowState :=
  retainedByteState_MemOK heapByteEnv H _ _ _ _ retainedEmpty 0 false [] rfl _ retained_regrow_state_result ok

theorem retained_regrow_alias_reads (horizon : Nat) :
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame horizon (.val (retainedRegrowState.1.get (.here)))).run retainedRegrowState = (.ok growBytes, retainedRegrowState) ∧
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame horizon (.val (retainedRegrowState.1.get (.there .here)))).run retainedRegrowState = (.ok growBytes, retainedRegrowState) := ⟨rfl, rfl⟩

def retainedStringZeroHeap := byteHeap.write 1 (.string []) (by rfl)
def retainedStringZeroPlacement : Placement retainedStringZeroHeap := retainedWritePlacement (bytePlacement 0) (bytePlacement 0)
  retainedInitial 1 (.string []) (by rfl) (.bytes 0) (.string _) (by decide)
def retainedStringZero : RetainedAllocation (bytePlacement 0) retainedStringZeroPlacement :=
  retainWritten _ _ retainedInitial 1 (.string []) (by rfl) (.bytes 0) (.string _) (by decide)
def retainedStringZeroPhysical := mstore resizedStringPhysical 256 0
def retainedString64Physical := mstore retainedStringZeroPhysical 256 64
def retainedString64Bytes : List UInt8 := resizedString ++ [0x61] ++ List.replicate 31 0xa5
def retainedString64Heap := retainedStringZeroHeap.write 1 (.string retainedString64Bytes) (by rfl)
def retainedString64Placement : Placement retainedString64Heap := retainedWritePlacement (bytePlacement 0) retainedStringZeroPlacement
  retainedStringZero 1 (.string retainedString64Bytes) (by rfl) (.bytes 64) (.string _) (by decide)
def retainedString64 : RetainedAllocation (bytePlacement 0) retainedString64Placement :=
  retainWritten _ _ retainedStringZero 1 (.string retainedString64Bytes) (by rfl) (.bytes 64) (.string _) (by decide)

theorem retained_string_zero : retainedByteWriteback byteHeap (bytePlacement 0) (bytePlacement 0) retainedInitial
    1 true stringOld rfl retainedStringZeroPhysical = some retainedStringZeroHeap := by
  simp only [retainedByteWriteback, retainedStringZeroPhysical,
    show (bytePlacement 0).address 1 = 256 from rfl, mload_mstore]
  rw [if_pos (by decide), decodeHeapByte_data, mload_mstore]
  rfl

theorem retained_33_zero_64_string : retainedByteWriteback retainedStringZeroHeap (bytePlacement 0) retainedStringZeroPlacement retainedStringZero
    1 true [] rfl retainedString64Physical = some retainedString64Heap := by
  simp only [retainedByteWriteback, retainedString64Physical,
    show retainedStringZeroPlacement.address 1 = 256 from rfl, mload_mstore]
  rw [if_pos (by decide), decodeHeapByte_data, mload_mstore]
  simp only [show (64 : Roadmap.Word).val = 64 by decide, show (256 + 32 : Nat) = 288 from rfl]
  have payload : readBytes (mstore retainedStringZeroPhysical 256 64) 288 64 = retainedString64Bytes := by decide
  rw [payload]
  rfl

def retainedStringZeroState := withSourceHeap stringAliasState retainedStringZeroHeap
def retainedString64State := withSourceHeap retainedStringZeroState retainedString64Heap

theorem retained_string_zero_state : retainedByteStateWriteback stringAliasState (bytePlacement 0) (bytePlacement 0) retainedInitial
    1 true stringOld rfl retainedStringZeroPhysical = some retainedStringZeroState := by
  change (retainedByteWriteback byteHeap _ _ _ _ _ _ rfl _).map (withSourceHeap stringAliasState) = some _
  rw [retained_string_zero]
  rfl

theorem retained_string64_state : retainedByteStateWriteback retainedStringZeroState (bytePlacement 0) retainedStringZeroPlacement retainedStringZero
    1 true [] rfl retainedString64Physical = some retainedString64State := by
  change (retainedByteWriteback retainedStringZeroHeap _ _ _ _ _ _ rfl _).map (withSourceHeap retainedStringZeroState) = some _
  rw [retained_33_zero_64_string]
  rfl

theorem retained_string_MemOK : Source.MemOK heapByteEnv byteHeap.ty retainedString64State :=
  retainedByteState_MemOK heapByteEnv byteHeap.ty _ _ _ _ retainedStringZero 1 true [] rfl _ retained_string64_state
    (retainedByteState_MemOK heapByteEnv byteHeap.ty _ _ _ _ retainedInitial 1 true stringOld rfl _ retained_string_zero_state string_alias_initial_MemOK)

theorem retained_string_alias_reads (horizon : Nat) :
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame horizon (.val (retainedString64State.1.get (.here)))).run retainedString64State = (.ok retainedString64Bytes, retainedString64State) ∧
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame horizon (.val (retainedString64State.1.get (.there .here)))).run retainedString64State = (.ok retainedString64Bytes, retainedString64State) := ⟨rfl, rfl⟩

theorem retained_reserved : ReservedOK retainedRegrowPhysical 512 ∧ ReservedOK retainedString64Physical 512 := by
  constructor
  · exact mstore_object_header_reserved emptyPhysical 128 4 512 (by decide) raw_resize_reserved.2.2
  · apply mstore_object_header_reserved _ 256 64 512 (by decide)
    apply mstore_object_header_reserved _ 256 0 512 (by decide)
    exact bytesObject_reserved _ _ bytePhysical 256 512 (by decide) resize_initial_reserved

theorem retained_old_counter_unchanged : heapByteResizeWriteback emptyHeap emptyPlacement 0 false [] rfl
    (mstore emptyPhysical 128 4) = none := historical_capacity_not_recovered

def retainedBothZeroHeap := emptyHeap.write 1 (.string []) (by rfl)
def retainedBothZeroPlacement : Placement retainedBothZeroHeap := retainedWritePlacement (bytePlacement 0) retainedEmptyPlacement
  retainedEmpty 1 (.string []) (by rfl) (.bytes 0) (.string _) (by decide)
def retainedBothZero : RetainedAllocation (bytePlacement 0) retainedBothZeroPlacement :=
  retainWritten _ _ retainedEmpty 1 (.string []) (by rfl) (.bytes 0) (.string _) (by decide)
def retainedBothAHeap := retainedBothZeroHeap.write 0 (.bytes growBytes) (by rfl)
def retainedBothAPlacement : Placement retainedBothAHeap := retainedWritePlacement (bytePlacement 0) retainedBothZeroPlacement
  retainedBothZero 0 (.bytes growBytes) (by rfl) (.bytes 4) (.bytes _) (by decide)
def retainedBothA : RetainedAllocation (bytePlacement 0) retainedBothAPlacement :=
  retainWritten _ _ retainedBothZero 0 (.bytes growBytes) (by rfl) (.bytes 4) (.bytes _) (by decide)
def retainedBothBHeap := retainedBothZeroHeap.write 1 (.string retainedString64Bytes) (by rfl)
def retainedBothBPlacement : Placement retainedBothBHeap := retainedWritePlacement (bytePlacement 0) retainedBothZeroPlacement
  retainedBothZero 1 (.string retainedString64Bytes) (by rfl) (.bytes 64) (.string _) (by decide)
def retainedBothB : RetainedAllocation (bytePlacement 0) retainedBothBPlacement :=
  retainWritten _ _ retainedBothZero 1 (.string retainedString64Bytes) (by rfl) (.bytes 64) (.string _) (by decide)
def retainedBothHeap := retainedBothAHeap.write 1 (.string retainedString64Bytes) (by rfl)
def retainedBothZeroPhysical := bytesObjectView [] (by decide) emptyPhysical 256
def retainedBothAPhysical := bytesObjectView growBytes (by decide) retainedBothZeroPhysical 128
def retainedBothBPhysical := bytesObjectView retainedString64Bytes (by decide) retainedBothZeroPhysical 256
def retainedBothPhysical := bytesObjectView retainedString64Bytes (by decide) retainedBothAPhysical 256

theorem retained_two_shrunk : retainedByteWriteback emptyHeap (bytePlacement 0) retainedEmptyPlacement retainedEmpty
    1 true stringOld rfl retainedBothZeroPhysical = some retainedBothZeroHeap :=
  retainedByte_encode _ _ _ _ _ _ _ _ rfl (by decide) (by decide) _

theorem retained_two_forward_a : retainedByteWriteback retainedBothZeroHeap (bytePlacement 0) retainedBothZeroPlacement retainedBothZero
    0 false [] rfl retainedBothAPhysical = some retainedBothAHeap :=
  retainedByte_encode _ _ _ _ _ _ _ _ rfl (by decide) (by decide) _

theorem retained_two_forward_b : retainedByteWriteback retainedBothAHeap (bytePlacement 0) retainedBothAPlacement retainedBothA
    1 true [] rfl retainedBothPhysical = some retainedBothHeap :=
  retainedByte_encode _ _ _ _ _ _ _ _ rfl (by decide) (by decide) _

theorem retained_two_reverse_b : retainedByteWriteback retainedBothZeroHeap (bytePlacement 0) retainedBothZeroPlacement retainedBothZero
    1 true [] rfl retainedBothBPhysical = some retainedBothBHeap :=
  retainedByte_encode _ _ _ _ _ _ _ _ rfl (by decide) (by decide) _

theorem retained_two_orders_agree : retainedBothHeap = retainedBothBHeap.write 0 (.bytes growBytes) (by rfl) :=
  heap_writes_commute retainedBothZeroHeap 0 1 (.bytes growBytes) (.string retainedString64Bytes) rfl rfl (by decide)

theorem retained_two_reverse_a : retainedByteWriteback retainedBothBHeap (bytePlacement 0) retainedBothBPlacement retainedBothB
    0 false [] rfl (bytesObjectView growBytes (by decide) retainedBothBPhysical 128) = some retainedBothHeap := by
  rw [retained_two_orders_agree]
  exact retainedByte_encode _ _ _ _ _ _ _ _ rfl (by decide) (by decide) _

theorem retained_other_cell_and_types : retainedBothHeap.get 2 = byteHeap.get 2 ∧
    retainedBothHeap.ty = byteHeap.ty ∧ retainedBothHeap.next = byteHeap.next := by
  refine ⟨rfl, ?_, rfl⟩
  funext b
  simp only [retainedBothHeap, retainedBothAHeap, retainedBothZeroHeap, emptyHeap, Source.Heap.write_ty]

theorem retained_both_reserved : ReservedOK retainedBothPhysical 512 :=
  by
    apply bytesObject_reserved _ _ retainedBothAPhysical 256 512 (by decide)
    apply bytesObject_reserved _ _ retainedBothZeroPhysical 128 512 (by decide)
    exact bytesObject_reserved _ _ emptyPhysical 256 512 (by decide) raw_resize_reserved.2.2

theorem retained_two_physical_orders : retainedBothPhysical =
    bytesObjectView growBytes (by decide) retainedBothBPhysical 128 :=
  bytesObject_disjoint_commute growBytes retainedString64Bytes (by decide) (by decide) retainedBothZeroPhysical 128 256 (Or.inl (by decide))

theorem retained_string_zero_alias_reads (horizon : Nat) :
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame horizon (.val (retainedStringZeroState.1.get (.here)))).run retainedStringZeroState = (.ok [], retainedStringZeroState) ∧
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame horizon (.val (retainedStringZeroState.1.get (.there .here)))).run retainedStringZeroState = (.ok [], retainedStringZeroState) := ⟨rfl, rfl⟩

theorem retained_regrow32 : retainedByteWriteback emptyHeap (bytePlacement 0) retainedEmptyPlacement retainedEmpty
    0 false [] rfl (bytesObjectView (List.replicate 32 0xff) (by decide) emptyPhysical 128) =
      some (emptyHeap.write 0 (.bytes (List.replicate 32 0xff)) (by rfl)) :=
  retainedByte_encode _ _ _ _ _ _ _ _ rfl (by decide) (by decide) _

def retainedBoundaryZeroHeap := (boundaryHeap 33).write 0 (.bytes []) (by rfl)
def retainedBoundaryZeroPlacement : Placement retainedBoundaryZeroHeap := retainedWritePlacement (boundaryPlacement 33) (boundaryPlacement 33)
  (retainInitial _ _) 0 (.bytes []) (by rfl) (.bytes 0) (.bytes _) (by decide)
def retainedBoundaryZero : RetainedAllocation (boundaryPlacement 33) retainedBoundaryZeroPlacement :=
  retainWritten _ _ (retainInitial _ _) 0 (.bytes []) (by rfl) (.bytes 0) (.bytes _) (by decide)

theorem retained_bytes33_zero : retainedByteWriteback (boundaryHeap 33) (boundaryPlacement 33) (boundaryPlacement 33) (retainInitial _ _)
    0 false (boundaryBytes 33) rfl (bytesObjectView [] (by decide) (boundaryPhysical 33) 128) = some retainedBoundaryZeroHeap :=
  retainedByte_encode _ _ _ _ _ _ _ _ rfl (by decide) (by decide) _

theorem retained_bytes33_zero64 : retainedByteWriteback retainedBoundaryZeroHeap (boundaryPlacement 33) retainedBoundaryZeroPlacement retainedBoundaryZero
    0 false [] rfl (bytesObjectView (List.replicate 64 0xff) (by decide) (boundaryPhysical 33) 128) =
      some (retainedBoundaryZeroHeap.write 0 (.bytes (List.replicate 64 0xff)) (by rfl)) :=
  retainedByte_encode _ _ _ _ _ _ _ _ rfl (by decide) (by decide) _

def retainedBothAliasState : Source.EMState heapByteEnv [.bytes .memory, .bytes .memory, .string .memory, .string .memory] :=
  ⟨.cons (.memRef rfl 0) (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) (.cons (.memRef rfl 1) .nil))), byteState.2⟩
def retainedBothZeroState := withSourceHeap retainedBothAliasState retainedBothZeroHeap
def retainedBothAState := withSourceHeap retainedBothZeroState retainedBothAHeap
def retainedBothState := withSourceHeap retainedBothAState retainedBothHeap

theorem retained_both_initial_MemOK : Source.MemOK heapByteEnv byteHeap.ty retainedBothAliasState := by
  refine ⟨⟨actual_initial_MemOK.1.1, ?_⟩, actual_initial_MemOK.2⟩
  exact ⟨⟨.bytes .memory, rfl, rfl⟩, ⟨⟨.bytes .memory, rfl, rfl⟩,
    ⟨⟨.string .memory, rfl, rfl⟩, ⟨⟨.string .memory, rfl, rfl⟩, trivial⟩⟩⟩⟩

theorem retained_both_zero_MemOK : Source.MemOK heapByteEnv byteHeap.ty retainedBothZeroState :=
  heapByte_write_MemOK heapByteEnv byteHeap.ty (withSourceHeap retainedBothAliasState emptyHeap) 1 true [] rfl
    (heapByte_write_MemOK heapByteEnv byteHeap.ty retainedBothAliasState 0 false [] rfl retained_both_initial_MemOK)

theorem retained_both_a_state_result : retainedByteStateWriteback retainedBothZeroState (bytePlacement 0) retainedBothZeroPlacement retainedBothZero
    0 false [] rfl retainedBothAPhysical = some retainedBothAState := by
  change (retainedByteWriteback retainedBothZeroHeap _ _ _ _ _ _ rfl _).map (withSourceHeap retainedBothZeroState) = some _
  rw [retained_two_forward_a]
  rfl

theorem retained_both_b_state_result : retainedByteStateWriteback retainedBothAState (bytePlacement 0) retainedBothAPlacement retainedBothA
    1 true [] rfl retainedBothPhysical = some retainedBothState := by
  change (retainedByteWriteback retainedBothAHeap _ _ _ _ _ _ rfl _).map (withSourceHeap retainedBothAState) = some _
  rw [retained_two_forward_b]
  rfl

theorem retained_both_MemOK : Source.MemOK heapByteEnv byteHeap.ty retainedBothState :=
  retainedByteState_MemOK heapByteEnv byteHeap.ty _ _ _ _ retainedBothA 1 true [] rfl _ retained_both_b_state_result
    (retainedByteState_MemOK heapByteEnv byteHeap.ty _ _ _ _ retainedBothZero 0 false [] rfl _ retained_both_a_state_result retained_both_zero_MemOK)

theorem retained_four_alias_reads (horizon : Nat) :
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame horizon (.val (retainedBothState.1.get (.here)))).run retainedBothState = (.ok growBytes, retainedBothState) ∧
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame horizon (.val (retainedBothState.1.get (.there .here)))).run retainedBothState = (.ok growBytes, retainedBothState) ∧
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame horizon (.val (retainedBothState.1.get (.there (.there .here))))).run retainedBothState = (.ok retainedString64Bytes, retainedBothState) ∧
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame horizon (.val (retainedBothState.1.get (.there (.there (.there .here)))))).run retainedBothState = (.ok retainedString64Bytes, retainedBothState) := ⟨rfl, rfl, rfl, rfl⟩

#print axioms retained_two_orders_agree
#print axioms retained_3_zero_4
#print axioms retained_33_zero_64_string
#print axioms retained_string_MemOK
end Solidity.Yul.Views.Controls
