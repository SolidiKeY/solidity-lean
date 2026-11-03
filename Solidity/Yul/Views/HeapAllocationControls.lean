import Solidity.Yul.Views.HeapAllocationReads
import Solidity.Yul.Views.HeapByteStateControls

namespace Solidity.Yul.Views.Controls

def haBytes : List UInt8 := [0xff,0,0x80]
def haState := byteAllocatedState byteState false haBytes

theorem ha_fresh : ∀ a, (byteHeap.cells a).isSome → (bytePlacement 0).address a≠512 := by
  intro a ha
  have bound := byteHeap_present_lt a ha
  change 128+a*128≠512
  omega

def haPlacement := byteAllocPlacement byteHeap (bytePlacement 0) false haBytes 512 576 (by decide) ha_fresh (by decide)
def haView := byteAllocationView haBytes 512 576 (by decide) bytePhysical

theorem ha_actual_allocRef : (Source.allocRef (Source.Data.bytes (D := heapByteEnv.layout) (l := .memory) haBytes)
    : Source.EM heapByteEnv [.bytes .memory,.string .memory] _).run byteState=
      (.ok (Source.Val.memRef (by rfl) 3),haState) := byteAllocRef_run byteState false haBytes

theorem ha_actual_MemOK : Source.MemOK heapByteEnv byteHeap.ty haState :=
  byteAllocRef_MemOK byteState false haBytes byteHeap.ty actual_initial_MemOK

theorem ha_free_zero_header : mload haView 64=576 ∧ mload haView 96=0 ∧ mload haView 512=3 := by decide
theorem ha_nonzero_padding : haView 547=0xa5 ∧ haView 575=0xa5 := by decide

theorem ha_old_region (a off : Nat) (ha : (byteHeap.cells a).isSome) (inside : off<((bytePlacement 0).shape a).size) :
    haView ((bytePlacement 0).address a+off)=bytePhysical ((bytePlacement 0).address a+off) :=
  byteAllocation_old_region byteHeap (bytePlacement 0) haBytes 512 576 (by decide) (by decide) bytePhysical a off ha inside

theorem ha_new_address : haPlacement.address 3=512 ∧ haPlacement.shape 3=.bytes 3 ∧ haPlacement.free=576 := by decide

theorem ha_read_aliases (n : Nat) :
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame n (.val (Source.Val.memRef (τ := .bytes .memory) (by rfl) 3))).run haState=(.ok haBytes,haState) ∧
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame n (.val (Source.Val.memRef (τ := .string .memory) (by rfl) 3))).run haState=(.ok haBytes,haState) := ⟨rfl,rfl⟩

theorem ha_old_aliases (n : Nat) :
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame n (.val (haState.1.get .here))).run haState=(.ok byteOld,haState) ∧
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame n (.val (haState.1.get (.there .here)))).run haState=(.ok byteOld,haState) := ⟨rfl,rfl⟩

theorem ha_unchanged_whole_state :
    heapByteStateWriteback haState haPlacement 3 false haBytes rfl haView=some haState :=
  byteAllocation_state_writeback byteState (bytePlacement 0) false haBytes 512 576 (by decide) ha_fresh (by decide) bytePhysical

def haSecondBytes : List UInt8 := [0,0xff,0x81,0x80]
def haSecond := byteAllocatedState haState true haSecondBytes
def haSecondPlacement := byteAllocPlacement haState.2.heap haPlacement true haSecondBytes 577 641 (by decide)
  (heap_later_fresh haState.2.heap haPlacement 577 (by decide)) (by decide)
def haSecondView := byteAllocationView haSecondBytes 577 641 (by decide) haView

theorem ha_second_MemOK : Source.MemOK heapByteEnv byteHeap.ty haSecond :=
  byteAllocRef_MemOK haState true haSecondBytes byteHeap.ty ha_actual_MemOK

theorem ha_second_coordinates : haSecondPlacement.address 3=512 ∧ haSecondPlacement.address 4=577 ∧
    haSecondPlacement.free=641 := by decide

theorem ha_second_old_alias (n : Nat) :
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame n (.val (Source.Val.memRef (τ := .bytes .memory) (by rfl) 3))).run haSecond=
      (.ok haBytes,haSecond) := rfl

theorem ha_second_new_alias (n : Nat) :
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame n (.val (Source.Val.memRef (τ := .string .memory) (by rfl) 4))).run haSecond=
      (.ok haSecondBytes,haSecond) := rfl

theorem ha_second_gap_and_tail : haSecondView 547=0xa5 ∧ haSecondView 576=0xa5 ∧ haSecondView 613=0xa5 := by decide

theorem ha_boundary_sizes : (MemoryShape.bytes 0).size=32 ∧ (MemoryShape.bytes 31).size=64 ∧
    (MemoryShape.bytes 32).size=64 ∧ (MemoryShape.bytes 33).size=96 := by decide

theorem ha_insufficient_footprint : ¬512+(MemoryShape.bytes 33).size≤576 := by decide

theorem ha_reserved_base_bad : ¬(bytePlacement 0).free.val≤96 := by decide

def haEmptyState := byteAllocatedState byteState false []
def haEmptyPlacement := byteAllocPlacement byteHeap (bytePlacement 0) false [] 512 544 (by decide) ha_fresh (by decide)

theorem ha_empty_allocated : haEmptyPlacement.address 3=512 ∧ haEmptyPlacement.shape 3=.bytes 0 ∧
    haEmptyState.2.heap.get 3=some ⟨.bytes .memory,Source.Data.bytes []⟩ := ⟨rfl,rfl,rfl⟩

theorem ha_empty_alias_read (n : Nat) :
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame n (.val (Source.Val.memRef (τ := .bytes .memory) (by rfl) 3))).run haEmptyState=
      (.ok [],haEmptyState) := rfl

end Solidity.Yul.Views.Controls
