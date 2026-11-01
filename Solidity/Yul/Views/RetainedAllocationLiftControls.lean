import Solidity.Yul.Views.RetainedAllocationRegions
import Solidity.Yul.Views.RetainedByteControls
import Solidity.Yul.Views.HeapAllocationControls

namespace Solidity.Yul.Views.Controls

def alBytes : List UInt8 := [0xfe,0,0xfd,0xfc]
def alOrigin := (byteHeap.alloc ⟨.string .memory,Source.Data.string alBytes⟩).1
def alState := byteAllocatedState emptyState true alBytes

def alOriginalPlacement := heapAllocPlacement byteHeap (bytePlacement 0) (Source.Data.string (l := .memory) alBytes)
  (.bytes 4) (.string _) 512 576 (by decide) ha_fresh (by decide)
def alPlacement := retainedAllocationPlacement (bytePlacement 0) retainedEmptyPlacement retainedEmpty
  (Source.Data.string (l := .memory) alBytes) (.bytes 4) (.string _) 512 576 (by decide) ha_fresh (by decide)
def alHistory : RetainedAllocation alOriginalPlacement alPlacement :=
  retainAllocated (bytePlacement 0) retainedEmptyPlacement retainedEmpty
    (Source.Data.string (l := .memory) alBytes) (.bytes 4) (.string _) 512 576 (by decide) ha_fresh (by decide)

def alPhysical := byteAllocationView alBytes 512 576 (by decide) emptyPhysical

theorem al_actual_allocation : (Source.allocRef (Source.Data.string (D := heapByteEnv.layout) (l := .memory) alBytes)
    : Source.EM heapByteEnv [.bytes .memory,.string .memory] _).run emptyState=
      (.ok (Source.Val.memRef (by rfl) 3),alState) := byteAllocRef_run emptyState true alBytes

theorem al_actual_MemOK : Source.MemOK heapByteEnv byteHeap.ty alState :=
  byteAllocRef_MemOK emptyState true alBytes byteHeap.ty actual_resize_MemOK.2.2

theorem al_preserved_capacity : alPlacement.shape 0=.bytes 0 ∧ alOriginalPlacement.shape 0=.bytes 3 ∧
    (alOriginalPlacement.shape 0).size=64 ∧ alPlacement.address 0=128 ∧ alPlacement.address 3=512 ∧
    alOriginalPlacement.shape 3=.bytes 4 := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem al_full_old_region (a off : Nat) (present : (byteHeap.cells a).isSome)
    (inside : off<((bytePlacement 0).shape a).size) :
    alPhysical (retainedEmptyPlacement.address a+off)=emptyPhysical (retainedEmptyPlacement.address a+off) :=
  retainedAllocation_full_region (bytePlacement 0) retainedEmptyPlacement retainedEmpty alBytes 512 576
    (by decide) (by decide) emptyPhysical a off present inside

def alGrowPhysical := mstore alPhysical 128 4
def alGrowHeap := alState.2.heap.write 0 (Source.Data.bytes growBytes) (by rfl)
def alGrowState := withSourceHeap alState alGrowHeap

theorem al_regrow : retainedByteWriteback alState.2.heap alOriginalPlacement alPlacement alHistory
    0 false [] rfl alGrowPhysical=some alGrowHeap := by
  simp only [retainedByteWriteback,alGrowPhysical,show alPlacement.address 0=128 from rfl,mload_mstore]
  rw [if_pos (by decide),decodeHeapByte_data,mload_mstore]
  simp only [show (4 : Roadmap.Word).val=4 by decide,show (128+32 : Nat)=160 from rfl]
  have bytes : readBytes (mstore alPhysical 128 4) 160 4=growBytes := by decide
  rw [bytes]
  rfl

theorem al_regrow_state : retainedByteStateWriteback alState alOriginalPlacement alPlacement alHistory
    0 false [] rfl alGrowPhysical=some alGrowState := by
  change (retainedByteWriteback alState.2.heap alOriginalPlacement alPlacement alHistory 0 false [] rfl alGrowPhysical).map
    (withSourceHeap alState)=some alGrowState
  rw [al_regrow]
  rfl

theorem al_regrow_every_H (H) (ok : Source.MemOK heapByteEnv H alState) : Source.MemOK heapByteEnv H alGrowState :=
  retainedByteState_MemOK heapByteEnv H alState alGrowState alOriginalPlacement alPlacement alHistory
    0 false [] rfl alGrowPhysical al_regrow_state ok

def alRegrowPlacement := retainedByteResultPlacement alState.2.heap alOriginalPlacement alPlacement alHistory
  0 false [] rfl alGrowPhysical alGrowHeap al_regrow

def alRegrowHistory : RetainedAllocation alOriginalPlacement alRegrowPlacement :=
  retainedByte_result_history alState.2.heap alOriginalPlacement alPlacement alHistory
    0 false [] rfl alGrowPhysical alGrowHeap al_regrow

theorem al_new_alias_unchanged (n : Nat) :
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame n (.val (Source.Val.memRef (τ := .string .memory) (by rfl) 3))).run alGrowState=
      (.ok alBytes,alGrowState) := rfl

theorem al_old_aliases_regrown (n : Nat) :
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame n (.val (alGrowState.1.get .here))).run alGrowState=(.ok growBytes,alGrowState) ∧
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame n (.val (alGrowState.1.get (.there .here)))).run alGrowState=(.ok growBytes,alGrowState) := ⟨rfl,rfl⟩

theorem al_new_raw_unchanged : mload alGrowPhysical 512=4 ∧
    readBytes alGrowPhysical 544 4=alBytes ∧ mload alGrowPhysical 64=576 ∧ mload alGrowPhysical 96=0 ∧
    alGrowPhysical 163=0xa5 ∧ alGrowPhysical 191=0xa5 ∧ alGrowPhysical 575=0xa5 := by decide

/-- Resetting origin to the shrunken current heap loses real capacity. None
here remains unsupported preparation; the lifted history succeeds above. -/
theorem al_reset_loses_capacity : retainedByteWriteback alState.2.heap alPlacement alPlacement (retainInitial _ _)
    0 false [] rfl alGrowPhysical=none := by
  simp only [retainedByteWriteback,alGrowPhysical,show alPlacement.address 0=128 from rfl,mload_mstore]
  rw [if_neg (by decide)]

/-- The actual callee allocates in the shared source heap and restores saved
caller locals. No external-frame heap rollback is inferred from EM.sub. -/
theorem al_suspended_caller :
    (Source.EM.sub (Γ := [.bytes .memory,.string .memory]) Source.Locals.nil
      (Source.allocRef (Source.Data.string (D := heapByteEnv.layout) (l := .memory) alBytes))).run emptyState=
      (.ok (Source.Val.memRef (by rfl) 3,Source.Locals.nil),alState) := rfl

end Solidity.Yul.Views.Controls
