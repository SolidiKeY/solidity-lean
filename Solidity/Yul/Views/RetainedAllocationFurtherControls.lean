import Solidity.Yul.Views.RetainedAllocationLiftControls

namespace Solidity.Yul.Views.Controls

def alGrowDirectPlacement := retainedWritePlacement alOriginalPlacement alPlacement alHistory
  0 (Source.Data.bytes growBytes) (by rfl) (.bytes 4) (.bytes _) (by decide)
def alGrowDirectHistory : RetainedAllocation alOriginalPlacement alGrowDirectPlacement :=
  retainWritten alOriginalPlacement alPlacement alHistory 0 (Source.Data.bytes growBytes) (by rfl)
    (.bytes 4) (.bytes _) (by decide)

def alNewZeroHeap := alGrowHeap.write 3 (Source.Data.string []) (by rfl)
def alNewZeroState := withSourceHeap alGrowState alNewZeroHeap
def alNewZeroPhysical := mstore alGrowPhysical 512 0
def alNewZeroPlacement := retainedWritePlacement alOriginalPlacement alGrowDirectPlacement alGrowDirectHistory
  3 (Source.Data.string []) (by rfl) (.bytes 0) (.string _) (by decide)
def alNewZeroHistory : RetainedAllocation alOriginalPlacement alNewZeroPlacement :=
  retainWritten alOriginalPlacement alGrowDirectPlacement alGrowDirectHistory 3 (Source.Data.string []) (by rfl)
    (.bytes 0) (.string _) (by decide)

theorem al_new_zero_source : (Source.heapPut (E := heapByteEnv) 3 ⟨.string .memory,.string []⟩).run alGrowState=
    (.ok (),alNewZeroState) := rfl

theorem al_new_zero_MemOK : Source.MemOK heapByteEnv byteHeap.ty alNewZeroState :=
  heapByte_write_MemOK heapByteEnv byteHeap.ty alGrowState 3 true [] (by rfl)
    (al_regrow_every_H byteHeap.ty al_actual_MemOK)

def alNextBytes : List UInt8 := [9,8]
def alTwiceState := byteAllocatedState alNewZeroState false alNextBytes
def alTwiceOriginalPlacement := heapAllocPlacement alOrigin alOriginalPlacement (Source.Data.bytes (l := .memory) alNextBytes)
  (.bytes 2) (.bytes _) 577 641 (by decide) (heap_later_fresh alOrigin alOriginalPlacement 577 (by decide)) (by decide)
def alTwicePlacement := retainedAllocationPlacement alOriginalPlacement alNewZeroPlacement alNewZeroHistory
  (Source.Data.bytes (l := .memory) alNextBytes) (.bytes 2) (.bytes _) 577 641 (by decide)
    (heap_later_fresh alOrigin alOriginalPlacement 577 (by decide)) (by decide)
def alTwiceHistory : RetainedAllocation alTwiceOriginalPlacement alTwicePlacement :=
  retainAllocated alOriginalPlacement alNewZeroPlacement alNewZeroHistory (Source.Data.bytes (l := .memory) alNextBytes)
    (.bytes 2) (.bytes _) 577 641 (by decide) (heap_later_fresh alOrigin alOriginalPlacement 577 (by decide)) (by decide)

def alTwicePhysical := byteAllocationView alNextBytes 577 641 (by decide) alNewZeroPhysical

theorem al_twice_MemOK : Source.MemOK heapByteEnv byteHeap.ty alTwiceState :=
  byteAllocRef_MemOK alNewZeroState false alNextBytes byteHeap.ty al_new_zero_MemOK

theorem al_twice_two_capacities : (alTwiceOriginalPlacement.shape 0).size=64 ∧
    (alTwiceOriginalPlacement.shape 3).size=64 ∧ (alTwicePlacement.shape 3).size=32 ∧
    alTwicePlacement.address 0=128 ∧ alTwicePlacement.address 3=512 ∧ alTwicePlacement.address 4=577 := by decide

def alFinalBytes := alBytes ++ List.replicate 4 0xa5
def alFinalPhysical := mstore alTwicePhysical 512 8
def alFinalHeap := alTwiceState.2.heap.write 3 (Source.Data.string alFinalBytes) (by rfl)
def alFinalState := withSourceHeap alTwiceState alFinalHeap

theorem al_new_regrow : retainedByteWriteback alTwiceState.2.heap alTwiceOriginalPlacement alTwicePlacement alTwiceHistory
    3 true [] rfl alFinalPhysical=some alFinalHeap := by
  simp only [retainedByteWriteback,alFinalPhysical,show alTwicePlacement.address 3=512 from rfl,mload_mstore]
  rw [if_pos (by decide),decodeHeapByte_data,mload_mstore]
  simp only [show (8 : Roadmap.Word).val=8 by decide,show (512+32 : Nat)=544 from rfl]
  have bytes : readBytes (mstore alTwicePhysical 512 8) 544 8=alFinalBytes := by decide
  rw [bytes]
  rfl

theorem al_new_regrow_state : retainedByteStateWriteback alTwiceState alTwiceOriginalPlacement alTwicePlacement alTwiceHistory
    3 true [] rfl alFinalPhysical=some alFinalState := by
  change (retainedByteWriteback alTwiceState.2.heap alTwiceOriginalPlacement alTwicePlacement alTwiceHistory
    3 true [] rfl alFinalPhysical).map (withSourceHeap alTwiceState)=some alFinalState
  rw [al_new_regrow]
  rfl

theorem al_final_MemOK : Source.MemOK heapByteEnv byteHeap.ty alFinalState :=
  retainedByteState_MemOK heapByteEnv byteHeap.ty alTwiceState alFinalState alTwiceOriginalPlacement alTwicePlacement alTwiceHistory
    3 true [] rfl alFinalPhysical al_new_regrow_state al_twice_MemOK

theorem al_three_aliases (n : Nat) :
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame n (.val (alFinalState.1.get .here))).run alFinalState=(.ok growBytes,alFinalState) ∧
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame n (.val (Source.Val.memRef (τ := .string .memory) (by rfl) 3))).run alFinalState=(.ok alFinalBytes,alFinalState) ∧
    (Source.bytesOfRV (E := heapByteEnv) byteReadFrame n (.val (Source.Val.memRef (τ := .bytes .memory) (by rfl) 4))).run alFinalState=(.ok alNextBytes,alFinalState) := ⟨rfl,rfl,rfl⟩

theorem al_final_raw_regions : readBytes alFinalPhysical 160 4=growBytes ∧
    readBytes alFinalPhysical 609 2=alNextBytes ∧ mload alFinalPhysical 64=641 ∧ mload alFinalPhysical 96=0 ∧
    alFinalPhysical 191=0xa5 ∧ alFinalPhysical 575=0xa5 ∧ alFinalPhysical 576=0xa5 := by decide

end Solidity.Yul.Views.Controls
