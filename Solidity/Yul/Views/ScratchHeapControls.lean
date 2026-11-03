import Solidity.Yul.Views.ScratchSourceWriteback
import Solidity.Yul.Views.HeapEnumerationControls

namespace Solidity.Yul.Views.Controls

def shEncoded := encodeMixedHeap mixedPlacement (generatedHeapEntries mixedPlacement) mixedResidual
def shCopy := copyBytes shEncoded (calldataBytes [0xab,0xcd]) 31 0 2

theorem sh_whole_map : shCopy=encodeMixedHeap mixedPlacement (generatedHeapEntries mixedPlacement)
    (copyBytes mixedResidual (calldataBytes [0xab,0xcd]) 31 0 2) :=
  encodeMixedHeap_scratch_copy _ _ _ _ 31 0 2 (by decide)

theorem sh_source_unchanged : enumeratedMemoryWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _) shCopy=
    .ok (some (.ok (),mixedState)) :=
  (ownerMemory_scratch_writeback mixedHeap.ty mixedState mixedPlacement mixedPlacement (retainInitial _ _)
    mixedResidual (calldataBytes [0xab,0xcd]) 31 0 2 (by decide) mixed_actual_MemOK generated_mixed_types_supported).2

theorem sh_encoded_low (a : Nat) (low : a<128) : shEncoded a=mixedResidual a :=
  encodeMixedHeap_below_reserved _ _ _ a low

theorem sh_copy_low (a : Nat) (low : a<128) :
    shCopy a=copyBytes mixedResidual (calldataBytes [0xab,0xcd]) 31 0 2 a := by
  change (if 31≤a ∧ a<31+2 then calldataBytes [0xab,0xcd] (0+(a-31)) else shEncoded a)=_
  unfold copyBytes
  split
  · rfl
  · exact sh_encoded_low a low

theorem sh_exact_prefix : readBytes shCopy 30 5=[0xa5,0xab,0xcd,0xa5,0xa5] := by
  rw [readBytes_congr_on shCopy (copyBytes mixedResidual (calldataBytes [0xab,0xcd]) 31 0 2) 30 5
    (fun i bound => sh_copy_low (30+i) (by omega))]
  decide

theorem sh_tail_preserved : shCopy 163=shEncoded 163 := copyBytes_outside _ _ _ _ _ _ (by omega)

/-- Nonzero padding also in the established concrete six-object image. The
computed-inventory identity above does not require reducing proof transports. -/
theorem sh_nonzero_padding : readBytes (copyBytes mixedPhysical (calldataBytes [0xab,0xcd]) 31 0 2) 163 3=
    [0xa5,0xa5,0xa5] := by decide

theorem sh_reserved : ReservedOK shCopy 1664 :=
  scratch_copy_reserved shEncoded _ 1664 31 0 2 (by decide)
    (encodeMixedHeap_reserved _ _ _ mixed_reserved_initial)

theorem sh_not_erased_scratch : shCopy 31≠shEncoded 31 := by
  rw [sh_copy_low 31 (by decide),sh_encoded_low 31 (by decide)]
  decide

/-- A copy outside the real scratch premise CAN corrupt the zero slot.
This is not an admission refusal or a restriction on general memory semantics. -/
def shOutside := copyBytes shEncoded (calldataBytes [0xab,0xcd]) 95 0 2

theorem sh_outside_corrupts_zero : shOutside 96=0xcd ∧ shEncoded 96=0 := by
  rw [sh_encoded_low 96 (by decide)]
  exact ⟨rfl,rfl⟩

theorem sh_no_false_reserved : ¬ReservedOK shOutside 1664 := by
  intro reserved
  have zero := reserved.2 ⟨0,by decide⟩
  exact (by decide : (0xcd : UInt8)≠0) zero

end Solidity.Yul.Views.Controls
