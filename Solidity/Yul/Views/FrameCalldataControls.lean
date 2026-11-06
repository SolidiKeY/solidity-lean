import Solidity.Yul.Views.FrameCalldata
import Solidity.Yul.Views.ResidualWindowControls

namespace Solidity.Yul.Views.FrameCalldataControls
open Controls ResidualWindowControls

def frame := mixedState.2.ex.enter 1 2 0 [0xab,0xcd] false
def emptyFrame := mixedState.2.ex.enter 1 2 0 [] false
def padded := frameCalldataCopy frame gapPlan mixedResidual 1
def maximal := frameCalldataCopy frame gapPlan mixedResidual highestUint

theorem actual_frame_input : frame.input=[0xab,0xcd] := rfl
theorem copied_end_padding : readBytes padded 219 5=[0xa5,0xcd,0,0,0xa5] := by decide
theorem copied_whole_input : readBytes (frameCalldataCopy frame gapPlan mixedResidual 0) 220 3=[0xab,0xcd,0] := by decide
theorem maximal_source_zero : readBytes maximal 220 3=[0,0,0] := by decide
theorem maximal_does_not_wrap : maximal 221≠calldataBytes frame.input 0 := by decide
theorem empty_input_zero : readBytes (frameCalldataCopy emptyFrame gapPlan mixedResidual 0) 220 3=[0,0,0] := by decide

theorem no_source_end_premise : highestUint.val+gapPlan.size.val>2^256 ∧
    readBytes maximal 220 3=[0,0,0] := ⟨by decide,maximal_source_zero⟩

theorem full_physical_map : calldatacopy (encodeMixedHeap mixedPlacement gapPlan.entries mixedResidual) frame.input 220 1 3=
    encodeMixedHeap mixedPlacement gapPlan.entries padded := frameCalldata_whole_map frame gapPlan mixedResidual 1

theorem whole_source : frameCalldataWriteback frame mixedState mixedPlacement mixedPlacement (retainInitial _ _) gapPlan mixedResidual 1=
    .ok (some ((.ok (),mixedState),padded)) :=
  frameCalldataWriteback_exact frame mixedState mixedPlacement mixedPlacement (retainInitial _ _) gapPlan mixedResidual 1 generated_mixed_types_supported

theorem every_H (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H mixedState) :
    ∃ after, frameCalldataWriteback frame mixedState mixedPlacement mixedPlacement (retainInitial _ _) gapPlan mixedResidual 1=
      .ok (some after) ∧ Source.MemOK mixedEnv H after.1.2 :=
  frameCalldataWriteback_every_H frame H mixedState mixedPlacement mixedPlacement (retainInitial _ _) gapPlan mixedResidual 1 generated_mixed_types_supported ok

theorem reserved_words : ReservedOK padded 1664 := frameCalldata_reserved frame gapPlan mixedResidual 1 mixed_reserved_initial

theorem exact_copied_hash (fixed : Roadmap.Evm.Fixed) :
    keccak256 fixed (encodeMixedHeap mixedPlacement gapPlan.entries padded) 220 3=
      ⟨fixed.keccak [0xcd,0,0],fixed.keccak_lt _⟩ := frameCalldata_hash frame fixed gapPlan mixedResidual 1

theorem empty_copy_unchanged : frameCalldataCopy frame zeroPlan mixedResidual highestUint=mixedResidual :=
  frameCalldata_zero_copy frame zeroPlan mixedResidual highestUint rfl

theorem static_input_copy : frameCalldataCopy {frame with static:=true} gapPlan mixedResidual 1=padded := rfl

theorem actual_source_aliases (horizon : Nat) : ∃ after,
    frameCalldataWriteback frame mixedState mixedPlacement mixedPlacement (retainInitial _ _) gapPlan mixedResidual 1=.ok (some after) ∧
    (Source.bytesOfRV (E:=mixedEnv) mixedReadFrame horizon (.val (after.1.2.1.get .here))).run after.1.2=(.ok mixedChild,after.1.2) ∧
    (Source.bytesOfRV (E:=mixedEnv) mixedReadFrame horizon (.val (after.1.2.1.get (.there .here)))).run after.1.2=(.ok mixedChild,after.1.2) :=
  ⟨((.ok (),mixedState),padded),whole_source,mixed_source_alias_reads horizon⟩

end Solidity.Yul.Views.FrameCalldataControls
