import Solidity.Yul.Views.ActualScalarSafety
import Solidity.Yul.Views.ActualScalarFrameControls
import Solidity.Yul.Views.ActualScalarTransientControls

/-! Inhabited original-H preservation through actual writes and refusal. Exact
caller aliases remain present while ancestors are dormant. MemOK is the owner's
heap property, not a physical padding or retained-path completeness theorem. -/
namespace Solidity.Yul.Views.Controls

theorem safety_shrunk : Source.MemOK agEnv agState.2.heap.ty agShrink.2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  have safe := Source.writeLen_mem (E:=agEnv) (H:=agState.2.heap.ty) packedStepFrame agPath 0 agAliases ag_alias_MemOK
  change Source.MemOK agEnv agState.2.heap.ty agShrink.2 at safe
  exact safe

theorem safety_persistent : Source.MemOK agEnv agState.2.heap.ty asWrite.1.2 :=
  actualScalarWrite_MemOK packedStepFrame rhC3.path rhC3.codec rhC3.slot _ rhRaw0 agShrink.2 _ safety_shrunk

theorem safety_second : Source.MemOK agEnv agState.2.heap.ty afSecond.1.2 :=
  actualScalarWrite_MemOK packedStepFrame rhC3.path rhC3.codec rhC3.slot _ asWrite.2 asWrite.1.2 _ safety_persistent

theorem safety_static : Source.MemOK agEnv agState.2.heap.ty
    (actualScalarWrite rcompoundStatic rhC3.path rhC3.codec rhC3.slot (Source.intWrap rcU16 154) rhRaw0 agShrink.2).1.2 :=
  actualScalarWrite_MemOK rcompoundStatic rhC3.path rhC3.codec rhC3.slot _ rhRaw0 agShrink.2 _ safety_shrunk

theorem safety_exact_aliases : asWrite.1.2.1=agShrink.2.1 :=
  (actualScalarWrite_locals_heap packedStepFrame rhC3.path rhC3.codec rhC3.slot _ rhRaw0 agShrink.2).1

theorem safety_both_dormant_aliases : asWrite.1.2.1.get .here=Source.Val.storRef (by rfl) (agInner 0) ∧
    asWrite.1.2.1.get (.there .here)=Source.Val.storRef (by rfl) (agInner 0) := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [safety_exact_aliases]
  exact ag_two_aliases_retained

theorem safety_not_padding_adequacy : Source.MemOK agEnv agState.2.heap.ty asWrite.1.2 ∧
    (asWrite.2 1000).val≠154+88*65536+77*2^32 := ⟨safety_persistent,as_wrong_clean_padding⟩

theorem safety_transient_initial : Source.MemOK rootEnv TransientSlotControls.state.2.heap.ty TransientSlotControls.state :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩

theorem safety_transient_before : Source.MemOK rootEnv TransientSlotControls.state.2.heap.ty atBefore := by
  first | (simp only;done) | decide | omega | rfl | skip
  have safe := Source.writeAt_mem (H:=TransientSlotControls.state.2.heap.ty) TransientSlotControls.frame
    (rootPath "a") (Source.intWrap rootU8 7) TransientSlotControls.state safety_transient_initial
  change Source.MemOK rootEnv TransientSlotControls.state.2.heap.ty atBefore at safe
  exact safe

theorem safety_transient : Source.MemOK rootEnv TransientSlotControls.state.2.heap.ty atWrite.1.2 :=
  actualScalarWrite_MemOK TransientSlotControls.frame atCell.path atCell.codec atCell.slot _ atRaw atBefore _ safety_transient_before
theorem safety_first_refusal_stops :
    actualScalarWritePair rcompoundStatic packedStepFrame rhC3.path rhC3.path rhC3.codec rhC3.codec
      rhC3.slot rhC3.slot (Source.intWrap rcU16 154) (Source.intWrap rcU16 308) rhRaw0 agShrink.2=
      ((.error (.revert []),agShrink.2),rhRaw0) := rfl

theorem safety_second_refusal_keeps_prefix :
    actualScalarWritePair packedStepFrame rcompoundStatic rhC3.path rhC3.path rhC3.codec rhC3.codec
      rhC3.slot rhC3.slot (Source.intWrap rcU16 154) (Source.intWrap rcU16 308) rhRaw0 agShrink.2=
      ((.error (.revert []),asWrite.1.2),asWrite.2) := rfl

theorem safety_pair : Source.MemOK agEnv agState.2.heap.ty
    (actualScalarWritePair packedStepFrame rcompoundStatic rhC3.path rhC3.path rhC3.codec rhC3.codec
      rhC3.slot rhC3.slot (Source.intWrap rcU16 154) (Source.intWrap rcU16 308) rhRaw0 agShrink.2).1.2 :=
  actualScalarWritePair_MemOK packedStepFrame rcompoundStatic rhC3.path rhC3.path rhC3.codec rhC3.codec
    rhC3.slot rhC3.slot _ _ rhRaw0 agShrink.2 _ safety_shrunk
end Solidity.Yul.Views.Controls
