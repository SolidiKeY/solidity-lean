import Solidity.Yul.Views.RetainedResidualGeometry
import Solidity.Yul.Views.HeapEnumerationNegativeControls
import Solidity.Yul.Views.MemoryControls

namespace Solidity.Yul.Views.ResidualWindowControls
open Controls

theorem gap_geometry : ResidualWindowDisjoint mixedPlacement (generatedHeapEntries mixedPlacement) 220 3 := by
  intro e member
  by_cases zero : e.id=0
  · have fits:=e.image.fits mixedPlacement e.id e.found
    rw [zero] at fits
    change e.image.span≤64 at fits
    exact Or.inr (Or.inr (Or.inr (by change 128+e.id*256+e.image.span≤220; omega)))
  · exact Or.inr (Or.inr (Or.inl (by change 220+3≤128+e.id*256; omega)))

theorem gap_checked : residualWindowCheck mixedPlacement (generatedHeapEntries mixedPlacement) 220 3=true :=
  (residualWindowCheck_iff _ _ _ _).mpr ⟨by decide,Or.inr (Or.inr (by decide)),gap_geometry⟩

def gapPlan : ResidualWindowPlan mixedPlacement := ⟨220,3,generatedHeapEntries mixedPlacement,generated_mixed_prepared,gap_checked⟩

theorem gap_computed_preparation : prepareResidualWindow mixedPlacement 220 3=.ok (some gapPlan) :=
  prepareResidualWindow_plan gapPlan

theorem gap_whole_source : residualMemoryWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _) gapPlan
    mixedResidual (calldataBytes [0xde,0xad,0x77]) 0=
      .ok (some ((.ok (),mixedState),copyBytes mixedResidual (calldataBytes [0xde,0xad,0x77]) 220 0 3)) :=
  residualMemoryWriteback_exact mixedState mixedPlacement mixedPlacement (retainInitial _ _) gapPlan
    mixedResidual _ 0 generated_mixed_types_supported

theorem gap_whole_map : copyBytes (encodeMixedHeap mixedPlacement gapPlan.entries mixedResidual)
    (calldataBytes [0xde,0xad,0x77]) 220 0 3=
      encodeMixedHeap mixedPlacement gapPlan.entries (copyBytes mixedResidual (calldataBytes [0xde,0xad,0x77]) 220 0 3) :=
  gapPlan.whole_map _ _ 0

theorem gap_reserved : ReservedOK (copyBytes mixedResidual (calldataBytes [0xde,0xad,0x77]) 220 0 3) 1664 :=
  gapPlan.reserved _ _ 0 mixed_reserved_initial

theorem gap_exact_delta : readBytes (copyBytes mixedResidual (calldataBytes [0xde,0xad,0x77]) 220 0 3) 219 5=
    [0xa5,0xde,0xad,0x77,0xa5] := by decide

theorem reserved_rejected : prepareResidualWindow mixedPlacement 64 1=.ok none := by
  have bad : residualWindowCheck mixedPlacement (generatedHeapEntries mixedPlacement) 64 1≠true := by
    intro yes
    have geometry := (residualWindowCheck_iff _ _ _ _).mp yes |>.2.1
    change (1=0 ∨ 64+1≤64 ∨ 128≤64) at geometry
    exact (by decide : ¬(1=0 ∨ 64+1≤64 ∨ 128≤64)) geometry
  exact prepareResidualWindow_none _ _ _ _ generated_mixed_prepared bad

theorem byte_window_overlap (destination : Roadmap.Word) (low : 128≤destination.val) (high : destination.val<163) :
    prepareResidualWindow mixedPlacement destination 1=.ok none := by
  obtain ⟨entry,member,zero⟩ := generated_mixed_coverage 0 (by rfl)
  have span := entry.bytes_span_at 0 mixedChild rfl zero
  have address : mixedPlacement.address entry.id=128 := by rw [zero]; rfl
  apply prepareResidualWindow_none _ _ _ _ generated_mixed_prepared
  apply residualWindowCheck_overlap mixedPlacement _ destination 1 entry member (by decide)
  · rw [span]; decide
  · rw [address,span]; exact high
  · rw [address]; change 128<destination.val+1; omega

theorem header_rejected : prepareResidualWindow mixedPlacement 128 1=.ok none := byte_window_overlap 128 (by decide) (by decide)
theorem payload_rejected : prepareResidualWindow mixedPlacement 160 1=.ok none := byte_window_overlap 160 (by decide) (by decide)

theorem overflow_rejected : prepareResidualWindow mixedPlacement highestUint 2=.ok none := by
  have bad : residualWindowCheck mixedPlacement (generatedHeapEntries mixedPlacement) highestUint 2≠true := by
    intro yes
    have bound := (residualWindowCheck_iff _ _ _ _).mp yes |>.1
    change 2^256-1+2≤2^256 at bound
    omega
  exact prepareResidualWindow_none _ _ _ _ generated_mixed_prepared bad

theorem zero_inside_reserved_checked : residualWindowCheck mixedPlacement (generatedHeapEntries mixedPlacement) 96 0=true := by
  apply (residualWindowCheck_iff _ _ _ _).mpr
  refine ⟨by decide,Or.inl rfl,?_⟩
  intro e member
  exact Or.inl rfl

def zeroPlan : ResidualWindowPlan mixedPlacement :=
  ⟨96,0,generatedHeapEntries mixedPlacement,generated_mixed_prepared,zero_inside_reserved_checked⟩

theorem zero_whole_state_and_residual : residualMemoryWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _) zeroPlan
    mixedResidual (calldataBytes [0xff]) 0=.ok (some ((.ok (),mixedState),mixedResidual)) := by
  rw [residualMemoryWriteback_exact mixedState mixedPlacement mixedPlacement (retainInitial _ _) zeroPlan
    mixedResidual (calldataBytes [0xff]) 0 generated_mixed_types_supported]
  exact congrArg (fun memory=>Except.ok (some ((Except.ok (),mixedState),memory))) (copyBytes_zero mixedResidual _ 96 0)

theorem unsupported_ids_not_skipped : prepareResidualWindow enumerationDanglingPlacement 220 3=.error [2] := by
  have bad := generated_missing_is_not_unsupported.2.2
  apply prepareResidualWindow_error _ _ _ [2]
  unfold prepareHeapInventory
  rw [bad]

theorem no_silent_inventory_drop : prepareHeapInventory mixedPlacement≠.ok [] := by
  intro empty
  rw [generated_mixed_prepared] at empty
  have ids := congrArg (List.map MixedHeapEntry.id) (Except.ok.inj empty)
  rw [generated_mixed_ids] at ids
  cases ids

end Solidity.Yul.Views.ResidualWindowControls
