import Solidity.Yul.Views.NestedDeclarationComposition

namespace Solidity.Yul.Views

/-- Executable individual-codec default check, not an assumed full-view law.
Function/reference types with no source default cannot pass this preparation. -/
def scalarZeroDefaultCheck {D L} (cs : List (ScalarPath D L)) : Bool :=
  cs.all (fun c => (Source.Val.default D (L c.path)).map (fun v => (c.codec.encode v).val) == some 0)

theorem scalarZeroDefaultCheck_sound {D L} (cs : List (ScalarPath D L)) (checked : scalarZeroDefaultCheck cs = true) :
    ∀ c ∈ cs, ∃ v, Source.Val.default D (L c.path) = some v ∧ (c.codec.encode v).val = 0 := by
  intro c member
  have each := (List.all_eq_true.mp checked) c member
  exact Option.map_eq_some_iff.mp (beq_iff_eq.mp each)

end Solidity.Yul.Views

namespace Solidity.Yul.Views.Controls

theorem nested_transient_defaults_checked : scalarZeroDefaultCheck (selectedSlotPaths (nestedDeclRegistry account) 4) = true := by decide

theorem nested_transient_full_raw_reset : reencodeTransientSlot nestedDeclRegistry (companionEndTx nestedChildCore) account 4 = some 0 :=
  packedEndTx_transient _ _ _ _ (scalarZeroDefaultCheck_sound _ nested_transient_defaults_checked)

theorem nested_child_every_H_MemOK (H : Source.HeapTy) (ok : Source.MemOK declBoundaryEnv H nestedDeclState) :
    Source.MemOK declBoundaryEnv H nestedTransientFrame.1.2 :=
  packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (nested_decl_every_H_MemOK H ok))

theorem nested_child_inhabited_MemOK : Source.MemOK declBoundaryEnv nestedDeclState.2.heap.ty nestedTransientFrame.1.2 :=
  nested_child_every_H_MemOK _ nested_decl_initial_MemOK

theorem nested_repeated_slot_order :
    reencodePersistentSlot nestedDeclRegistry (runPackedSlots nestedInitialCore [nestedPlan6,nestedChildPlan]) account 6 = some packedRawB ∧
    reencodePersistentSlot nestedDeclRegistry (runPackedSlots nestedInitialCore [nestedChildPlan,nestedPlan6]) account 6 = some nestedRaw6 ∧
    packedRawB ≠ nestedRaw6 :=
  ⟨packedPersistent_reencode _ nestedChildPlan rfl (nested_decl_separated _),
    packedPersistent_reencode _ nestedPlan6 rfl (nested_decl_separated _),by decide⟩

end Solidity.Yul.Views.Controls
