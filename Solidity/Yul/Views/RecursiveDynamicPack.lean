import Solidity.Yul.Views.RecursiveDynamicLeaves

namespace Solidity.Yul.Views.Controls

theorem rcX_end : rcXOut.2 = 96 := rfl
theorem rcY_end : rcYOut.2 = 128 := rfl
theorem rcTag_end : rcTagOut.2 = 131 := rfl
theorem rcStamp_end : rcStampOut.2 = 1 := rfl
theorem rcGuard_end : rcGuardOut.2 = 34 := rfl
theorem rcBool_end : rcBoolOut.2 = 192 := rfl
theorem rcWho_end : rcWhoOut.2 = 212 := rfl
theorem rcMarker_end : rcMarkerOut.2 = 256 := rfl

theorem rcInner_body : rcInnerMembers.pack 0 ⟨rcName "box",[.field 1,.field 1]⟩ account 64 =
    .ok (rcInnerOut.1,rcTagOut.2) := by
  refine recursive_fields_cons_ok rcXLeaf _ 0 ⟨rcName "box",[.field 1,.field 1]⟩ account 64 rcXOut.1 rcXOut.2 (rcYOut.1++rcTagOut.1) rcTagOut.2 ?_ ?_
  · exact checkedRecursivePack_of rcXLeaf _ _ _ _ _ rfl rcX_packed
  · rw [rcX_end]
    refine recursive_fields_cons_ok rcYLeaf _ 1 ⟨rcName "box",[.field 1,.field 1]⟩ account 96 rcYOut.1 rcYOut.2 rcTagOut.1 rcTagOut.2 ?_ ?_
    · exact checkedRecursivePack_of rcYLeaf _ _ _ _ _ rfl rcY_packed
    · rw [rcY_end]
      simpa only [List.append_nil] using
        recursive_fields_cons_ok rcTagLeaf .nil 2 ⟨rcName "box",[.field 1,.field 1]⟩ account 128 _ _ [] _
          (checkedRecursivePack_of rcTagLeaf _ _ _ _ _ rfl rcTag_packed) (RecursiveStorageFields.pack_nil _ _ _ _ _)

theorem rcInner_packed : rcInner.pack ⟨rcName "box",[.field 1,.field 1]⟩ account 34 = .ok rcInnerOut := by
  change alignFixedPack (rcInnerMembers.pack 0) ⟨rcName "box",[.field 1,.field 1]⟩ account 34 = .ok rcInnerOut
  unfold alignFixedPack
  rw [show roundSlot 34 = 64 from rfl,rcInner_body]
  rfl

theorem rcInner_end : rcInnerOut.2 = 160 := by rw [show rcInnerOut.2 = roundSlot rcTagOut.2 from rfl,rcTag_end]; rfl

theorem rcMid_body : rcMidMembers.pack 0 ⟨rcName "box",[.field 1]⟩ account 32 = .ok (rcMidOut.1,rcBoolOut.2) := by
  refine recursive_fields_cons_ok rcGuardLeaf _ 0 ⟨rcName "box",[.field 1]⟩ account 32 rcGuardOut.1 rcGuardOut.2 (rcInnerOut.1++rcBoolOut.1) rcBoolOut.2 ?_ ?_
  · exact checkedRecursivePack_of rcGuardLeaf _ _ _ _ _ rfl rcGuard_packed
  · rw [rcGuard_end]
    refine recursive_fields_cons_ok rcInner _ 1 ⟨rcName "box",[.field 1]⟩ account 34 rcInnerOut.1 rcInnerOut.2 rcBoolOut.1 rcBoolOut.2 ?_ ?_
    · exact checkedRecursivePack_of rcInner _ _ _ _ _ rfl rcInner_packed
    · rw [rcInner_end]
      simpa only [List.append_nil] using
        recursive_fields_cons_ok rcBoolLeaf .nil 2 ⟨rcName "box",[.field 1]⟩ account 160 _ _ [] _
          (checkedRecursivePack_of rcBoolLeaf _ _ _ _ _ rfl rcBool_packed) (RecursiveStorageFields.pack_nil _ _ _ _ _)

theorem rcMid_packed : rcMid.pack ⟨rcName "box",[.field 1]⟩ account 1 = .ok rcMidOut := by
  change alignFixedPack (rcMidMembers.pack 0) ⟨rcName "box",[.field 1]⟩ account 1 = .ok rcMidOut
  unfold alignFixedPack
  rw [show roundSlot 1 = 32 from rfl,rcMid_body]
  rfl

theorem rcMid_end : rcMidOut.2 = 192 := by rw [show rcMidOut.2 = roundSlot rcBoolOut.2 from rfl,rcBool_end]; rfl

theorem rcOuter_body : rcOuterMembers.pack 0 ⟨rcName "box",[]⟩ account 0 = .ok (rcOuterOut.1,rcWhoOut.2) := by
  refine recursive_fields_cons_ok rcStampLeaf _ 0 ⟨rcName "box",[]⟩ account 0 rcStampOut.1 rcStampOut.2 (rcMidOut.1++rcWhoOut.1) rcWhoOut.2 ?_ ?_
  · exact checkedRecursivePack_of rcStampLeaf _ _ _ _ _ rfl rcStamp_packed
  · rw [rcStamp_end]
    refine recursive_fields_cons_ok rcMid _ 1 ⟨rcName "box",[]⟩ account 1 rcMidOut.1 rcMidOut.2 rcWhoOut.1 rcWhoOut.2 ?_ ?_
    · exact checkedRecursivePack_of rcMid _ _ _ _ _ rfl rcMid_packed
    · rw [rcMid_end]
      simpa only [List.append_nil] using
        recursive_fields_cons_ok rcWhoLeaf .nil 2 ⟨rcName "box",[]⟩ account 192 _ _ [] _
          (checkedRecursivePack_of rcWhoLeaf _ _ _ _ _ rfl rcWho_packed) (RecursiveStorageFields.pack_nil _ _ _ _ _)

theorem rcOuter_packed : rcOuter.pack ⟨rcName "box",[]⟩ account 0 = .ok rcOuterOut := by
  change alignFixedPack (rcOuterMembers.pack 0) ⟨rcName "box",[]⟩ account 0 = .ok rcOuterOut
  unfold alignFixedPack
  rw [show roundSlot 0 = 0 from rfl,rcOuter_body]
  rfl

theorem rcOuter_end : rcOuterOut.2 = 224 := by rw [show rcOuterOut.2 = roundSlot rcWhoOut.2 from rfl,rcWho_end]; rfl

theorem rcDeclarations_packed : rcDeclarations.pack account 0 = .ok rcRootOut := by
  unfold rcDeclarations
  rw [RecursiveRootDeclarations.pack_cons,if_pos (show rcEnv.rootTy (rcName "box") = some (.struct .storage (rcTypeName "OuterR")) from rfl),rcOuter_packed]
  simp only [Except.bind]
  change ((RecursiveRootDeclarations.cons rcMarkerLeaf .nil).pack account rcOuterOut.2).map (fun out => (rcOuterOut.1++out.1,out.2)) = _
  rw [rcOuter_end,RecursiveRootDeclarations.pack_cons,if_pos (show rcEnv.rootTy (rcName "marker") = some (.int .u256) from rfl),rcMarker_packed]
  change (Except.ok (rcOuterOut.1++(rcMarkerOut.1++[]),rcMarkerOut.2) : Except DeclarationPackingError (List (ScalarPath rcEnv.layout (rcEnv.lay account)) × Nat)) = .ok rcRootOut
  rw [List.append_nil]
  rfl

end Solidity.Yul.Views.Controls
