import Solidity.Yul.Views.RecursiveDynamicMetadata

namespace Solidity.Yul.Views.Controls

def rcXPath : Source.SPath := ⟨rcName "box",[.field 1,.field 1,.field 0]⟩
def rcYPath : Source.SPath := ⟨rcName "box",[.field 1,.field 1,.field 1]⟩
def rcBPath : Source.SPath := ⟨rcName "box",[.field 1,.field 2]⟩
def rcStampLeaf := RecursiveStorageDeclaration.leaf (E := rcEnv) (.fixed (.scalar (.int ⟨false,8,by decide⟩) rfl))
theorem rcStamp_ready : (rcStampLeaf.pack ⟨rcName "box",[.field 0]⟩ account 0).toOption.isSome := by decide
def rcStampOut := (rcStampLeaf.pack ⟨rcName "box",[.field 0]⟩ account 0).toOption.get rcStamp_ready
theorem rcStamp_packed : rcStampLeaf.pack ⟨rcName "box",[.field 0]⟩ account 0 = .ok rcStampOut := except_computed_value _ rcStamp_ready
def rcGuardLeaf := RecursiveStorageDeclaration.leaf (E := rcEnv) (.fixed (.scalar (.int rcU16) rfl))
theorem rcGuard_ready : (rcGuardLeaf.pack ⟨rcName "box",[.field 1,.field 0]⟩ account 32).toOption.isSome := by decide
def rcGuardOut := (rcGuardLeaf.pack ⟨rcName "box",[.field 1,.field 0]⟩ account 32).toOption.get rcGuard_ready
theorem rcGuard_packed : rcGuardLeaf.pack ⟨rcName "box",[.field 1,.field 0]⟩ account 32 = .ok rcGuardOut := except_computed_value _ rcGuard_ready
def rcXLeaf := RecursiveStorageDeclaration.leaf (E := rcEnv) (.packedUnsignedArray rcU16 rfl (by decide))
theorem rcX_ready : (rcXLeaf.pack rcXPath account 64).toOption.isSome := by decide
def rcXOut := (rcXLeaf.pack rcXPath account 64).toOption.get rcX_ready
theorem rcX_packed : rcXLeaf.pack rcXPath account 64 = .ok rcXOut := except_computed_value _ rcX_ready
def rcYLeaf := RecursiveStorageDeclaration.leaf (E := rcEnv) (.signedArray rcI24 rfl)
theorem rcY_ready : (rcYLeaf.pack rcYPath account 96).toOption.isSome := by decide
def rcYOut := (rcYLeaf.pack rcYPath account 96).toOption.get rcY_ready
theorem rcY_packed : rcYLeaf.pack rcYPath account 96 = .ok rcYOut := except_computed_value _ rcY_ready
def rcTagLeaf := RecursiveStorageDeclaration.leaf (E := rcEnv) (.fixed (.scalar rcBytes.ty rfl))
theorem rcTag_ready : (rcTagLeaf.pack ⟨rcName "box",[.field 1,.field 1,.field 2]⟩ account 128).toOption.isSome := by decide
def rcTagOut := (rcTagLeaf.pack ⟨rcName "box",[.field 1,.field 1,.field 2]⟩ account 128).toOption.get rcTag_ready
theorem rcTag_packed : rcTagLeaf.pack ⟨rcName "box",[.field 1,.field 1,.field 2]⟩ account 128 = .ok rcTagOut := except_computed_value _ rcTag_ready
def rcBoolLeaf := RecursiveStorageDeclaration.leaf (E := rcEnv) (.scalarArray .bool)
theorem rcBool_ready : (rcBoolLeaf.pack rcBPath account 160).toOption.isSome := by decide
def rcBoolOut := (rcBoolLeaf.pack rcBPath account 160).toOption.get rcBool_ready
theorem rcBool_packed : rcBoolLeaf.pack rcBPath account 160 = .ok rcBoolOut := except_computed_value _ rcBool_ready
def rcWhoLeaf := RecursiveStorageDeclaration.leaf (E := rcEnv) (.fixed (.scalar rcAddress.ty rfl))
theorem rcWho_ready : (rcWhoLeaf.pack ⟨rcName "box",[.field 2]⟩ account 192).toOption.isSome := by decide
def rcWhoOut := (rcWhoLeaf.pack ⟨rcName "box",[.field 2]⟩ account 192).toOption.get rcWho_ready
theorem rcWho_packed : rcWhoLeaf.pack ⟨rcName "box",[.field 2]⟩ account 192 = .ok rcWhoOut := except_computed_value _ rcWho_ready
def rcMarkerLeaf := RecursiveStorageDeclaration.leaf (E := rcEnv) (.fixed (.scalar (.int .u256) rfl))
theorem rcMarker_ready : (rcMarkerLeaf.pack ⟨rcName "marker",[]⟩ account 224).toOption.isSome := by decide
def rcMarkerOut := (rcMarkerLeaf.pack ⟨rcName "marker",[]⟩ account 224).toOption.get rcMarker_ready
theorem rcMarker_packed : rcMarkerLeaf.pack ⟨rcName "marker",[]⟩ account 224 = .ok rcMarkerOut := except_computed_value _ rcMarker_ready

def rcInnerOut := (rcXOut.1 ++ (rcYOut.1 ++ rcTagOut.1),roundSlot rcTagOut.2)
def rcMidOut := (rcGuardOut.1 ++ (rcInnerOut.1 ++ rcBoolOut.1),roundSlot rcBoolOut.2)
def rcOuterOut := (rcStampOut.1 ++ (rcMidOut.1 ++ rcWhoOut.1),roundSlot rcWhoOut.2)
def rcRootOut := (rcOuterOut.1 ++ rcMarkerOut.1,rcMarkerOut.2)

end Solidity.Yul.Views.Controls
