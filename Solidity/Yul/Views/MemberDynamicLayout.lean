import Solidity.Yul.Views.MemberOwnershipResidual

-- Serialize concrete proof elaboration to bound pending computed-state memory.
set_option Elab.async false

namespace Solidity.Yul.Views.Controls

def mdU16 : Source.IntTy := ⟨false,16,by decide⟩
def mdI24 : Source.IntTy := ⟨true,24,by decide⟩
def mdBytes : DynamicScalarKind := .fixedBytes 3 (by decide)
def mdAddress : DynamicScalarKind := .address false
def mdName (s : String) : Source.DeclName := ⟨some "ND",s⟩
def mdPath (s : String) : Source.SPath := ⟨mdName s,[]⟩
def mdStruct : Source.DeclName := ⟨none,"S"⟩
def mdEnv : Source.Env := ⟨[
  ⟨.contract,"ND",none,true,.contract false "ND" .none .nil .nil⟩,
  ⟨.struct,"S",none,true,.struct "S" (.structMember (.elem (.int false 16 (by decide))) "guard")
    (.cons (.structMember (.array (.elem (.int false 16 (by decide))) .none) "xs")
    (.cons (.structMember (.array (.elem (.int true 24 (by decide))) .none) "ys")
    (.cons (.structMember (.elem (.fixedBytes 3 (by decide))) "tag")
    (.cons (.structMember (.elem .address) "who") .nil))))⟩,
  ⟨.stateVar,"box",some "ND",false,.stateVar (.userType ⟨"S",[]⟩) none none none false "box" .none⟩,
  ⟨.stateVar,"top",some "ND",false,.stateVar (.array (.elem .bool) .none) none none none false "top" .none⟩,
  ⟨.stateVar,"marker",some "ND",false,.stateVar (.elem (.int false 256 (by decide))) none none none false "marker" .none⟩]⟩
def mdFields : List (String × Source.STy) := [("guard",.int mdU16),("xs",.array .storage (.int mdU16) none),
  ("ys",.array .storage (.int mdI24) none),("tag",mdBytes.ty),("who",mdAddress.ty)]
def mdMembers : MemberStorageDeclarations mdEnv (mdFields.map Prod.snd) :=
  .cons (.fixed (.scalar (.int mdU16) rfl)) (.cons (.packedUnsignedArray mdU16 rfl (by decide))
    (.cons (.signedArray mdI24 rfl) (.cons (.fixed (.scalar mdBytes.ty rfl))
      (.cons (.fixed (.scalar mdAddress.ty rfl)) .nil))))
def mdTypes : List (Source.DeclName × Source.STy) := [(mdName "box",.struct .storage mdStruct),
  (mdName "top",.array .storage .bool none),(mdName "marker",.int .u256)]
def mdDeclarations : RootMemberDeclarations mdEnv mdTypes :=
  .cons (.strct mdStruct mdFields rfl mdMembers rfl)
    (.cons (.leaf (.scalarArray .bool)) (.cons (.leaf (.fixed (.scalar (.int .u256) rfl))) .nil))
theorem md_ready : (prepareMemberComputedStorage mdDeclarations "ND" account).toOption.isSome := by decide
def mdLayout := (prepareMemberComputedStorage mdDeclarations "ND" account).toOption.get md_ready

end Solidity.Yul.Views.Controls
