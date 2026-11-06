import Solidity.Yul.Views.RecursiveStorageEquations

namespace Solidity.Yul.Views.Controls

def rcU16 : Source.IntTy := ⟨false,16,by decide⟩
def rcI24 : Source.IntTy := ⟨true,24,by decide⟩
def rcBytes : DynamicScalarKind := .fixedBytes 3 (by decide)
def rcAddress : DynamicScalarKind := .address false
def rcName (s : String) : Source.DeclName := ⟨some "RC",s⟩
def rcPath (s : String) : Source.SPath := ⟨rcName s,[]⟩
def rcTypeName (s : String) : Source.DeclName := ⟨none,s⟩
def rcEnv : Source.Env := ⟨[
  ⟨.contract,"RC",none,true,.contract false "RC" .none .nil .nil⟩,
  ⟨.struct,"InnerR",none,true,.struct "InnerR" (.structMember (.array (.elem (.int false 16 (by decide))) .none) "xs")
    (.cons (.structMember (.array (.elem (.int true 24 (by decide))) .none) "ys")
    (.cons (.structMember (.elem (.fixedBytes 3 (by decide))) "tag") .nil))⟩,
  ⟨.struct,"MidR",none,true,.struct "MidR" (.structMember (.elem (.int false 16 (by decide))) "guard")
    (.cons (.structMember (.userType ⟨"InnerR",[]⟩) "inner")
    (.cons (.structMember (.array (.elem .bool) .none) "bs") .nil))⟩,
  ⟨.struct,"OuterR",none,true,.struct "OuterR" (.structMember (.elem (.int false 8 (by decide))) "stamp")
    (.cons (.structMember (.userType ⟨"MidR",[]⟩) "mid")
    (.cons (.structMember (.elem .address) "who") .nil))⟩,
  ⟨.stateVar,"box",some "RC",false,.stateVar (.userType ⟨"OuterR",[]⟩) none none none false "box" .none⟩,
  ⟨.stateVar,"marker",some "RC",false,.stateVar (.elem (.int false 256 (by decide))) none none none false "marker" .none⟩]⟩
def rcInnerTypes : List (String × Source.STy) := [("xs",.array .storage (.int rcU16) none),("ys",.array .storage (.int rcI24) none),("tag",rcBytes.ty)]
def rcInnerMembers : RecursiveStorageFields rcEnv (rcInnerTypes.map Prod.snd) true :=
  .cons (.leaf (.packedUnsignedArray rcU16 rfl (by decide))) (.cons (.leaf (.signedArray rcI24 rfl)) (.cons (.leaf (.fixed (.scalar rcBytes.ty rfl))) .nil))
def rcInner : RecursiveStorageDeclaration rcEnv (.struct .storage (rcTypeName "InnerR")) true :=
  .strct (rcTypeName "InnerR") rcInnerTypes rfl rcInnerMembers

def rcMidTypes : List (String × Source.STy) := [("guard",.int rcU16),("inner",.struct .storage (rcTypeName "InnerR")),("bs",.array .storage .bool none)]
def rcMidMembers : RecursiveStorageFields rcEnv (rcMidTypes.map Prod.snd) true :=
  .cons (.leaf (.fixed (.scalar (.int rcU16) rfl))) (.cons rcInner (.cons (.leaf (.scalarArray .bool)) .nil))
def rcMid : RecursiveStorageDeclaration rcEnv (.struct .storage (rcTypeName "MidR")) true :=
  .strct (rcTypeName "MidR") rcMidTypes rfl rcMidMembers

def rcOuterTypes : List (String × Source.STy) := [("stamp",.int ⟨false,8,by decide⟩),("mid",.struct .storage (rcTypeName "MidR")),("who",rcAddress.ty)]
def rcOuterMembers : RecursiveStorageFields rcEnv (rcOuterTypes.map Prod.snd) true :=
  .cons (.leaf (.fixed (.scalar (.int ⟨false,8,by decide⟩) rfl))) (.cons rcMid (.cons (.leaf (.fixed (.scalar rcAddress.ty rfl))) .nil))
def rcOuter : RecursiveStorageDeclaration rcEnv (.struct .storage (rcTypeName "OuterR")) true :=
  .strct (rcTypeName "OuterR") rcOuterTypes rfl rcOuterMembers

def rcTypes : List (Source.DeclName × Source.STy) := [(rcName "box",.struct .storage (rcTypeName "OuterR")),(rcName "marker",.int .u256)]
def rcDeclarations : RecursiveRootDeclarations rcEnv rcTypes := .cons rcOuter (.cons (.leaf (.fixed (.scalar (.int .u256) rfl))) .nil)

end Solidity.Yul.Views.Controls
