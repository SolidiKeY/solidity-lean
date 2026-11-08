import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarLeaves

/-! Actual intrinsic argument, memory-variable and return views. All readers
use recursors whose motives generalize the family indices. Names and types
remain payload metadata, and every result carries its constructor equation. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallViews

structure PrimitiveArgument {C : Contract} {Γ ps : Ctx} (source : Args C Γ ps) : Type where
 previousCtx : Ctx
 previous : Args C Γ previousCtx
 primitive : PrimTy
 name : Var
 value : Val C Γ primitive
 output : ps=.val primitive::previousCtx
 shape : HEq source (Args.snoc previous primitive name value)

def readPrimitiveArgument {C : Contract} {Γ ps : Ctx} (source : Args C Γ ps) : Option (PrimitiveArgument source) :=
 Args.casesOn (motive:=fun _ source => Option (PrimitiveArgument source)) source
   (nil:=none) (snoc:=fun previous primitive name value => some ⟨_,previous,primitive,name,value,rfl,HEq.rfl⟩)
   (snocStorage:=by intros;exact none) (snocMemory:=by intros;exact none)

structure MemoryArgument {C : Contract} {Γ ps : Ctx} (source : Args C Γ ps) : Type where
 previousCtx : Ctx
 previous : Args C Γ previousCtx
 reference : RefTy
 name : Var
 value : MPath C Γ (.ref reference)
 output : ps=.mem reference::previousCtx
 shape : HEq source (Args.snocMemory previous reference name value)

def readMemoryArgument {C : Contract} {Γ ps : Ctx} (source : Args C Γ ps) : Option (MemoryArgument source) :=
 Args.casesOn (motive:=fun _ source => Option (MemoryArgument source)) source
   (nil:=none) (snoc:=by intros;exact none) (snocStorage:=by intros;exact none)
   (snocMemory:=fun previous reference name value => some ⟨_,previous,reference,name,value,rfl,HEq.rfl⟩)

def readNilArguments {C : Contract} {Γ ps : Ctx} (source : Args C Γ ps) :
 Option (PLift (HEq source (Args.nil : Args C Γ []))) :=
 Args.casesOn (motive:=fun _ source => Option (PLift (HEq source (Args.nil : Args C Γ [])))) source
   (nil:=some ⟨HEq.rfl⟩) (snoc:=by intros;exact none)
   (snocStorage:=by intros;exact none) (snocMemory:=by intros;exact none)

structure MemoryVariable {C : Contract} {Γ : Ctx} {T : Ty} (source : MPath C Γ T) : Type where
 reference : RefTy
 slot : Idx Γ (.mem reference)
 memoryFree : (Ty.ref reference).mapFree=true
 output : T=.ref reference
 shape : HEq source (MPath.var (C:=C) slot memoryFree)

def readMemoryVariable {C : Contract} {Γ : Ctx} {T : Ty} (source : MPath C Γ T) : Option (MemoryVariable source) :=
 MPath.casesOn (motive_3:=fun _ source => Option (MemoryVariable source)) source
   (var:=fun slot memoryFree => some ⟨_,slot,memoryFree,rfl,HEq.rfl⟩)
   (loc:=by intros;exact none)

structure ValueReturn {Γ rs Δ : Ctx} (source : CallRet Γ rs Δ) : Type where
 primitive : PrimTy
 name : Var
 destination : Option (Idx Γ (.val primitive))
 results : rs=[.val primitive]
 output : Δ=Γ
 shape : HEq source (CallRet.val primitive name destination)

def readValueReturn {Γ rs Δ : Ctx} (source : CallRet Γ rs Δ) : Option (ValueReturn source) :=
 CallRet.casesOn (motive:=fun _ _ source => Option (ValueReturn source)) source
   (none:=none) (val:=fun primitive name destination => some ⟨primitive,name,destination,rfl,rfl,HEq.rfl⟩)
   (rets:=by intros;exact none) (mem:=by intros;exact none) (storage:=by intros;exact none)

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallViews
