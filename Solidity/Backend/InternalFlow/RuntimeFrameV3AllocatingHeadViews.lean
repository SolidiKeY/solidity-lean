import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingSourceViews

/-! Typed, context-generalized statement-head views for allocating recursion.
All payloads refer to actual intrinsic syntax and carry constructor equations.
No source/target semantics, erased IR or admission is introduced. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

structure Conditional {C : Contract} {Γ Δ : Ctx} (source : Stmt C Γ Δ) : Type where
 leftCtx : Ctx
 rightCtx : Ctx
 condition : Val C Γ .bool
 left : Prog C Γ leftCtx
 right : Prog C Γ rightCtx
 output : Δ=Γ
 shape : HEq source (Stmt.ite condition left right)

structure RecursiveCall {C : Contract} {Γ Δ : Ctx} (source : Stmt C Γ Δ) : Type where
 parameters : Ctx
 results : Ctx
 function : Name
 index : Nat
 arguments : Args C Γ parameters
 ret : CallRet Γ results Δ
 child : Unit → Prog C (results++parameters) (results++parameters)
 shape : source=.callRec function index arguments ret child

structure Block {C : Contract} {Γ Δ : Ctx} (source : Stmt C Γ Δ) : Type where
 inside : Ctx
 body : Prog C Γ inside
 output : Δ=Γ
 shape : HEq source (Stmt.block body)

structure MemoryDeclaration {C : Contract} {Γ Δ : Ctx} (source : Stmt C Γ Δ) : Type where
 reference : RefTy
 name : Var
 initial : Option (MRhs C Γ reference)
 defaultAllowed : (initial.isSome || (Ty.ref reference).defaultOkS)=true
 memoryFree : (Ty.ref reference).mapFree=true
 output : Δ=.mem reference::Γ
 shape : HEq source (Stmt.declMem reference name initial defaultAllowed memoryFree)

structure LocalAssignment {C : Contract} {Γ Δ : Ctx} (source : Stmt C Γ Δ) : Type where
 primitive : PrimTy
 slot : Idx Γ (.val primitive)
 value : Val C Γ primitive
 output : Δ=Γ
 shape : HEq source (Stmt.assignLocal slot value)

inductive Head {C : Contract} {Γ Δ : Ctx} (source : Stmt C Γ Δ) : Type where
 | conditional (observed : Conditional source)
 | recursiveCall (observed : RecursiveCall source)
 | block (observed : Block source)
 | memoryDeclaration (observed : MemoryDeclaration source)
 | localAssignment (observed : LocalAssignment source)

def read {C : Contract} {Γ Δ : Ctx} (source : Stmt C Γ Δ) : Option (Head source) :=
 Stmt.casesOn (motive_1:=fun _ _ source => Option (Head source)) source
   (assign := by intros;exact none)
   (rebind := by intros;exact none)
   (assignLocal := fun slot value => some (.localAssignment ⟨_,slot,value,rfl,HEq.rfl⟩))
   (declLocal := by intros;exact none)
   (declStorage := by intros;exact none)
   (opAssign := by intros;exact none)
   (incDec := by intros;exact none)
   (assignIncDec := by intros;exact none)
   (assignLocalPush := by intros;exact none)
   (push := by intros;exact none)
   (pop := by intros;exact none)
   (transfer := by intros;exact none)
   (send := by intros;exact none)
   (declMem := fun reference name initial defaultAllowed memoryFree => some (.memoryDeclaration ⟨reference,name,initial,defaultAllowed,memoryFree,rfl,HEq.rfl⟩))
   (rebindMem := by intros;exact none)
   (assignFromMem := by intros;exact none)
   (assignMem := by intros;exact none)
   (delete := by intros;exact none)
   (deleteMem := by intros;exact none)
   (assignNew := by intros;exact none)
   (ite := fun condition left right => some (.conditional ⟨_,_,condition,left,right,rfl,HEq.rfl⟩))
   (require := by intros;exact none)
   (assert := by intros;exact none)
   (revert := by intros;exact none)
   (assumeFalse := by intros;exact none)
   (call := by intros;exact none)
   (tryCall := by intros;exact none)
   (loop := by intros;exact none)
   (block := fun body => some (.block ⟨_,body,rfl,HEq.rfl⟩))
   (pushOpAssign := by intros;exact none)
   (pushIncDec := by intros;exact none)
   (callReceiver := by intros;exact none)
   (callReceiverPush := by intros;exact none)
   (callRec := fun function index arguments ret child => some (.recursiveCall ⟨_,_,function,index,arguments,ret,child,rfl⟩))
   (revertData := by intros;exact none)
   (catchData := by intros;exact none)

def readConditional {C : Contract} {Γ Δ : Ctx} (source : Stmt C Γ Δ) : Option (Conditional source) := do
 let observed ← read source
 match observed with
 | .conditional found => some found
 | _ => none

def readRecursiveCall {C : Contract} {Γ Δ : Ctx} (source : Stmt C Γ Δ) : Option (RecursiveCall source) := do
 let observed ← read source
 match observed with
 | .recursiveCall found => some found
 | _ => none

def readBlock {C : Contract} {Γ Δ : Ctx} (source : Stmt C Γ Δ) : Option (Block source) := do
 let observed ← read source
 match observed with
 | .block found => some found
 | _ => none

def readMemoryDeclaration {C : Contract} {Γ Δ : Ctx} (source : Stmt C Γ Δ) : Option (MemoryDeclaration source) := do
 let observed ← read source
 match observed with
 | .memoryDeclaration found => some found
 | _ => none

def readLocalAssignment {C : Contract} {Γ Δ : Ctx} (source : Stmt C Γ Δ) : Option (LocalAssignment source) := do
 let observed ← read source
 match observed with
 | .localAssignment found => some found
 | _ => none

structure NilView {C : Contract} {Γ Δ : Ctx} (source : Prog C Γ Δ) : Type where
 output : Δ=Γ
 shape : HEq source (.nil : Prog C Γ Γ)

def readNil {C : Contract} {Γ Δ : Ctx} (source : Prog C Γ Δ) : Option (NilView source) :=
 Prog.casesOn (motive_2:=fun _ _ source => Option (NilView source)) source
   (some ⟨rfl,HEq.rfl⟩) (fun _ _ => none)

structure Literal {C : Contract} {Γ : Ctx} {p : PrimTy} (source : Simple C Γ p) : Type where
 number : Int
 valid : p.inRange number=true
 shape : source=.lit number valid

def readLiteral {C : Contract} {Γ : Ctx} {p : PrimTy} (source : Simple C Γ p) : Option (Literal source) :=
 Simple.casesOn (motive:=fun _ source => Option (Literal source)) source
   (lit:=fun number valid => some ⟨number,valid,rfl⟩)
   (bool:=fun _ => none) («local»:=fun _ => none) (env:=fun _ _ => none)

structure NewArray {C : Contract} {Γ : Ctx} {R : RefTy} (source : MRhs C Γ R) : Type where
 length : Simple C Γ .uint
 allowed : R.newArrOk=true
 shape : source=.newArr length allowed

def readNewArray {C : Contract} {Γ : Ctx} {R : RefTy} (source : MRhs C Γ R) : Option (NewArray source) :=
 MRhs.casesOn (motive:=fun source => Option (NewArray source)) source
   (alias:=fun _ => none) (copy:=fun _ _ => none) (newArr:=fun length allowed => some ⟨length,allowed,rfl⟩)

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews
