import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingCallViews

/-! Exact original allocating-recursion arguments and scalar return binding.
All fields come from actual typed views; names, contexts, reference types and
slots are checked metadata. No source equivalence or execution is assumed. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallLeaves
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource AllocatingCallViews

structure UintArgument {C : Contract} {R : RefTy} (source : Args C (Frame R) (Parameters R)) : Type where
 previous : Args C (Frame R) [.mem R]
 name : Var
 value : Val C (Frame R) .uint
 shape : source=.snoc previous .uint name value

def closeUintArgument {C : Contract} {R : RefTy} {source : Args C (Frame R) (Parameters R)}
 (view : PrimitiveArgument source) (primitiveEq : view.primitive=.uint)
 (previousEq : view.previousCtx=[.mem R]) : UintArgument source := by
 rcases view with ⟨previousCtx,previous,primitive,name,value,output,shape⟩
 simp only [] at primitiveEq previousEq
 subst primitive
 subst previousCtx
 exact ⟨previous,name,value,eq_of_heq shape⟩

structure AliasArgument {C : Contract} {R : RefTy} (source : Args C (Frame R) [.mem R]) : Type where
 previous : Args C (Frame R) []
 name : Var
 value : MPath C (Frame R) (.ref R)
 shape : source=.snocMemory previous R name value

def closeAliasArgument {C : Contract} {R : RefTy} {source : Args C (Frame R) [.mem R]}
 (view : MemoryArgument source) (referenceEq : view.reference=R)
 (previousEq : view.previousCtx=[]) : AliasArgument source := by
 rcases view with ⟨previousCtx,previous,reference,name,value,output,shape⟩
 simp only [] at referenceEq previousEq
 subst reference
 subst previousCtx
 exact ⟨previous,name,value,eq_of_heq shape⟩

structure Variable {C : Contract} {R : RefTy} (source : MPath C (Frame R) (.ref R)) : Type where
 slot : Idx (Frame R) (.mem R)
 memoryFree : (Ty.ref R).mapFree=true
 shape : source=.var slot memoryFree

def closeVariable {C : Contract} {R : RefTy} {source : MPath C (Frame R) (.ref R)}
 (view : MemoryVariable source) (referenceEq : view.reference=R) : Variable source := by
 rcases view with ⟨reference,slot,memoryFree,output,shape⟩
 simp only [] at referenceEq
 subst reference
 exact ⟨slot,memoryFree,eq_of_heq shape⟩

def checkAlias {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (source : Args C (Frame R) [.mem R]) :
 Option (PLift (source=.snocMemory .nil R (.user "alias") (.var (.there (.there .here)) hm))) := do
 let observed ← readMemoryArgument source
 if referenceEq : observed.reference=R then
   if previousEq : observed.previousCtx=[] then
     let view := closeAliasArgument observed referenceEq previousEq
     let empty ← readNilArguments view.previous
     let rawVariable ← readMemoryVariable view.value
     if variableType : rawVariable.reference=R then
       let selectedVariable := closeVariable rawVariable variableType
       if nameEq : view.name=.user "alias" then
         if slotEq : selectedVariable.slot=.there (.there .here) then
           pure ⟨by simp only [view.shape,eq_of_heq empty.down,selectedVariable.shape,nameEq,slotEq]⟩
         else none
       else none
     else none
   else none
 else none

def checkNext {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (source : Args C (Frame R) (Parameters R)) : Option (PLift (source=next R hm)) := do
 let observed ← readPrimitiveArgument source
 if primitiveEq : observed.primitive=.uint then
   if previousEq : observed.previousCtx=[.mem R] then
     let view := closeUintArgument observed primitiveEq previousEq
     let aliasEq ← checkAlias hm view.previous
     let valueEq ← AllocatingScalarLeaves.binary view.value .sub rfl rfl (.there .here) 1 rfl
     if nameEq : view.name=.user "count" then
       pure ⟨by simp only [view.shape,aliasEq.down,valueEq.down,nameEq,ScalarRecursiveSource.next]⟩
     else none
   else none
 else none

structure Return {R : RefTy} (source : CallRet (Frame R) [.val .uint] (Frame R)) : Type where
 name : Var
 destination : Option (Idx (Frame R) (.val .uint))
 shape : source=.val .uint name destination

def closeReturn {R : RefTy} {source : CallRet (Frame R) [.val .uint] (Frame R)}
 (view : ValueReturn source) (primitiveEq : view.primitive=.uint) : Return source := by
 rcases view with ⟨primitive,name,destination,results,output,shape⟩
 simp only [] at primitiveEq
 subst primitive
 exact ⟨name,destination,eq_of_heq shape⟩

def checkResult {R : RefTy} (source : CallRet (Frame R) [.val .uint] (Frame R)) :
 Option (PLift (source=result R)) := do
 let observed ← readValueReturn source
 if primitiveEq : observed.primitive=.uint then
   let view := closeReturn observed primitiveEq
   if nameEq : view.name=.user "result" then
     if destinationEq : view.destination=some .here then
       pure ⟨by simp only [view.shape,nameEq,destinationEq,ScalarRecursiveSource.result]⟩
     else none
   else none
 else none

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallLeaves
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallLeaves.closeUintArgument' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallLeaves.closeUintArgument
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallLeaves.closeAliasArgument' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallLeaves.closeAliasArgument
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallLeaves.closeVariable' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallLeaves.closeVariable
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallLeaves.closeReturn' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallLeaves.closeReturn
