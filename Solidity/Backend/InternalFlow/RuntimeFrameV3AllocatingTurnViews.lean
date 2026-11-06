import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingDeclarationCheck

/-! Executable recognition of an allocating conditional root. The result keeps
its actual guard, continuation and alternative branch, with an exact syntax
reconstruction. It does not recognize the recursive child or prove execution,
compiler selection, admission or approved-domain provenance. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews
open Evm Evm.Memory AllocatingHeadViews

structure ClosedConditional {C : Contract} {Γ : Ctx} (source : Stmt C Γ Γ) : Type where
 condition : Val C Γ .bool
 left : Prog C Γ Γ
 right : Prog C Γ Γ
 shape : source=.ite condition left right

def closeConditional {C : Contract} {Γ : Ctx} {source : Stmt C Γ Γ}
 (view : Conditional source) (leftEq : view.leftCtx=Γ) (rightEq : view.rightCtx=Γ) :
 ClosedConditional source := by
 rcases view with ⟨leftCtx,rightCtx,condition,left,right,output,shape⟩
 simp only [] at leftEq rightEq
 subst leftCtx
 subst rightCtx
 exact ⟨condition,left,right,eq_of_heq shape⟩

def readClosedConditional {C : Contract} {Γ : Ctx} (source : Stmt C Γ Γ) :
 Option (ClosedConditional source) := do
 let view ← readConditional source
 if leftEq : view.leftCtx=Γ then
   if rightEq : view.rightCtx=Γ then
     pure (closeConditional view leftEq rightEq)
   else none
 else none

structure Turn {C : Contract} {Γ : Ctx} (source : Prog C Γ Γ) : Type where
 condition : Val C Γ .bool
 continuation : Prog C Γ Γ
 alternative : Prog C Γ Γ
 shape : source=.cons (.ite condition
   (.cons AllocatingDeclarationCheck.allocation continuation) alternative) .nil

def assemble {C : Contract} {Γ : Ctx} {source : Prog C Γ Γ}
 (root : AllocatingSourceViews.ClosedCons source)
 (branch : ClosedConditional root.head)
 (ending : NilView root.tail)
 (positive : AllocatingSourceViews.ClosedCons branch.left)
 (allocation : positive.head=AllocatingDeclarationCheck.allocation) : Turn source := by
 refine ⟨branch.condition,positive.tail,branch.right,?_⟩
 simp only [root.shape,branch.shape,positive.shape,allocation,eq_of_heq ending.shape]

def read {C : Contract} {Γ : Ctx} (source : Prog C Γ Γ) : Option (Turn source) := do
 let root ← AllocatingSourceViews.readClosedCons source
 let branch ← readClosedConditional root.head
 let ending ← readNil root.tail
 let positive ← AllocatingSourceViews.readClosedCons branch.left
 let allocation ← AllocatingDeclarationCheck.check positive.head
 pure (assemble root branch ending positive allocation.down)

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.closeConditional' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.closeConditional
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.assemble' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.assemble
