import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingValueViews

/-! Exact scalar leaves for allocating-recursion recognition. Checks consume
actual generalized views and compare only literal/operator/slot metadata.
Returned equalities are syntactic, with no run, compiler or profile premise. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource AllocatingValueViews

def literal {C : Contract} {Γ : Ctx} (source : Val C Γ .uint) (number : Int)
 (valid : PrimTy.uint.inRange number=true) : Option (PLift (source=.simple (.lit number valid))) := do
 let simple ← readSimple source
 let observed ← AllocatingHeadViews.readLiteral simple.value
 if same : observed.number=number then
   pure ⟨by simp only [simple.shape,observed.shape,same]⟩
 else none

def localValue {C : Contract} {Γ : Ctx} (source : Val C Γ .uint) (slot : Idx Γ (.val .uint)) :
 Option (PLift (source=.simple (.local slot))) := do
 let simple ← readSimple source
 let observed ← readLocal simple.value
 if same : observed.slot=slot then
   pure ⟨by simp only [simple.shape,observed.shape,same]⟩
 else none

theorem binary_eq {C : Contract} {Γ : Ctx} {q : PrimTy} {source : Val C Γ q}
 (view : UintBinary source) (op : BinOp) (accepted : op.accepts .uint=true) (output : op.ret .uint=q)
 (same : view.operator=op) (slot : Idx Γ (.val .uint)) (number : Int) (valid : PrimTy.uint.inRange number=true)
 (left : view.left=.simple (.local slot)) (right : view.right=.simple (.lit number valid)) :
 source=.binop op accepted output (.simple (.local slot)) (.simple (.lit number valid)) := by
 simp only [view.shape,same,left,right]

def binary {C : Contract} {Γ : Ctx} {q : PrimTy} (source : Val C Γ q)
 (op : BinOp) (accepted : op.accepts .uint=true) (output : op.ret .uint=q)
 (slot : Idx Γ (.val .uint)) (number : Int) (valid : PrimTy.uint.inRange number=true) :
 Option (PLift (source=.binop op accepted output (.simple (.local slot)) (.simple (.lit number valid)))) := do
 let view ← readUintBinary source
 if same : view.operator=op then
   let left ← localValue view.left slot
   let right ← literal view.right number valid
   pure ⟨binary_eq view op accepted output same slot number valid left.down right.down⟩
 else none

structure Assignment {C : Contract} {Γ : Ctx} (source : Stmt C Γ Γ) : Type where
 slot : Idx Γ (.val .uint)
 value : Val C Γ .uint
 shape : source=.assignLocal slot value

def closeAssignment {C : Contract} {Γ : Ctx} {source : Stmt C Γ Γ}
 (view : AllocatingHeadViews.LocalAssignment source) (same : view.primitive=.uint) : Assignment source := by
 rcases view with ⟨primitive,slot,value,output,shape⟩
 simp only [] at same
 subst primitive
 exact ⟨slot,value,eq_of_heq shape⟩

def assignment {C : Contract} {Γ : Ctx} (source : Stmt C Γ Γ)
 (slot : Idx Γ (.val .uint)) (expected : Val C Γ .uint)
 (check : (actual : Val C Γ .uint) → Option (PLift (actual=expected))) :
 Option (PLift (source=.assignLocal slot expected)) := do
 let observed ← AllocatingHeadViews.readLocalAssignment source
 if sameType : observed.primitive=.uint then
   let view := closeAssignment observed sameType
   if sameSlot : view.slot=slot then
     let valueEq ← check view.value
     pure ⟨by simp only [view.shape,sameSlot,valueEq.down]⟩
   else none
 else none

def checkGuard {C : Contract} {R : RefTy} (source : Val C (Frame R) .bool) :
 Option (PLift (source=ScalarRecursiveSource.guard)) :=
 binary source .gt rfl rfl (.there .here) 0 rfl

def checkZero {C : Contract} {R : RefTy} (source : Stmt C (Frame R) (Frame R)) :
 Option (PLift (source=ScalarRecursiveSource.zero)) :=
 assignment source .here (.simple (.lit 0 rfl)) (fun value => literal value 0 rfl)

def checkIncrement {C : Contract} {R : RefTy} (source : Stmt C (Frame R) (Frame R)) :
 Option (PLift (source=ScalarRecursiveSource.increment)) :=
 assignment source .here (.binop .add rfl rfl (.simple (.local .here)) (.simple (.lit 1 rfl)))
   (fun value => binary value .add rfl rfl .here 1 rfl)

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.binary_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.binary_eq
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.closeAssignment' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.closeAssignment
