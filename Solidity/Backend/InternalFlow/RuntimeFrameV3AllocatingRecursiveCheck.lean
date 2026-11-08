import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingCallLeaves
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingGuardedTurn

/-! Actual allocating recursive-head recognition and source-certificate
construction. The real child thunk is retained. Verification follows the
existing quotation Nat and requires every inspected call index to agree;
there is no independent fuel, runtime cutoff, execution or selector premise. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

structure ClosedCall {C : Contract} {R : RefTy} (source : Stmt C (Frame R) (Frame R)) : Type where
 function : Name
 index : Nat
 arguments : Args C (Frame R) (Parameters R)
 ret : CallRet (Frame R) [.val .uint] (Frame R)
 child : Unit → Prog C (Frame R) (Frame R)
 shape : source=.callRec function index arguments ret child

def closeCall {C : Contract} {R : RefTy} {source : Stmt C (Frame R) (Frame R)}
 (view : AllocatingHeadViews.RecursiveCall source) (parametersEq : view.parameters=Parameters R)
 (resultsEq : view.results=[.val .uint]) : ClosedCall source := by
 rcases view with ⟨parameters,results,function,index,arguments,ret,child,shape⟩
 simp only [] at parametersEq resultsEq
 subst parameters
 subst results
 exact ⟨function,index,arguments,ret,child,shape⟩

structure Head {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true)
 (source : Prog C (Frame R) (Frame R)) : Type where
 index : Nat
 child : Unit → Prog C (Frame R) (Frame R)
 shape : source=AllocatingScalarSource.step R hm index child

def assemble {C : Contract} {R : RefTy} {hm : (Ty.ref R).mapFree=true}
 {source : Prog C (Frame R) (Frame R)} (root : AllocatingGuardedTurn.Head R source)
 (parts : AllocatingSourceViews.ClosedCons root.continuation)
 (ending : parts.tail=.cons increment .nil) (call : ClosedCall parts.head)
 (argumentsEq : call.arguments=next R hm) (returnEq : call.ret=result R)
 (nameEq : call.function="allocatingScalar") : Head R hm source := by
 refine ⟨call.index,call.child,?_⟩
 simp only [root.shape,parts.shape,ending,call.shape,argumentsEq,returnEq,nameEq,
     AllocatingScalarSource.step,AllocatingScalarSource.continuation]

def readHead {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true)
 (source : Prog C (Frame R) (Frame R)) : Option (Head R hm source) := do
 let root ← AllocatingGuardedTurn.read R source
 let parts ← AllocatingSourceViews.readClosedCons root.continuation
 let ending ← AllocatingGuardedTurn.checkTail parts.tail
 let observed ← AllocatingHeadViews.readRecursiveCall parts.head
 if parametersEq : observed.parameters=Parameters R then
   if resultsEq : observed.results=[.val .uint] then
     let call := closeCall observed parametersEq resultsEq
     let argumentsEq ← AllocatingCallLeaves.checkNext hm call.arguments
     let returnEq ← AllocatingCallLeaves.checkResult call.ret
     if nameEq : call.function="allocatingScalar" then
       pure (assemble root parts ending.down call argumentsEq.down returnEq.down nameEq)
     else none
   else none
 else none

def certify {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) :
 (depth : Nat) → (source : Prog C (Frame R) (Frame R)) →
 Option (PLift (AllocatingSourceCertificate.Certificate R hm depth source))
 | 0, source => AllocatingSourceViews.certifyBase R hm source
 | depth+1, source => do
   let head ← readHead R hm source
   if indexEq : head.index=depth then
     let child ← certify R hm depth (head.child ())
     pure ⟨by
       have shape : source=AllocatingScalarSource.step R hm depth head.child :=
         head.shape.trans (by rw [indexEq])
       exact shape.symm ▸ AllocatingSourceCertificate.Certificate.turn child.down⟩
   else none

/-- Successful actual syntax checking produces the existing full source-run
relation. The acceptance premise is checker success, not source equivalence,
execution or approved-domain admission. -/
theorem source_run {C : Contract} {R : RefTy} {hm : (Ty.ref R).mapFree=true}
 {depth : Nat} {source : Prog C (Frame R) (Frame R)}
 (accepted : (certify R hm depth source).isSome=true) :
 source.runR=(AllocatingScalarSource.body R hm depth).runR :=
 AllocatingSourceCertificate.sound ((certify R hm depth source).get accepted).down

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.closeCall' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.closeCall
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.assemble' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.assemble

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.source_run
