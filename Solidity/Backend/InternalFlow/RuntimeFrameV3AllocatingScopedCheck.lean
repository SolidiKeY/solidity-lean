import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScopeView
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingRecursiveCheck

/-! Checking the existing scoped allocating quotation family. Each non-base
activation has the exact default-local decorator; the existing recBase is
unchanged. Real children are checked at the original quotation predecessor.
This does not claim recognition of every scope certificate or compiler input. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

def certify {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) :
 (depth : Nat) → (source : Prog C (Frame R) (Frame R)) →
 Option (PLift (AllocatingSourceCertificate.Certificate R hm depth source))
 | 0, source => AllocatingSourceViews.certifyBase R hm source
 | depth+1, source => do
   let scope ← AllocatingScopeView.read source
   let head ← AllocatingRecursiveCheck.readHead R hm scope.body
   if indexEq : head.index=depth then
     let child ← certify R hm depth (head.child ())
     pure ⟨by
       have bodyShape : scope.body=AllocatingScalarSource.step R hm depth head.child :=
         head.shape.trans (by rw [indexEq])
       have bodyChecked : AllocatingSourceCertificate.Certificate R hm (depth+1) scope.body :=
         bodyShape.symm ▸ AllocatingSourceCertificate.Certificate.turn child.down
       exact scope.shape.symm ▸ AllocatingSourceCertificate.Certificate.scope scope.primitive scope.name bodyChecked⟩
   else none

theorem source_run {C : Contract} {R : RefTy} {hm : (Ty.ref R).mapFree=true}
 {depth : Nat} {source : Prog C (Frame R) (Frame R)}
 (accepted : (certify R hm depth source).isSome=true) :
 source.runR=(AllocatingScalarSource.body R hm depth).runR :=
 AllocatingSourceCertificate.sound ((certify R hm depth source).get accepted).down

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.source_run
