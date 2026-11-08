import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScopedCheck

/-! Frozen runtime claims for actual accepted scoped syntax. These quantify
over every original Entry, caller, frame, machine, cursor and source result.
Checker acceptance is not approved-profile admission or compiler selection.
Bare revert asserts no failed State, payload, rollback or world property. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedTransport
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent

theorem claims {depth : Nat} {source : Prog C (Frame A) (Frame A)}
 (accepted : (AllocatingScopedCheck.certify A rfl depth source).isSome=true) :
 InterfaceV1.ReturnClaim 2 F (AllocatingSourceCertificate.call depth source) (AllocatingOuterPlan.plan.at depth) ∧
 InterfaceV1.BareRevertClaim 2 F (AllocatingSourceCertificate.call depth source) (AllocatingOuterPlan.plan.at depth) :=
 let verified : AllocatingSourceCertificate.Certificate A rfl depth source :=
   ((AllocatingScopedCheck.certify A rfl depth source).get accepted).down
 ⟨AllocatingSourceCertificate.returns verified,AllocatingSourceCertificate.bare_revert verified⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedTransport
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedTransport.claims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedTransport.claims
