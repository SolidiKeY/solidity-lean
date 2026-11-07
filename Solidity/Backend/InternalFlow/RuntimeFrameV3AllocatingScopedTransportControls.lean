import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScopedEndpointControls
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingOuterClaimsControls

/-! Actual checked scoped-call argument-underflow transport. This consumes
the same all-entry API as successful scoped endpoints, retains the exact
bare-revert class and supplies no failed-State, effects or journal conclusion. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedTransport.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent

abbrev failing := AllocatingOuterClaims.Controls.failing
abbrev before := AllocatingOuterClaims.Controls.before

theorem failure (p : PrimTy) (name : Var) (depth : Nat) :
 (AllocatingScopedEndpoint.call p name depth).run failing=.error .revert ∧
 run (AllocatingOuterPlan.plan.at depth).code before=.revert ∧
 (¬∃ out,(AllocatingScopedEndpoint.call p name depth).run failing=.ok out) ∧
 (AllocatingScopedEndpoint.call p name depth).run failing≠.error .panic ∧
 (AllocatingScopedEndpoint.call p name depth).run failing≠.error .exhausted ∧
 (∀ last,run (AllocatingOuterPlan.plan.at depth).code before≠.ok last 0) := by
 have same : (AllocatingScopedEndpoint.call p name depth).run failing=(AllocatingOuterFamily.source depth).run failing :=
   congrFun (AllocatingSourceCertificate.call_run (AllocatingScopedEndpoint.checked p name depth)) failing
 have native : (AllocatingScopedEndpoint.call p name depth).run failing=.error .revert :=
   same.trans (AllocatingOuterClaims.Controls.failure depth).1
 have actual : run (AllocatingOuterPlan.plan.at depth).code before=.revert :=
   (claims (AllocatingScopedEndpoint.accepted p name depth)).2
     1 16 failing CountdownWitness.P.base before 9 (AllocatingOuterClaims.Controls.entry depth) native
 refine ⟨native,actual,?_,?_,?_,?_⟩
 · rintro ⟨out,wrong⟩
   rw [native] at wrong
   cases wrong
 · rw [native]
   intro wrong
   cases wrong
 · rw [native]
   intro wrong
   cases wrong
 · intro last
   rw [actual]
   intro wrong
   cases wrong

theorem at_two :
 (AllocatingScopedEndpoint.call .bool (.user "unused") 2).run failing=.error .revert ∧
 run (AllocatingOuterPlan.plan.at 2).code before=.revert :=
 ⟨(failure .bool (.user "unused") 2).1,(failure .bool (.user "unused") 2).2.1⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedTransport.Controls
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedTransport.Controls.failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedTransport.Controls.failure
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedTransport.Controls.at_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedTransport.Controls.at_two
