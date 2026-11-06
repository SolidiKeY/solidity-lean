import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScopedEndpoint

/-! Populated checked scoped returns at the original fixed C/A/caller.
The destination and caller counter are observed on the SAME target carrying
all original representation, allocation and older-frame obligations. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent

theorem two_bool :
 ∃ out, (call .bool (.user "unused") 2).run caller=.ok out ∧
 InterfaceV1.Returned (AllocatingOuterPlan.plan.at 2) 1 2 16 caller CountdownWitness.P.base before 9 out :=
 actual .bool (.user "unused") 2 (by decide)

theorem three_uint :
 ∃ out, (call .uint (.user "different") 3).run caller=.ok out ∧
 InterfaceV1.Returned (AllocatingOuterPlan.plan.at 3) 1 2 16 caller CountdownWitness.P.base before 9 out :=
 actual .uint (.user "different") 3 (by decide)

theorem result_and_frame :
 ∃ (out : Solidity.Out C caller.H (Frame A)) (target : Machine) (addresses : Nat → Fin W),
 (call .bool (.user "unused") 2).run caller=.ok out ∧
 run (AllocatingOuterPlan.plan.at 2).code before=.ok target 0 ∧
 StateRepr 1 2 16 F out.st addresses target ∧
 target.mem 4=w[1] ∧ target.mem 3=w[2] ∧ target.stack=[w[77]] ∧
 Footprint.Words 8 9 before target ∧ target.mem 4≠w[2] := by
 obtain ⟨out,target,addresses,native,executed,represented,stack,_baseExtended,_growth,_pointer,older,vector⟩ :=
   observations .bool (.user "unused") 2 (by decide)
 have stackEq : target.stack=[w[77]] := congrArg Prod.fst vector
 have resultEq := congrArg (fun seen => seen[3]?) (congrArg Prod.snd vector)
 change some (target.mem 4)=some w[1] at resultEq
 have resultWord : target.mem 4=w[1] := Option.some.inj resultEq
 have counterEq := congrArg (fun seen => seen[2]?) (congrArg Prod.snd vector)
 change some (target.mem 3)=some w[2] at counterEq
 have counterWord : target.mem 3=w[2] := Option.some.inj counterEq
 refine ⟨out,target,addresses,native,executed,represented,resultWord,counterWord,stackEq,older,?_⟩
 rw [resultWord]
 decide

theorem too_small_frame :
 ¬InterfaceV1.Entry (AllocatingOuterPlan.plan.at 2) 1 2 8 F caller CountdownWitness.P.base before 9 :=
 fun admitted => Nat.lt_irrefl 8 admitted.pointerBelow

theorem zero_without_owner :
 (∃ out, (call .bool (.user "unused") 1).run zeroCaller=.ok out ∧
 InterfaceV1.Returned (AllocatingOuterPlan.plan.at 1) 1 2 16 zeroCaller CountdownWitness.P.base zeroBefore 10 out) ∧
 ¬∃ cursor, StructAllocatorRepr zeroCaller.heap CountdownWitness.P.base 16 cursor zeroBefore :=
 zero_actual .bool (.user "unused") 0

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.Controls
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.Controls.two_bool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.Controls.two_bool
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.Controls.three_uint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.Controls.three_uint
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.Controls.result_and_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.Controls.result_and_frame
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.Controls.too_small_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.Controls.too_small_frame

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.Controls.zero_without_owner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.Controls.zero_without_owner
