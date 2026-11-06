import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingOuterPlan
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingOuterFamilyControls

/-! Inhabited frozen Entry and Returned for the actual state-indexed plan.
This witnesses a positive allocating call, not approved-domain closure. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterPlan.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent
abbrev σ := AllocatingOuterFamily.Controls.σ
abbrev before := AllocatingOuterFamily.Controls.startNine

theorem entry (depth : Nat) : InterfaceV1.Entry (plan.at depth) 1 2 16 F σ CountdownWitness.P.base before 9 := by
 have original : StateRepr 1 2 16 F σ CountdownWitness.P.base AllocatingOuterFamily.Controls.input :=
   reserved_write AllocatingScalarTarget.represented 7 (by decide) (by decide) w[10]
 have repr : StateRepr 1 2 16 F σ CountdownWitness.P.base before :=
   reserved_write original 8 (by decide) (by decide) w[9]
 have owned : StructAllocatorRepr σ.heap CountdownWitness.P.base 16 (⟨22,by decide⟩ : Fin W) before :=
   (AllocatingScalarTarget.ownership.localWrite 7 (by decide) (by decide) w[10]).localWrite 8 (by decide) (by decide) w[9]
 have demandEq : demand σ=1 := demand_value σ 1 (by decide) CountdownWitness.P.r0 rfl rfl
 have arena : (plan.at depth).arenaWords σ=6 := by simp only [plan,InterfaceV1.RecursiveEmission.at,demandEq];decide
 have cost : (plan.at depth).heapCost σ=4 := by simp only [plan,InterfaceV1.RecursiveEmission.at,demandEq]
 refine ⟨repr,(by change 5≤8;decide),(by change 5≤8;decide),(by change 5≤8;decide),
   (by change 8≤8;decide),(by change 8<16;decide),(by change 8≤9;decide),?_,?_,?_,?_,rfl,?_⟩
 · rw [arena];decide
 · rw [arena];decide
 · exact .inl (by change 8<9;decide)
 · rw [arena];decide
 · rw [cost]
   exact .inr ⟨by decide,⟨22,by decide⟩,owned,by decide⟩

theorem actual (depth : Nat) (enough : 1<depth) :
 ∃ out, (AllocatingOuterFamily.source depth).run σ=.ok out ∧
 InterfaceV1.Returned (plan.at depth) 1 2 16 σ CountdownWitness.P.base before 9 out :=
 return_from_entry depth 1 (by decide) σ (by decide) CountdownWitness.P.r0 rfl rfl
   1 16 CountdownWitness.P.base before 9 (entry depth) enough

theorem observations (depth : Nat) (enough : 1<depth) :
 ∃ (out : Solidity.Out C σ.H (Frame A)) (last : Machine) (addresses : Nat → Fin W),
 (AllocatingOuterFamily.source depth).run σ=.ok out ∧ run (plan.at depth).code before=.ok last 0 ∧
 StateRepr 1 2 16 F out.st addresses last ∧
 (last.stack,[last.mem 0,last.mem 2,last.mem 3,last.mem 4,last.mem 8])=
 ([w[77]],[w[26],w[16],w[2],w[1],w[9]]) ∧ run (plan.at depth).code before≠.revert := by
 obtain ⟨out,returnedSource,returned⟩ := actual depth enough
 obtain ⟨seen,last,addresses,native,executed,represented,words,vector,wrong⟩ := AllocatingOuterFamily.Controls.dynamic_one depth enough
 have same : seen=out := Except.ok.inj (native.symm.trans returnedSource)
 subst seen
 refine ⟨out,last,addresses,returnedSource,executed,represented,vector,?_⟩
 rw [show run (plan.at depth).code before=.ok last 0 from executed]
 intro bad;cases bad

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterPlan.Controls
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterPlan.Controls.entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterPlan.Controls.entry
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterPlan.Controls.actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterPlan.Controls.actual
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterPlan.Controls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterPlan.Controls.observations
