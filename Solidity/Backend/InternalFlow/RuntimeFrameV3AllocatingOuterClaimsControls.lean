import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingOuterClaims
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingOuterPlanControls

/-! Inhabited universal-claim consumers, including checked argument underflow
at every quotation index. Bare revert stays distinct from panic/exhaustion;
no failed output State, rollback, byte payload or world claim is inferred. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent
abbrev σ := AllocatingOuterPlan.Controls.σ
abbrev input := AllocatingOuterPlan.Controls.before

theorem success (depth : Nat) (enough : 1<depth) :
 ∃ out, (AllocatingOuterFamily.source depth).run σ=.ok out ∧
 InterfaceV1.Returned (AllocatingOuterPlan.plan.at depth) 1 2 16 σ CountdownWitness.P.base input 9 out := by
 obtain ⟨out,native,known⟩ := AllocatingOuterPlan.Controls.actual depth enough
 exact ⟨out,native,returns depth 1 16 σ CountdownWitness.P.base input 9 (AllocatingOuterPlan.Controls.entry depth) out native⟩

def failing := σ.setLocal (.there .here) (countValue 0 W_pos)
def before := writeMachine input 3 w[0]

theorem entry (depth : Nat) : InterfaceV1.Entry (AllocatingOuterPlan.plan.at depth) 1 2 16 F failing CountdownWitness.P.base before 9 := by
 have initial : StateRepr 1 2 16 F σ CountdownWitness.P.base input :=
   (AllocatingOuterPlan.Controls.entry depth).represented
 have represented : StateRepr 1 2 16 F failing CountdownWitness.P.base before :=
   initial.setVal (.there .here) (countValue 0 W_pos) w[0] (ReprV.uint_of rfl)
 have demandEq : AllocatingOuterPlan.demand failing=0 := by
   simp only [AllocatingOuterPlan.demand,next_zero failing CountdownWitness.P.r0 rfl rfl]
 have arena : (AllocatingOuterPlan.plan.at depth).arenaWords failing=4 := by
   simp only [AllocatingOuterPlan.plan,InterfaceV1.RecursiveEmission.at,demandEq];decide
 have cost : (AllocatingOuterPlan.plan.at depth).heapCost failing=0 := by
   simp only [AllocatingOuterPlan.plan,InterfaceV1.RecursiveEmission.at,demandEq,Nat.mul_zero]
 refine ⟨represented,(by change 5≤8;decide),(by change 5≤8;decide),(by change 5≤8;decide),
   (by change 8≤8;decide),(by change 8<16;decide),(by change 8≤9;decide),?_,?_,?_,?_,rfl,?_⟩
 · rw [arena];decide
 · rw [arena];decide
 · exact .inl (by change 8<9;decide)
 · rw [arena];decide
 · exact .inl cost

theorem failure (depth : Nat) :
 (AllocatingOuterFamily.source depth).run failing=.error .revert ∧
 run (AllocatingOuterPlan.plan.at depth).code before=.revert ∧
 (¬∃ out,(AllocatingOuterFamily.source depth).run failing=.ok out) ∧
 (AllocatingOuterFamily.source depth).run failing≠.error .panic ∧
 (AllocatingOuterFamily.source depth).run failing≠.error .exhausted ∧
 (∀ last,run (AllocatingOuterPlan.plan.at depth).code before≠.ok last 0) := by
 have native := source_zero depth failing CountdownWitness.P.r0 rfl rfl
 have actual := bare_revert depth 1 16 failing CountdownWitness.P.base before 9 (entry depth) native
 refine ⟨native,actual,?_,?_,?_,?_⟩
 · rintro ⟨out,wrong⟩;rw [native] at wrong;cases wrong
 · rw [native];intro wrong;cases wrong
 · rw [native];intro wrong;cases wrong
 · intro last;rw [actual];intro wrong;cases wrong

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.Controls
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.Controls.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.Controls.success
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.Controls.entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.Controls.entry
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.Controls.failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.Controls.failure
