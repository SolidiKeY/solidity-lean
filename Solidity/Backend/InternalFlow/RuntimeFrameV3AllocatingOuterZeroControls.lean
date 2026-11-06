import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingOuterZero
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingOuterFamilyControls

/-! Zero-cost execution with a represented heap but NO allocator witness.
The input cursor word is zero below the frame. It remains a valid zero-cost
Entry and actual Returned; no failed target State is used. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterZero.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent
abbrev caller := AllocatingOuterFamily.Controls.zeroCaller
abbrev input := AllocatingOuterFamily.Controls.zeroInput
def before := writeMachine input 0 w[0]

theorem represented : StateRepr 1 2 16 F caller CountdownWitness.P.base before := by
 have initial : StateRepr 1 2 16 F AllocatingOuterFamily.Controls.σ CountdownWitness.P.base AllocatingOuterFamily.Controls.input :=
   reserved_write AllocatingScalarTarget.represented 7 (by decide) (by decide) w[10]
 have zero : StateRepr 1 2 16 F caller CountdownWitness.P.base input :=
   initial.setVal (.there .here) (countValue 1 (by decide)) w[1] (ReprV.uint_of rfl)
 exact Restored.memory_transport zero before.mem (by
   intro t index observed
   exact upd_other _ _ (by change 2+((Frame A).length-1-index.toNat)≠0;omega))
   (by intro x high;exact upd_other _ _ (by omega))

theorem no_allocator : ¬∃ cursor, StructAllocatorRepr caller.heap CountdownWitness.P.base 16 cursor before := by
 rintro ⟨cursor,owner⟩
 have cell : w[0]=.val cursor := owner.arrays.free.cell
 have zero : cursor.val=0 := congrArg Fin.val (Word.val.inj cell.symm)
 have above := owner.arrays.free.above
 omega

theorem entry (depth : Nat) : InterfaceV1.Entry (AllocatingOuterPlan.plan.at depth) 1 2 16 F caller CountdownWitness.P.base before 10 := by
 have demandEq := AllocatingOuterPlan.demand_value caller 0 (by decide) CountdownWitness.P.r0 rfl rfl
 have arena : (AllocatingOuterPlan.plan.at depth).arenaWords caller=4 := by
   simp only [AllocatingOuterPlan.plan,InterfaceV1.RecursiveEmission.at,demandEq];decide
 have cost : (AllocatingOuterPlan.plan.at depth).heapCost caller=0 := by
   simp only [AllocatingOuterPlan.plan,InterfaceV1.RecursiveEmission.at,demandEq,Nat.mul_zero]
 refine ⟨represented,(by change 5≤8;decide),(by change 5≤8;decide),(by change 5≤8;decide),
   (by change 8≤8;decide),(by change 8<16;decide),(by change 8≤10;decide),?_,?_,?_,?_,rfl,?_⟩
 · rw [arena];decide
 · rw [arena];decide
 · exact .inl (by change 8<10;decide)
 · rw [arena];decide
 · exact .inl cost

theorem actual (depth : Nat) :
 (∃ out, (AllocatingOuterFamily.source (depth+1)).run caller=.ok out ∧
 InterfaceV1.Returned (AllocatingOuterPlan.plan.at (depth+1)) 1 2 16 caller CountdownWitness.P.base before 10 out) ∧
 ¬∃ cursor, StructAllocatorRepr caller.heap CountdownWitness.P.base 16 cursor before :=
 ⟨return_from_entry depth caller CountdownWitness.P.r0 rfl rfl 1 16 CountdownWitness.P.base before 10 (entry (depth+1)),no_allocator⟩

theorem observations (depth : Nat) :
 ∃ (out : Solidity.Out C caller.H (Frame A)) (last : Machine) (addresses : Nat → Fin W),
 (AllocatingOuterFamily.source (depth+1)).run caller=.ok out ∧ run AllocatingOuterFamily.image before=.ok last 0 ∧
 StateRepr 1 2 16 F out.st addresses last ∧
 (last.stack,[last.mem 0,last.mem 2,last.mem 3,last.mem 4,last.mem 8])=
 ([w[77]],[w[0],w[16],w[1],w[0],w[10]]) ∧
 last.mem 0≠w[22] ∧ run AllocatingOuterFamily.image before≠.revert := by
 obtain ⟨out,last,addresses,native,executed,repr,stack,position,reference,countWord,resultWord,cursorCell,extended,growth,olderWords⟩ :=
   endpoint depth 10 caller CountdownWitness.P.r0 rfl rfl CountdownWitness.P.base before represented
     (by decide) (by decide) (by decide) rfl
 refine ⟨out,last,addresses,native,executed,repr,?_,?_,?_⟩
 · rw [stack,cursorCell,reference,countWord,resultWord,position];rfl
 · rw [cursorCell];decide
 · rw [executed];intro bad;cases bad

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterZero.Controls
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterZero.Controls.represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterZero.Controls.represented
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterZero.Controls.no_allocator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterZero.Controls.no_allocator
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterZero.Controls.entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterZero.Controls.entry
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterZero.Controls.actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterZero.Controls.actual

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterZero.Controls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterZero.Controls.observations
