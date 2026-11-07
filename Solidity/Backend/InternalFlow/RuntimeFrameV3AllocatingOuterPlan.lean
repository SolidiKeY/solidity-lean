import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingOuterFamily

/-! State-indexed metadata and actual frozen Returned transport for positive
allocating scalar counts. Demand uses the existing argument evaluator. This
is not an approved profile, general recursive selector, or zero-cost proof. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterPlan
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent

def demand (caller : State C (Frame A)) : Nat :=
 match (next A (by rfl)).evalT caller with
 | .ok arguments => arguments.1.word.val
 | .error _ => 0

def plan : InterfaceV1.RecursiveEmission C (Frame A) (Frame A) :=
 ⟨AllocatingOuterFamily.image,fun _ => F,fun _ => 3,8,8,
   fun _ caller => max 4 (3+3*demand caller),fun _ caller => 4*demand caller⟩

theorem demand_value (caller : State C (Frame A)) (n : Nat) (fit : n+1<W) (ref : HRef caller.H A)
 (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) caller.env=countValue (n+1) fit)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame A) (.mem A)) caller.env=some ref) :
 demand caller=n := by
 have evaluated := next_eval (by rfl) caller n fit ref counter alias
 simp only [demand,evaluated]
 rfl

theorem return_from_entry (depth n : Nat) (positive : 0<n) (caller : State C (Frame A))
 (fit : n+1<W) (ref : HRef caller.H A)
 (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) caller.env=countValue (n+1) fit)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame A) (.mem A)) caller.env=some ref)
 (L frame : Nat) (base : Nat → Fin W) (before : Machine) (start : Nat)
 (entry : InterfaceV1.Entry (plan.at depth) L 2 frame F caller base before start)
 (enough : n<depth) :
 ∃ out, (AllocatingOuterFamily.source depth).run caller=.ok out ∧
 InterfaceV1.Returned (plan.at depth) L 2 frame caller base before start out := by
 have demandEq := demand_value caller n fit ref counter alias
 have reserve : start+max 4 (3+3*n)≤frame := by
   simpa only [plan,InterfaceV1.RecursiveEmission.at,demandEq] using entry.reserve
 have noWrap : start+max 4 (3+3*n)<W := by
   simpa only [plan,InterfaceV1.RecursiveEmission.at,demandEq] using entry.noWrap
 have above : 8≤start := entry.payloadAbove
 have separated : 8<start ∨ start+max 4 (3+3*n)≤8 := by
   simpa only [plan,InterfaceV1.RecursiveEmission.at,demandEq] using entry.separate
 have startAbove : 9≤start := by omega
 have capacity : AllocationInput 2 frame (4*n) caller base before := by
   simpa only [plan,InterfaceV1.RecursiveEmission.at,demandEq] using entry.capacity
 rcases capacity with zero | ⟨basePositive,cursor,owned,space⟩
 · omega
 · obtain ⟨out,last,addresses,native,actual,represented,stack,position,reference,countWord,resultWord,owner,extended,growth,olderWords⟩ :=
     AllocatingOuterFamily.dynamic_endpoint depth n start caller fit ref counter alias base before entry.represented
       cursor owned startAbove (by omega) space (by omega) entry.cursor enough
   refine ⟨out,native,last,addresses,actual,represented,stack,extended,?_,position,olderWords⟩
   simpa only [plan,InterfaceV1.RecursiveEmission.at,demandEq] using growth

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterPlan
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterPlan.demand_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterPlan.demand_value
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterPlan.return_from_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterPlan.return_from_entry
