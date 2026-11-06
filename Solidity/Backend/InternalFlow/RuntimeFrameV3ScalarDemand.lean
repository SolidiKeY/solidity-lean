import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarClaims

/-! Actual-count arena metadata for the existing scalar-family image. This
uses the existing source value evaluator only to compute a natural demand;
no second evaluator, success filter or approved domain is introduced. The old
quotation-based plan and all frozen interfaces remain unchanged. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarDemand
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

def reserve {C : Contract} {Γ : Ctx} (count : Val C Γ .uint) (caller : State C Γ) : Nat :=
 max (Γ.length+1) (match count.evalT caller with | .ok value => 2*value.word.val | .error _ => 0)

theorem reserve_value {C : Contract} {Γ : Ctx} {count : Val C Γ .uint} {caller : State C Γ}
 (value : PrimTy.uint.Denote) (evaluated : count.evalT caller=.ok value) :
 reserve count caller=max (Γ.length+1) (2*value.word.val) := by
 simp only [reserve,evaluated]

theorem reserve_error {C : Contract} {Γ : Ctx} {count : Val C Γ .uint} {caller : State C Γ}
 (halt : THalt) (failed : count.evalT caller=.error halt) :
 reserve count caller=max (Γ.length+1) 0 := by
 simp only [reserve,failed]

def plan {C : Contract} {Γ : Ctx} {R : RefTy} {b c selectedFrame pointer bottom : Nat}
 {F : Frag Γ} {count : Val C Γ .uint}
 (emitted : ScalarEmitter.Emission b c selectedFrame pointer bottom F count)
 (reference : Idx Γ (.mem R)) (destination : Idx Γ (.val .uint)) : InterfaceV1.RecursiveEmission C Γ Γ :=
 ⟨emitted.code reference destination,fun _ => F,fun _ => c+3-b,pointer,pointer,
   fun _ caller => reserve count caller,fun _ _ => 0⟩

/-- A proof-only metadata bridge at the actual count. It changes no executed
code, caller, cursor, source statement or observation index of the new plan. -/
theorem success_entry {C : Contract} {Γ : Ctx} {R : RefTy}
 {b c selectedFrame pointer bottom L frame depth : Nat} {F : Frag Γ} {count : Val C Γ .uint}
 (emitted : ScalarEmitter.Emission b c selectedFrame pointer bottom F count)
 (reference : Idx Γ (.mem R)) (destination : Idx Γ (.val .uint))
 {caller : State C Γ} {base : Nat → Fin W} {before : Machine} {start : Nat}
 (entry : InterfaceV1.Entry ((plan emitted reference destination).at depth) L b frame F caller base before start)
 (value : PrimTy.uint.Denote) (evaluated : count.evalT caller=.ok value) :
 InterfaceV1.Entry ((ScalarPlan.plan emitted reference destination).at (value.word.val+1)) L b frame F caller base before start := by
 have demand := reserve_value value evaluated
 refine ⟨entry.represented,entry.callerBound,entry.resultBound,entry.workspace,entry.pointerAbove,
   entry.pointerBelow,entry.payloadAbove,?_,?_,?_,?_,entry.cursor,entry.capacity⟩
 · simpa only [plan,ScalarPlan.plan,InterfaceV1.RecursiveEmission.at,demand,Nat.add_sub_cancel] using entry.reserve
 · simpa only [plan,ScalarPlan.plan,InterfaceV1.RecursiveEmission.at,demand,Nat.add_sub_cancel] using entry.controlSpace
 · simpa only [plan,ScalarPlan.plan,InterfaceV1.RecursiveEmission.at,demand,Nat.add_sub_cancel] using entry.separate
 · simpa only [plan,ScalarPlan.plan,InterfaceV1.RecursiveEmission.at,demand,Nat.add_sub_cancel] using entry.noWrap

theorem failure_entry {C : Contract} {Γ : Ctx} {R : RefTy}
 {b c selectedFrame pointer bottom L frame depth : Nat} {F : Frag Γ} {count : Val C Γ .uint}
 (emitted : ScalarEmitter.Emission b c selectedFrame pointer bottom F count)
 (reference : Idx Γ (.mem R)) (destination : Idx Γ (.val .uint))
 {caller : State C Γ} {base : Nat → Fin W} {before : Machine} {start : Nat}
 (entry : InterfaceV1.Entry ((plan emitted reference destination).at depth) L b frame F caller base before start)
 (halt : THalt) (failed : count.evalT caller=.error halt) :
 InterfaceV1.Entry ((ScalarPlan.plan emitted reference destination).at 0) L b frame F caller base before start := by
 have demand := reserve_error halt failed
 refine ⟨entry.represented,entry.callerBound,entry.resultBound,entry.workspace,entry.pointerAbove,
   entry.pointerBelow,entry.payloadAbove,?_,?_,?_,?_,entry.cursor,entry.capacity⟩
 · simpa only [plan,ScalarPlan.plan,InterfaceV1.RecursiveEmission.at,demand] using entry.reserve
 · simpa only [plan,ScalarPlan.plan,InterfaceV1.RecursiveEmission.at,demand] using entry.controlSpace
 · simpa only [plan,ScalarPlan.plan,InterfaceV1.RecursiveEmission.at,demand] using entry.separate
 · simpa only [plan,ScalarPlan.plan,InterfaceV1.RecursiveEmission.at,demand] using entry.noWrap

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarDemand
