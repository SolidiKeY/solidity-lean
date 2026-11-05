import Solidity.Backend.InternalFlow.RuntimeFrameReturnReentry
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarContinuationControls

/-! Re-enter the scalar family after actual mutation and allocation. The next
argument reads the updated old array; a new allocated object and its actual
frontier remain live. No general selector or approved profile is supplied. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarReentry
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open DisjointScalarReturn.Client

def prefixPlan : InterfaceV1.Emission CountdownWitness.P.C Γ Γ :=
 { (ScalarDemandDual.outputPlan.at 4) with code:=ScalarContinuation.image,heapCost:=fun _ => 4 }

theorem prefix_entry : InterfaceV1.Entry prefixPlan 1 1 16 F caller CountdownWitness.P.base before 10 := by
 have entry := ScalarDemandDual.good_entry 4
 exact ⟨entry.represented,entry.callerBound,entry.resultBound,entry.workspace,entry.pointerAbove,
   entry.pointerBelow,entry.payloadAbove,entry.reserve,entry.controlSpace,entry.separate,entry.noWrap,
   entry.cursor,ScalarContinuation.capacity⟩

theorem prefix_cursor : ScalarContinuation.target.mem 9=w[10] :=
 Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[9]?) ScalarContinuation.Controls.complete_observations)

theorem prefix_words : Footprint.Words 9 10 before ScalarContinuation.target := by
 obtain ⟨middle,addresses,executed,repr,stack,extended,growth,cursor,words⟩ :=
   ScalarDemandDual.producer.required_return 4 1 16 caller CountdownWitness.P.base before 10
     (ScalarDemandDual.good_entry 4) _ ScalarDual.good_source
 have same : middle=machine := (Evm.Out.ok.inj (executed.symm.trans (ScalarDemandDual.good_execution 4))).1
 subst middle
 intro address lower upper
 exact (ScalarContinuation.allocation_facts.2.2.2.2 address (by omega) (by omega)).trans (words address lower upper)

theorem prefix_returned : InterfaceV1.Returned prefixPlan 1 1 16 caller CountdownWitness.P.base before 10 ScalarContinuation.output :=
 ⟨ScalarContinuation.target,ScalarContinuation.finalBase,ScalarContinuation.target_execution,
   ScalarContinuation.endpoint.2.2.1,ScalarContinuation.endpoint.2.2.2.1,
   ScalarContinuation.bases_preserved,ScalarContinuation.growth,prefix_cursor,prefix_words⟩

def count : Val CountdownWitness.P.C Γ .uint :=
 .readMem (.index .dyn (.var reference rfl) (.simple (.lit 0 rfl)))
def emitted : ScalarEmitter.Emission 1 5 16 9 8 F count :=
 (ScalarEmitter.compile 1 5 16 9 8 F count).get (by rfl)
def plan := ScalarDemand.plan emitted reference (.here : Idx Γ (.val .uint))
def statement (depth : Nat) := DisjointScalarReturn.call rfl reference count (.here : Idx Γ (.val .uint)) "scalarCountdown" depth

theorem selected : ScalarEmitter.compile 1 5 16 9 8 F count=some emitted := rfl

theorem actual_count : count.evalT ScalarContinuation.final=.ok (countValue 3 (by decide)) := by
 with_unfolding_all rfl

theorem arena (depth : Nat) : (plan.at depth).arenaWords ScalarContinuation.final=6 := by
 change ScalarDemand.reserve count ScalarContinuation.final=6
 rw [ScalarDemand.reserve_value _ actual_count]
 rfl

theorem entry (depth : Nat) : InterfaceV1.Entry (plan.at depth) 1 1 16 F ScalarContinuation.final
 ScalarContinuation.finalBase ScalarContinuation.target 10 := by
 apply ReturnReentry.reached_entry (first:=prefixPlan) (next:=plan.at depth) (out:=ScalarContinuation.output) prefix_entry
   ScalarContinuation.endpoint.2.2.1 ScalarContinuation.growth prefix_cursor rfl rfl (by change 7≤7;decide) (by decide)
 · change (plan.at depth).arenaWords ScalarContinuation.final≤ScalarDemand.reserve ScalarDual.choice caller
   rw [arena,ScalarDemandDual.good_reserve]
   decide
 · change 5≤(plan.at depth).arenaWords ScalarContinuation.final
   rw [arena]
   decide
 · change AllocationInput 1 16 (4+0) caller CountdownWitness.P.base before
   exact ScalarContinuation.capacity

/-- The next actual source call reads the mutated heap, rather than a literal
or the older pre-mutation source state. -/
theorem source (depth : Nat) : (statement depth).run ScalarContinuation.final=
 if 3<depth then .ok ⟨ScalarContinuation.final.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩
 else .error .exhausted := by
 have called := ScalarClaims.source_value rfl reference count .here "scalarCountdown" depth ScalarContinuation.final
   (CountdownWitness.P.r0.wk ScalarContinuation.extension) (by with_unfolding_all rfl)
   (countValue 3 (by decide)) actual_count
 exact called

theorem returned : InterfaceV1.Returned (plan.at 4) 1 1 16 ScalarContinuation.final ScalarContinuation.finalBase
 ScalarContinuation.target 10 ⟨ScalarContinuation.final.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩ := by
 apply ScalarDemand.returns emitted (by decide) rfl reference .here "scalarCountdown" 4
   1 16 ScalarContinuation.final ScalarContinuation.finalBase ScalarContinuation.target 10 (entry 4)
 exact (source 4).trans (if_pos (by decide))

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarReentry
