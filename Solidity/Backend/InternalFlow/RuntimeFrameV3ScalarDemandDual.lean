import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarDemandClaims
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarDualControls

/-! The same selected image and represented callers with actual-count demand.
All quotation indices now share the same initial resource requirement. The
known index-five obstruction is removed; approved provenance and coverage for
the whole original source domain remain separate obligations. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarDemandDual
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open DisjointScalarReturn.Client

def outputPlan := ScalarDemand.plan ScalarDual.emitted reference (.here : Idx Γ (.val .uint))

theorem good_reserve : ScalarDemand.reserve ScalarDual.choice caller=6 := by
 rw [ScalarDemand.reserve_value _ ScalarDual.good_eval]
 rfl

theorem bad_reserve : ScalarDemand.reserve ScalarDual.choice ScalarDual.rejectedCaller=5 := by
 rw [ScalarDemand.reserve_error _ ScalarDual.bad_eval]
 rfl

theorem good_entry (depth : Nat) : InterfaceV1.Entry (outputPlan.at depth) 1 1 16 F caller CountdownWitness.P.base before 10 where
 represented := initial
 callerBound := by change 1+Γ.length≤9;decide
 resultBound := by change 1+Γ.length≤9;decide
 workspace := by change 1+(5+3-1)≤9;decide
 pointerAbove := by change 9≤9;decide
 pointerBelow := by change 9<16;decide
 payloadAbove := by change 9≤10;decide
 reserve := by change 10+ScalarDemand.reserve ScalarDual.choice caller≤16;rw [good_reserve];decide
 controlSpace := by change 5≤ScalarDemand.reserve ScalarDual.choice caller;rw [good_reserve];decide
 separate := Or.inl (by change 9<10;decide)
 noWrap := by change 10+ScalarDemand.reserve ScalarDual.choice caller<W;rw [good_reserve];decide
 cursor := rfl
 capacity := Or.inl rfl

theorem bad_entry (depth : Nat) : InterfaceV1.Entry (outputPlan.at depth) 1 1 16 F ScalarDual.rejectedCaller CountdownWitness.P.base ScalarDual.rejectedMachine 10 where
 represented := ScalarDual.rejected_repr
 callerBound := by change 1+Γ.length≤9;decide
 resultBound := by change 1+Γ.length≤9;decide
 workspace := by change 1+(5+3-1)≤9;decide
 pointerAbove := by change 9≤9;decide
 pointerBelow := by change 9<16;decide
 payloadAbove := by change 9≤10;decide
 reserve := by change 10+ScalarDemand.reserve ScalarDual.choice ScalarDual.rejectedCaller≤16;rw [bad_reserve];decide
 controlSpace := by change 5≤ScalarDemand.reserve ScalarDual.choice ScalarDual.rejectedCaller;rw [bad_reserve];decide
 separate := Or.inl (by change 9<10;decide)
 noWrap := by change 10+ScalarDemand.reserve ScalarDual.choice ScalarDual.rejectedCaller<W;rw [bad_reserve];decide
 cursor := rfl
 capacity := Or.inl rfl

def producer : InterfaceV2.PendingRecursiveReturns 1 F "scalarCountdown"
 (DisjointScalarEntry.args rfl reference ScalarDual.choice) (.val .uint (.user "result") (some (.here : Idx Γ (.val .uint))))
 (ScalarRecursiveSource.step CountdownWitness.A rfl) where
 plan := outputPlan
 required_successful_entry := ⟨4,1,16,caller,CountdownWitness.P.base,before,10,
   ⟨caller.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩,good_entry 4,ScalarDual.good_source⟩
 required_source_coherence := ScalarDual.producer.required_source_coherence
 required_return := fun depth => ScalarDemand.returns ScalarDual.emitted (by decide) rfl reference .here "scalarCountdown" depth
 required_bare_revert := fun depth => ScalarDemand.bare_revert ScalarDual.emitted (by decide) rfl reference .here "scalarCountdown" depth

theorem reverting_entry : InterfaceV2.RevertingEntry 1 F (ScalarDual.statement 0) (outputPlan.at 0) :=
 ⟨1,16,ScalarDual.rejectedCaller,CountdownWitness.P.base,ScalarDual.rejectedMachine,10,bad_entry 0,ScalarDual.bad_source⟩

/-- Logical assembly only. Agreement/coverage/membership are externally
supplied and do not themselves authenticate approved-source provenance. -/
def with_domain (approved admitted : Nat → InterfaceV3.Admission CountdownWitness.P.C Γ)
 (agreement : InterfaceV3.FamilyAdmissionAgreement approved admitted)
 (coverage : InterfaceV3.FamilyEntryCoverage 1 F admitted outputPlan)
 (success : admitted 4 1 16 caller CountdownWitness.P.base before 10)
 (failure : admitted 0 1 16 ScalarDual.rejectedCaller CountdownWitness.P.base ScalarDual.rejectedMachine 10) :
 InterfaceV3.PendingRecursiveReturns 1 F approved admitted "scalarCountdown"
 (DisjointScalarEntry.args rfl reference ScalarDual.choice) (.val .uint (.user "result") (some (.here : Idx Γ (.val .uint))))
 (ScalarRecursiveSource.step CountdownWitness.A rfl) where
 plan := outputPlan
 required_profile := agreement
 required_coverage := coverage
 required_successful_entry := ⟨4,1,16,caller,CountdownWitness.P.base,before,10,
   ⟨caller.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩,success,good_entry 4,ScalarDual.good_source⟩
 required_reverting_entry := ⟨0,1,16,ScalarDual.rejectedCaller,CountdownWitness.P.base,ScalarDual.rejectedMachine,10,failure,bad_entry 0,ScalarDual.bad_source⟩
 required_source_coherence := producer.required_source_coherence
 required_return := producer.required_return
 required_bare_revert := producer.required_bare_revert

theorem unchanged_code (n k : Nat) : (outputPlan.at n).code=(ScalarDual.outputPlan.at k).code := rfl

theorem good_execution (depth : Nat) : run (outputPlan.at depth).code before=.ok machine 0 := ScalarDual.good_execution

theorem bad_execution (depth : Nat) : run (outputPlan.at depth).code ScalarDual.rejectedMachine=.revert := ScalarDual.bad_execution

theorem repaired_index_five :
 (¬InterfaceV1.Entry (ScalarDual.outputPlan.at 5) 1 1 16 F caller CountdownWitness.P.base before 10) ∧
 InterfaceV1.Entry (outputPlan.at 5) 1 1 16 F caller CountdownWitness.P.base before 10 :=
 ⟨ScalarDual.Controls.index_five_not_entry,good_entry 5⟩

theorem insufficient_actual_demand : ¬InterfaceV1.Entry (outputPlan.at 5) 1 1 15 F caller CountdownWitness.P.base before 10 := by
 intro invalid
 have space := invalid.reserve
 change 10+ScalarDemand.reserve ScalarDual.choice caller≤15 at space
 rw [good_reserve] at space
 omega

theorem failure_control_floor : ¬InterfaceV1.Entry (outputPlan.at 0) 1 1 14 F ScalarDual.rejectedCaller CountdownWitness.P.base ScalarDual.rejectedMachine 10 := by
 intro invalid
 have space := invalid.reserve
 change 10+ScalarDemand.reserve ScalarDual.choice ScalarDual.rejectedCaller≤14 at space
 rw [bad_reserve] at space
 omega

theorem complete_observations :
 (machine.stack,[machine.mem 0,machine.mem 1,machine.mem 2,machine.mem 3,machine.mem 4,
 machine.mem 5,machine.mem 6,machine.mem 7,machine.mem 8,machine.mem 9,machine.mem 10,
 machine.mem 11,machine.mem 12,machine.mem 13,machine.mem 14,machine.mem 15,machine.mem 16,
 machine.mem 17,machine.mem 18,machine.mem 19,machine.mem 20,machine.mem 21])=
 ([w[77]],[w[22],w[16],w[16],w[2],w[3],w[16],w[3],w[3],w[10],w[10],w[16],w[3],
 w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[0],w[1],w[4]]) := ScalarDual.Controls.complete_observations

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarDemandDual
