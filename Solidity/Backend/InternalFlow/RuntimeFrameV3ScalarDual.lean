import Solidity.Backend.InternalFlow.RuntimeFrameArgumentAgreement
import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV3
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarClaims
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarPlanControls
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarRecursiveAgreement

/-! One selected scalar-family image has real success and bare-revert entries
at different represented callers. The frozen V2 family producer is inhabited;
this is not V3 approved-domain coverage or general source-body selection. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarDual
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open DisjointScalarReturn.Client

def choiceGuard : Val CountdownWitness.P.C Γ .bool :=
 .binop .gt rfl rfl (.simple (.local (.there .here))) (.simple (.lit 0 rfl))
def choice : Val CountdownWitness.P.C Γ .uint := .ternary choiceGuard count badCount
def emitted : ScalarEmitter.Emission 1 5 16 9 8 F choice :=
 (ScalarEmitter.compile 1 5 16 9 8 F choice).get (by rfl)
def outputPlan := ScalarPlan.plan emitted reference (.here : Idx Γ (.val .uint))
def statement (depth : Nat) := DisjointScalarReturn.call rfl reference choice (.here : Idx Γ (.val .uint)) "scalarCountdown" depth

def rejectedCaller := caller.setLocal (.there .here : Idx Γ (.val .uint)) (countValue 0 W_pos)
def rejectedMachine := writeMachine before 3 w[0]

theorem selected : ScalarEmitter.compile 1 5 16 9 8 F choice=some emitted := rfl

theorem good_eval : choice.evalT caller=.ok (countValue 3 (by decide)) := by
 with_unfolding_all rfl

theorem bad_eval : choice.evalT rejectedCaller=.error .revert := by
 with_unfolding_all rfl

theorem rejected_repr : StateRepr 1 1 16 F rejectedCaller CountdownWitness.P.base rejectedMachine :=
 initial.setVal (.there .here) (countValue 0 W_pos) w[0] (ReprV.uint_of rfl)

theorem good_entry : InterfaceV1.Entry (outputPlan.at 4) 1 1 16 F caller CountdownWitness.P.base before 10 where
 represented := initial
 callerBound := by decide
 resultBound := by decide
 workspace := by decide
 pointerAbove := by decide
 pointerBelow := by decide
 payloadAbove := by decide
 reserve := by decide
 controlSpace := by decide
 separate := Or.inl (by decide)
 noWrap := by decide
 cursor := rfl
 capacity := Or.inl rfl

theorem bad_entry : InterfaceV1.Entry (outputPlan.at 0) 1 1 16 F rejectedCaller CountdownWitness.P.base rejectedMachine 10 where
 represented := rejected_repr
 callerBound := by decide
 resultBound := by decide
 workspace := by decide
 pointerAbove := by decide
 pointerBelow := by decide
 payloadAbove := by decide
 reserve := by decide
 controlSpace := by decide
 separate := Or.inl (by decide)
 noWrap := by decide
 cursor := rfl
 capacity := Or.inl rfl

theorem good_source : (statement 4).run caller=.ok ⟨caller.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩ := by
 have source := ScalarClaims.source_value rfl reference choice .here "scalarCountdown" 4 caller
   CountdownWitness.P.r0 (by with_unfolding_all rfl) (countValue 3 (by decide)) good_eval
 simpa only [show (countValue 3 (by decide)).word.val=3 from rfl,if_pos (show 3<4 from by decide)] using source

theorem bad_source : (statement 0).run rejectedCaller=.error .revert :=
 ScalarClaims.source_revert rfl reference choice .here "scalarCountdown" 0 rejectedCaller bad_eval

theorem successful_entry : InterfaceV2.SuccessfulEntry 1 F (statement 4) (outputPlan.at 4) :=
 ⟨1,16,caller,CountdownWitness.P.base,before,10,⟨caller.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩,good_entry,good_source⟩

theorem reverting_entry : InterfaceV2.RevertingEntry 1 F (statement 0) (outputPlan.at 0) :=
 ⟨1,16,rejectedCaller,CountdownWitness.P.base,rejectedMachine,10,bad_entry,bad_source⟩

def producer : InterfaceV2.PendingRecursiveReturns 1 F "scalarCountdown"
 (DisjointScalarEntry.args rfl reference choice) (.val .uint (.user "result") (some (.here : Idx Γ (.val .uint))))
 (ScalarRecursiveSource.step CountdownWitness.A rfl) where
 plan := outputPlan
 required_successful_entry := ⟨4,successful_entry⟩
 required_source_coherence := ScalarRecursiveSource.source_coherence rfl "scalarCountdown" _ _
 required_return := fun depth => ScalarClaims.returns emitted (by decide) rfl reference .here "scalarCountdown" depth
 required_bare_revert := fun depth => ScalarClaims.bare_revert emitted (by decide) rfl reference .here "scalarCountdown" depth

theorem good_execution : run (outputPlan.at 4).code before=.ok machine 0 := by
 have shared := ArgumentAgreement.entry_suffix emitted.value value reference initial (c:=5) (by decide) (by decide)
   (countValue 3 (by decide)) good_eval rfl
 change run (DisjointScalarReturn.code 1 5 reference emitted.value (.here : Idx Γ (.val .uint)) 9 8) before=_
 unfold DisjointScalarReturn.code
 rw [shared]
 exact specification.1

theorem bad_execution : run (outputPlan.at 0).code rejectedMachine=.revert :=
 producer.required_bare_revert 0 1 16 rejectedCaller CountdownWitness.P.base rejectedMachine 10 bad_entry bad_source

/-- Assemble the frozen V3 record from explicit external agreement, coverage
and memberships. Agreement alone does not authenticate approved-domain
provenance; that remains a separate ApprovedProfile duty. No domain, whitelist
or target simulation is selected here. -/
def with_domain (approved admitted : Nat → InterfaceV3.Admission CountdownWitness.P.C Γ)
 (agreement : InterfaceV3.FamilyAdmissionAgreement approved admitted)
 (coverage : InterfaceV3.FamilyEntryCoverage 1 F admitted outputPlan)
 (success : admitted 4 1 16 caller CountdownWitness.P.base before 10)
 (failure : admitted 0 1 16 rejectedCaller CountdownWitness.P.base rejectedMachine 10) :
 InterfaceV3.PendingRecursiveReturns 1 F approved admitted "scalarCountdown"
 (DisjointScalarEntry.args rfl reference choice) (.val .uint (.user "result") (some (.here : Idx Γ (.val .uint))))
 (ScalarRecursiveSource.step CountdownWitness.A rfl) where
 plan := outputPlan
 required_profile := agreement
 required_coverage := coverage
 required_successful_entry := ⟨4,1,16,caller,CountdownWitness.P.base,before,10,
   ⟨caller.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩,success,good_entry,good_source⟩
 required_reverting_entry := ⟨0,1,16,rejectedCaller,CountdownWitness.P.base,rejectedMachine,10,failure,bad_entry,bad_source⟩
 required_source_coherence := producer.required_source_coherence
 required_return := producer.required_return
 required_bare_revert := producer.required_bare_revert

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarDual
