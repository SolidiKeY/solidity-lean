import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarPhysicalInputs
import Solidity.Backend.InternalFlow.RuntimeFrameV3FrozenScopeHorizons

/-! Universal physical coverage and real dual membership for the frozen
scoped family. Only agreement with an independently supplied approved domain
is pending in the assembly below. This is NOT original source-profile
provenance, general recursive selection or full failure/termination adequacy. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.FrozenScopeCoverage
open Evm Evm.Memory
open DisjointScalarReturn.Client (Γ F reference)

/-- Physical feasibility only, with no source outcome or index filtering. -/
def inputs : Nat → InterfaceV3.Admission SameCallInputs.C Γ :=
 ScalarPhysicalInputs.domain 1 5 9 F ScalarReentry.count

theorem coverage : InterfaceV3.FamilyEntryCoverage 1 F inputs FrozenScopeRuntime.producer.plan :=
 ScalarPhysicalInputs.coverage ScalarReentry.emitted reference .here

theorem good_member (depth : Nat) : inputs depth 1 16 ScalarContinuation.final
 ScalarContinuation.finalBase ScalarContinuation.target 10 :=
 ScalarPhysicalInputs.of_entry ScalarReentry.emitted reference .here (ScalarReentry.entry depth)

theorem bad_member (depth : Nat) : inputs depth 1 16 SameCallInputs.caller
 SameCallInputs.addresses SameCallInputs.machine 10 :=
 ScalarPhysicalInputs.of_entry ScalarReentry.emitted reference .here (FrozenScopeClient.bad_entry depth)

/-- All runtime-side V3 fields are proved. The remaining agreement is an
explicit external duty, never chosen as reflexivity or an approved := inputs
alias. ApprovedProfile's original-source provenance duty remains separate. -/
def with_profile (approved : Nat → InterfaceV3.Admission SameCallInputs.C Γ)
 (agreement : InterfaceV3.FamilyAdmissionAgreement approved inputs) :
 InterfaceV3.PendingRecursiveReturns 1 F approved inputs "scalarCountdown"
 (DisjointScalarEntry.args rfl reference ScalarReentry.count)
 (.val .uint (.user "result") (some (.here : Idx Γ (.val .uint))))
 (FrozenScopeFamily.step CountdownWitness.A rfl .uint (.user "sameCall")) where
 plan := FrozenScopeRuntime.producer.plan
 required_profile := agreement
 required_coverage := coverage
 required_successful_entry := ⟨4,1,16,ScalarContinuation.final,ScalarContinuation.finalBase,
   ScalarContinuation.target,10,⟨ScalarReentry.Endpoint.resultState,List.prefix_refl _⟩,
   good_member 4,FrozenScopeClient.good_entry,FrozenScopeClient.good_source⟩
 required_reverting_entry := ⟨0,1,16,SameCallInputs.caller,SameCallInputs.addresses,
   SameCallInputs.machine,10,bad_member 0,FrozenScopeClient.bad_entry 0,FrozenScopeClient.bad_source 0⟩
 required_source_coherence := FrozenScopeRuntime.producer.required_source_coherence
 required_return := FrozenScopeRuntime.producer.required_return
 required_bare_revert := FrozenScopeRuntime.producer.required_bare_revert

theorem no_index_filter (left right : Nat) : inputs left=inputs right := rfl

/-- The unchanged exhausted base is physically covered as well. Coverage
therefore cannot be used to infer full source/target outcome equivalence. -/
theorem exhausted_is_covered :
 inputs 0 1 16 ScalarContinuation.final ScalarContinuation.finalBase ScalarContinuation.target 10 ∧
 (FrozenScopeClient.statement 0).run ScalarContinuation.final=.error .exhausted :=
 ⟨good_member 0,(FrozenScopeHorizons.exhausted_boundary 0 (by decide)).1⟩

theorem wrong_frame : ¬inputs 4 1 9 ScalarContinuation.final
 ScalarContinuation.finalBase ScalarContinuation.target 10 :=
 fun input => Nat.lt_irrefl 9 input.pointerBelow

end Solidity.Backend.InternalFlow.RuntimeFrame.FrozenScopeCoverage
