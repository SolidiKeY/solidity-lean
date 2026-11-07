import Solidity.Lowering.P8.DeclarationGraphAdmissionV2

/-! H57/H128 consumer regression: mapping-bearing metadata keeps all computed
location graphs under v2 refusal, while the frozen v1 negative stays true.
Existing Source-owner controls separately provide actual initialized-storage
and compatible Bool derivations; none is copied here. This is local-declaration
and graph evidence, not whole-program Source/origin/lifecycle adequacy. -/
namespace H128.H24V2ConsumptionControls
open Solidity Solidity.Lowering
open V07

def mixed_admitted : P8.DeclarationGraphAdmissionV2.EnvAdmission LocationProducerControls.mixed :=
  P8.DeclarationGraphAdmissionV2.of_graphs _ (fun loc => by
    cases loc with
    | storage =>
      exact GraphAdmissionAssembly.graph_of_produce
        "h15-computed-storage" _ .storage LocationProducerControls.mixed_storage_success
    | memory =>
      exact GraphAdmissionAssembly.graph_of_produce
        "h15-computed-memory" _ .memory LocationProducerControls.mixed_memory_success
    | calldata =>
      exact GraphAdmissionAssembly.graph_of_produce
        "h15-computed-calldata" _ .calldata LocationProducerControls.mixed_calldata_success)

/-- Joint nonempty versioned environment contract, retaining existing physical IDs. -/
theorem mixed_contract_and_ids :
    P8.DeclarationGraphAdmissionV2.EnvAdmission LocationProducerControls.mixed ∧
    (LocationGraphProducer.choices LocationProducerControls.mixed .memory).length = 1 ∧
    LocationProducerControls.memoryResult.1.declId ⟨0, by decide⟩ = 1 := by
  exact ⟨mixed_admitted, LocationProducerControls.memory_physical_identity.1,
    LocationProducerControls.memory_physical_identity.2.1⟩

/-- V2 is an explicit version change, never a repair of the frozen v1 predicate. -/
theorem no_refusal_backtransport :
    ¬ (∀ E, P8.DeclarationGraphAdmissionV2.SourceRefusesNonAdmissible E →
      LocationGraphInterface.SourceRefusesNonAdmissible E) := by
  intro transport
  exact LocationGraphLaws.refusal_missing (transport _ (P8.DeclarationGraphAdmissionV2.source_refuses _))

/-- info: 'H128.H24V2ConsumptionControls.mixed_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixed_admitted
/-- info: 'H128.H24V2ConsumptionControls.mixed_contract_and_ids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixed_contract_and_ids
/-- info: 'H128.H24V2ConsumptionControls.no_refusal_backtransport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_refusal_backtransport
end H128.H24V2ConsumptionControls
