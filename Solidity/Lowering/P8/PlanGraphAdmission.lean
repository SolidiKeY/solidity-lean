import Solidity.Lowering.P8.PlanWitness
import Solidity.Lowering.V07.GraphAdmissionAssembly

/-! MODEL-only H121 consumer of the shared V07 empty-environment helper.
Regression purpose: inhabit the model H24 record while preserving its exact
existing base producer, without duplicating declaration-refusal proofs.
This remains the PlanWitness model (empty Source program, model reference),
not actual Source/sessionAt or aggregate-lifecycle adequacy. -/
namespace Solidity.Lowering.P8.PlanGraphAdmission

def producer : DeclarationGraphAdmission.Producer
    PlanWitness.planSource PlanWitness.planReference PlanWitness.planOrigins PlanWitness.planRoots :=
  V07.GraphAdmissionAssembly.declarationGraphProducerOfEmpty
    PlanWitness.planProducer (fun _ _ _ _ => rfl)

theorem base_exact : producer.base = PlanWitness.planProducer := rfl

theorem inhabited : Nonempty (DeclarationGraphAdmission.Producer
    PlanWitness.planSource PlanWitness.planReference PlanWitness.planOrigins PlanWitness.planRoots) :=
  ⟨producer⟩

/-- info: 'Solidity.Lowering.P8.PlanGraphAdmission.producer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms producer

/-- info: 'Solidity.Lowering.P8.PlanGraphAdmission.base_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms base_exact

/-- info: 'Solidity.Lowering.P8.PlanGraphAdmission.inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inhabited

end Solidity.Lowering.P8.PlanGraphAdmission
