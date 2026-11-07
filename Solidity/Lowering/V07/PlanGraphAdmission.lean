import Solidity.Lowering.V07.GraphAdmissionAssembly
import Solidity.Lowering.P8.PlanWitness

/-!
# H24 declaration-graph admission at the P8 model producer

`P8.PlanWitness.planProducer` inhabits the frozen `P8a.Producer`. Its origins
map every admitted input to `sourceOf`, whose environment is
`P8.PlanWitness.emptyEnv = ⟨[]⟩`, so the hypothesis of
`GraphAdmissionAssembly.admissionOfEmpty` (`accepted_empty`) holds by `rfl`. The record is degenerate (zero-node certificates, no struct
to refuse; see `GraphAdmissionAssembly.empty_admitted`): it shows that the
additive `DeclarationGraphAdmission.Producer` is inhabited, not that H24 holds
for real accepted Source.
-/
namespace Solidity.Lowering.V07.PlanGraphAdmission
open Solidity.Lowering P8.PlanWitness

/-- Every accepted Source of the model producer has the empty environment. -/
theorem accepted_empty (i : planSource.Input) (r : planSource.Resolved)
    (h : planProducer.admission.frontend i = some r) (art : Roadmap.Artifact) :
    (P8Bindings.acceptedSource planProducer i r h art).1 = GraphAdmissionAssembly.emptyEnv :=
  rfl

/-- The H24 field at the model producer. -/
def planAdmission : LocationGraphInterface.Admission planProducer :=
  GraphAdmissionAssembly.admissionOfEmpty planProducer accepted_empty

/-- The additive P8 record at the model producer. -/
def planDeclarationGraphProducer :
    P8.DeclarationGraphAdmission.Producer planSource planReference planOrigins planRoots :=
  GraphAdmissionAssembly.declarationGraphProducerOfEmpty planProducer accepted_empty

/-- The record carries exactly the model producer. -/
theorem plan_record_producer : planDeclarationGraphProducer.1 = planProducer := rfl

/-- info: 'Solidity.Lowering.V07.PlanGraphAdmission.accepted_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_empty
/-- info: 'Solidity.Lowering.V07.PlanGraphAdmission.planAdmission' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms planAdmission
/-- info: 'Solidity.Lowering.V07.PlanGraphAdmission.planDeclarationGraphProducer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms planDeclarationGraphProducer
/-- info: 'Solidity.Lowering.V07.PlanGraphAdmission.plan_record_producer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms plan_record_producer

end Solidity.Lowering.V07.PlanGraphAdmission
