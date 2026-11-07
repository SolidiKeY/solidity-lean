import Solidity.Lowering.P8.ConditionalAssemblyV2
import Solidity.Lowering.P8.PlanGraphAdmission

/-! MODEL-only receipt/graph premise satisfiability and fail-closed receipt control.
Regression purpose: the joint v2 consumer binds the supplied model's exact
checker/origin/graph, and malformed receipts cannot supply that contract.
Reuse the existing PlanWitness/PlanGraphAdmission without new Source cases.
Its empty Source program/model reference is NOT actual Source adequacy. -/
namespace H128.ConditionalH24V2Controls
open Solidity Solidity.Lowering Solidity.Roadmap Solidity.Roadmap.Controls
open P8

def model := ConditionalAssemblyV2.from_v1_graphs PlanGraphAdmission.producer

def input (toy : Toy) (pipeline : Pipeline) : ToyInput :=
  {text := toy.text, pipeline := pipeline}

def resolution (toy : Toy) (pipeline : Pipeline) : ToyRes :=
  ⟨toy, pipeline, (input toy pipeline).coder⟩

/-- Every existing toy shape/pipeline supplies an actual successful checker receipt. -/
theorem receipt (toy : Toy) (pipeline : Pipeline) :
    model.base.checkedFrontend.produce (input toy pipeline) = some (resolution toy pipeline, toy) := by
  change (accept (input toy pipeline)).map (fun r => (r, r.prog)) = _
  have parsed : accept (input toy pipeline) = some (resolution toy pipeline) := by
    simp only [accept, input, parse_text, ite_true, Option.map_some, resolution]
  rw [parsed]
  rfl

/-- Joint MODEL premise satisfiability, not independent actual-Source origin evidence. -/
theorem model_receipt_graph_premises (toy : Toy) (pipeline : Pipeline)
    (art : Artifact) (loc : Source.DataLoc) :
    ∃ n, ∃ G : TypeGraph.Schema n,
      Nonempty (V07.LocationGraphInterface.LocationDeclarationGraph
        (PlanWitness.sourceOf toy).1 loc G) ∧
      DeclarationGraphAdmissionV2.SourceRefusesNonAdmissible (PlanWitness.sourceOf toy).1 := by
  have joint := ConditionalAssemblyV2.checked_contract model (input toy pipeline)
    (resolution toy pipeline) toy (receipt toy pipeline) art loc
  exact joint.2

/-- The unchanged model checker rejects malformed input, for any alleged receipt. -/
theorem malformed_receipt_refused (r : ToyRes) (cert : Toy) :
    model.base.checkedFrontend.produce ({text := []} : ToyInput) ≠ some (r, cert) :=
  ConditionalAssemblyV2.rejected_receipt model _ r cert (by rfl)

/-- info: 'H128.ConditionalH24V2Controls.receipt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms receipt
/-- info: 'H128.ConditionalH24V2Controls.model_receipt_graph_premises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms model_receipt_graph_premises
/-- info: 'H128.ConditionalH24V2Controls.malformed_receipt_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms malformed_receipt_refused
end H128.ConditionalH24V2Controls
