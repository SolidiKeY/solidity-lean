import Solidity.Lowering.V07.GraphAdmissionAssembly

/-! Necessary H24 constraints at the exact accepted Source origin. These
proofs retain the actual environment/program equality; they neither construct
an origin nor establish admission or execution adequacy. They expose the
current Source typing restriction for a nameable mapping-bearing struct,
without a Nat-resource premise or a claim that all library producers fail.
Regression purpose: an empty-environment model cannot be substituted for a
consumer's different, library-containing Source program. No Source definition,
frozen interface, profile or failure assumption is changed. -/
namespace Solidity.Lowering.P8.DeclarationGraphConstraints
open Solidity Solidity.Lowering.V07

variable {S : P8a.Spec} {reference : P8a.OperationalReference}
  {origins : P8a.SourceOrigins S} {roots : P8a.RootModel S}

/-- Every accepted origin of an H24 producer satisfies the exact current-Source
refusal characterization, at the same artifact and frontend derivation. -/
theorem accepted_mapping_free
    (producer : DeclarationGraphAdmission.Producer S reference origins roots)
    (input : S.Input) (resolved : S.Resolved)
    (accepted : producer.base.admission.frontend input = some resolved)
    (artifact : Roadmap.Artifact) :
    SourceRefusal.NameableStructsMappingFree
      (P8Bindings.acceptedSource producer.base input resolved accepted artifact).1 :=
  (SourceRefusal.refuses_iff _).mp
    (producer.declarationGraphs.source_refuses input resolved accepted artifact)

/-- Consumer linkage retains equality of the whole environment-indexed Source
program, including its pipeline and fixed parameters, not merely an equal name. -/
theorem program_mapping_free
    (producer : DeclarationGraphAdmission.Producer S reference origins roots)
    (input : S.Input) (resolved : S.Resolved)
    (accepted : producer.base.admission.frontend input = some resolved)
    (artifact : Roadmap.Artifact) (E : Source.Env) (program : Source.SrcProg E)
    (same : P8Bindings.acceptedSource producer.base input resolved accepted artifact = ⟨E,program⟩) :
    SourceRefusal.NameableStructsMappingFree E := by
  have environment := congrArg Sigma.fst same
  simpa only [environment] using accepted_mapping_free producer input resolved accepted artifact

/-- This particular accepted program cannot contain a nameable mapping-bearing
struct on the current typing. All lookup/kind/mapping facts concern its exact
Source environment. This conditional contradiction is not a witness of
admission and does not refute programs lacking such a declaration. -/
theorem mapping_program_origin_impossible
    (producer : DeclarationGraphAdmission.Producer S reference origins roots)
    (input : S.Input) (resolved : S.Resolved)
    (accepted : producer.base.admission.frontend input = some resolved)
    (artifact : Roadmap.Artifact) (E : Source.Env) (program : Source.SrcProg E)
    (same : P8Bindings.acceptedSource producer.base input resolved accepted artifact = ⟨E,program⟩)
    (scope : Option String) (path : Source.IdPath) (declaration : Source.Decl)
    (lookup : E.lookupPath scope path = [declaration])
    (kind : declaration.kind = .struct)
    (mapping : E.hasMapping (E.structCount + 1)
      (.struct .storage ⟨declaration.scope,declaration.name⟩) = true) : False := by
  have clear := program_mapping_free producer input resolved accepted artifact E program same
    scope path declaration lookup kind
  rw [mapping] at clear
  cases clear

/-- info: 'Solidity.Lowering.P8.DeclarationGraphConstraints.accepted_mapping_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_mapping_free
/-- info: 'Solidity.Lowering.P8.DeclarationGraphConstraints.program_mapping_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms program_mapping_free
/-- info: 'Solidity.Lowering.P8.DeclarationGraphConstraints.mapping_program_origin_impossible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mapping_program_origin_impossible

end Solidity.Lowering.P8.DeclarationGraphConstraints
