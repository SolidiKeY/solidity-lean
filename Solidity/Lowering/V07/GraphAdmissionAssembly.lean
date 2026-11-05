import Solidity.Lowering.V07.LocationGraphCompleteness
import Solidity.Lowering.V07.LocationProducerControls
import Solidity.Lowering.V07.SourceRefusal
import Solidity.Lowering.P8.DeclarationGraphAdmission

/-!
# H24 declaration-graph admission: assembly from named premises

`LocationGraphInterface.Admission producer` (the H24 field of
`P8.DeclarationGraphAdmission.Producer`) has two fields over every accepted
source of an admitted input: a per-location certificate (`graphs`) and actual
Source refusal (`source_refuses`). This module reduces both to premises about
the accepted `Source.Env` alone and supplies no producer.

- `graph_of_produce`/`graph_of_premises`: the computed per-location producer
  (`LocationGraphProducer.produce`) yields the certificate; its success follows
  from `GraphPremises`, the structural inputs of
  `LocationGraphCompleteness.producer_success` (selection, related and
  supported fields, nonempty distinct fields, a valid comparison rank).
- `EnvAdmission E`: certificates at every location plus refusal, for one
  environment. `env_admission_iff` shows that, on the current Source typing,
  refusal is exactly `SourceRefusal.NameableStructsMappingFree`.
- `admission`/`declarationGraphProducer`: the H24 field and the additive P8
  record from those per-environment premises. Existing P8 statements,
  premises and exclusions are unchanged.

Open (recorded in the feature document): every `P8a.Producer`-indexed result
is vacuous until P8-SPEC-LAW1 is resolved; `GraphPremises` is not derived
from accepted Source (Source admits inline-recursive structs,
`GraphAdmissionBoundary`); refusal for mapping-containing structs needs the
VY5 Source repair (`SourceRefusal.envLocOK`).
-/
namespace Solidity.Lowering.V07.GraphAdmissionAssembly
open Solidity Solidity.Lowering.V07 LocationGraphInterface LocationGraphProducer

/-- A successful computed producer run is a certificate. -/
theorem graph_of_produce (origin : Name) (E : Source.Env) (loc : Source.DataLoc)
    (h : (produce origin E loc).isSome = true) :
    ∃ n, ∃ G : TypeGraph.Schema n, Nonempty (LocationDeclarationGraph E loc G) := by
  cases hp : produce origin E loc with
  | none => rw [hp] at h; cases h
  | some v => exact ⟨_, v.1, ⟨v.2⟩⟩

/-- The structural inputs of `LocationGraphCompleteness.producer_success`. The
rank is proof-only; no run of the producer is a premise. -/
structure GraphPremises (E : Source.Env) (loc : Source.DataLoc) where
  selected : SelectionOK E loc
  fs : Fin (choices E loc).length → List (Name × TypeGraph.Ty (choices E loc).length)
  related : ∀ i, GraphFieldsRel E.layout (name E loc) (sourceFields E loc i) (fs i)
  supported : ∀ i s, s ∈ sourceFields E loc i → LocalFieldSupport.Supported E.layout s.2
  nonempty : ∀ i, (fs i).isEmpty = false
  distinct : ∀ i, Semantics.nodupKeysB (fs i) = true
  rank : Fin (choices E loc).length → Nat
  valid : ∀ i f, f ∈ fs i → f.2.inlineRank rank < rank i

theorem graph_of_premises (E : Source.Env) (loc : Source.DataLoc) (p : GraphPremises E loc) :
    ∃ n, ∃ G : TypeGraph.Schema n, Nonempty (LocationDeclarationGraph E loc G) :=
  graph_of_produce "h24-graph-admission" E loc
    (LocationGraphCompleteness.producer_success E loc _ p.selected p.fs p.related p.supported
      p.nonempty p.distinct p.rank p.valid)

/-- Both H15 obligations for one accepted environment. -/
structure EnvAdmission (E : Source.Env) : Prop where
  graphs : ∀ loc : Source.DataLoc,
    ∃ n, ∃ G : TypeGraph.Schema n, Nonempty (LocationDeclarationGraph E loc G)
  source_refuses : SourceRefusesNonAdmissible E

/-- On the current Source typing, per-environment admission is certificates
plus mapping-free nameable structs. -/
theorem env_admission_iff (E : Source.Env) :
    EnvAdmission E ↔ (∀ loc : Source.DataLoc,
      ∃ n, ∃ G : TypeGraph.Schema n, Nonempty (LocationDeclarationGraph E loc G)) ∧
      SourceRefusal.NameableStructsMappingFree E :=
  ⟨fun h => ⟨h.graphs, (SourceRefusal.refuses_iff E).mp h.source_refuses⟩,
   fun h => ⟨h.1, (SourceRefusal.refuses_iff E).mpr h.2⟩⟩

theorem env_admission_of_premises (E : Source.Env) (premises : ∀ loc, GraphPremises E loc)
    (free : SourceRefusal.NameableStructsMappingFree E) : EnvAdmission E :=
  ⟨fun loc => graph_of_premises E loc (premises loc), SourceRefusal.refuses_of_mapping_free E free⟩

section Producer
variable {S : P8.P8a.Spec} {reference : P8.P8a.OperationalReference}
  {origins : P8.P8a.SourceOrigins S} {roots : P8.P8a.RootModel S}

/-- The H24 field from per-accepted-environment admission. -/
def admission (producer : P8.P8a.Producer S reference origins roots)
    (env : ∀ (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r)
      (art : Roadmap.Artifact), EnvAdmission (P8Bindings.acceptedSource producer i r h art).1) :
    Admission producer where
  graphs i r h art loc := (env i r h art).graphs loc
  source_refuses i r h art := (env i r h art).source_refuses

/-- The additive P8 record (`DeclarationGraphAdmission.Producer`). -/
def declarationGraphProducer (producer : P8.P8a.Producer S reference origins roots)
    (env : ∀ (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r)
      (art : Roadmap.Artifact), EnvAdmission (P8Bindings.acceptedSource producer i r h art).1) :
    P8.DeclarationGraphAdmission.Producer S reference origins roots :=
  ⟨producer, admission producer env⟩

end Producer

/-! ## Controls -/

/-- A mapping-free three-struct chain: certificates at all three locations by
the actual producer, and refusal on the current Source typing. -/
def chainEnv : Source.Env := RecursiveGraphControls.chain

theorem chain_produces : ∀ loc, (produce "h24-chain" chainEnv loc).isSome = true := by
  intro loc
  cases loc <;> decide

theorem chain_admitted : EnvAdmission chainEnv :=
  ⟨fun loc => graph_of_produce "h24-chain" chainEnv loc (chain_produces loc),
   SourceRefusal.refuses_of_decls chainEnv (by decide)⟩

/-- The same chain beside a mapping struct: certificates still exist at every
location (the mapping struct is selected only in storage), yet the current
Source typing admits `Loop memory x;`, so admission fails on refusal alone. -/
def mixedEnv : Source.Env := LocationProducerControls.chain

theorem mixed_produces : ∀ loc, (produce "h24-mixed" mixedEnv loc).isSome = true := by
  intro loc
  cases loc <;> decide

theorem mixed_memory_excludes_mapping : (choices mixedEnv .memory).length = 3 ∧
    (choices mixedEnv .storage).length = 4 := by
  decide

theorem mixed_not_admitted : ¬ EnvAdmission mixedEnv := by
  intro h
  have hd : mixedEnv.lookupPath none ⟨"Loop", []⟩ = [RecursiveGraphControls.mapDecl] := rfl
  exact SourceRefusal.not_refuses_of_mapping_struct mixedEnv none ⟨"Loop", []⟩ _ hd rfl
    (by decide) h.source_refuses

theorem mixed_graphs : ∀ loc : Source.DataLoc,
    ∃ n, ∃ G : TypeGraph.Schema n, Nonempty (LocationDeclarationGraph mixedEnv loc G) :=
  fun loc => graph_of_produce "h24-mixed" mixedEnv loc (mixed_produces loc)

/-- info: 'Solidity.Lowering.V07.GraphAdmissionAssembly.graph_of_produce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms graph_of_produce
/-- info: 'Solidity.Lowering.V07.GraphAdmissionAssembly.graph_of_premises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms graph_of_premises
/-- info: 'Solidity.Lowering.V07.GraphAdmissionAssembly.env_admission_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms env_admission_iff
/-- info: 'Solidity.Lowering.V07.GraphAdmissionAssembly.env_admission_of_premises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms env_admission_of_premises
/-- info: 'Solidity.Lowering.V07.GraphAdmissionAssembly.chain_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms chain_admitted
/-- info: 'Solidity.Lowering.V07.GraphAdmissionAssembly.mixed_not_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixed_not_admitted
/-- info: 'Solidity.Lowering.V07.GraphAdmissionAssembly.mixed_graphs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixed_graphs

end Solidity.Lowering.V07.GraphAdmissionAssembly
