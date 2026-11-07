import Solidity.Lowering.V07.GraphAdmissionAssembly
import Solidity.Source.TypingV2

/-! H57/H128 versioned H24 local-declaration refusal.
Regression purpose: consume actual environment-aware v2 derivations without
rewriting the frozen v1 refusal or its mapping-bearing negative witnesses.
Graphs, accepted-source environment/artifact indices and base producer identity
remain unchanged. This is neither whole-program v2 typing nor a concrete
Source/origin/compiler/lifecycle producer; v1 consumers require separate migration. -/
namespace Solidity.Lowering.P8.DeclarationGraphAdmissionV2
open Solidity Solidity.Lowering.V07 LocationGraphInterface

/-- The v2 pair of the frozen v1 LOCAL-declaration refusal predicate. -/
def SourceRefusesNonAdmissible (E : Source.Env) : Prop :=
  ∀ (C : Source.Ctx), C.env = E → ∀ (k : Source.SCtx)
    (L L' : List (String × Source.STy)) (t : Source.Syn .typeName)
    (τ : Source.STy) (loc : Source.DataLoc) (x : String) (init : Source.Syn (.opt .expr)),
    t.ty C.env C.scope loc = some τ →
    Source.V2.StmtD C (k := k) L (.simpleStmt (.declVar (.varDecl t (some loc) x) init)) L' →
      AdmissibleLocation E τ loc

/-- Actual v2 derivations imply the unchanged H24 location policy in every environment. -/
theorem source_refuses (E : Source.Env) : SourceRefusesNonAdmissible E := by
  intro C same k L L' t ty loc name init typed derivation
  have admitted := Source.V2.declaration_admissible C k L L' t loc name init ty typed derivation
  rw [same] at admitted
  exact admitted

/-- The promoted Source check is the existing H24 environment-aware formula. -/
theorem location_policy_eq (E : Source.Env) (ty : Source.STy)
    (loc : Option Source.DataLoc) (initialized : Bool) :
    Source.envLocOK E ty loc initialized = SourceRefusal.envLocOK E ty loc initialized :=
  (SourceRefusal.envLocOK_eq_patch E ty loc initialized).symm

/-- Versioned per-environment contract; graph certificates are the original type. -/
structure EnvAdmission (E : Source.Env) : Prop where
  graphs : ∀ loc : Source.DataLoc,
    ∃ n, ∃ G : TypeGraph.Schema n, Nonempty (LocationDeclarationGraph E loc G)
  source_refuses : SourceRefusesNonAdmissible E

/-- V2 local refusal does not discharge graph construction or its structural premises. -/
def of_graphs (E : Source.Env)
    (graphs : ∀ loc : Source.DataLoc,
      ∃ n, ∃ G : TypeGraph.Schema n, Nonempty (LocationDeclarationGraph E loc G)) :
    EnvAdmission E := ⟨graphs, source_refuses E⟩

/-- Reuse all selection, field, nonempty/distinct and rank obligations unchanged. -/
def of_premises (E : Source.Env) (premises : ∀ loc, GraphAdmissionAssembly.GraphPremises E loc) :
    EnvAdmission E :=
  of_graphs E (fun loc => GraphAdmissionAssembly.graph_of_premises E loc (premises loc))

/-- Reuse a v1 record's graphs only; this is not a v1-to-v2 typing conversion. -/
def from_v1_graphs {E : Source.Env} (old : GraphAdmissionAssembly.EnvAdmission E) :
    EnvAdmission E := of_graphs E old.graphs

theorem from_v1_graphs_exact {E : Source.Env} (old : GraphAdmissionAssembly.EnvAdmission E) :
    (from_v1_graphs old).graphs = old.graphs := rfl

section Producer
variable {S : P8a.Spec} {reference : P8a.OperationalReference}
  {origins : P8a.SourceOrigins S} {roots : P8a.RootModel S}

/-- H57 pair of v1 Admission, with exactly the same acceptedSource/artifact indices. -/
structure Admission (producer : P8a.Producer S reference origins roots) where
  graphs : ∀ (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r)
    (art : Roadmap.Artifact) (loc : Source.DataLoc),
    ∃ n, ∃ G : TypeGraph.Schema n,
      Nonempty (LocationDeclarationGraph (P8Bindings.acceptedSource producer i r h art).1 loc G)
  source_refuses : ∀ (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r)
    (art : Roadmap.Artifact),
    SourceRefusesNonAdmissible (P8Bindings.acceptedSource producer i r h art).1

/-- A separately named producer contract; no coercion into frozen v1 consumers. -/
structure Producer (S : P8a.Spec) (reference : P8a.OperationalReference)
    (origins : P8a.SourceOrigins S) (roots : P8a.RootModel S) where
  base : P8a.Producer S reference origins roots
  declarationGraphs : Admission base

def admission (producer : P8a.Producer S reference origins roots)
    (env : ∀ (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r)
      (art : Roadmap.Artifact), EnvAdmission (P8Bindings.acceptedSource producer i r h art).1) :
    Admission producer where
  graphs i r h art loc := (env i r h art).graphs loc
  source_refuses i r h art := (env i r h art).source_refuses

def declarationGraphProducer (producer : P8a.Producer S reference origins roots)
    (env : ∀ (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r)
      (art : Roadmap.Artifact), EnvAdmission (P8Bindings.acceptedSource producer i r h art).1) :
    Producer S reference origins roots := ⟨producer, admission producer env⟩

end Producer

/-- info: 'Solidity.Lowering.P8.DeclarationGraphAdmissionV2.source_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_refuses
/-- info: 'Solidity.Lowering.P8.DeclarationGraphAdmissionV2.location_policy_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms location_policy_eq
/-- info: 'Solidity.Lowering.P8.DeclarationGraphAdmissionV2.of_premises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms of_premises
/-- info: 'Solidity.Lowering.P8.DeclarationGraphAdmissionV2.from_v1_graphs_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms from_v1_graphs_exact
/-- info: 'Solidity.Lowering.P8.DeclarationGraphAdmissionV2.admission' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms admission
/-- info: 'Solidity.Lowering.P8.DeclarationGraphAdmissionV2.declarationGraphProducer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declarationGraphProducer
end Solidity.Lowering.P8.DeclarationGraphAdmissionV2
