import Solidity.Lowering.V07.P8Bindings

/-!
# H15 admissible-location declaration graph interface

Policy: certificates are required at locations where solc
0.8.38 admits the type; mappings, including mapping-containing aggregates,
are storage-only. This is an owner-reviewed interface revision, NOT a Source
profile exclusion.

Existing Source.hasMapping is reused as the location policy's executable
predicate. General agreement with solc and Source refusal are explicit proof
obligations; this file supplies no fake frontend, SourceSpec or Producer.
-/
namespace Solidity.Lowering.V07.LocationGraphInterface
open Solidity.Lowering.P8

/-- H15 type-location policy using the published Source mapping detector.
Its existing structCount+1 search is reused, not a new admission-depth cap. -/
def AdmissibleLocation (E : Source.Env) (τ : Source.STy) (loc : Source.DataLoc) : Prop :=
  loc = .storage ∨ E.hasMapping (E.structCount+1) τ = false

instance (E : Source.Env) (τ : Source.STy) (loc : Source.DataLoc) :
    Decidable (AdmissibleLocation E τ loc) :=
  inferInstanceAs (Decidable (loc = .storage ∨ E.hasMapping (E.structCount+1) τ = false))

/-- Declaration metadata is checked for each type at the requested location. -/
def StructAdmissible (E : Source.Env) (dn : Source.DeclName) (loc : Source.DataLoc) : Prop :=
  AdmissibleLocation E (.struct .storage dn) loc

instance (E : Source.Env) (dn : Source.DeclName) (loc : Source.DataLoc) :
    Decidable (StructAdmissible E dn loc) :=
  inferInstanceAs (Decidable (AdmissibleLocation E (.struct .storage dn) loc))

/-- H15 necessary Source LOCAL-DECLARATION refusal obligation, using actual
StmtD admission including initialization. Raw name resolution alone is not
whole-program admission. Parameter/return and whole-program coverage remain
separate obligations; no false generic refusal theorem is assumed here. -/
def SourceRefusesNonAdmissible (E : Source.Env) : Prop :=
  ∀ (C : Source.Ctx), C.env = E → ∀ (k : Source.SCtx)
    (L L' : List (String × Source.STy)) (t : Source.Syn .typeName)
    (τ : Source.STy) (loc : Source.DataLoc) (x : String) (init : Source.Syn (.opt .expr)),
    t.ty C.env C.scope loc = some τ →
    Source.StmtD C (k := k) L (.simpleStmt (.declVar (.varDecl t (some loc) x) init)) L' →
      AdmissibleLocation E τ loc

/-- H15 per-location certificate over existing intrinsic metadata. It covers
ALL and ONLY declarations admissible at loc, preserving original physical IDs.
This permits a memory-capable type beside a separate storage-only declaration;
it does not require every declaration in the source unit to share one location.
No Source/target value, heap, evaluator or AST representation changes. -/
structure LocationDeclarationGraph (E : Source.Env) (loc : Source.DataLoc) {n : Nat}
    (G : TypeGraph.Schema n) where
  sourceName : Fin n → Source.DeclName
  sourceName_injective : Function.Injective sourceName
  sourceIndex : Fin n → Fin E.decls.length
  identity : ∀ i, G.declId i = (sourceIndex i).val
  source_kind : ∀ i, (E.decls[sourceIndex i]).kind = .struct
  source_scope : ∀ i, (E.decls[sourceIndex i]).scope = (sourceName i).scope
  source_name : ∀ i, (E.decls[sourceIndex i]).name = (sourceName i).name
  source_resolves : ∀ i, E.declOf .struct (sourceName i) = some E.decls[sourceIndex i]
  source_admissible : ∀ i, StructAdmissible E (sourceName i) loc
  target_name : ∀ i, G.name i = (sourceName i).name
  sourceFields : Fin n → List (String × Source.STy)
  fields_resolve : ∀ i, E.structFields (sourceName i) loc = some (sourceFields i)
  fields_relate : ∀ i, GraphFieldsRel E.layout sourceName (sourceFields i) (G.fields i)
  complete : ∀ j : Fin E.decls.length, (E.decls[j]).kind = .struct →
    StructAdmissible E ⟨(E.decls[j]).scope,(E.decls[j]).name⟩ loc →
      ∃ i, sourceIndex i = j

/-- Existing storage certificates survive H15 unchanged. The proof is direct
field transport plus the automatically discharged storage-location policy. -/
def ofStorage {E : Source.Env} {n : Nat} {G : TypeGraph.Schema n}
    (c : DeclarationGraph E .storage G) : LocationDeclarationGraph E .storage G where
  sourceName := c.sourceName
  sourceName_injective := c.sourceName_injective
  sourceIndex := c.sourceIndex
  identity := c.identity
  source_kind := c.source_kind
  source_scope := c.source_scope
  source_name := c.source_name
  source_resolves := c.source_resolves
  source_admissible := fun _ => by simp only [StructAdmissible,AdmissibleLocation,true_or]
  target_name := c.target_name
  sourceFields := c.sourceFields
  fields_resolve := c.fields_resolve
  fields_relate := c.fields_relate
  complete := fun j kind _ => c.complete j kind

/-- H15 revised G18.01 target at the EXACT frozen P8a source origin.
Both fields are required: per-admissible-declaration graphs AND actual Source
refusal. No inhabitant or all-admitted-success theorem is supplied here. Everything indexed by `P8a.Producer` is vacuous until P8-SPEC-LAW1 is
resolved: the frozen V1 `Producer` is uninhabited over the current `Nat`
resource (`Lowering/P8/ResourceContractLaw1.lean`). -/
structure Admission {S : P8a.Spec} {reference : P8a.OperationalReference}
    {origins : P8a.SourceOrigins S} {roots : P8a.RootModel S}
    (producer : P8a.Producer S reference origins roots) where
  graphs : ∀ (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r)
    (art : Roadmap.Artifact) (loc : Source.DataLoc),
    ∃ n, ∃ G : TypeGraph.Schema n,
      Nonempty (LocationDeclarationGraph (P8Bindings.acceptedSource producer i r h art).1 loc G)
  source_refuses : ∀ (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r)
    (art : Roadmap.Artifact),
    SourceRefusesNonAdmissible (P8Bindings.acceptedSource producer i r h art).1

end Solidity.Lowering.V07.LocationGraphInterface
