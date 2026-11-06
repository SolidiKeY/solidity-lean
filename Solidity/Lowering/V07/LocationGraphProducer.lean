import Solidity.Lowering.V07.RecursiveGraph
import Solidity.Lowering.V07.LocationGraphInterface
/-! H15 computed admissible-location producer over EXISTING intrinsic types.
None is a component failure, never Source rejection. Structural selection,
field and rank checks are computed; no final certificate/preservation premise.
Source refusal and all-admitted success remain separate obligations.
The results indexed by `P8a.Producer` are vacuous until P8-SPEC-LAW1 is
resolved (`Lowering/P8/ResourceContractLaw1.lean`). -/
namespace Solidity.Lowering.V07.LocationGraphProducer
open Solidity Solidity.Lowering.V07
open LocationGraphInterface

/-- Selection carries an actual proof of the H15 location policy. -/
def choices (E : Source.Env) (loc : Source.DataLoc) :=
  (List.finRange (PrimitiveGraph.nodes E).length).filterMap fun i =>
    if h : StructAdmissible E (PrimitiveGraph.name E i) loc then some (⟨i,h⟩ :
      {i : Fin (PrimitiveGraph.nodes E).length // StructAdmissible E (PrimitiveGraph.name E i) loc})
    else none

def oldIndex (E : Source.Env) (loc : Source.DataLoc) (i : Fin (choices E loc).length) :=
  ((choices E loc)[i.val]).val

def sourceIndex (E : Source.Env) (loc : Source.DataLoc) (i : Fin (choices E loc).length) :=
  PrimitiveGraph.index E (oldIndex E loc i)

def name (E : Source.Env) (loc : Source.DataLoc) (i : Fin (choices E loc).length) :=
  PrimitiveGraph.name E (oldIndex E loc i)

/-- Finite checks over the computed selection, not supplied certificates. -/
def SelectionOK (E : Source.Env) (loc : Source.DataLoc) : Prop :=
  PrimitiveGraph.UniqueNames E ∧
  (∀ i j : Fin (choices E loc).length, name E loc i = name E loc j → i = j) ∧
  (∀ j : Fin E.decls.length, E.decls[j].kind = .struct →
    StructAdmissible E ⟨E.decls[j].scope,E.decls[j].name⟩ loc →
      ∃ i, sourceIndex E loc i = j)

instance (E : Source.Env) (loc : Source.DataLoc) : Decidable (SelectionOK E loc) :=
  inferInstanceAs (Decidable (PrimitiveGraph.UniqueNames E ∧
    (∀ i j : Fin (choices E loc).length, name E loc i = name E loc j → i = j) ∧
    (∀ j : Fin E.decls.length, E.decls[j].kind = .struct →
      StructAdmissible E ⟨E.decls[j].scope,E.decls[j].name⟩ loc → ∃ i, sourceIndex E loc i = j)))

def sourceFields (E : Source.Env) (loc : Source.DataLoc) (i : Fin (choices E loc).length) :=
  (E.structFields (name E loc i) loc).getD []

def fieldCertificate (E : Source.Env) (loc : Source.DataLoc) (i : Fin (choices E loc).length) :=
  RecursiveGraph.lowerFields E.layout (name E loc) (sourceFields E loc i)

def targetFields (E : Source.Env) (loc : Source.DataLoc) (i : Fin (choices E loc).length) :
    List (Name × TypeGraph.Ty (choices E loc).length) :=
  ((fieldCertificate E loc i).map Subtype.val).getD []

def ranks (E : Source.Env) (loc : Source.DataLoc) :=
  RecursiveGraph.rankIter (targetFields E loc) (choices E loc).length

def FieldsOK (E : Source.Env) (loc : Source.DataLoc) : Prop :=
  ∀ i : Fin (choices E loc).length,
    (fieldCertificate E loc i).isSome = true ∧
    (targetFields E loc i).isEmpty = false ∧
    Semantics.nodupKeysB (targetFields E loc i) = true ∧
    (targetFields E loc i).all (fun f => decide (f.2.inlineRank (ranks E loc) < ranks E loc i)) = true

instance (E : Source.Env) (loc : Source.DataLoc) : Decidable (FieldsOK E loc) :=
  inferInstanceAs (Decidable (∀ i : Fin (choices E loc).length,
    (fieldCertificate E loc i).isSome = true ∧ (targetFields E loc i).isEmpty = false ∧
    Semantics.nodupKeysB (targetFields E loc i) = true ∧
    (targetFields E loc i).all (fun f => decide (f.2.inlineRank (ranks E loc) < ranks E loc i)) = true))

theorem index_injective (E : Source.Env) (loc : Source.DataLoc) (hs : SelectionOK E loc)
    (i j : Fin (choices E loc).length) (h : sourceIndex E loc i = sourceIndex E loc j) : i = j := by
  apply hs.2.1 i j
  exact congrArg (fun k : Fin E.decls.length =>
    Source.DeclName.mk (E.decls.get k).scope (E.decls.get k).name) h

theorem selected_admissible (E : Source.Env) (loc : Source.DataLoc) (i : Fin (choices E loc).length) :
    StructAdmissible E (name E loc i) loc := by
  exact ((choices E loc)[i.val]).property

def schema (origin : Name) (E : Source.Env) (loc : Source.DataLoc)
    (hs : SelectionOK E loc) (hf : FieldsOK E loc) : TypeGraph.Schema (choices E loc).length where
  origin := origin
  declId := fun i => (sourceIndex E loc i).val
  declId_injective := fun i j h => index_injective E loc hs i j (Fin.ext h)
  name := fun i => (name E loc i).name
  fields := targetFields E loc
  rank := ranks E loc
  nonempty := fun i => (hf i).2.1
  distinct := fun i => (hf i).2.2.1
  guarded := fun i f h => of_decide_eq_true ((List.all_eq_true.mp (hf i).2.2.2) f h)

theorem fields_related (E : Source.Env) (loc : Source.DataLoc) (hf : FieldsOK E loc)
    (i : Fin (choices E loc).length) :
    GraphFieldsRel E.layout (name E loc) (sourceFields E loc i) (targetFields E loc i) := by
  have h := (hf i).1
  cases he : fieldCertificate E loc i with
  | none => simp only [he,Option.isSome_none,Bool.false_eq_true] at h
  | some c => simpa only [targetFields,he,Option.map_some,Option.getD_some] using c.property

theorem fields_resolved (E : Source.Env) (loc : Source.DataLoc) (hf : FieldsOK E loc)
    (i : Fin (choices E loc).length) :
    E.structFields (name E loc i) loc = some (sourceFields E loc i) := by
  cases he : E.structFields (name E loc i) loc with
  | some fs => simp only [sourceFields,he,Option.getD_some]
  | none =>
    have rel : GraphFieldsRel E.layout (name E loc) [] (targetFields E loc i) := by
      simpa only [sourceFields,he,Option.getD_none] using fields_related E loc hf i
    have empty := RecursiveGraph.nil_fields_inv rel
    have h := (hf i).2.1
    rw [empty] at h
    cases h

def certificate (origin : Name) (E : Source.Env) (loc : Source.DataLoc)
    (hs : SelectionOK E loc) (hf : FieldsOK E loc) :
    LocationDeclarationGraph E loc (schema origin E loc hs hf) where
  sourceName := name E loc
  sourceName_injective := hs.2.1
  sourceIndex := sourceIndex E loc
  identity := fun _ => rfl
  source_kind := fun i => PrimitiveGraph.index_kind E (oldIndex E loc i)
  source_scope := fun _ => rfl
  source_name := fun _ => rfl
  source_resolves := fun i => PrimitiveGraph.resolves E hs.1 (oldIndex E loc i)
  source_admissible := selected_admissible E loc
  target_name := fun _ => rfl
  sourceFields := sourceFields E loc
  fields_resolve := fields_resolved E loc hf
  fields_relate := fields_related E loc hf
  complete := hs.2.2

/-- Pure computed component: no Source admission or desired result premise. -/
def produce (origin : Name) (E : Source.Env) (loc : Source.DataLoc) :
    Option ((G : TypeGraph.Schema (choices E loc).length) × LocationDeclarationGraph E loc G) :=
  if hs : SelectionOK E loc then
    if hf : FieldsOK E loc then some ⟨schema origin E loc hs hf,certificate origin E loc hs hf⟩
    else none
  else none

/-- Exact frozen P8a source origin; no alternative source contract or evaluator. -/
def produceAccepted {S : Solidity.Lowering.P8.P8a.Spec}
    {reference : Solidity.Lowering.P8.P8a.OperationalReference}
    {origins : Solidity.Lowering.P8.P8a.SourceOrigins S} {roots : Solidity.Lowering.P8.P8a.RootModel S}
    (producer : Solidity.Lowering.P8.P8a.Producer S reference origins roots)
    (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r)
    (art : Roadmap.Artifact) (origin : Name) (loc : Source.DataLoc) :=
  produce origin (P8Bindings.acceptedSource producer i r h art).1 loc

end Solidity.Lowering.V07.LocationGraphProducer
