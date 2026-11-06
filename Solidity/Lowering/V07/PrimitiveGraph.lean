import Solidity.Lowering.V07.DeclarationGraph

/-! Computed primitive-field graph admission over the existing Source environment.
This supported-case producer is not complete accepted-source admission. Unsupported
field types are component failures, never new Source exclusions. -/
namespace Solidity.Lowering.V07.PrimitiveGraph

/-- Actual source positions of all and only struct declarations, in source order. -/
def nodes (E : Source.Env) : List (Fin E.decls.length) :=
  (List.finRange E.decls.length).filter fun j => E.decls[j].kind == .struct

def index (E : Source.Env) (i : Fin (nodes E).length) : Fin E.decls.length :=
  (nodes E)[i.val]

def name (E : Source.Env) (i : Fin (nodes E).length) : Source.DeclName :=
  ⟨E.decls[index E i].scope, E.decls[index E i].name⟩

theorem index_kind (E : Source.Env) (i : Fin (nodes E).length) :
    E.decls[index E i].kind = .struct := by
  have h := List.getElem_mem (l := nodes E) i.isLt
  have hm := (List.mem_filter.mp h).2
  exact of_decide_eq_true hm

theorem index_complete (E : Source.Env) (j : Fin E.decls.length)
    (hj : E.decls[j].kind = .struct) : ∃ i, index E i = j := by
  have hmem : j ∈ List.finRange E.decls.length := by
    apply List.mem_iff_getElem.mpr
    refine ⟨j.val, ?_, ?_⟩
    · simpa only [List.length_finRange] using j.isLt
    · simp only [List.getElem_finRange]
      apply Fin.ext
      rfl
  have h : j ∈ nodes E := List.mem_filter.mpr ⟨hmem, by simp only [hj, beq_self_eq_true]⟩
  obtain ⟨k, hk, heq⟩ := List.getElem_of_mem h
  exact ⟨⟨k,hk⟩,heq⟩

/-- These constructors erase integer widths only as specified by integerPrim;
all value/range obligations remain owned by scalar lowering. -/
def lowerType : Source.STy → Option PrimTy
  | .int t => some (integerPrim t)
  | .bool => some .bool
  | .address _ => some .uint
  | _ => none

theorem lowerType_sound {D : Source.Layout} {n : Nat}
    {names : Fin n → Source.DeclName} {τ : Source.STy} {p : PrimTy}
    (h : lowerType τ = some p) : GraphTypeRel D names τ (.prim p) := by
  cases τ <;> simp only [lowerType, reduceCtorEq, Option.some.injEq] at h
  next t => cases h; exact .int t
  next => cases h; exact .bool
  next payable => cases h; exact .address payable

def lowerFields : List (String × Source.STy) → Option (List (Name × PrimTy))
  | [] => some []
  | (s,τ) :: rest =>
    match lowerType τ, lowerFields rest with
    | some p, some ps => some ((s,p) :: ps)
    | _, _ => none

def fields {n : Nat} (ps : List (Name × PrimTy)) : List (Name × TypeGraph.Ty n) :=
  ps.map fun f => (f.1, .prim f.2)

theorem lowerFields_sound {D : Source.Layout} {n : Nat}
    {names : Fin n → Source.DeclName} {ss : List (String × Source.STy)}
    {ps : List (Name × PrimTy)} (h : lowerFields ss = some ps) :
    GraphFieldsRel D names ss (fields ps) := by
  induction ss generalizing ps with
  | nil => cases h; exact .nil
  | cons s ss ih =>
    rcases s with ⟨s,τ⟩
    simp only [lowerFields] at h
    cases ht : lowerType τ with
    | none => simp only [ht, reduceCtorEq] at h
    | some p =>
      cases hs : lowerFields ss with
      | none => simp only [ht, hs, reduceCtorEq] at h
      | some rest =>
        simp only [ht, hs, Option.some.injEq] at h
        cases h
        exact .cons rfl (lowerType_sound ht) (ih hs)

theorem fields_rank_zero {n : Nat} (rank : Fin n → Nat) (ps : List (Name × PrimTy))
    (f : Name × TypeGraph.Ty n) (hf : f ∈ fields ps) : f.2.inlineRank rank = 0 := by
  obtain ⟨p,_,hp⟩ := List.mem_map.mp hf
  cases hp
  rfl

/-- Name uniqueness is checked only among actual selected declarations. -/
def UniqueNames (E : Source.Env) : Prop :=
  ∀ i j : Fin (nodes E).length, name E i = name E j → i = j

instance (E : Source.Env) : Decidable (UniqueNames E) :=
  inferInstanceAs (Decidable (∀ i j : Fin (nodes E).length, name E i = name E j → i = j))

theorem index_injective (E : Source.Env) (hu : UniqueNames E)
    (i j : Fin (nodes E).length) (h : index E i = index E j) : i = j := by
  apply hu i j
  exact congrArg (fun k : Fin E.decls.length =>
    Source.DeclName.mk (E.decls.get k).scope (E.decls.get k).name) h

theorem resolves (E : Source.Env) (hu : UniqueNames E) (i : Fin (nodes E).length) :
    E.declOf .struct (name E i) = some E.decls[index E i] := by
  change E.decls.find? _ = _
  apply List.find?_eq_some_iff_getElem.mpr
  refine ⟨?_, (index E i).val, (index E i).isLt, rfl, ?_⟩
  · simp only [index_kind, beq_self_eq_true, name, Bool.and_self]
  · intro k hk
    have hbound : k < E.decls.length := Nat.lt_trans hk (index E i).isLt
    by_cases hp : (E.decls[k].kind == Source.DeclKind.struct &&
        E.decls[k].scope == (name E i).scope && E.decls[k].name == (name E i).name) = true
    · have hm : E.decls[k].kind = .struct ∧
          E.decls[k].scope = (name E i).scope ∧ E.decls[k].name = (name E i).name := by
        simpa only [Bool.and_eq_true, beq_iff_eq, and_assoc] using hp
      obtain ⟨j,hj⟩ := index_complete E ⟨k,hbound⟩ hm.1
      have hn : name E j = name E i := by
        unfold name
        simpa only [List.get_eq_getElem, hj] using
          (congr (congrArg Source.DeclName.mk hm.2.1) hm.2.2 :
            Source.DeclName.mk (E.decls.get ⟨k,hbound⟩).scope (E.decls.get ⟨k,hbound⟩).name = name E i)
      have he : k = (index E i).val := by
        have hij := hu j i hn
        have hidx := congrArg (index E) hij
        rw [hj] at hidx
        exact congrArg Fin.val hidx
      omega
    · simpa only [Bool.not_eq_true'] using (Bool.eq_false_iff.mpr hp)

/-- Ordered fields are read from actual Source resolution, never caller-provided
schema fields. Failed resolution and unsupported shapes remain distinguishable
at this boundary by the original Source option and lowerFields option. -/
def sourceFields (E : Source.Env) (loc : Source.DataLoc) (i : Fin (nodes E).length) :=
  (E.structFields (name E i) loc).getD []

def primitiveFields (E : Source.Env) (loc : Source.DataLoc) (i : Fin (nodes E).length) :=
  lowerFields (sourceFields E loc i)

def targetFields (E : Source.Env) (loc : Source.DataLoc) (i : Fin (nodes E).length) :
    List (Name × TypeGraph.Ty (nodes E).length) :=
  fields ((primitiveFields E loc i).getD [])

/-- All clauses are finite checks over computed fields. No preservation,
Source execution, prebuilt Schema or desired rank proof is supplied. -/
def FieldsOK (E : Source.Env) (loc : Source.DataLoc) : Prop :=
  ∀ i : Fin (nodes E).length,
    (primitiveFields E loc i).isSome = true ∧
    (targetFields E loc i).isEmpty = false ∧
    Semantics.nodupKeysB (targetFields E loc i) = true

instance (E : Source.Env) (loc : Source.DataLoc) : Decidable (FieldsOK E loc) :=
  inferInstanceAs (Decidable (∀ i : Fin (nodes E).length,
    (primitiveFields E loc i).isSome = true ∧
    (targetFields E loc i).isEmpty = false ∧
    Semantics.nodupKeysB (targetFields E loc i) = true))

def schema (origin : Name) (E : Source.Env) (loc : Source.DataLoc)
    (hu : UniqueNames E) (hf : FieldsOK E loc) : TypeGraph.Schema (nodes E).length where
  origin := origin
  declId := fun i => (index E i).val
  declId_injective := fun i j h => index_injective E hu i j (Fin.ext h)
  name := fun i => (name E i).name
  fields := targetFields E loc
  rank := fun _ => 1
  nonempty := fun i => (hf i).2.1
  distinct := fun i => (hf i).2.2
  guarded := by
    intro i f h
    rw [fields_rank_zero _ _ f h]
    exact Nat.zero_lt_succ 0

theorem fields_resolved (E : Source.Env) (loc : Source.DataLoc) (hf : FieldsOK E loc)
    (i : Fin (nodes E).length) :
    E.structFields (name E i) loc = some (sourceFields E loc i) := by
  cases he : E.structFields (name E i) loc with
  | some fs => simp only [sourceFields, he, Option.getD_some]
  | none =>
    have hne := (hf i).2.1
    change (fields ((lowerFields ((E.structFields (name E i) loc).getD [])).getD [])).isEmpty = false at hne
    simp only [he, Option.getD_none, lowerFields, Option.getD_some, fields,
      List.map_nil, List.isEmpty_nil, reduceCtorEq] at hne

theorem fields_related (E : Source.Env) (loc : Source.DataLoc) (hf : FieldsOK E loc)
    (i : Fin (nodes E).length) : GraphFieldsRel E.layout (name E)
      (sourceFields E loc i) (targetFields E loc i) := by
  apply lowerFields_sound
  have h := (hf i).1
  change lowerFields (sourceFields E loc i) = some ((primitiveFields E loc i).getD [])
  cases he : primitiveFields E loc i with
  | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at h
  | some ps => exact he

def certificate (origin : Name) (E : Source.Env) (loc : Source.DataLoc)
    (hu : UniqueNames E) (hf : FieldsOK E loc) :
    DeclarationGraph E loc (schema origin E loc hu hf) where
  sourceName := name E
  sourceName_injective := hu
  sourceIndex := index E
  identity := fun _ => rfl
  source_kind := index_kind E
  source_scope := fun _ => rfl
  source_name := fun _ => rfl
  source_resolves := resolves E hu
  target_name := fun _ => rfl
  sourceFields := sourceFields E loc
  fields_resolve := fields_resolved E loc hf
  fields_relate := fields_related E loc hf
  complete := index_complete E

/-- A genuine computed producer: selects every actual struct position, checks
name uniqueness and fields, then constructs the intrinsic schema and certificate.
No length/depth cap. `none` is a component failure, NOT source rejection. -/
def produce (origin : Name) (E : Source.Env) (loc : Source.DataLoc) :
    Option ((G : TypeGraph.Schema (nodes E).length) × DeclarationGraph E loc G) :=
  if hu : UniqueNames E then
    if hf : FieldsOK E loc then some ⟨schema origin E loc hu hf, certificate origin E loc hu hf⟩
    else none
  else none

theorem produce_success (origin : Name) (E : Source.Env) (loc : Source.DataLoc)
    (hu : UniqueNames E) (hf : FieldsOK E loc) :
    produce origin E loc = some ⟨schema origin E loc hu hf, certificate origin E loc hu hf⟩ := by
  simp only [produce, dif_pos hu, dif_pos hf]

theorem produce_failure_names (origin : Name) (E : Source.Env) (loc : Source.DataLoc)
    (hu : ¬ UniqueNames E) : produce origin E loc = none := by
  simp only [produce, dif_neg hu]

theorem produce_failure_fields (origin : Name) (E : Source.Env) (loc : Source.DataLoc)
    (hf : ¬ FieldsOK E loc) : produce origin E loc = none := by
  by_cases hu : UniqueNames E
  · simp only [produce, dif_pos hu, dif_neg hf]
  · simp only [produce, dif_neg hu]

/-- Physical source positions survive filtering; no compacted graph position
is substituted for the declaration identity supplied to downstream consumers. -/
theorem schema_identity (origin : Name) (E : Source.Env) (loc : Source.DataLoc)
    (hu : UniqueNames E) (hf : FieldsOK E loc) (i : Fin (nodes E).length) :
    (schema origin E loc hu hf).declId i = (index E i).val := rfl

theorem memory_layout (origin : Name) (E : Source.Env)
    (hu : UniqueNames E) (hf : FieldsOK E .memory) (i : Fin (nodes E).length) :
    E.layout.fields (name E i) = (sourceFields E .memory i).map Prod.snd :=
  (certificate origin E .memory hu hf).memory_layout i

end Solidity.Lowering.V07.PrimitiveGraph
