import Solidity.Lowering.V07.PrimitiveGraph

/-! Computed declaration graph certificates over existing Source.STy and
TypeGraph.Ty. None is a COMPONENT failure, never rejection of source admission.
No alternative AST, graph representation, evaluator or state carrier. -/
namespace Solidity.Lowering.V07.RecursiveGraph
open PrimitiveGraph (nodes index name UniqueNames sourceFields)

/-- Recursion follows the actual finite Source type. Struct references are
looked up among actual declaration identities, never unfolded recursively. -/
def lowerType (D : Source.Layout) {n : Nat} (names : Fin n → Source.DeclName) :
    (τ : Source.STy) → Option {T : TypeGraph.Ty n // GraphTypeRel D names τ T}
  | .int t => some ⟨.prim (integerPrim t),.int t⟩
  | .bool => some ⟨.prim .bool,.bool⟩
  | .address p => some ⟨.prim .uint,.address p⟩
  | .enum d => if h : D.enumSize d ≤ 2^256 then some ⟨.prim .uint,.enum d h⟩ else none
  | .udvt d => match h : PrimitiveGraph.lowerType (D.underlying d) with
    | some p => some ⟨.prim p,.udvt (PrimitiveGraph.lowerType_sound h)⟩
    | none => none
  | .struct loc d => (List.finRange n).findSome? fun i =>
      if h : names i = d then some ⟨.node i,by rw [← h]; exact .node loc i⟩ else none
  | .array loc τ none => match lowerType D names τ with
    | some t => some ⟨.array t.val,.array loc t.property⟩
    | none => none
  | .array loc τ (some m) => if h : 0 < m ∧ m < 2^256 then
      match lowerType D names τ with
      | some t => some ⟨.fixed t.val ⟨m,h⟩,.fixed loc ⟨m,h⟩ t.property⟩
      | none => none
    else none
  | .mapping κ τ => match lowerType D names κ with
    | some ⟨.prim k,hk⟩ => match lowerType D names τ with
      | some t => some ⟨.mapping k t.val,.mapping hk t.property⟩
      | none => none
    | _ => none
  | _ => none

def lowerFields (D : Source.Layout) {n : Nat} (names : Fin n → Source.DeclName) :
    (ss : List (String × Source.STy)) →
      Option {fs : List (Name × TypeGraph.Ty n) // GraphFieldsRel D names ss fs}
  | [] => some ⟨[],.nil⟩
  | (s,τ)::ss => match lowerType D names τ,lowerFields D names ss with
    | some t,some rest => some ⟨(s,t.val)::rest.val,.cons rfl t.property rest.property⟩
    | _,_ => none

def fieldCertificate (E : Source.Env) (loc : Source.DataLoc) (i : Fin (nodes E).length) :=
  lowerFields E.layout (name E) (sourceFields E loc i)

def targetFields (E : Source.Env) (loc : Source.DataLoc) (i : Fin (nodes E).length) :
    List (Name × TypeGraph.Ty (nodes E).length) :=
  ((fieldCertificate E loc i).map Subtype.val).getD []

/-- One finite dependency propagation, with syntactic fixed-array weights.
This is metadata computation, not an unrolling limit on source/runtime paths. -/
def rankStep {n : Nat} (fs : Fin n → List (Name × TypeGraph.Ty n))
    (rank : Fin n → Nat) (i : Fin n) : Nat :=
  (fs i).foldr (fun f acc => max (f.2.inlineRank rank) acc) 0 + 1

def rankIter {n : Nat} (fs : Fin n → List (Name × TypeGraph.Ty n)) : Nat → Fin n → Nat
  | 0 => fun _ => 0
  | k+1 => rankStep fs (rankIter fs k)

def ranks (E : Source.Env) (loc : Source.DataLoc) :=
  rankIter (targetFields E loc) (nodes E).length

/-- All checks are computed from actual Source fields, with existing explicit
capacity obligations. No supplied schema, rank proof or preservation result. -/
def FieldsOK (E : Source.Env) (loc : Source.DataLoc) : Prop :=
  ∀ i : Fin (nodes E).length,
    (fieldCertificate E loc i).isSome = true ∧
    (targetFields E loc i).isEmpty = false ∧
    Semantics.nodupKeysB (targetFields E loc i) = true ∧
    (targetFields E loc i).all (fun f => decide (f.2.inlineRank (ranks E loc) < ranks E loc i)) = true

instance (E : Source.Env) (loc : Source.DataLoc) : Decidable (FieldsOK E loc) :=
  inferInstanceAs (Decidable (∀ i : Fin (nodes E).length,
    (fieldCertificate E loc i).isSome = true ∧
    (targetFields E loc i).isEmpty = false ∧
    Semantics.nodupKeysB (targetFields E loc i) = true ∧
    (targetFields E loc i).all (fun f => decide (f.2.inlineRank (ranks E loc) < ranks E loc i)) = true))

def schema (origin : Name) (E : Source.Env) (loc : Source.DataLoc)
    (hu : UniqueNames E) (hf : FieldsOK E loc) : TypeGraph.Schema (nodes E).length where
  origin := origin
  declId := fun i => (index E i).val
  declId_injective := fun i j h => PrimitiveGraph.index_injective E hu i j (Fin.ext h)
  name := fun i => (name E i).name
  fields := targetFields E loc
  rank := ranks E loc
  nonempty := fun i => (hf i).2.1
  distinct := fun i => (hf i).2.2.1
  guarded := by
    intro i f h
    have all := (List.all_eq_true.mp (hf i).2.2.2) f h
    exact of_decide_eq_true all

theorem fields_related (E : Source.Env) (loc : Source.DataLoc) (hf : FieldsOK E loc)
    (i : Fin (nodes E).length) :
    GraphFieldsRel E.layout (name E) (sourceFields E loc i) (targetFields E loc i) := by
  have h := (hf i).1
  cases he : fieldCertificate E loc i with
  | none => simp only [he,Option.isSome_none,Bool.false_eq_true] at h
  | some c => simpa only [targetFields,he,Option.map_some,Option.getD_some] using c.property

theorem nil_fields_inv {D : Source.Layout} {n : Nat} {names : Fin n → Source.DeclName}
    {fs : List (Name × TypeGraph.Ty n)} (h : GraphFieldsRel D names [] fs) : fs = [] := by
  cases h
  rfl

theorem fields_resolved (E : Source.Env) (loc : Source.DataLoc) (hf : FieldsOK E loc)
    (i : Fin (nodes E).length) :
    E.structFields (name E i) loc = some (sourceFields E loc i) := by
  cases he : E.structFields (name E i) loc with
  | some fs => simp only [sourceFields,he,Option.getD_some]
  | none =>
    have rel : GraphFieldsRel E.layout (name E) [] (targetFields E loc i) := by
      simpa only [sourceFields,he,Option.getD_none] using fields_related E loc hf i
    have empty : targetFields E loc i = [] := nil_fields_inv rel
    have h := (hf i).2.1
    rw [empty] at h
    cases h

def certificate (origin : Name) (E : Source.Env) (loc : Source.DataLoc)
    (hu : UniqueNames E) (hf : FieldsOK E loc) :
    DeclarationGraph E loc (schema origin E loc hu hf) where
  sourceName := name E
  sourceName_injective := hu
  sourceIndex := index E
  identity := fun _ => rfl
  source_kind := PrimitiveGraph.index_kind E
  source_scope := fun _ => rfl
  source_name := fun _ => rfl
  source_resolves := PrimitiveGraph.resolves E hu
  target_name := fun _ => rfl
  sourceFields := sourceFields E loc
  fields_resolve := fields_resolved E loc hf
  fields_relate := fields_related E loc hf
  complete := PrimitiveGraph.index_complete E

/-- Computed supported-case producer. None is not a Source-profile exclusion.
Total success for the frozen P8a Producer is NOT a supplied premise or theorem. -/
def produce (origin : Name) (E : Source.Env) (loc : Source.DataLoc) :
    Option ((G : TypeGraph.Schema (nodes E).length) × DeclarationGraph E loc G) :=
  if hu : UniqueNames E then
    if hf : FieldsOK E loc then some ⟨schema origin E loc hu hf,certificate origin E loc hu hf⟩
    else none
  else none

theorem produce_success (origin : Name) (E : Source.Env) (loc : Source.DataLoc)
    (hu : UniqueNames E) (hf : FieldsOK E loc) :
    produce origin E loc = some ⟨schema origin E loc hu hf,certificate origin E loc hu hf⟩ := by
  simp only [produce,dif_pos hu,dif_pos hf]

theorem produce_failure_fields (origin : Name) (E : Source.Env) (loc : Source.DataLoc)
    (hf : ¬ FieldsOK E loc) : produce origin E loc = none := by
  by_cases hu : UniqueNames E
  · simp only [produce,dif_pos hu,dif_neg hf]
  · simp only [produce,dif_neg hu]

theorem memory_layout (origin : Name) (E : Source.Env)
    (hu : UniqueNames E) (hf : FieldsOK E .memory) (i : Fin (nodes E).length) :
    E.layout.fields (name E i) = (sourceFields E .memory i).map Prod.snd :=
  (certificate origin E .memory hu hf).memory_layout i

end Solidity.Lowering.V07.RecursiveGraph
