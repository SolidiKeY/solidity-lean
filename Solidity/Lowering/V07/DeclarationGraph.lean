import Solidity.Lowering.V07.Scalar
import Solidity.Source.Machine
import Solidity.TypeGraph

/-! G18.01 typed handoff interface. This relates existing Source types and
schema metadata; it introduces no values, heap, evaluator or compiler IR.
A producer for every accepted source is an OPEN admission obligation. The
constructors describe supported shape correspondence, not a source exclusion.
Bytes/string/function-valued fields need their existing owners' interfaces. -/
namespace Solidity.Lowering.V07

/-- Structural type correspondence at existing Source and graph types.
Capacity evidence of fixed arrays is retained by the existing graph size. -/
inductive GraphTypeRel (D : Source.Layout) {n : Nat} (names : Fin n → Source.DeclName) :
    Source.STy → TypeGraph.Ty n → Prop where
  | int (t : Source.IntTy) : GraphTypeRel D names (.int t) (.prim (integerPrim t))
  | bool : GraphTypeRel D names .bool (.prim .bool)
  | address (payable : Bool) : GraphTypeRel D names (.address payable) (.prim .uint)
  | enum (d : Source.DeclName) (capacity : D.enumSize d ≤ 2^256) :
      GraphTypeRel D names (.enum d) (.prim .uint)
  | udvt {d : Source.DeclName} {T : TypeGraph.Ty n}
      (underlying : GraphTypeRel D names (D.underlying d) T) :
      GraphTypeRel D names (.udvt d) T
  | node (loc : Source.DataLoc) (i : Fin n) :
      GraphTypeRel D names (.struct loc (names i)) (.node i)
  | array (loc : Source.DataLoc) {τ : Source.STy} {T : TypeGraph.Ty n}
      (elem : GraphTypeRel D names τ T) :
      GraphTypeRel D names (.array loc τ none) (.array T)
  | fixed (loc : Source.DataLoc) (size : TypeGraph.FixedSize)
      {τ : Source.STy} {T : TypeGraph.Ty n} (elem : GraphTypeRel D names τ T) :
      GraphTypeRel D names (.array loc τ (some size.val)) (.fixed T size)
  | mapping {κ τ : Source.STy} {K : PrimTy} {T : TypeGraph.Ty n}
      (key : GraphTypeRel D names κ (.prim K)) (value : GraphTypeRel D names τ T) :
      GraphTypeRel D names (.mapping κ τ) (.mapping K T)

/-- Ordered field correspondence is a proposition over existing field lists. -/
inductive GraphFieldsRel (D : Source.Layout) {n : Nat} (names : Fin n → Source.DeclName) :
    List (String × Source.STy) → List (Name × TypeGraph.Ty n) → Prop where
  | nil : GraphFieldsRel D names [] []
  | cons {s : String × Source.STy} {t : Name × TypeGraph.Ty n}
      {ss : List (String × Source.STy)} {ts : List (Name × TypeGraph.Ty n)}
      (name : s.1 = t.1) (type : GraphTypeRel D names s.2 t.2)
      (rest : GraphFieldsRel D names ss ts) : GraphFieldsRel D names (s :: ss) (t :: ts)

/-- A complete node-index/field correspondence for ONE existing environment,
location and schema. All fields are proof obligations for a real producer;
this certificate does NOT assert Source execution or lowering preservation.
Location is explicit because mapping fields fail memory type resolution. -/
structure DeclarationGraph (E : Source.Env) (loc : Source.DataLoc) {n : Nat}
    (G : TypeGraph.Schema n) where
  sourceName : Fin n → Source.DeclName
  sourceName_injective : Function.Injective sourceName
  sourceIndex : Fin n → Fin E.decls.length
  identity : ∀ i, G.declId i = (sourceIndex i).val
  source_kind : ∀ i, (E.decls[sourceIndex i]).kind = .struct
  source_scope : ∀ i, (E.decls[sourceIndex i]).scope = (sourceName i).scope
  source_name : ∀ i, (E.decls[sourceIndex i]).name = (sourceName i).name
  source_resolves : ∀ i, E.declOf .struct (sourceName i) = some E.decls[sourceIndex i]
  target_name : ∀ i, G.name i = (sourceName i).name
  sourceFields : Fin n → List (String × Source.STy)
  fields_resolve : ∀ i, E.structFields (sourceName i) loc = some (sourceFields i)
  fields_relate : ∀ i, GraphFieldsRel E.layout sourceName (sourceFields i) (G.fields i)
  complete : ∀ j : Fin E.decls.length, (E.decls[j]).kind = .struct →
    ∃ i, sourceIndex i = j

namespace DeclarationGraph
variable {E : Source.Env} {loc : Source.DataLoc} {n : Nat} {G : TypeGraph.Schema n}

theorem identity_reflection (c : DeclarationGraph E loc G) (i j : Fin n) :
    c.sourceIndex i = c.sourceIndex j ↔ i = j := by
  constructor
  · intro h
    apply G.declId_injective
    rw [c.identity, c.identity, h]
  · intro h
    rw [h]

theorem field_count (c : DeclarationGraph E loc G) (i : Fin n) :
    (c.sourceFields i).length = (G.fields i).length := by
  have h := c.fields_relate i
  generalize c.sourceFields i = xs at h ⊢
  generalize G.fields i = ys at h ⊢
  induction h with
  | nil => rfl
  | cons _ _ _ ih => exact congrArg Nat.succ ih

theorem field_names (c : DeclarationGraph E loc G) (i : Fin n) :
    (c.sourceFields i).map Prod.fst = (G.fields i).map Prod.fst := by
  have h := c.fields_relate i
  generalize c.sourceFields i = xs at h ⊢
  generalize G.fields i = ys at h ⊢
  induction h with
  | nil => rfl
  | cons name _ _ ih => exact congr (congrArg List.cons name) ih

theorem memory_layout (c : DeclarationGraph E .memory G) (i : Fin n) :
    E.layout.fields (c.sourceName i) = (c.sourceFields i).map Prod.snd := by
  change ((E.structFields (c.sourceName i) .memory).getD []).map Prod.snd = _
  rw [c.fields_resolve]
  rfl

end DeclarationGraph
end Solidity.Lowering.V07
