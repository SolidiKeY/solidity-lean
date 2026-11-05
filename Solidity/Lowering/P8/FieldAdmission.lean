import Solidity.Lowering.P8.ScalarSchemaControls

/-! Necessary source-field admission consequences of actual V07 graph certificates.
These do not strengthen Source.WellFormed or silently exclude declarations. -/
namespace Solidity.Lowering.P8
open V07

theorem fields_lookup_none {D : Source.Layout} {n : Nat}
    {names : Fin n → Source.DeclName} {ss : List (String × Source.STy)}
    {ts : List (Name × TypeGraph.Ty n)} (h : GraphFieldsRel D names ss ts) (key : String) :
    (Semantics.lookupBy key ss).isNone = (Semantics.lookupBy key ts).isNone := by
  induction h with
  | nil => rfl
  | @cons s t ss ts hn _ _ ih =>
    cases s with
    | mk sn st =>
      cases t with
      | mk tn tt =>
        change sn = tn at hn
        subst tn
        simp only [Semantics.lookupBy]
        split
        · rfl
        · exact ih

theorem fields_distinct_iff {D : Source.Layout} {n : Nat}
    {names : Fin n → Source.DeclName} {ss : List (String × Source.STy)}
    {ts : List (Name × TypeGraph.Ty n)} (h : GraphFieldsRel D names ss ts) :
    Semantics.nodupKeysB ss = Semantics.nodupKeysB ts := by
  induction h with
  | nil => rfl
  | @cons s t ss ts hn _ hr ih =>
    change ((Semantics.lookupBy s.1 ss).isNone && Semantics.nodupKeysB ss) =
      ((Semantics.lookupBy t.1 ts).isNone && Semantics.nodupKeysB ts)
    rw [hn, fields_lookup_none hr, ih]

theorem graph_source_fields_distinct {E : Source.Env} {loc : Source.DataLoc} {n : Nat}
    {G : TypeGraph.Schema n} (c : DeclarationGraph E loc G) (i : Fin n) :
    Semantics.nodupKeysB (c.sourceFields i) = true :=
  (fields_distinct_iff (c.fields_relate i)).trans (G.distinct i)

/-- The duplicate is genuinely accepted by the current CORE predicates yet
cannot be the resolved source fields of ANY actual graph node. This identifies
an admission/proof obligation, not a change to the approved source profile. -/
theorem duplicate_cannot_be_graph_fields {E : Source.Env} {loc : Source.DataLoc} {n : Nat}
    {G : TypeGraph.Schema n} (c : DeclarationGraph E loc G) (i : Fin n) :
    c.sourceFields i ≠ [("value", .int Source.IntTy.u8), ("value", .bool)] := by
  intro he
  have hu := graph_source_fields_distinct c i
  rw [he] at hu
  cases hu

#print axioms fields_distinct_iff
#print axioms graph_source_fields_distinct
#print axioms duplicate_cannot_be_graph_fields
end Solidity.Lowering.P8
