import Solidity.Source.Agreement.Locals
import Solidity.Lowering.V07.DoubleAssignment

/-! Exact roundtrips for existing relations. No new production relation,
world correspondence, execution assumption, compiler or evaluator is added. -/
namespace H55.SourceRelations
open Solidity Solidity.Source Solidity.Source.Agreement

/-- PrimitiveRel is the graph of the existing total producer, with both
integer ranges retained by that producer. -/
theorem primitive_iff_ofModel (D : Layout) (p : PrimTy)
    (v : Source.Val D (sourceTy p)) (w : p.Denote) :
    PrimitiveRel D p v w ↔ v = ofModel D p w := by
  constructor
  · intro related
    cases related <;> rfl
  · intro same
    subst v
    exact ofModel_related D p w

theorem primitive_right_unique {D : Layout} {p : PrimTy}
    {v : Source.Val D (sourceTy p)} {a b : p.Denote}
    (ha : PrimitiveRel D p v a) (hb : PrimitiveRel D p v b) : a = b := by
  have same : ofModel D p a = ofModel D p b :=
    ((primitive_iff_ofModel D p v a).mp ha).symm.trans
      ((primitive_iff_ofModel D p v b).mp hb)
  cases p with
  | bool => exact Source.Val.bool.inj same
  | uint =>
    apply Subtype.ext
    exact Option.some.inj (congrArg Source.Val.key same)
  | int =>
    apply Subtype.ext
    exact Option.some.inj (congrArg Source.Val.key same)

theorem ofModel_injective (D : Layout) (p : PrimTy) (a b : p.Denote)
    (same : ofModel D p a = ofModel D p b) : a = b := by
  have related : PrimitiveRel D p (ofModel D p a) b :=
    same.symm ▸ ofModel_related D p b
  exact primitive_right_unique (ofModel_related D p a) related

/-- Every related primitive local environment is exactly the existing producer's
output. This is locals only; no heap/storage/world projection is asserted. -/
theorem locals_iff_ofModel (D : Layout) (C : Contract) (H : HTy)
    (ps : List PrimTy) (vs : Locals D (sourceContext ps))
    (ws : TEnv C H (modelContext ps)) :
    LocalsRel D C H ps vs ws ↔ vs = localsOfModel D C H ps ws := by
  constructor
  · intro related
    induction related with
    | nil => rfl
    | cons head tail ih =>
      rw [(primitive_iff_ofModel _ _ _ _).mp head, ih]
      rfl
  · intro same
    subst vs
    exact localsOfModel_related D C H ps ws

open Solidity.Lowering.V07
/-- The observation relation is exactly the existing integer producer's graph,
for every source integer width and signedness, with the same range premise. -/
theorem integer_iff_producer {D : Layout} (t : IntTy) (n : Int)
    (range : t.lo ≤ n ∧ n ≤ t.hi) (w : (integerPrim t).Denote) :
    IntValueRel t (.int n range : Source.Val D (.int t)) w ↔
      w = integerValue t n range := by
  constructor
  · exact integer_relation_target t n range w
  · intro same
    subst w
    exact integer_related t n range

/-- Every source value at one of the three supported primitive types has a
model correspondent, without a new range or representability assumption. -/
theorem primitive_source_total (D : Layout) (p : PrimTy)
    (v : Source.Val D (sourceTy p)) : ∃ w, PrimitiveRel D p v w := by
  cases p with
  | bool =>
    cases v with
    | bool b => exact ⟨b, .bool b⟩
    | memRef h _ => cases h
    | storRef h _ => cases h
    | cdRef h _ _ => cases h
  | uint =>
    cases v with
    | int n range => exact ⟨⟨n, (Solidity.Source.Agreement.uint_range n).mpr range⟩, .uint (⟨n, (Solidity.Source.Agreement.uint_range n).mpr range⟩ : PrimTy.uint.Denote) range⟩
    | memRef h _ => cases h
    | storRef h _ => cases h
    | cdRef h _ _ => cases h
  | int =>
    cases v with
    | int n range => exact ⟨⟨n, (Solidity.Source.Agreement.int_range n).mpr range⟩, .int (⟨n, (Solidity.Source.Agreement.int_range n).mpr range⟩ : PrimTy.int.Denote) range⟩
    | memRef h _ => cases h
    | storRef h _ => cases h
    | cdRef h _ _ => cases h

theorem primitive_source_unique (D : Layout) (p : PrimTy)
    (v : Source.Val D (sourceTy p)) : ∃ w, PrimitiveRel D p v w ∧ ∀ other, PrimitiveRel D p v other → other = w := by
  obtain ⟨w, related⟩ := primitive_source_total D p v
  exact ⟨w, related, fun other h => primitive_right_unique h related⟩

theorem locals_source_total (D : Layout) (C : Contract) (H : HTy)
    (ps : List PrimTy) (vs : Locals D (sourceContext ps)) :
    ∃ ws, LocalsRel D C H ps vs ws := by
  induction ps with
  | nil => cases vs; exact ⟨(), .nil⟩
  | cons p ps ih =>
    cases vs with
    | cons v vs =>
      obtain ⟨w, head⟩ := primitive_source_total D p v
      obtain ⟨ws, tail⟩ := ih vs
      exact ⟨(w, ws), .cons head tail⟩


#print axioms primitive_iff_ofModel
#print axioms primitive_right_unique
#print axioms ofModel_injective
#print axioms locals_iff_ofModel
#print axioms integer_iff_producer
#print axioms primitive_source_total
#print axioms primitive_source_unique
#print axioms locals_source_total
end H55.SourceRelations
