import Solidity.Lowering.V07.RecursiveGraph
namespace Solidity.Lowering.V07.FieldCompleteness
theorem functional {D : Source.Layout} {n : Nat} {names : Fin n → Source.DeclName}
    (injective : Function.Injective names) {τ : Source.STy} {A B : TypeGraph.Ty n}
    (left : GraphTypeRel D names τ A) (right : GraphTypeRel D names τ B) : A = B := by
  induction left generalizing B with
  | int t => cases right; rfl
  | bool => cases right; rfl
  | address p => cases right; rfl
  | enum d capacity => cases right; rfl
  | udvt underlying ih => cases right with
    | udvt other => exact ih other
  | node loc i =>
    generalize hd : names i = d at right
    cases right with
    | node _ j => exact congrArg TypeGraph.Ty.node (injective hd)
  | array loc elem ih => cases right with
    | array _ other => exact congrArg TypeGraph.Ty.array (ih other)
  | fixed loc size elem ih =>
    generalize hm : size.val = m at right
    cases right with
    | fixed _ otherSize other =>
      have same : size = otherSize := Subtype.ext hm
      cases same
      exact congrArg (fun t => TypeGraph.Ty.fixed t size) (ih other)
  | mapping key value ihk ihv => cases right with
    | mapping otherKey otherVal =>
      have hk := ihk otherKey
      cases hk
      exact congrArg (TypeGraph.Ty.mapping _) (ihv otherVal)
/-- Completeness for the existing correspondence when UDVT underlyings are
in the existing primitive producer's supported component. This is a component
premise, not Source admission or an exclusion of other admitted source types. -/
theorem complete {D : Source.Layout} {n : Nat} {names : Fin n → Source.DeclName}
    (injective : Function.Injective names)
    (underlying : ∀ d, (PrimitiveGraph.lowerType (D.underlying d)).isSome = true)
    {τ : Source.STy} {T : TypeGraph.Ty n} (rel : GraphTypeRel D names τ T) :
    (RecursiveGraph.lowerType D names τ).isSome = true := by
  induction rel with
  | int t => rfl
  | bool => rfl
  | address p => rfl
  | enum d capacity => simp only [RecursiveGraph.lowerType,dif_pos capacity,Option.isSome_some]
  | udvt elem ih =>
    rename_i d T
    have supported := underlying d
    cases hp : PrimitiveGraph.lowerType (D.underlying d) with
    | none => simp only [hp,Option.isSome_none,Bool.false_eq_true] at supported
    | some p =>
      unfold RecursiveGraph.lowerType
      split
      · rfl
      · rename_i bad
        rw [hp] at bad
        cases bad
  | node loc i =>
    apply List.findSome?_isSome_iff.mpr
    refine ⟨i,?_,?_⟩
    · apply List.mem_iff_getElem.mpr
      refine ⟨i.val,by simpa only [List.length_finRange] using i.isLt,?_⟩
      simp only [List.getElem_finRange]
      apply Fin.ext
      rfl
    · simp only [↓reduceDIte,Option.isSome_some]
  | array loc elem ih =>
    rename_i τ T
    cases he : RecursiveGraph.lowerType D names τ with
    | none => simp only [he,Option.isSome_none,Bool.false_eq_true] at ih
    | some c => simp only [RecursiveGraph.lowerType,he,Option.isSome_some]
  | fixed loc size elem ih =>
    rename_i τ T
    cases he : RecursiveGraph.lowerType D names τ with
    | none => simp only [he,Option.isSome_none,Bool.false_eq_true] at ih
    | some c => simp only [RecursiveGraph.lowerType,dif_pos size.property,he,Option.isSome_some]
  | mapping key value ihk ihv =>
    rename_i κ τ K T
    cases hk : RecursiveGraph.lowerType D names κ with
    | none => simp only [hk,Option.isSome_none,Bool.false_eq_true] at ihk
    | some c =>
      have shape := functional injective c.property key
      rcases c with ⟨v,prop⟩
      change v = .prim K at shape
      subst v
      cases hv : RecursiveGraph.lowerType D names τ with
      | none => simp only [hv,Option.isSome_none,Bool.false_eq_true] at ihv
      | some d => simp only [RecursiveGraph.lowerType,hk,hv,Option.isSome_some]
/-- Ordered fields all succeed under the same explicit supported-component
premises. No fields are dropped, reordered, or accepted from Source by this law. -/
theorem fields_complete {D : Source.Layout} {n : Nat} {names : Fin n → Source.DeclName}
    (injective : Function.Injective names)
    (underlying : ∀ d, (PrimitiveGraph.lowerType (D.underlying d)).isSome = true)
    {ss : List (String × Source.STy)} {ts : List (Name × TypeGraph.Ty n)}
    (rel : GraphFieldsRel D names ss ts) :
    (RecursiveGraph.lowerFields D names ss).isSome = true := by
  induction rel with
  | nil => rfl
  | cons name type rest ih =>
    rename_i s t ss ts
    have supported := complete injective underlying type
    cases ht : RecursiveGraph.lowerType D names s.2 with
    | none => simp only [ht,Option.isSome_none,Bool.false_eq_true] at supported
    | some c =>
      cases hr : RecursiveGraph.lowerFields D names ss with
      | none => simp only [hr,Option.isSome_none,Bool.false_eq_true] at ih
      | some tail => simp only [RecursiveGraph.lowerFields,ht,hr,Option.isSome_some]
end Solidity.Lowering.V07.FieldCompleteness
