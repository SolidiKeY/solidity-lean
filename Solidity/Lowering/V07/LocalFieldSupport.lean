import Solidity.Lowering.V07.FieldCompleteness

/-! Component support over existing Source types, not admission or a new AST.
Only actually traversed UDVT underlyings constrain these proofs. -/
namespace Solidity.Lowering.V07.LocalFieldSupport

def Supported (D : Source.Layout) : Source.STy → Prop
  | .udvt d => (PrimitiveGraph.lowerType (D.underlying d)).isSome = true
  | .array _ elem _ => Supported D elem
  | .mapping key value => Supported D key ∧ Supported D value
  | _ => True
theorem type_complete {D : Source.Layout} {n : Nat} {names : Fin n → Source.DeclName}
    (injective : Function.Injective names)
    {τ : Source.STy} {T : TypeGraph.Ty n} (rel : GraphTypeRel D names τ T) (supported : Supported D τ) :
    (RecursiveGraph.lowerType D names τ).isSome = true := by
  revert supported
  induction rel with
  | int t => intro _; rfl
  | bool => intro _; rfl
  | address p => intro _; rfl
  | enum d capacity => intro _; simp only [RecursiveGraph.lowerType,dif_pos capacity,Option.isSome_some]
  | udvt elem ih =>
    rename_i d T
    intro supported
    change (PrimitiveGraph.lowerType (D.underlying d)).isSome = true at supported
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
    intro _
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
    intro supported
    have ih := ih supported
    cases he : RecursiveGraph.lowerType D names τ with
    | none => simp only [he,Option.isSome_none,Bool.false_eq_true] at ih
    | some c => simp only [RecursiveGraph.lowerType,he,Option.isSome_some]
  | fixed loc size elem ih =>
    rename_i τ T
    intro supported
    have ih := ih supported
    cases he : RecursiveGraph.lowerType D names τ with
    | none => simp only [he,Option.isSome_none,Bool.false_eq_true] at ih
    | some c => simp only [RecursiveGraph.lowerType,dif_pos size.property,he,Option.isSome_some]
  | mapping key value ihk ihv =>
    rename_i κ τ K T
    intro supported
    have ihk := ihk supported.1
    have ihv := ihv supported.2
    cases hk : RecursiveGraph.lowerType D names κ with
    | none => simp only [hk,Option.isSome_none,Bool.false_eq_true] at ihk
    | some c =>
      have shape := FieldCompleteness.functional injective c.property key
      rcases c with ⟨v,prop⟩
      change v = .prim K at shape
      subst v
      cases hv : RecursiveGraph.lowerType D names τ with
      | none => simp only [hv,Option.isSome_none,Bool.false_eq_true] at ihv
      | some d => simp only [RecursiveGraph.lowerType,hk,hv,Option.isSome_some]

/-- Only members of the actual ordered source-field list require component
support; unrelated declarations cannot introduce additional obligations. -/
theorem fields_complete {D : Source.Layout} {n : Nat} {names : Fin n → Source.DeclName}
    (injective : Function.Injective names)
    {ss : List (String × Source.STy)} {ts : List (Name × TypeGraph.Ty n)}
    (rel : GraphFieldsRel D names ss ts) (supported : ∀ s ∈ ss, Supported D s.2) :
    (RecursiveGraph.lowerFields D names ss).isSome = true := by
  revert supported
  induction rel with
  | nil => intro _; rfl
  | cons name type rest ih =>
    rename_i s t ss ts
    intro supported
    have head := type_complete injective type (supported s List.mem_cons_self)
    have tail := ih (fun g hg => supported g (List.mem_cons_of_mem s hg))
    cases ht : RecursiveGraph.lowerType D names s.2 with
    | none => simp only [ht,Option.isSome_none,Bool.false_eq_true] at head
    | some c =>
      cases hr : RecursiveGraph.lowerFields D names ss with
      | none => simp only [hr,Option.isSome_none,Bool.false_eq_true] at tail
      | some cs => simp only [RecursiveGraph.lowerFields,ht,hr,Option.isSome_some]
end Solidity.Lowering.V07.LocalFieldSupport
