import Solidity.Lowering.V07.LocalFieldSupport
import Solidity.Lowering.V07.NodeRank

/-! Exact ordered component output and executable declaration-graph success.
No source execution/admission or graph-rank existence is assumed discharged. -/
namespace Solidity.Lowering.V07.LocationGraphCompleteness

/-- Recover the exact ordered field values from structural correspondence,
without assuming a successful lowerer invocation or its desired output. -/
theorem fields_exact {D : Source.Layout} {n : Nat} {names : Fin n → Source.DeclName}
    (injective : Function.Injective names)
    {ss : List (String × Source.STy)} {ts : List (Name × TypeGraph.Ty n)}
    (rel : GraphFieldsRel D names ss ts)
    (supported : ∀ s ∈ ss, LocalFieldSupport.Supported D s.2) :
    (RecursiveGraph.lowerFields D names ss).map Subtype.val = some ts := by
  revert supported
  induction rel with
  | nil => intro _; rfl
  | cons name type rest ih =>
    rename_i s t ss ts
    intro supported
    have head := LocalFieldSupport.type_complete injective type (supported s List.mem_cons_self)
    have tail := ih (fun g hg => supported g (List.mem_cons_of_mem s hg))
    cases ht : RecursiveGraph.lowerType D names s.2 with
    | none => simp only [ht,Option.isSome_none,Bool.false_eq_true] at head
    | some c =>
      have value := FieldCompleteness.functional injective c.property type
      cases hr : RecursiveGraph.lowerFields D names ss with
      | none => simp only [hr,Option.map_none,reduceCtorEq] at tail
      | some cs =>
        simp only [hr,Option.map_some,Option.some.injEq] at tail
        simp only [RecursiveGraph.lowerFields,ht,hr,Option.map_some,Option.some.injEq]
        change (s.1,c.val)::cs.val = t::ts
        rw [value,tail]
        rcases t with ⟨key,T⟩
        exact congrArg (fun k => (k,T)::ts) name
/-- Actual computed producer success from structural premises. These are
component obligations, not admitted-Source completeness or execution preservation.
The comparison assignment is never supplied to the executable producer. -/
theorem producer_success (E : Source.Env) (loc : Source.DataLoc) (origin : Name)
    (selected : LocationGraphProducer.SelectionOK E loc)
    (fs : Fin (LocationGraphProducer.choices E loc).length →
      List (Name × TypeGraph.Ty (LocationGraphProducer.choices E loc).length))
    (related : ∀ i, GraphFieldsRel E.layout (LocationGraphProducer.name E loc)
      (LocationGraphProducer.sourceFields E loc i) (fs i))
    (supported : ∀ i s, s ∈ LocationGraphProducer.sourceFields E loc i →
      LocalFieldSupport.Supported E.layout s.2)
    (nonempty : ∀ i, (fs i).isEmpty = false)
    (distinct : ∀ i, Semantics.nodupKeysB (fs i) = true)
    (r : Fin (LocationGraphProducer.choices E loc).length → Nat)
    (valid : ∀ i f, f ∈ fs i → f.2.inlineRank r < r i) :
    (LocationGraphProducer.produce origin E loc).isSome = true := by
  have injective : Function.Injective (LocationGraphProducer.name E loc) := by
    intro i j h
    exact selected.2.1 i j h
  have exactFields (i : Fin (LocationGraphProducer.choices E loc).length) :=
    fields_exact injective (related i) (supported i)
  have targetEq : ∀ i, LocationGraphProducer.targetFields E loc i = fs i := by
    intro i
    change ((RecursiveGraph.lowerFields E.layout (LocationGraphProducer.name E loc)
      (LocationGraphProducer.sourceFields E loc i)).map Subtype.val).getD [] = fs i
    rw [exactFields i]
    rfl
  have present : ∀ i, (LocationGraphProducer.fieldCertificate E loc i).isSome = true := by
    intro i
    have e := exactFields i
    change (LocationGraphProducer.fieldCertificate E loc i).map Subtype.val = some (fs i) at e
    cases h : LocationGraphProducer.fieldCertificate E loc i with
    | none => simp only [h,Option.map_none,reduceCtorEq] at e
    | some c => rfl
  have actualValid : ∀ i f, f ∈ LocationGraphProducer.targetFields E loc i →
      f.2.inlineRank r < r i := by
    intro i f member
    exact valid i f (by rwa [targetEq i] at member)
  have checked : LocationGraphProducer.FieldsOK E loc :=
    NodeRank.location_fields_ok E loc present
      (fun i => by rw [targetEq i]; exact nonempty i)
      (fun i => by rw [targetEq i]; exact distinct i) r actualValid
  simp only [LocationGraphProducer.produce,dif_pos selected,dif_pos checked,Option.isSome_some]
end Solidity.Lowering.V07.LocationGraphCompleteness
