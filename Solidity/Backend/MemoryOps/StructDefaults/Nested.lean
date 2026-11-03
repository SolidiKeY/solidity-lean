import Solidity.Backend.MemoryOps.StructDefaults.Frame

namespace Solidity.Backend.MemoryOps.StructDefaults

/-- Lift an actual typed field-default evaluation through the existing source
struct allocator. This does not assume a parent object or a word-level frame. -/
theorem source_struct_of_fields {E : Source.Env} {Γ : Source.RCtx}
    (y z : Source.EMState E Γ) (dn : Source.DeclName) (fuel : Nat)
    (fs : Source.DataList E.layout (E.layout.fields dn))
    (evaluated : (Source.zeroFields (E := E) (Γ := Γ) fuel (E.layout.fields dn)).run y =
      (.ok fs, z)) :
    (Source.zeroVal (E := E) (Γ := Γ) (fuel+2) (.struct .memory dn)).run y =
      (.ok (.memRef rfl z.2.heap.next),
        (z.1, {z.2 with heap := (z.2.heap.alloc
          ⟨.struct .memory dn, Source.Data.struct fs⟩).1})) := by
  change (do
    let data ← (do let fs ← Source.zeroFields (E := E) (Γ := Γ) fuel (E.layout.fields dn)
                   pure (Source.Data.struct (l := .memory) (d := dn) fs))
    Source.allocRef data).run y = _
  rw [Source.Hoare.run_bind, Source.Hoare.run_bind, evaluated]
  rfl

/-- A finite nested layout allocates its child's child, then the child struct,
then the outer struct. Actual evaluator runs determine every fresh address. -/
theorem source_nested_default {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (inner outer : Source.DeclName)
    (innerLayout : E.layout.fields inner = PairFields)
    (outerLayout : E.layout.fields outer = [.struct .memory inner, .bool]) (fuel : Nat) :
    ∃ innerFields : Source.DataList E.layout (E.layout.fields inner),
    ∃ outerFields : Source.DataList E.layout (E.layout.fields outer),
      (Source.zeroVal (E := E) (Γ := Γ) (fuel+9) (.struct .memory outer)).run y =
        (.ok (.memRef rfl (y.2.heap.next+2)),
          (y.1, {y.2 with heap := ((pairHeap y.2.heap inner innerFields).alloc
            ⟨.struct .memory outer, Source.Data.struct outerFields⟩).1})) ∧
      outerFields.nth 0 (.struct .memory inner) =
        .ok (.val (.memRef rfl (y.2.heap.next+1))) ∧
      outerFields.nth 1 .bool = .ok (.val (.bool false)) := by
  obtain ⟨ifs, innerRun, _, _⟩ := source_pair_default y inner innerLayout fuel
  have fields : ∃ ofs : Source.DataList E.layout (E.layout.fields outer),
      (Source.zeroFields (E := E) (Γ := Γ) (fuel+7) (E.layout.fields outer)).run y =
        (.ok ofs, (y.1, {y.2 with heap := pairHeap y.2.heap inner ifs})) ∧
      ofs.nth 0 (.struct .memory inner) = .ok (.val (.memRef rfl (y.2.heap.next+1))) ∧
      ofs.nth 1 .bool = .ok (.val (.bool false)) := by
    rw [outerLayout]
    refine ⟨.cons (.val (.memRef rfl (y.2.heap.next+1)))
      (.cons (.val (.bool false)) .nil), ?_, by simp only [Source.DataList.nth, dite_true]; rfl, rfl⟩
    change (do
      let v ← Source.zeroVal (E := E) (Γ := Γ) (fuel+6) (.struct .memory inner)
      let rest ← Source.zeroFields (fuel+6) [.bool]
      pure (Source.DataList.cons (.val v) rest)).run y = _
    rw [Source.Hoare.run_bind, innerRun]
    rfl
  obtain ⟨ofs, outerFieldsRun, first, second⟩ := fields
  exact ⟨ifs, ofs, source_struct_of_fields y _ outer (fuel+7) ofs outerFieldsRun, first, second⟩

#print axioms source_struct_of_fields
#print axioms source_nested_default
end Solidity.Backend.MemoryOps.StructDefaults
