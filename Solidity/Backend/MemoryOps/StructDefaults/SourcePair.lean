import Solidity.Backend.MemoryOps.SourceDefault

/-! G33 struct-only construction: actual independent Source zeroVal allocates
an empty Boolean child before the named two-field parent. Existing Source
allocator and child-default implementation are reused. -/
namespace Solidity.Backend.MemoryOps.StructDefaults
open Source

abbrev SourceBoolArrayTy : Source.STy := .array .memory .bool none

abbrev PairFields : List Source.STy := [.int .u256, SourceBoolArrayTy]

def pairValues {D : Source.Layout} (child : Nat) : Source.DataList D PairFields :=
  .cons (.val (.int 0 Source.IntTy.u256.zero_mem))
    (.cons (.val (.memRef rfl child)) .nil)

theorem zeroFields_pair {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (fuel : Nat) :
    (Source.zeroFields (E := E) (Γ := Γ) (fuel+4) PairFields).run y =
      (.ok (pairValues y.2.heap.next),
        (y.1, {y.2 with heap := (y.2.heap.alloc
          ⟨SourceBoolArrayTy, sourceBoolMemory []⟩).1})) := by
  change (do
    let first ← Source.zeroVal (E := E) (Γ := Γ) (fuel+3) (.int .u256)
    let rest ← Source.zeroFields (fuel+3) [SourceBoolArrayTy]
    pure (Source.DataList.cons (.val first) rest)).run y = _
  rw [Source.Hoare.run_bind]
  change (do
    let child ← Source.zeroVal (E := E) (Γ := Γ) (fuel+2) SourceBoolArrayTy
    let rest ← Source.zeroFields (fuel+2) []
    pure (Source.DataList.cons (.val (.int 0 Source.IntTy.u256.zero_mem))
      (.cons (.val child) rest))).run y = _
  rw [Source.Hoare.run_bind, source_bool_default_run]
  rfl

/-- The layout witness comes from the actual source environment. No reference
child pointer or final parent representation is assumed. -/
theorem source_pair_default {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (dn : Source.DeclName)
    (layout : E.layout.fields dn = PairFields) (fuel : Nat) :
    ∃ fields : Source.DataList E.layout (E.layout.fields dn),
      (Source.zeroVal (E := E) (Γ := Γ) (fuel+6) (.struct .memory dn)).run y =
        (.ok (.memRef rfl (y.2.heap.next+1)),
          (y.1, {y.2 with heap :=
            ((y.2.heap.alloc ⟨SourceBoolArrayTy, sourceBoolMemory []⟩).1.alloc
              ⟨.struct .memory dn, Source.Data.struct fields⟩).1})) ∧
      fields.nth 0 (.int .u256) = .ok (.val (.int 0 Source.IntTy.u256.zero_mem)) ∧
      fields.nth 1 SourceBoolArrayTy = .ok (.val (.memRef rfl y.2.heap.next)) := by
  have fields : ∃ fs : Source.DataList E.layout (E.layout.fields dn),
      (Source.zeroFields (E := E) (Γ := Γ) (fuel+4) (E.layout.fields dn)).run y =
        (.ok fs, (y.1, {y.2 with heap :=
          (y.2.heap.alloc ⟨SourceBoolArrayTy, sourceBoolMemory []⟩).1})) ∧
      fs.nth 0 (.int .u256) = .ok (.val (.int 0 Source.IntTy.u256.zero_mem)) ∧
      fs.nth 1 SourceBoolArrayTy = .ok (.val (.memRef rfl y.2.heap.next)) := by
    rw [layout]
    exact ⟨pairValues y.2.heap.next, zeroFields_pair y fuel, rfl, rfl⟩
  obtain ⟨fs, evaluated, first, child⟩ := fields
  refine ⟨fs, ?_, first, child⟩
  change (do
    let data ← (do let fs ← Source.zeroFields (E := E) (Γ := Γ) (fuel+4) (E.layout.fields dn)
                   pure (Source.Data.struct (l := .memory) (d := dn) fs))
    Source.allocRef data).run y = _
  rw [Source.Hoare.run_bind, Source.Hoare.run_bind, evaluated]
  rfl

#print axioms zeroFields_pair
#print axioms source_pair_default
end Solidity.Backend.MemoryOps.StructDefaults
