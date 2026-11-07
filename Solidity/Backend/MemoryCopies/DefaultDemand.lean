import Solidity.Backend.MemoryCopies.DefaultDemandInterface

/-! Existing finite default-plan costs agree with the actual intrinsic copy
fold. No planner is widened and no capacity antecedent is assumed. -/
namespace Solidity.Backend.MemoryCopies
open Semantics Evm.Memory

mutual
theorem finite_default_words (T : Ty) (cost : Nat)
    (selected : finiteDefaultCells T = some cost) : liveWordCount (SVal.dflt T) = cost := by
  cases T with
  | prim p =>
    simp only [finiteDefaultCells, Option.some.injEq] at selected
    rw [← selected, SVal.dflt_prim]
    rfl
  | ref R =>
    cases R with
    | array E =>
      cases E with
      | prim p =>
        simp only [finiteDefaultCells, Option.some.injEq] at selected
        rw [← selected, SVal.dflt_array]
        rfl
      | ref Q => simp only [finiteDefaultCells, reduceCtorEq] at selected
    | struct s =>
      rw [finiteDefaultCells] at selected
      cases children : finiteDefaultFieldCells (structDef s) with
      | none => rw [children] at selected; cases selected
      | some amount =>
        have total : amount + structAllocationSize s = cost := by
          simpa only [children, Option.map_some, Option.some.injEq] using selected
        rw [SVal.dflt_struct, liveWordCount,
          finite_default_field_words (structDef s) amount children]
        exact total
    | fixed E n => simp only [finiteDefaultCells, reduceCtorEq] at selected
    | mapping K V => simp only [finiteDefaultCells, reduceCtorEq] at selected
termination_by (tyRank T, sizeOf T)
decreasing_by
  subst T R
  exact Prod.Lex.left _ _ (structDef_rank_lt _)

theorem finite_default_field_words : (fields : List (Name × Ty)) → (cost : Nat) →
    finiteDefaultFieldCells fields = some cost → fieldWordCount (SFields.dflt fields) = cost
  | [], cost, selected => by
    simp only [finiteDefaultFieldCells, Option.some.injEq] at selected
    rw [← selected]
    rfl
  | (name, T) :: rest, cost, selected => by
    rw [finiteDefaultFieldCells] at selected
    cases head : finiteDefaultCells T with
    | none => rw [head] at selected; cases selected
    | some first =>
      cases tail : finiteDefaultFieldCells rest with
      | none => rw [head, tail] at selected; cases selected
      | some later =>
        have total : first + later = cost := by
          rw [head, tail] at selected
          exact Option.some.inj selected
        simp only [SFields.dflt, fieldWordCount]
        rw [finite_default_words T first head, finite_default_field_words rest later tail]
        exact total
termination_by fields _ _ => (fieldsRank fields, sizeOf fields)
decreasing_by
  all_goals (apply lex_le_lt
             · simp only [fieldsRank]; omega
             · simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]; omega)

end

theorem default_allocation_words {H : HTy} (heap : Heap H) (R : RefTy)
    (memory : (Ty.ref R).mapFree = true) :
    heapWords (heap.allocDefault R memory).heap =
      heapWords heap + liveWordCount (SVal.dflt (.ref R)) :=
  valueCopy_words (SVal.dflt (.ref R)) memory heap

theorem default_plan_words {R : RefTy} (plan : DefaultPlan R)
    {H : HTy} (heap : Heap H) (memory : (Ty.ref R).mapFree = true) :
    heapWords (heap.allocDefault R memory).heap = heapWords heap + plan.cost := by
  rw [default_allocation_words, finite_default_words (.ref R) plan.cost plan.cells]

theorem default_fields_plan_words {fields : List (Name × Ty)} (plan : DefaultFieldsPlan fields)
    {H : HTy} (heap : Heap H) (memory : ∀ field ∈ fields, field.2.mapFree = true) :
    heapWords ((SFields.dflt fields).copyStToM heap memory).heap = heapWords heap + plan.cost := by
  rw [fieldsCopy_words, finite_default_field_words fields plan.cost plan.cells]

theorem replicated_element_words {T : Ty} (value : SVal T) (count : Nat) :
    elementWordCount (SVec.replicate value count) = count * liveWordCount value := by
  induction count with
  | zero => simp only [SVec.replicate, elementWordCount, Nat.zero_mul]
  | succ count previous =>
    simp only [SVec.replicate, elementWordCount, previous, Nat.succ_mul, Nat.add_comm]

theorem fixed_default_words (element : Ty) (count : Nat) :
    liveWordCount (SVal.dflt (.ref (.fixed element count))) =
      max 1 count + count * liveWordCount (SVal.dflt element) := by
  rw [SVal.dflt_fixed, liveWordCount, replicated_element_words, Nat.add_comm]

theorem dynamic_default_words (element : Ty) :
    liveWordCount (SVal.dflt (.ref (.array element))) = 1 := by
  rw [SVal.dflt_array]
  rfl

def defaultDemand : DefaultDemandCertificate := ⟨finite_default_words, default_allocation_words⟩

#print axioms finite_default_words
#print axioms finite_default_field_words
#print axioms default_allocation_words
#print axioms default_plan_words
#print axioms default_fields_plan_words
#print axioms replicated_element_words
#print axioms fixed_default_words
#print axioms dynamic_default_words
#print axioms defaultDemand
end Solidity.Backend.MemoryCopies
