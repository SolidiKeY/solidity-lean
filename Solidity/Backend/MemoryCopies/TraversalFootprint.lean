import Solidity.Backend.MemoryCopies.TraversalFootprintInterface

/-! Live object counts for the existing intrinsic deep-copy fold.
Storage-only dynamic-array shadow entries are intentionally not traversed. -/
namespace Solidity.Backend.MemoryCopies

mutual
def liveObjectCount : {T : Ty} → SVal T → Nat
  | _, .prim _ => 0
  | _, .struct fields => fieldObjectCount fields + 1
  | _, .array values _ _ => elementObjectCount values + 1
  | _, .fixed values => elementObjectCount values + 1
  | _, .map _ _ => 0

def fieldObjectCount : {fields : List (Name × Ty)} → SFields fields → Nat
  | _, .nil => 0
  | _, .cons value rest => liveObjectCount value + fieldObjectCount rest

def elementObjectCount : {T : Ty} → {count : Nat} → SVec T count → Nat
  | _, _, .nil => 0
  | _, _, .cons value rest => liveObjectCount value + elementObjectCount rest
end

mutual
theorem valueCopy_count : {T : Ty} → (value : SVal T) → (memory : T.mapFree = true) →
    {H : HTy} → (heap : Heap H) →
    (value.copyStToM heap memory).H'.length = H.length + liveObjectCount value
  | _, .prim value, memory, _, heap => by
    rw [SVal.copyStToM_prim]
    rfl
  | _, .struct fields, memory, _, heap => by
    rw [SVal.copyStToM_struct]
    change ((fields.copyStToM heap _).H' ++ [_]).length = _
    rw [List.length_append,List.length_singleton,fieldsCopy_count]
    simp only [liveObjectCount,Nat.add_assoc]
  | _, .array values shadow bound, memory, _, heap => by
    rw [SVal.copyStToM_array]
    change ((values.copyStToM heap _).H' ++ [_]).length = _
    rw [List.length_append,List.length_singleton,elementsCopy_count]
    simp only [liveObjectCount,Nat.add_assoc]
  | _, .fixed values, memory, _, heap => by
    rw [SVal.copyStToM_fixed]
    change ((values.copyStToM heap _).H' ++ [_]).length = _
    rw [List.length_append,List.length_singleton,elementsCopy_count]
    simp only [liveObjectCount,Nat.add_assoc]
  | _, .map _ _, memory, _, _ => by
    simp only [Ty.mapFree,Bool.false_eq_true] at memory

theorem fieldsCopy_count : {fields : List (Name × Ty)} → (values : SFields fields) →
    (memory : ∀ field ∈ fields, field.2.mapFree = true) → {H : HTy} → (heap : Heap H) →
    (values.copyStToM heap memory).H'.length = H.length + fieldObjectCount values
  | _, .nil, memory, _, heap => by
    rw [SFields.copyStToM_nil]
    rfl
  | _, .cons value rest, memory, _, heap => by
    rw [SFields.copyStToM_cons]
    change (rest.copyStToM (value.copyStToM heap _).heap _).H'.length = _
    rw [fieldsCopy_count,valueCopy_count]
    simp only [fieldObjectCount,Nat.add_assoc]

theorem elementsCopy_count : {T : Ty} → {count : Nat} → (values : SVec T count) →
    (memory : T.mapFree = true) → {H : HTy} → (heap : Heap H) →
    (values.copyStToM heap memory).H'.length = H.length + elementObjectCount values
  | _, _, .nil, memory, _, heap => by
    rw [SVec.copyStToM_nil]
    rfl
  | _, _, .cons value rest, memory, _, heap => by
    rw [SVec.copyStToM_cons]
    change (rest.copyStToM (value.copyStToM heap memory).heap memory).H'.length = _
    rw [elementsCopy_count,valueCopy_count]
    simp only [elementObjectCount,Nat.add_assoc]
end

theorem copy_parent_last {R : RefTy} (value : SVal (.ref R))
    (memory : (Ty.ref R).mapFree = true) {H : HTy} (heap : Heap H) :
    (value.copyStToM heap memory).val.id + 1 = (value.copyStToM heap memory).H'.length := by
  cases value with
  | struct fields =>
    rw [SVal.copyStToM_struct]
    simp only [Grown.alloc,Heap.alloc,List.length_append,List.length_singleton]
  | array values shadow bound =>
    rw [SVal.copyStToM_array]
    simp only [Grown.alloc,Heap.alloc,List.length_append,List.length_singleton]
  | fixed values =>
    rw [SVal.copyStToM_fixed]
    simp only [Grown.alloc,Heap.alloc,List.length_append,List.length_singleton]
  | map entries default => simp only [Ty.mapFree,Bool.false_eq_true] at memory

def traversalFootprint {R : RefTy} (value : SVal (.ref R))
    (memory : (Ty.ref R).mapFree = true) {H : HTy} (heap : Heap H) :
    TraversalFootprintCertificate heap value memory (liveObjectCount value) :=
  ⟨valueCopy_count value memory heap,copy_parent_last value memory heap⟩

theorem liveObjectCount_positive {R : RefTy} (value : SVal (.ref R))
    (memory : (Ty.ref R).mapFree = true) : 0 < liveObjectCount value := by
  have count : (value.copyStToM (H := []) () memory).H'.length = liveObjectCount value := by
    simpa only [List.length_nil,Nat.zero_add] using valueCopy_count value memory (H := []) ()
  have last : (value.copyStToM (H := []) () memory).val.id + 1 =
      (value.copyStToM (H := []) () memory).H'.length := copy_parent_last value memory (H := []) ()
  omega

theorem copy_root_index {R : RefTy} (value : SVal (.ref R))
    (memory : (Ty.ref R).mapFree = true) {H : HTy} (heap : Heap H) :
    (value.copyStToM heap memory).val.id = H.length + liveObjectCount value - 1 := by
  have count : (value.copyStToM heap memory).H'.length = H.length + liveObjectCount value :=
    valueCopy_count value memory heap
  have last : (value.copyStToM heap memory).val.id + 1 = (value.copyStToM heap memory).H'.length :=
    copy_parent_last value memory heap
  omega

def traversalPairFootprint {R Q : RefTy} (first : SVal (.ref R)) (second : SVal (.ref Q))
    (firstMemory : (Ty.ref R).mapFree = true) (secondMemory : (Ty.ref Q).mapFree = true)
    {H : HTy} (heap : Heap H) :
    TraversalPairFootprint heap first second firstMemory secondMemory (liveObjectCount first) (liveObjectCount second) where
  first_count := valueCopy_count first firstMemory heap
  second_count := by
    rw [valueCopy_count,valueCopy_count]
  separated := ⟨(first.copyStToM heap firstMemory).val.id_lt,
    SVal.copyStToM_id_ge (first.copyStToM heap firstMemory).heap second secondMemory⟩

#print axioms valueCopy_count
#print axioms fieldsCopy_count
#print axioms elementsCopy_count
#print axioms copy_parent_last
#print axioms traversalFootprint
#print axioms liveObjectCount_positive
#print axioms copy_root_index
#print axioms traversalPairFootprint
end Solidity.Backend.MemoryCopies
