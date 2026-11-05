import Solidity.Backend.MemoryCopies.TraversalWordsInterface

/-! Exact symbolic cell demand of the existing intrinsic storage-to-memory fold.
This sums reservations of actual typed objects, not addresses or machine gas. -/
namespace Solidity.Backend.MemoryCopies
open Semantics

/-- Parent reservation, including the existing header and empty-object padding. -/
def objectWords {H : HTy} : (R : RefTy) → MObj H R → Nat
  | .struct s, _ => max 1 (structDef s).length
  | .array _, object => 1 + object.1.length
  | .fixed _ count, _ => max 1 count
  | .mapping _ _, object => object.elim

def objectsWords {H : HTy} : (types : List RefTy) → Objs H types → Nat
  | [], _ => 0
  | type :: types, objects => objectWords type objects.1 + objectsWords types objects.2

def heapWords {H : HTy} (heap : Heap H) : Nat := objectsWords H heap

mutual
def liveWordCount : {T : Ty} → SVal T → Nat
  | _, .prim _ => 0
  | _, @SVal.struct s fields => fieldWordCount fields + max 1 (structDef s).length
  | _, @SVal.array _ count values _ _ => elementWordCount values + (1 + count)
  | _, @SVal.fixed _ count values => elementWordCount values + max 1 count
  | _, .map _ _ => 0

def fieldWordCount : {fields : List (Name × Ty)} → SFields fields → Nat
  | _, .nil => 0
  | _, .cons value rest => liveWordCount value + fieldWordCount rest

def elementWordCount : {T : Ty} → {count : Nat} → SVec T count → Nat
  | _, _, .nil => 0
  | _, _, .cons value rest => liveWordCount value + elementWordCount rest
end

theorem objectWords_wk {H H' : HTy} (extension : H <+: H')
    (R : RefTy) (object : MObj H R) :
    objectWords R (MObj.wk extension R object) = objectWords R object := by
  cases R with
  | struct s => rfl
  | array E => simp only [objectWords, MObj.wk, List.length_map]
  | fixed E count => rfl
  | mapping K V => exact object.elim

theorem objectsWords_wk {H H' : HTy} (extension : H <+: H') :
    (types : List RefTy) → (objects : Objs H types) →
    objectsWords types (Objs.wk extension types objects) = objectsWords types objects
  | [], _ => rfl
  | type :: types, objects => by
    simp only [objectsWords, Objs.wk, objectWords_wk, objectsWords_wk]

theorem objectsWords_snoc {H : HTy} {R : RefTy} (object : MObj H R) :
    (types : List RefTy) → (objects : Objs H types) →
    objectsWords (types ++ [R]) (Objs.snoc object types objects) =
      objectsWords types objects + objectWords R object
  | [], _ => by simp only [List.nil_append, Objs.snoc, objectsWords, Nat.add_zero, Nat.zero_add]
  | type :: types, objects => by
    simp only [List.cons_append, Objs.snoc, objectsWords, objectsWords_snoc, Nat.add_assoc]

theorem heapWords_alloc {H : HTy} (heap : Heap H) {R : RefTy} (object : MObj H R) :
    heapWords (heap.alloc object).1 = heapWords heap + objectWords R object := by
  simp only [heapWords, Heap.alloc, objectsWords_snoc, objectsWords_wk, objectWords_wk]

theorem objectWords_cells {H : HTy} (heap : Heap H) {R : RefTy} (reference : HRef H R) :
    objectWords R (heap.get reference) = Evm.Memory.Objects.cells heap reference := by
  cases R with
  | struct s => rfl
  | array E =>
    simp only [objectWords, Evm.Memory.Objects.cells, Heap.len, MObj.elems_dyn]
  | fixed E count => rfl
  | mapping K V => exact (heap.get reference).elim

mutual
theorem valueCopy_words : {T : Ty} → (value : SVal T) → (memory : T.mapFree = true) →
    {H : HTy} → (heap : Heap H) →
    heapWords (value.copyStToM heap memory).heap = heapWords heap + liveWordCount value
  | _, .prim value, memory, _, heap => by
    rw [SVal.copyStToM_prim]
    rfl
  | _, .struct fields, memory, _, heap => by
    rw [SVal.copyStToM_struct]
    change heapWords ((fields.copyStToM heap _).heap.alloc _).1 = _
    rw [heapWords_alloc, fieldsCopy_words]
    simp only [objectWords, liveWordCount, Nat.add_assoc]
  | _, .array values shadow bound, memory, _, heap => by
    rw [SVal.copyStToM_array]
    change heapWords ((values.copyStToM heap _).heap.alloc _).1 = _
    rw [heapWords_alloc, elementsCopy_words]
    simp only [objectWords, (values.copyStToM heap _).val.2, liveWordCount, Nat.add_assoc]
  | _, .fixed values, memory, _, heap => by
    rw [SVal.copyStToM_fixed]
    change heapWords ((values.copyStToM heap _).heap.alloc _).1 = _
    rw [heapWords_alloc, elementsCopy_words]
    simp only [objectWords, liveWordCount, Nat.add_assoc]
  | _, .map _ _, memory, _, _ => by
    simp only [Ty.mapFree, Bool.false_eq_true] at memory

theorem fieldsCopy_words : {fields : List (Name × Ty)} → (values : SFields fields) →
    (memory : ∀ field ∈ fields, field.2.mapFree = true) → {H : HTy} → (heap : Heap H) →
    heapWords (values.copyStToM heap memory).heap = heapWords heap + fieldWordCount values
  | _, .nil, memory, _, heap => by
    rw [SFields.copyStToM_nil]
    rfl
  | _, .cons value rest, memory, _, heap => by
    rw [SFields.copyStToM_cons]
    change heapWords (rest.copyStToM (value.copyStToM heap _).heap _).heap = _
    rw [fieldsCopy_words, valueCopy_words]
    simp only [fieldWordCount, Nat.add_assoc]

theorem elementsCopy_words : {T : Ty} → {count : Nat} → (values : SVec T count) →
    (memory : T.mapFree = true) → {H : HTy} → (heap : Heap H) →
    heapWords (values.copyStToM heap memory).heap = heapWords heap + elementWordCount values
  | _, _, .nil, memory, _, heap => by
    rw [SVec.copyStToM_nil]
    rfl
  | _, _, .cons value rest, memory, _, heap => by
    rw [SVec.copyStToM_cons]
    change heapWords (rest.copyStToM (value.copyStToM heap memory).heap memory).heap = _
    rw [elementsCopy_words, valueCopy_words]
    simp only [elementWordCount, Nat.add_assoc]
end

theorem copy_old_cells {T : Ty} (value : SVal T) (memory : T.mapFree = true)
    {H : HTy} (heap : Heap H) {R : RefTy} (reference : HRef H R) :
    Evm.Memory.Objects.cells (value.copyStToM heap memory).heap
      (reference.wk (value.copyStToM heap memory).ext) =
      Evm.Memory.Objects.cells heap reference := by
  rw [← objectWords_cells, SVal.keeps_copyStToM, objectWords_wk, objectWords_cells]

def traversalWords : TraversalWordsCertificate (@heapWords) (@liveWordCount) :=
  ⟨valueCopy_words, copy_old_cells⟩

#print axioms objectWords_wk
#print axioms objectsWords_wk
#print axioms objectsWords_snoc
#print axioms heapWords_alloc
#print axioms objectWords_cells
#print axioms valueCopy_words
#print axioms fieldsCopy_words
#print axioms elementsCopy_words
#print axioms copy_old_cells
#print axioms traversalWords
end Solidity.Backend.MemoryCopies
