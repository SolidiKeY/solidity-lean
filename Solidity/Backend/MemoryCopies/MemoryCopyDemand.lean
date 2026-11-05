import Solidity.Backend.MemoryCopies.MemoryCopyDemandInterface

/-! Demand follows actual memory snapshots and the existing copy fold. Shared
references are unfolded by that fold, not collapsed by a new graph traversal. -/
namespace Solidity.Backend.MemoryCopies

mutual
theorem liveWordCount_strip : {T : Ty} → (value : SVal T) →
    liveWordCount value.strip = liveWordCount value
  | _, .prim value => by rw [SVal.strip_prim]
  | _, .struct fields => by
    rw [SVal.strip_struct]
    simp only [liveWordCount, fieldWordCount_strip]
  | _, .array values shadow bound => by
    rw [SVal.strip_array]
    simp only [liveWordCount, elementWordCount_strip]
  | _, .fixed values => by
    rw [SVal.strip_fixed]
    simp only [liveWordCount, elementWordCount_strip]
  | _, .map values default => by rw [SVal.strip_map]

theorem fieldWordCount_strip : {fields : List (Name × Ty)} → (values : SFields fields) →
    fieldWordCount values.strip = fieldWordCount values
  | _, .nil => by rw [SFields.strip_nil]
  | _, .cons value rest => by
    rw [SFields.strip_cons]
    simp only [fieldWordCount, liveWordCount_strip, fieldWordCount_strip]

theorem elementWordCount_strip : {T : Ty} → {count : Nat} → (values : SVec T count) →
    elementWordCount values.strip = elementWordCount values
  | _, _, .nil => by rw [SVec.strip_nil]
  | _, _, .cons value rest => by
    rw [SVec.strip_cons]
    simp only [elementWordCount, liveWordCount_strip, elementWordCount_strip]
end

theorem reference_word_count_positive {R : RefTy} (value : SVal (.ref R))
    (memory : (Ty.ref R).mapFree = true) : 0 < liveWordCount value := by
  cases value with
  | struct fields => simp only [liveWordCount]; omega
  | array values shadow bound => simp only [liveWordCount]; omega
  | fixed values => simp only [liveWordCount]; omega
  | map values default => simp only [Ty.mapFree, Bool.false_eq_true] at memory

theorem copied_read_word_count {R : RefTy} (value : SVal (.ref R))
    (memory : (Ty.ref R).mapFree = true) {H : HTy} (heap : Heap H) :
    liveWordCount (MVal.copyMToSt (value.copyStToM heap memory).heap
      (T := .ref R) (value.copyStToM heap memory).val) = liveWordCount value := by
  rw [(storageHeapContents value memory).contents heap, liveWordCount_strip]

def memoryCopyDemand {H : HTy} {R : RefTy} (heap : Heap H) (input : HRef H R)
    (memory : (Ty.ref R).mapFree = true) : MemoryCopyDemandCertificate heap input memory where
  growth := valueCopy_words (MVal.copyMToSt heap (T := .ref R) input) memory heap
  positive := reference_word_count_positive _ memory
  recopy := copied_read_word_count _ memory heap

/-- Copying the new snapshot again has the same demand, even when the initial
heap had shared children. Each copy's actual fold allocates its own descendants. -/
theorem memory_copy_twice_words {H : HTy} {R : RefTy} (heap : Heap H) (input : HRef H R)
    (memory : (Ty.ref R).mapFree = true) :
    let snapshot := MVal.copyMToSt heap (T := .ref R) input
    let first := snapshot.copyStToM heap memory
    let second := (MVal.copyMToSt first.heap (T := .ref R) first.val).copyStToM first.heap memory
    heapWords second.heap = heapWords heap + 2 * liveWordCount snapshot := by
  dsimp only
  rw [valueCopy_words, copied_read_word_count, valueCopy_words]
  omega

/-- Real successful alias rebinding changes a local only. The existing compiled
alias theorem remains separate; no heap-identity-only record is assumed here. -/
theorem alias_rebind_words {C : Contract} {Γ : Ctx} {R : RefTy} (state : State C Γ)
    (path : MPath C Γ (.ref R)) (destination : Idx Γ (.mem R)) (reference : HRef state.H R)
    (resolved : path.mvalT state = .ok reference) :
    TRun.rebindMem destination (.alias path) state =
      .ok ⟨state.setLocal destination (some reference), List.prefix_refl _⟩ ∧
    heapWords (state.setLocal destination (some reference)).heap = heapWords state.heap := by
  refine ⟨?_, rfl⟩
  simp only [TRun.rebindMem, MRhs.evalT, resolved, bind, Except.bind, pure, Except.pure]

def memoryAliasDemand : MemoryAliasDemandCertificate := ⟨alias_rebind_words⟩

#print axioms liveWordCount_strip
#print axioms fieldWordCount_strip
#print axioms elementWordCount_strip
#print axioms reference_word_count_positive
#print axioms copied_read_word_count
#print axioms memoryCopyDemand
#print axioms memory_copy_twice_words
#print axioms alias_rebind_words
#print axioms memoryAliasDemand
end Solidity.Backend.MemoryCopies
