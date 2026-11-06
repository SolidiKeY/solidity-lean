import Solidity.Backend.MemoryCopies.FixedReferenceLiveInterface

/-! Normalize only the live child value while preserving the original storage
copy fold and exact intrinsic fixed index. No stored value is overwritten. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem fixed_reference_live_count {primitive : PrimTy} {count : Nat}
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count))) :
    (fixedReferenceLiveRows value).length = count := by
  simp only [fixedReferenceLiveRows,List.length_map,SVec.length_toList]

theorem fixed_reference_live_rows {primitive : PrimTy} {count : Nat}
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count))) :
    (fixedReferenceLiveCanonical value).view.toList =
      (fixedReferenceLiveRows value).map (fun row => primitiveArrayValue primitive row.val row.property) := by
  cases value with
  | fixed elements =>
    simp only [fixedReferenceLiveCanonical,fixedReferenceLiveRows,SVal.view,SVec.toList_ofLen,
      List.map_map,Function.comp_def,fixedReferenceLiveChild,fixedReferenceLiveRow]
    rfl

theorem fixed_reference_live_vector_copy {primitive : PrimTy} {count : Nat}
    (elements : SVec (.ref (.array (.prim primitive))) count) {H : HTy} (heap : Heap H) :
    elements.copyStToM heap rfl =
      (SVec.ofLen fixedReferenceLiveChild count elements.toList (SVec.length_toList elements)).copyStToM heap rfl := by
  cases elements with
  | nil => simp only [SVec.toList_nil,SVec.ofLen,SVec.copyStToM_nil]
  | cons value rest =>
    have head : value.copyStToM heap rfl = (fixedReferenceLiveChild value).copyStToM heap rfl :=
      primitive_live_copy value heap
    simp only [SVec.toList_cons,SVec.ofLen,SVec.copyStToM_cons]
    rw [head,fixed_reference_live_vector_copy rest]

theorem fixed_reference_live_copy {primitive : PrimTy} {count : Nat}
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count))) {H : HTy} (heap : Heap H) :
    value.copyStToM heap rfl = (fixedReferenceLiveCanonical value).copyStToM heap rfl := by
  cases value with
  | fixed elements =>
    simp only [fixedReferenceLiveCanonical,SVal.view,SVal.copyStToM_fixed,fixed_reference_live_vector_copy elements heap]

theorem fixed_reference_live_representation {primitive : PrimTy} {count : Nat}
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (store : WordStore) (limit : Nat) (source : Slot)
    (represented : ReprAt store limit (.ref (.fixed (.ref (.array (.prim primitive))) count)) source value) :
    ReprAt store limit (.ref (.fixed (.ref (.array (.prim primitive))) count)) source
      (fixedReferenceLiveCanonical value) := by
  cases represented with
  | fixed elements =>
    apply ReprAt.fixed
    intro index child selected
    simp only [fixedReferenceLiveCanonical,SVal.view,SVec.toList_ofLen,List.getElem?_map] at selected
    obtain ⟨original,chosen,rfl⟩ := Option.map_eq_some_iff.mp selected
    exact primitive_live_representation original store limit _ (elements index original chosen)

theorem fixed_reference_live_contents {primitive : PrimTy} {count : Nat}
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count))) :
    (fixedReferenceLiveCanonical value).strip = value.strip := by
  have sameCopy : value.copyStToM (H := []) Heap.empty rfl =
      (fixedReferenceLiveCanonical value).copyStToM (H := []) Heap.empty rfl := fixed_reference_live_copy value Heap.empty
  have original : MVal.copyMToSt (value.copyStToM (H := []) Heap.empty rfl).heap
      (value.copyStToM (H := []) Heap.empty rfl).val = value.strip :=
    (storageHeapContents value rfl).contents (H := []) Heap.empty
  have normalized : MVal.copyMToSt ((fixedReferenceLiveCanonical value).copyStToM (H := []) Heap.empty rfl).heap
      ((fixedReferenceLiveCanonical value).copyStToM (H := []) Heap.empty rfl).val = (fixedReferenceLiveCanonical value).strip :=
    (storageHeapContents (fixedReferenceLiveCanonical value) rfl).contents (H := []) Heap.empty
  rw [sameCopy] at original
  exact normalized.symm.trans original

def fixedReferenceLive {primitive : PrimTy} {count : Nat}
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count))) : FixedReferenceLiveCertificate value :=
  ⟨fixed_reference_live_count value,fixed_reference_live_rows value,fixed_reference_live_copy value,
    fixed_reference_live_representation value,fixed_reference_live_contents value⟩

/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_live_count' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms fixed_reference_live_count
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_live_rows' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms fixed_reference_live_rows
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_live_vector_copy' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms fixed_reference_live_vector_copy
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_live_copy' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms fixed_reference_live_copy
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_live_representation' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_live_representation
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_live_contents' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_live_contents
/--
info: 'Solidity.Backend.MemoryCopies.fixedReferenceLive' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms fixedReferenceLive
end Solidity.Backend.MemoryCopies
