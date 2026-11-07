import Solidity.Backend.MemoryCopies.HeapContents

/-! Populated intrinsic copy controls. Nested live lengths include empty and
64-element children; storage-only shadow entries are not live contents. These
are kernel observations of the existing intrinsic copy, not EVM gas claims. -/
namespace Solidity.Backend.MemoryCopies.HeapContentsControls

private def seven : SVal (.prim .uint) := .prim ⟨7, by decide⟩
private def eight : SVal (.prim .uint) := .prim ⟨8, by decide⟩
private def eleven : SVal (.prim .uint) := .prim ⟨11, by decide⟩
private def thirteen : SVal (.prim .uint) := .prim ⟨13, by decide⟩
private def ninetyNine : SVal (.prim .uint) := .prim ⟨99, by decide⟩
private def childTy : Ty := .ref (.array (.prim .uint))

private def populated : SVal childTy :=
  .array (.cons seven (.cons eleven .nil)) (.cons ninetyNine .nil) (by decide)
private def wrong : SVal childTy :=
  .array (.cons eight (.cons eleven .nil)) .nil (by decide)
private def empty : SVal childTy := .array .nil (.cons ninetyNine .nil) (by decide)
private def long : SVal childTy :=
  .array (SVec.replicate thirteen 64) (.cons ninetyNine .nil) (by decide)
private def nested : SVal (.ref (.array childTy)) :=
  .array (.cons populated (.cons empty (.cons long .nil))) .nil (by decide)
private def basket : SVal (.ref (.struct "Basket")) := .struct (.cons populated .nil)
private def fixed : SVal (.ref (.fixed childTy 2)) := .fixed (.cons populated (.cons empty .nil))
private def initial : Heap [] := ()

/-- The generic contents signature is inhabited, without a capacity premise. -/
theorem mirror_inhabited : Nonempty MirrorContentsCertificate := ⟨mirrorContents⟩

theorem nested_certificate_inhabited : Nonempty (V2.StorageHeapCertificate nested rfl) :=
  ⟨storageHeapContents nested rfl⟩

/-- This equality preserves every live nested element, not just the lengths. -/
theorem nested_roundtrip {H : HTy} (heap : Heap H) :
    MVal.copyMToSt (nested.copyStToM heap rfl).heap (nested.copyStToM heap rfl).val =
      nested.strip := (storageHeapContents nested rfl).contents heap

/-- All three child objects and their fresh parent are actually allocated. -/
theorem nested_root_and_count :
    (nested.copyStToM initial rfl).val.id = 3 ∧
      (nested.copyStToM initial rfl).H'.length = 4 := by
  decide +kernel

/-- Parent live elements select the populated, empty and long copied children. -/
theorem nested_child_lengths :
    let grown := nested.copyStToM initial rfl
    (MObj.elems .dyn (grown.heap.get grown.val)).map
      (fun child => grown.heap.len child .dyn) = [2, 0, 64] := by
  decide +kernel

private theorem different_live_contents : populated.strip ≠ wrong.strip := by
  decide +kernel

/-- A wrong live word cannot satisfy the roundtrip result, even though shadow
slots are intentionally removed by the published model. -/
theorem wrong_contents_rejected {H : HTy} (heap : Heap H) :
    MVal.copyMToSt (populated.copyStToM heap rfl).heap
      (populated.copyStToM heap rfl).val ≠ wrong.strip := by
  rw [(storageHeapContents populated rfl).contents heap]
  exact different_live_contents

/-- Copies strip the nonempty shadow of an empty live array. -/
theorem empty_live_shadow_removed {H : HTy} (heap : Heap H) :
    MVal.copyMToSt (empty.copyStToM heap rfl).heap (empty.copyStToM heap rfl).val =
      SVal.array (E := .prim .uint) .nil .nil (by decide) := by
  rw [(storageHeapContents empty rfl).contents heap]
  simp only [empty, SVal.strip_array, SVec.strip_nil]

/-- Both struct-held and fixed-array-held dynamic children retain live data. -/
theorem struct_and_fixed_roundtrip {H : HTy} (heap : Heap H) :
    MVal.copyMToSt (basket.copyStToM heap rfl).heap (basket.copyStToM heap rfl).val =
      basket.strip ∧
    MVal.copyMToSt (fixed.copyStToM heap rfl).heap (fixed.copyStToM heap rfl).val =
      fixed.strip :=
  ⟨(storageHeapContents basket rfl).contents heap, (storageHeapContents fixed rfl).contents heap⟩

#print axioms struct_and_fixed_roundtrip
#print axioms mirror_inhabited
#print axioms nested_certificate_inhabited
#print axioms nested_roundtrip
#print axioms nested_root_and_count
#print axioms nested_child_lengths
#print axioms wrong_contents_rejected
#print axioms empty_live_shadow_removed
end Solidity.Backend.MemoryCopies.HeapContentsControls
