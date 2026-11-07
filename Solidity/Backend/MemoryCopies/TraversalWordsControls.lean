import Solidity.Backend.MemoryCopies.TraversalWords
import Solidity.Backend.MemoryCopies.TraversalFootprint

/-! Inhabited and negative controls for intrinsic cell-sum demand. -/
namespace Solidity.Backend.MemoryCopies.TraversalWordsControls
private def leafType : Ty := .ref (.array (.prim .uint))
private def branchType : Ty := .ref (.fixed leafType 2)
private def seven : SVal (.prim .uint) := .prim ⟨7, by decide⟩
private def leaf : SVal leafType :=
  .array (.cons seven (.cons seven .nil)) (.cons seven .nil) (by decide)
private def branch : SVal branchType := .fixed (.cons leaf (.cons leaf .nil))
private def tree : SVal (.ref (.array branchType)) :=
  .array (.cons branch (.cons branch .nil)) (.cons branch .nil) (by decide)
private def empty : SVal (.ref (.array branchType)) := .array .nil (.cons branch .nil) (by decide)
private def emptyFixed : SVal (.ref (.fixed leafType 0)) := .fixed .nil
/-- Intrinsic empty-node padding only; this name is not claimed source-admitted. -/
private def emptyStruct : SVal (.ref (.struct "")) := .struct .nil
private def basket : SVal (.ref (.struct "Basket")) := .struct (.cons leaf .nil)
private def account : SVal (.ref (.struct "Account")) :=
  .struct (.cons seven (.cons (.struct (.cons seven .nil)) .nil))
private def long : SVal (.ref (.array branchType)) :=
  .array (SVec.replicate branch 64) (.cons branch .nil) (by decide)
private def seed := leaf.copyStToM (H := []) () rfl
private def grown := tree.copyStToM seed.heap rfl
private def second := tree.copyStToM grown.heap rfl

theorem demand_values : liveWordCount seven = 0 ∧ liveWordCount leaf = 3 ∧
    liveWordCount branch = 8 ∧ liveWordCount tree = 19 ∧ liveWordCount basket = 4 ∧
    liveWordCount account = 3 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem certificate_inhabited : TraversalWordsCertificate (@heapWords) (@liveWordCount) :=
  traversalWords

theorem empty_padding : liveWordCount empty = 1 ∧ liveWordCount emptyFixed = 1 ∧
    liveWordCount emptyStruct = 1 ∧
    heapWords (empty.copyStToM seed.heap rfl).heap = 4 ∧
    heapWords (emptyFixed.copyStToM seed.heap rfl).heap = 4 ∧
    heapWords (seed.heap.alloc (R := .struct "") ()).1 = 4 := by decide +kernel

theorem exact_heap_growth : heapWords seed.heap = 3 ∧ heapWords grown.heap = 22 ∧
    heapWords second.heap = 41 := by decide +kernel

theorem old_reservation_retained :
    Evm.Memory.Objects.cells grown.heap (seed.val.wk grown.ext) =
      Evm.Memory.Objects.cells seed.heap seed.val := copy_old_cells tree rfl seed.heap seed.val

theorem root_cells_are_not_total : Evm.Memory.Objects.cells grown.heap grown.val = 3 ∧
    liveWordCount tree ≠ 3 := by decide +kernel

theorem identities_are_not_words : liveObjectCount tree = 7 ∧ liveWordCount tree ≠ 7 := by
  decide +kernel

/-- Equal children are copied separately; their eight-word subtrees occur twice. -/
theorem repeated_children : liveWordCount tree = 8 + 8 + 3 ∧ liveWordCount tree ≠ 8 + 3 := by
  decide +kernel

/-- A stored shadow subtree does not increase actual live allocation demand. -/
theorem shadow_not_counted : liveWordCount tree =
    liveWordCount (SVal.array (.cons branch (.cons branch .nil)) .nil (by decide)) ∧
    liveWordCount empty ≠ 1 + liveWordCount branch := by decide +kernel

theorem long_growth {H : HTy} (heap : Heap H) :
    heapWords (long.copyStToM heap rfl).heap = heapWords heap + 577 := by
  have demand : liveWordCount long = 577 := by decide +kernel
  simpa only [demand] using valueCopy_words long rfl heap

theorem mapping_not_memory : (Ty.ref (.mapping .uint (.prim .uint))).mapFree ≠ true := by decide

#print axioms demand_values
#print axioms certificate_inhabited
#print axioms empty_padding
#print axioms exact_heap_growth
#print axioms old_reservation_retained
#print axioms root_cells_are_not_total
#print axioms identities_are_not_words
#print axioms repeated_children
#print axioms shadow_not_counted
#print axioms long_growth
#print axioms mapping_not_memory
end Solidity.Backend.MemoryCopies.TraversalWordsControls
