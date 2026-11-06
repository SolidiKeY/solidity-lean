import Solidity.Yul.Views.EnumeratedMemory
import Solidity.Yul.Views.HeapPreparationMemOK
import Solidity.Yul.Views.MixedHeapControls

namespace Solidity.Yul.Views.Controls

def enumerationEmptyPlacement : Placement (Source.Heap.empty : Source.Heap mixedLayout) where
  address := fun _ => 128
  shape := fun _ => .bytes 0
  free := 128
  free_start := by decide
  distinct _ _ present _ _ := by cases present
  typed _ _ _ found := by cases found
  starts _ present := by cases present
  ends _ present := by cases present
  separate _ _ present _ _ := by cases present

theorem enumeration_empty_exact : prepareHeapInventory enumerationEmptyPlacement = .ok [] ∧
    missingHeapCells enumerationEmptyPlacement = [] ∧ unsupportedHeapCells enumerationEmptyPlacement = [] := ⟨rfl,rfl,rfl⟩

def enumerationSparseHeap : Source.Heap mixedLayout where
  cells a := if a = 2 then some ⟨.bytes .memory,.bytes mixedChild⟩ else none
  next := 5
  bounded a bound := if_neg (by omega)

def enumerationSparsePlacement : Placement enumerationSparseHeap where
  address a := 128 + a * 64
  shape := fun _ => .bytes 3
  free := 512
  free_start := by decide
  distinct a b _ _ eq := by omega
  typed a τ d found := by
    change (if a = 2 then some (⟨.bytes .memory,.bytes mixedChild⟩ : Sigma (Source.Data mixedLayout)) else none) = some ⟨τ,d⟩ at found
    split at found
    · cases found; exact .bytes _
    · cases found
  starts _ _ := by omega
  ends a present := by
    have atTwo : a = 2 := by
      change (if a = 2 then some _ else none).isSome = true at present
      split at present
      · assumption
      · cases present
    subst a
    decide
  separate a b pa pb neq := by
    have atTwo (a : Nat) (present : (enumerationSparseHeap.cells a).isSome) : a = 2 := by
      change (if a = 2 then some _ else none).isSome = true at present
      split at present
      · assumption
      · cases present
    exact False.elim (neq ((atTwo a pa).trans (atTwo b pb).symm))

theorem enumeration_sparse_exact : missingHeapCells enumerationSparsePlacement = [0,1,3,4] ∧
    unsupportedHeapCells enumerationSparsePlacement = [] ∧
    (generatedHeapEntries enumerationSparsePlacement).map MixedHeapEntry.id = [2] := by decide

theorem enumeration_sparse_coverage : CoversMixedHeap (generatedHeapEntries enumerationSparsePlacement) :=
  generatedHeapEntries_coverage _ enumeration_sparse_exact.2.1

theorem enumeration_missing_child : prepareElement enumerationSparsePlacement (Source.Val.memRef (τ := .bytes .memory) rfl 0) = none := by decide

theorem enumeration_wrong_child_type : prepareElement mixedPlacement (Source.Val.memRef (τ := .bytes .memory) rfl 2) = none := by decide

theorem enumeration_inline_not_pointer : prepareMember mixedPlacement (Source.Data.bytes (D := mixedLayout) (l := .memory) mixedChild) = none := rfl

/-- Valid placement does not imply child ownership: this actual array points
to a missing cell. The WHOLE preparation reports its occupied unsupported ID. -/
def enumerationDanglingHeap : Source.Heap mixedLayout where
  cells a := if a = 2 then some ⟨mixedArrayTy,mixedDynamic⟩ else none
  next := 5
  bounded a bound := if_neg (by omega)

def enumerationDanglingPlacement : Placement enumerationDanglingHeap where
  address := enumerationSparsePlacement.address
  shape := fun _ => .array true 2
  free := 512
  free_start := by decide
  distinct a b _ _ eq := by change 128+a*64 = 128+b*64 at eq; omega
  typed a τ d found := by
    change (if a = 2 then some (⟨mixedArrayTy,mixedDynamic⟩ : Sigma (Source.Data mixedLayout)) else none) = some ⟨τ,d⟩ at found
    split at found
    · cases found; exact .array 2 _ _
    · cases found
  starts _ _ := by change 128 ≤ 128+_*64; omega
  ends a present := by
    change (if a = 2 then some _ else none).isSome = true at present
    split at present
    · subst a; decide
    · cases present
  separate a b pa pb neq := by
    change (if a = 2 then some _ else none).isSome = true at pa
    change (if b = 2 then some _ else none).isSome = true at pb
    split at pa <;> split at pb
    · exact False.elim (neq (by omega))
    all_goals simp only [Option.isSome_none,Bool.false_eq_true] at pa pb

theorem enumeration_occupied_failure_exact : prepareHeapInventory enumerationDanglingPlacement = .error [2] ∧
    missingHeapCells enumerationDanglingPlacement = [0,1,3,4] ∧
    (generatedHeapEntries enumerationDanglingPlacement).map MixedHeapEntry.id = [] := by
  constructor
  · unfold prepareHeapInventory
    rw [show unsupportedHeapCells enumerationDanglingPlacement = [2] from by decide]
  · constructor <;> decide

end Solidity.Yul.Views.Controls
