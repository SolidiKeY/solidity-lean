import Solidity.Backend.MemoryOps.SliceBounds

/-!
# Snapshot and overlap laws for existing typed element lists

These operation-side list adapters can be instantiated with `MObj.elems`.
They do not supply a target emitter or claim an EVM simulation. In particular,
reference elements are copied as identities; a deep-copy premise stays open.
-/
namespace Solidity.Backend.MemoryOps

/-- Replace an interval using an already captured payload. -/
def replaceSlice {α : Type} (xs : List α) (dst : Nat) (payload : List α) : List α :=
  xs.take dst ++ (payload ++ xs.drop (dst + payload.length))

theorem replaceSlice_length {α : Type} (xs payload : List α) (dst : Nat)
    (h : dst + payload.length ≤ xs.length) :
    (replaceSlice xs dst payload).length = xs.length := by
  have hd : dst ≤ xs.length := by omega
  simp only [replaceSlice, List.length_append, List.length_take,
    Nat.min_eq_left hd, List.length_drop]
  omega

theorem replaceSlice_inside {α : Type} (xs payload : List α) (dst i : Nat)
    (h : dst + payload.length ≤ xs.length) (hi : i < payload.length) :
    (replaceSlice xs dst payload)[dst + i]? = payload[i]? := by
  have hd : dst ≤ xs.length := by omega
  simp only [replaceSlice, List.getElem?_append, List.length_take,
    Nat.min_eq_left hd, if_neg (show ¬ dst + i < dst by omega),
    Nat.add_sub_cancel_left, if_pos hi]

theorem replaceSlice_before {α : Type} (xs payload : List α) (dst i : Nat)
    (h : dst + payload.length ≤ xs.length) (hi : i < dst) :
    (replaceSlice xs dst payload)[i]? = xs[i]? := by
  have hd : dst ≤ xs.length := by omega
  simp only [replaceSlice, List.getElem?_append, List.length_take,
    Nat.min_eq_left hd, if_pos hi, List.getElem?_take_of_lt hi]

theorem replaceSlice_after {α : Type} (xs payload : List α) (dst i : Nat)
    (h : dst + payload.length ≤ xs.length) (hi : dst + payload.length ≤ i) :
    (replaceSlice xs dst payload)[i]? = xs[i]? := by
  have hd : dst ≤ xs.length := by omega
  simp only [replaceSlice, List.getElem?_append, List.length_take,
    Nat.min_eq_left hd, if_neg (show ¬ i < dst by omega),
    if_neg (show ¬ i - dst < payload.length by omega), List.getElem?_drop]
  congr 1
  omega

theorem replaceSlice_empty {α : Type} (xs : List α) (dst : Nat) :
    replaceSlice xs dst [] = xs := by
  simp only [replaceSlice, List.length_nil, Nat.add_zero, List.nil_append,
    List.take_append_drop]

/-- Capture from the original list before replacing: both overlap directions
use the same original values, regardless of the destination interval. -/
def snapshotCopy {α : Type} (xs : List α) (src len dst : Nat) : List α :=
  replaceSlice xs dst ((xs.drop src).take len)

theorem snapshotCopy_read {α : Type} (xs : List α) (src len dst i : Nat)
    (hs : src + len ≤ xs.length) (hd : dst + len ≤ xs.length) (hi : i < len) :
    (snapshotCopy xs src len dst)[dst + i]? = xs[src + i]? := by
  have hl : ((xs.drop src).take len).length = len := by
    rw [List.length_take, List.length_drop]
    exact Nat.min_eq_left (by omega)
  rw [snapshotCopy, replaceSlice_inside xs _ dst i (by omega) (by omega),
    List.getElem?_take_of_lt hi, List.getElem?_drop]

theorem snapshotCopy_length {α : Type} (xs : List α) (src len dst : Nat)
    (hs : src + len ≤ xs.length) (hd : dst + len ≤ xs.length) :
    (snapshotCopy xs src len dst).length = xs.length := by
  apply replaceSlice_length
  have hl : ((xs.drop src).take len).length = len := by
    rw [List.length_take, List.length_drop]
    exact Nat.min_eq_left (by omega)
  omega

/-- Zero-length copies make no element observation and change nothing. -/
theorem snapshotCopy_empty {α : Type} (xs : List α) (src dst : Nat) :
    snapshotCopy xs src 0 dst = xs := by
  simp only [snapshotCopy, List.take_zero, replaceSlice_empty]

/-- Checked adapter: invalid source or destination endpoints fail explicitly. -/
def checkedSnapshotCopy {α : Type} (xs : List α) (src len dst : Nat) : Option (List α) :=
  if src + len ≤ xs.length ∧ dst + len ≤ xs.length then
    some (snapshotCopy xs src len dst)
  else none

theorem checkedSnapshotCopy_none_iff {α : Type} (xs : List α) (src len dst : Nat) :
    checkedSnapshotCopy xs src len dst = none ↔
      xs.length < src + len ∨ xs.length < dst + len := by
  by_cases h : src + len ≤ xs.length ∧ dst + len ≤ xs.length
  · rw [checkedSnapshotCopy, if_pos h]
    constructor
    · intro he
      cases he
    · intro bad
      rcases bad with hs | hd <;> omega
  · rw [checkedSnapshotCopy, if_neg h]
    constructor
    · intro _
      by_cases hs : src + len ≤ xs.length
      · right
        have hn : ¬ dst + len ≤ xs.length := fun hd => h ⟨hs, hd⟩
        omega
      · left
        omega
    · intro _
      rfl

/-- In-bounds success has exact length and captures every source value. -/
theorem checkedSnapshotCopy_correct {α : Type} (xs : List α) (src len dst : Nat)
    (hs : src + len ≤ xs.length) (hd : dst + len ≤ xs.length) :
    ∃ ys, checkedSnapshotCopy xs src len dst = some ys ∧ ys.length = xs.length ∧
      ∀ i, i < len → ys[dst + i]? = xs[src + i]? := by
  refine ⟨snapshotCopy xs src len dst, ?_, snapshotCopy_length xs src len dst hs hd, ?_⟩
  · simp only [checkedSnapshotCopy, if_pos (And.intro hs hd)]
  · intro i hi
    exact snapshotCopy_read xs src len dst i hs hd hi

/-- Both ends of the checked failure boundary are inhabited. -/
theorem checked_controls :
    checkedSnapshotCopy [1, 2, 3, 4] 0 3 1 = some [1, 1, 2, 3] ∧
    checkedSnapshotCopy [1, 2, 3, 4] 0 3 2 = none ∧
    checkedSnapshotCopy [1, 2, 3, 4] 2 3 0 = none ∧
    checkedSnapshotCopy ([] : List Nat) 0 0 0 = some [] := by decide

/-- Both overlapping directions and the streaming-copy counterexample. -/
theorem overlap_controls :
    snapshotCopy [1, 2, 3, 4] 0 3 1 = [1, 1, 2, 3] ∧
    snapshotCopy [1, 2, 3, 4] 1 3 0 = [2, 3, 4, 4] ∧
    snapshotCopy [1, 2, 3, 4] 0 3 1 ≠ [1, 1, 1, 1] := by decide

/-- A nonempty payload has source and destination crossing index 32; the suffix is framed. -/
theorem boundary_nonempty :
    (snapshotCopy (List.range 65) 31 33 0)[0]? = some 31 ∧
    (snapshotCopy (List.range 65) 31 33 0)[32]? = some 63 ∧
    (snapshotCopy (List.range 65) 31 33 0)[33]? = some 33 ∧
    (snapshotCopy (List.range 65) 31 33 0)[64]? = some 64 ∧
    (snapshotCopy (List.range 65) 31 33 0).length = 65 := by decide

/-- An empty copy at an element-index boundary is an identity for every payload length. -/
theorem boundary_empty {α : Type} (xs : List α) : snapshotCopy xs 32 0 32 = xs :=
  snapshotCopy_empty xs 32 32

/-- info: 'Solidity.Backend.MemoryOps.checkedSnapshotCopy_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedSnapshotCopy_correct
/-- info: 'Solidity.Backend.MemoryOps.checkedSnapshotCopy_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedSnapshotCopy_none_iff
/-- info: 'Solidity.Backend.MemoryOps.snapshotCopy_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms snapshotCopy_read
/-- info: 'Solidity.Backend.MemoryOps.snapshotCopy_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms snapshotCopy_length
/-- info: 'Solidity.Backend.MemoryOps.replaceSlice_after' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms replaceSlice_after
/-- info: 'Solidity.Backend.MemoryOps.overlap_controls' does not depend on any axioms -/
#guard_msgs in #print axioms overlap_controls

end Solidity.Backend.MemoryOps
