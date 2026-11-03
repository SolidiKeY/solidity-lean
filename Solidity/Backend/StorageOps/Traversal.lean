import Solidity.Semantics.RecursiveStorage.Copy

/-!
Runtime-length storage-to-storage traversal over the published intrinsic graph
slots. The loop visits the union of the old and new live prefixes. Its leaf
operation is the existing semantic `Slot.overlay`; nested traversal realization
and the opcode loop remain separate obligations. No source admission is added.
-/

namespace Solidity.Backend.StorageOps

open TypeGraph

/-- Visit successive indices, preserving the unvisited suffix. The count is a
runtime length, not an admission or recursion-depth bound. -/
def visit {n extent : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (target : Fin extent → Slot G E) : Nat →
    (Fin extent → Slot G E) → (Fin extent → Slot G E)
  | 0, initial => initial
  | count + 1, initial =>
    let prior := visit target count initial
    if h : count < extent then
      let value := target ⟨count, h⟩
      fun i => if i.val = count then value else prior i
    else prior

/-- Exact loop invariant, including every unvisited retained slot. -/
theorem visit_prefix {n extent : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (target initial : Fin extent → Slot G E) (count : Nat) (i : Fin extent) :
    visit target count initial i = if i.val < count then target i else initial i := by
  induction count with
  | zero => simp only [visit, Nat.not_lt_zero, if_false]
  | succ count ih =>
    simp only [visit]
    split
    next inside =>
      by_cases equal : i.val = count
      · have same : (⟨count, inside⟩ : Fin extent) = i := Fin.ext equal.symm
        simp only [if_pos equal, same, if_pos (show i.val < count + 1 by omega)]
      · simp only [if_neg equal, ih]
        by_cases before : i.val < count
        · simp only [if_pos before, if_pos (show i.val < count + 1 by omega)]
        · simp only [if_neg before, if_neg (show ¬ i.val < count + 1 by omega)]
    next outside =>
      rw [ih]
      have before : i.val < count := by have bound := i.isLt; omega
      simp only [if_pos before, if_pos (show i.val < count + 1 by omega)]

/-- Lift old slots to the resulting retained extent without allocating values. -/
def oldSlot {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (extent : Extent) (slots : Fin extent.val → Slot G E) (i : Nat) : Slot G E :=
  if h : i < extent.val then slots ⟨i, h⟩ else .absent

/-- One array traversal. Source and destination slots are captured before the
loop. A former live tail is cleared; an older shadow is left alone. -/
def traverse {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (oe : Extent) (ol : Index) (_oh : ol.val ≤ oe.val) (os : Fin oe.val → Slot G E)
    (ne : Extent) (nl : Index) (nh : nl.val ≤ ne.val) (ns : Fin ne.val → Slot G E) :
    Value G (.array E) :=
  let extent : Extent := ⟨max oe.val nl.val, by
    have ho := oe.isLt
    have hn := nl.isLt
    omega⟩
  let initial : Fin extent.val → Slot G E := fun i => oldSlot oe os i.val
  let target : Fin extent.val → Slot G E := fun i =>
    if h : i.val < nl.val then
      Slot.overlay (initial i) (ns ⟨i.val, Nat.lt_of_lt_of_le h nh⟩)
    else if i.val < ol.val then (initial i).clear else initial i
  .array extent nl (Nat.le_max_right _ _)
    (visit target (max ol.val nl.val) initial)

/-- The finite runtime loop implements the independent snapshot-copy meaning.
This is an intrinsic graph-array theorem, not an EVM representation theorem. -/
theorem traverse_eq_overlay {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (oe : Extent) (ol : Index) (oh : ol.val ≤ oe.val) (os : Fin oe.val → Slot G E)
    (ne : Extent) (nl : Index) (nh : nl.val ≤ ne.val) (ns : Fin ne.val → Slot G E) :
    traverse oe ol oh os ne nl nh ns =
      (Value.array oe ol oh os).overlay (.array ne nl nh ns) := by
  unfold traverse Value.overlay
  dsimp only
  congr 1
  funext i
  rw [visit_prefix]
  by_cases visited : i.val < max ol.val nl.val
  · simp only [if_pos visited, oldSlot]
  · have oldEnd : ¬ i.val < ol.val := by omega
    have newEnd : ¬ i.val < nl.val := by omega
    simp only [if_neg visited, dif_neg newEnd, if_neg oldEnd, oldSlot]

/-- The constructor's existing live/retained bound, used only as a proof. -/
theorem array_live_bound {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (v : Value G (.array E)) : v.length.val ≤ v.extent.val := by
  cases v with
  | array _ _ bound _ => exact bound

/-- Array copy with runtime traversal, using the existing intrinsic projections
rather than a new indexed-family match in kernel-evaluated code. -/
def copyArray {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old src : Value G (.array E)) : Value G (.array E) :=
  traverse old.extent old.length (array_live_bound old) old.slots
    src.extent src.length (array_live_bound src) src.slots

theorem copyArray_eq_overlay {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old src : Value G (.array E)) : copyArray old src = old.overlay src := by
  cases old
  cases src
  exact traverse_eq_overlay _ _ _ _ _ _ _ _

/-- Capture an array source before changing any destination path, even when
both paths overlap. Failure returns no modified root. -/
def copyAt {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root : Value G A) (dst src : TypeGraph.Path G A (.array E)) : Option (Value G A) := do
  let snapshot ← root.find src
  let old ← root.find dst
  root.save dst (copyArray old snapshot)

theorem copyAt_eq_semantics {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root : Value G A) (dst src : TypeGraph.Path G A (.array E)) :
    copyAt root dst src = root.copyAt dst src := by
  simp only [copyAt, Value.copyAt, Value.write, copyArray_eq_overlay]

/-- Read-back states overlay, rather than equality to a source with a different
retained history. No disjointness premise is imposed on the two paths. -/
theorem copyAt_readback {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root result : Value G A) (dst src : TypeGraph.Path G A (.array E))
    (old snapshot : Value G (.array E))
    (readDst : root.find dst = some old) (readSrc : root.find src = some snapshot)
    (copied : copyAt root dst src = some result) :
    result.find dst = some (old.overlay snapshot) := by
  rw [copyAt_eq_semantics] at copied
  exact root.find_copyAt result dst src old snapshot readDst readSrc copied

/-- A failed source read fails before any destination update. -/
theorem copyAt_missing_source {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root : Value G A) (dst src : TypeGraph.Path G A (.array E))
    (missing : root.find src = none) : copyAt root dst src = none := by
  unfold copyAt
  rw [missing]
  rfl

/-- An unavailable destination also fails, including nested-array paths. -/
theorem copyAt_missing_destination {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root : Value G A) (dst src : TypeGraph.Path G A (.array E))
    (missing : root.find dst = none) : copyAt root dst src = none := by
  unfold copyAt
  cases readSrc : root.find src with
  | none => rfl
  | some snapshot => simp only [Option.bind_eq_bind, Option.bind_some, missing, Option.bind_none]

/-- The loop never changes an index beyond its runtime visit count. -/
theorem visit_frame {n extent : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (target initial : Fin extent → Slot G E) (count : Nat) (i : Fin extent)
    (outside : count ≤ i.val) : visit target count initial i = initial i := by
  rw [visit_prefix, if_neg (Nat.not_lt_of_ge outside)]

/-- Restarting a snapshot traversal extends its prefix, rather than reading
partially overwritten source data. -/
theorem visit_restart {n extent : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (target initial : Fin extent → Slot G E) (first second : Nat) :
    visit target second (visit target first initial) =
      visit target (max first second) initial := by
  funext i
  simp only [visit_prefix]
  by_cases a : i.val < first <;> by_cases b : i.val < second
  · simp only [if_pos a, if_pos b, if_pos (show i.val < max first second by omega)]
  · simp only [if_pos a, if_neg b, if_pos (show i.val < max first second by omega)]
  · simp only [if_neg a, if_pos b, if_pos (show i.val < max first second by omega)]
  · simp only [if_neg a, if_neg b, if_neg (show ¬ i.val < max first second by omega)]

theorem copyArray_length {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old src : Value G (.array E)) : (copyArray old src).length = src.length := by
  rw [copyArray_eq_overlay]
  exact Value.overlay_length old src

theorem copyArray_extent {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old src : Value G (.array E)) :
    (copyArray old src).extent.val = max old.extent.val src.length.val := by
  rw [copyArray_eq_overlay]
  exact Value.overlay_extent old src

/-- Clearing a mapping slot preserves its lookup meaning, including absent
slots. Explicit presence itself is intentionally not an observation. -/
theorem clear_mapping_slot {n : Nat} {G : Schema n} {K : PrimTy} {V : TypeGraph.Ty n}
    (old : Slot G (.mapping K V)) :
    old.clear.getD (Value.dflt _) = old.getD (Value.dflt _) := by
  cases old with
  | absent => rfl
  | present v => cases v; rfl

/-- Neither an absent source nor an explicit source replaces the destination
mapping. This is an internal operation law, not source assignment admission. -/
theorem overlay_mapping_slot {n : Nat} {G : Schema n} {K : PrimTy} {V : TypeGraph.Ty n}
    (old src : Slot G (.mapping K V)) :
    (old.overlay src).getD (Value.dflt _) = old.getD (Value.dflt _) := by
  cases src with
  | absent => exact clear_mapping_slot old
  | present v => exact Value.overlay_mapping _ v

/-- At every previously allocated mapping element, both copying and stale-tail
clearing preserve all keys, including keys below arbitrary recursive paths. -/
theorem copyArray_mapping_slot {n : Nat} {G : Schema n} {K : PrimTy} {V : TypeGraph.Ty n}
    (oe : Extent) (ol : Index) (oh : ol.val ≤ oe.val)
    (os : Fin oe.val → Slot G (.mapping K V))
    (ne : Extent) (nl : Index) (nh : nl.val ≤ ne.val)
    (ns : Fin ne.val → Slot G (.mapping K V)) (i : Fin oe.val) :
    ((copyArray (.array oe ol oh os) (.array ne nl nh ns)).slots
      ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_max_left _ _)⟩).getD (Value.dflt _) =
      (os i).getD (Value.dflt _) := by
  simp only [copyArray, traverse, Value.extent, Value.length, Value.slots, visit_prefix, oldSlot, dif_pos i.isLt]
  split
  · split
    · exact overlay_mapping_slot _ _
    · split
      · exact clear_mapping_slot _
      · rfl
  · rfl

end Solidity.Backend.StorageOps
