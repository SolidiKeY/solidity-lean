import Solidity.Semantics.RecursiveStorage.Arrays

/-!
Storage-to-storage snapshot copying over a guarded graph. Recursion follows
present source values, not declaration rank. Missing source slots mean copying
a synthesized default, implemented by clearing the destination slot; this
preserves destination mappings without recursively allocating defaults.

This is the internal copy operation, not a source-admission decision. Solidity
rejects whole assignments of types containing mappings, even though the storage
operation has a meaning at those types.
-/

namespace Solidity.TypeGraph

mutual
/-- Copy the source's live contents over the destination. Source shadows are
ignored; shortened destination live slots are cleared; older shadows survive. -/
def Value.overlay {n : Nat} {G : Schema n} :
    {T : Ty n} → Value G T → Value G T → Value G T
  | _, _, .prim v => .prim v
  | _, .node old, .node src => .node (fun p => Value.overlay (old p) (src p))
  | _, .array oe ol _ os, .array ne nl nh ns =>
    .array ⟨max oe.val nl.val, by
        have ho := oe.isLt
        have hn := nl.isLt
        omega⟩ nl (Nat.le_max_right _ _)
      (fun i =>
        let old := if h : i.val < oe.val then os ⟨i.val, h⟩ else .absent
        if h : i.val < nl.val then
          Slot.overlay old (ns ⟨i.val, Nat.lt_of_lt_of_le h nh⟩)
        else if i.val < ol.val then old.clear else old)
  | _, .fixed old, .fixed src => .fixed (fun i => Slot.overlay (old i) (src i))
  | _, old, .mapping _ => old

/-- An implicit default clears old contents; an explicit source is copied
against the existing destination, or against its default if unallocated. -/
def Slot.overlay {n : Nat} {G : Schema n} :
    {T : Ty n} → Slot G T → Slot G T → Slot G T
  | _, old, .absent => old.clear
  | _, old, .present src => .present (Value.overlay (old.getD (Value.dflt _)) src)
end

/-- Extensional equality of array constructors without heterogeneous function
congruence goals. Equal extents identify the domains before comparing slots. -/
private theorem array_eq_of_slots {n : Nat} {G : Schema n} {E : Ty n}
    (left right : Extent) (length : Index)
    (leftBound : length.val ≤ left.val) (rightBound : length.val ≤ right.val)
    (leftSlots : Fin left.val → Slot G E) (rightSlots : Fin right.val → Slot G E)
    (extentEq : left.val = right.val)
    (slotsEq : ∀ (i : Fin left.val) (j : Fin right.val),
      i.val = j.val → leftSlots i = rightSlots j) :
    Value.array left length leftBound leftSlots =
      Value.array right length rightBound rightSlots := by
  have equality : left = right := Fin.ext extentEq
  cases equality
  have slots : leftSlots = rightSlots := funext fun i => slotsEq i i rfl
  cases slots
  rfl

/-- Copying a synthesized default clears the old value, including mapping
barriers and retained array histories. The rank is used only for default
construction, never as a recursion bound on stored recursive data. -/
theorem Value.overlay_defaultBelow {n : Nat} {G : Schema n} (fuel : Nat) :
    (T : Ty n) → (h : T.inlineRank G.rank < fuel) → (old : Value G T) →
    old.overlay (Value.defaultBelow fuel T h) = old.clear := by
  induction fuel with
  | zero => intro T h; exact False.elim ((Nat.not_lt_zero _) h)
  | succ fuel ih =>
    intro T h old
    cases T with
    | prim p => cases old; rfl
    | node i =>
      cases old with
      | node fields =>
        apply congrArg Value.node
        funext U position
        exact ih U _ (fields position)
    | array E =>
      cases old with
      | array extent length le slots =>
        simp only [Value.defaultBelow, Value.overlay, Value.clear, Nat.max_zero,
          dif_neg (Nat.not_lt_zero _)]
        apply array_eq_of_slots
        · exact Nat.max_zero _
        · intro i j equal
          have inside : i.val < extent.val := by
            rw [equal]
            exact j.isLt
          have sameIndex : (⟨i.val, inside⟩ : Fin extent.val) = j := Fin.ext equal
          simp only [dif_pos inside]
          rw [sameIndex, equal]
    | fixed E size => cases old; rfl
    | mapping K V => cases old; rfl

theorem Value.overlay_dflt {n : Nat} {G : Schema n} {T : Ty n} (old : Value G T) :
    old.overlay (Value.dflt T) = old.clear :=
  Value.overlay_defaultBelow _ T _ old

/-- A detached source snapshot, with no source shadow history or mappings. -/
def Value.strip {n : Nat} {G : Schema n} {T : Ty n} (src : Value G T) : Value G T :=
  (Value.dflt T).overlay src

/-- Storage assignment at a typed destination. The caller has already captured
its source; reads and writes use retained bounds, as storage aliases do. -/
def Value.write {n : Nat} {G : Schema n} {A T : Ty n}
    (root : Value G A) (dst : Path G A T) (src : Value G T) : Option (Value G A) := do
  let old ← root.find dst
  root.save dst (old.overlay src)

/-- Capture the source before modifying the destination, including when the
two paths overlap. Source admission must separately check copy legality. -/
def Value.copyAt {n : Nat} {G : Schema n} {A T : Ty n}
    (root : Value G A) (dst src : Path G A T) : Option (Value G A) := do
  let snapshot ← root.find src
  root.write dst snapshot

@[simp] theorem Value.overlay_prim {n : Nat} {G : Schema n} {p : PrimTy}
    (old : Value G (.prim p)) (src : p.Denote) :
    old.overlay (.prim src) = .prim src := by
  cases old
  rfl

/-- Internal copying never replaces a destination mapping. -/
theorem Value.overlay_mapping {n : Nat} {G : Schema n} {K : PrimTy} {V : Ty n}
    (old src : Value G (.mapping K V)) : old.overlay src = old := by
  cases old
  cases src
  rfl

theorem Slot.overlay_absent {n : Nat} {G : Schema n} {T : Ty n}
    (old : Slot G T) : old.overlay .absent = old.clear := rfl

theorem Value.overlay_length {n : Nat} {G : Schema n} {E : Ty n}
    (old src : Value G (.array E)) : (old.overlay src).length = src.length := by
  cases old
  cases src
  rfl

theorem Value.overlay_extent {n : Nat} {G : Schema n} {E : Ty n}
    (old src : Value G (.array E)) :
    (old.overlay src).extent.val = max old.extent.val src.length.val := by
  cases old
  cases src
  rfl

/-- Older shadows survive a copy whenever the source does not make them live. -/
theorem Value.overlay_tail {n : Nat} {G : Schema n} {E : Ty n}
    (oe : Extent) (ol : Index) (oh : ol.val ≤ oe.val) (os : Fin oe.val → Slot G E)
    (ne : Extent) (nl : Index) (nh : nl.val ≤ ne.val) (ns : Fin ne.val → Slot G E)
    (i : Index) (allocated : i.val < oe.val)
    (oldShadow : ol.val ≤ i.val) (newShadow : nl.val ≤ i.val) :
    ((Value.array oe ol oh os).overlay (.array ne nl nh ns)).slots
        ⟨i.val, Nat.lt_of_lt_of_le allocated (Nat.le_max_left _ _)⟩ =
      os ⟨i.val, allocated⟩ := by
  simp only [Value.overlay, Value.slots, dif_neg (Nat.not_lt_of_ge newShadow),
    if_neg (Nat.not_lt_of_ge oldShadow), dif_pos allocated]

/-- A former live destination slot beyond the new end is cleared. -/
theorem Value.overlay_shortened {n : Nat} {G : Schema n} {E : Ty n}
    (oe : Extent) (ol : Index) (oh : ol.val ≤ oe.val) (os : Fin oe.val → Slot G E)
    (ne : Extent) (nl : Index) (nh : nl.val ≤ ne.val) (ns : Fin ne.val → Slot G E)
    (i : Index) (live : i.val < ol.val) (newShadow : nl.val ≤ i.val) :
    ((Value.array oe ol oh os).overlay (.array ne nl nh ns)).slots
        ⟨i.val, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le live oh) (Nat.le_max_left _ _)⟩ =
      (os ⟨i.val, Nat.lt_of_lt_of_le live oh⟩).clear := by
  simp only [Value.overlay, Value.slots, dif_neg (Nat.not_lt_of_ge newShadow),
    if_pos live, dif_pos (Nat.lt_of_lt_of_le live oh)]

/-- Read-back of assignment is the copy result, not necessarily the raw source
(which may have different mapping contents or shadow histories). -/
theorem Value.find_write {n : Nat} {G : Schema n} {A T : Ty n}
    (root result : Value G A) (dst : Path G A T) (src old : Value G T)
    (read : root.find dst = some old) (written : root.write dst src = some result) :
    result.find dst = some (old.overlay src) := by
  simp only [Value.write, read, Option.bind_some] at written
  exact root.find_save result dst (old.overlay src) written

theorem Value.find_copyAt {n : Nat} {G : Schema n} {A T : Ty n}
    (root result : Value G A) (dst src : Path G A T) (old snapshot : Value G T)
    (readDst : root.find dst = some old) (readSrc : root.find src = some snapshot)
    (copied : root.copyAt dst src = some result) :
    result.find dst = some (old.overlay snapshot) := by
  simp only [Value.copyAt, readSrc, Option.bind_some] at copied
  exact root.find_write result dst snapshot old readDst copied

end Solidity.TypeGraph
