import Solidity.Backend.StorageOps.RecursiveClear

/-! Recursive graph operation traversal. Present source constructors drive
structural recursion; every dynamic array uses the runtime prefix loop.
The independent overlay semantics is used only in correspondence proofs. -/
namespace Solidity.Backend.StorageOps
open TypeGraph

/-- Type-level views generalize indices before eliminating an intrinsic value. -/
def NodeView {n : Nat} (G : Schema n) : TypeGraph.Ty n → Type
  | .node i => Fields G (G.fields i)
  | _ => PUnit
def nodeView {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (v : Value G T) : NodeView G T :=
  Value.casesOn (motive_1 := fun T _ => NodeView G T) v
    (fun _ => PUnit.unit) (fun fields => fields)
    (fun _ _ _ _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => PUnit.unit)
def FixedView {n : Nat} (G : Schema n) : TypeGraph.Ty n → Type
  | .fixed E m => Fin m.val → Slot G E
  | _ => PUnit
def fixedView {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (v : Value G T) : FixedView G T :=
  Value.casesOn (motive_1 := fun T _ => FixedView G T) v
    (fun _ => PUnit.unit) (fun _ => PUnit.unit)
    (fun _ _ _ _ => PUnit.unit) (fun slots => slots) (fun _ => PUnit.unit)

mutual
/-- Snapshot copy with generalized-index recursors, without rank/depth/fuel.
Function-valued fields/slots retain the intrinsic demand-driven execution model. -/
def recursiveCopy {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) : Value G T :=
  Value.casesOn (motive_1 := fun T _ => Value G T → Value G T) src
    (fun value _old => .prim value)
    (fun fields old => .node (fun p => recursiveCopy (nodeView old p) (fields p)))
    (fun ne nl nh ns old =>
      let oe := old.extent
      let ol := old.length
      let extent : Extent := ⟨max oe.val nl.val, by
        have ho := oe.isLt
        have hn := nl.isLt
        omega⟩
      let initial : Fin extent.val → Slot G _ := fun i => oldSlot oe old.slots i.val
      let target : Fin extent.val → Slot G _ := fun i =>
        if h : i.val < nl.val then
          recursiveSlot (initial i) (ns ⟨i.val, Nat.lt_of_lt_of_le h nh⟩)
        else if i.val < ol.val then recursiveClearSlot (initial i) else initial i
      .array extent nl (Nat.le_max_right _ _) (visit target (max ol.val nl.val) initial))
    (fun slots old => .fixed (fun i => recursiveSlot (fixedView old i) (slots i)))
    (fun _ old => old) old

/-- Absent source clears; present source recurses against existing/default data.
Slot elimination also generalizes its type index rather than casting it. -/
def recursiveSlot {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Slot G T) : Slot G T :=
  Slot.casesOn (motive_2 := fun T _ => Slot G T → Slot G T) src
    (fun old => recursiveClearSlot old)
    (fun value old => .present (recursiveCopy (old.getD (Value.dflt _)) value)) old
end

mutual
/-- Total constructor recursion and runtime loops realize independent overlay. -/
theorem recursiveCopy_eq_overlay {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (old src : Value G T) → recursiveCopy old src = old.overlay src
  | _, old, .prim _ => by cases old; rfl
  | _, .node old, .node src => by
    apply congrArg Value.node
    funext U p
    exact recursiveCopy_eq_overlay (old p) (src p)
  | _, .array oe ol oh os, .array ne nl nh ns => by
    unfold recursiveCopy Value.overlay
    dsimp only [Value.extent, Value.length, Value.slots]
    congr 1
    funext i
    rw [visit_prefix]
    by_cases visited : i.val < max ol.val nl.val
    · simp only [if_pos visited, oldSlot]
      split
      · exact recursiveSlot_eq_overlay _ _
      · simp only [recursiveClearSlot_eq_clear]
    · have a : ¬ i.val < nl.val := by omega
      have b : ¬ i.val < ol.val := by omega
      simp only [if_neg visited, dif_neg a, if_neg b, oldSlot]
  | _, .fixed old, .fixed src => by
    apply congrArg Value.fixed
    funext i
    exact recursiveSlot_eq_overlay (old i) (src i)
  | _, old, .mapping _ => by cases old; rfl

theorem recursiveSlot_eq_overlay {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (old src : Slot G T) → recursiveSlot old src = old.overlay src
  | _, old, .absent => recursiveClearSlot_eq_clear old
  | _, _old, .present src => congrArg Slot.present (recursiveCopy_eq_overlay _ src)
end

/-- Capture both reads from the unchanged root, before any destination save. -/
def recursiveCopyAt {n : Nat} {G : Schema n} {A T : TypeGraph.Ty n}
    (root : Value G A) (dst src : TypeGraph.Path G A T) : Option (Value G A) := do
  let snapshot ← root.find src
  let old ← root.find dst
  root.save dst (recursiveCopy old snapshot)

theorem recursiveCopyAt_eq_semantics {n : Nat} {G : Schema n} {A T : TypeGraph.Ty n}
    (root : Value G A) (dst src : TypeGraph.Path G A T) :
    recursiveCopyAt root dst src = root.copyAt dst src := by
  simp only [recursiveCopyAt, Value.copyAt, Value.write, recursiveCopy_eq_overlay]

/-- The actual array-level loop prefix: processed slots use the captured
recursive operation; unvisited slots remain exactly the destination snapshot.
At every recursive array invocation the count runs to max old/new live length. -/
theorem recursive_prefix {n extent : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (initial source : Fin extent → Slot G E) (live oldLive count : Nat)
    (i : Fin extent) :
    visit (fun j => if j.val < live then recursiveSlot (initial j) (source j)
      else if j.val < oldLive then (initial j).clear else initial j) count initial i =
    if i.val < count then
      (if i.val < live then recursiveSlot (initial i) (source i)
       else if i.val < oldLive then (initial i).clear else initial i)
    else initial i := visit_prefix _ _ _ _

theorem recursiveCopyAt_readback {n : Nat} {G : Schema n} {A T : TypeGraph.Ty n}
    (root result : Value G A) (dst src : TypeGraph.Path G A T)
    (old snapshot : Value G T) (rd : root.find dst = some old)
    (rs : root.find src = some snapshot)
    (copied : recursiveCopyAt root dst src = some result) :
    result.find dst = some (recursiveCopy old snapshot) := by
  rw [recursiveCopyAt_eq_semantics] at copied
  rw [recursiveCopy_eq_overlay]
  exact root.find_copyAt result dst src old snapshot rd rs copied

theorem recursiveCopyAt_missing_source {n : Nat} {G : Schema n} {A T : TypeGraph.Ty n}
    (root : Value G A) (dst src : TypeGraph.Path G A T)
    (missing : root.find src = none) : recursiveCopyAt root dst src = none := by
  unfold recursiveCopyAt
  rw [missing]
  rfl

theorem recursiveCopyAt_missing_destination {n : Nat} {G : Schema n} {A T : TypeGraph.Ty n}
    (root : Value G A) (dst src : TypeGraph.Path G A T)
    (missing : root.find dst = none) : recursiveCopyAt root dst src = none := by
  unfold recursiveCopyAt
  cases readSrc : root.find src with
  | none => rfl
  | some snapshot => simp only [Option.bind_eq_bind, Option.bind_some, missing, Option.bind_none]

theorem recursiveCopy_mapping_read {n : Nat} {G : Schema n} {A : TypeGraph.Ty n}
    {K : PrimTy} {V : TypeGraph.Ty n} (old src : Value G A)
    (path : TypeGraph.Path G A (.mapping K V)) (value : Value G (.mapping K V))
    (read : old.find path = some value) : (recursiveCopy old src).find path = some value := by
  rw [recursiveCopy_eq_overlay]
  exact overlay_mapping_read old src path value read

theorem recursiveCopy_tail {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (oe : Extent) (ol : Index) (oh : ol.val ≤ oe.val) (os : Fin oe.val → Slot G E)
    (ne : Extent) (nl : Index) (nh : nl.val ≤ ne.val) (ns : Fin ne.val → Slot G E)
    (i : Index) (allocated : i.val < oe.val)
    (oldShadow : ol.val ≤ i.val) (newShadow : nl.val ≤ i.val) :
    (recursiveCopy (.array oe ol oh os) (.array ne nl nh ns)).slots
      ⟨i.val, Nat.lt_of_lt_of_le allocated (Nat.le_max_left _ _)⟩ = os ⟨i.val, allocated⟩ := by
  simp only [recursiveCopy, Value.slots, Value.extent, Value.length, visit_prefix,
    if_neg (show ¬ i.val < max ol.val nl.val by omega), oldSlot, dif_pos allocated]

theorem recursiveCopy_shortened {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (oe : Extent) (ol : Index) (oh : ol.val ≤ oe.val) (os : Fin oe.val → Slot G E)
    (ne : Extent) (nl : Index) (nh : nl.val ≤ ne.val) (ns : Fin ne.val → Slot G E)
    (i : Index) (live : i.val < ol.val) (newShadow : nl.val ≤ i.val) :
    (recursiveCopy (.array oe ol oh os) (.array ne nl nh ns)).slots
      ⟨i.val, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le live oh) (Nat.le_max_left _ _)⟩ =
      (os ⟨i.val, Nat.lt_of_lt_of_le live oh⟩).clear := by
  simp only [recursiveCopy, Value.slots, Value.extent, Value.length, visit_prefix,
    if_pos (show i.val < max ol.val nl.val by omega),
    dif_neg (Nat.not_lt_of_ge newShadow), if_pos live, oldSlot,
    dif_pos (Nat.lt_of_lt_of_le live oh), recursiveClearSlot_eq_clear]

/-- info: 'Solidity.Backend.StorageOps.NodeView' does not depend on any axioms -/
#guard_msgs in #print axioms NodeView
/-- info: 'Solidity.Backend.StorageOps.nodeView' does not depend on any axioms -/
#guard_msgs in #print axioms nodeView
/-- info: 'Solidity.Backend.StorageOps.FixedView' does not depend on any axioms -/
#guard_msgs in #print axioms FixedView
/-- info: 'Solidity.Backend.StorageOps.fixedView' does not depend on any axioms -/
#guard_msgs in #print axioms fixedView

end Solidity.Backend.StorageOps
