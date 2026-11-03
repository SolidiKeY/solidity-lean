import Solidity.Backend.StorageOps.RecursiveCopy

/-! Partial execution of the very same array loop used by recursiveCopy.
Only slots are exposed: no prematurely updated header or world is claimed. -/
namespace Solidity.Backend.StorageOps
open TypeGraph

/-- Captured recursive array target; no source reads from partially updated slots. -/
def recursiveArrayTarget {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (oe : Extent) (ol : Index) (os : Fin oe.val → Slot G E)
    (ne : Extent) (nl : Index) (nh : nl.val ≤ ne.val) (ns : Fin ne.val → Slot G E)
    (i : Fin (max oe.val nl.val)) : Slot G E :=
  let initial := oldSlot oe os i.val
  if h : i.val < nl.val then
    recursiveSlot initial (ns ⟨i.val, Nat.lt_of_lt_of_le h nh⟩)
  else if i.val < ol.val then recursiveClearSlot initial else initial

/-- A finite prefix of actual recursive operation steps, parameterized by the
runtime progress count. This is not a new graph state or source evaluator. -/
def recursiveArrayPrefix {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (oe : Extent) (ol : Index) (os : Fin oe.val → Slot G E)
    (ne : Extent) (nl : Index) (nh : nl.val ≤ ne.val) (ns : Fin ne.val → Slot G E)
    (count : Nat) : Fin (max oe.val nl.val) → Slot G E :=
  visit (recursiveArrayTarget oe ol os ne nl nh ns) count (fun i => oldSlot oe os i.val)

theorem recursiveArrayPrefix_progress {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (oe : Extent) (ol : Index) (os : Fin oe.val → Slot G E)
    (ne : Extent) (nl : Index) (nh : nl.val ≤ ne.val) (ns : Fin ne.val → Slot G E)
    (count : Nat) (i : Fin (max oe.val nl.val)) :
    recursiveArrayPrefix oe ol os ne nl nh ns count i =
      if i.val < count then recursiveArrayTarget oe ol os ne nl nh ns i
      else oldSlot oe os i.val := visit_prefix _ _ _ _

/-- Completion is definitionally the slots of the independently implemented
recursive copy, with its runtime max(old live,new live) bound. -/
theorem recursiveArrayPrefix_complete {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (oe : Extent) (ol : Index) (oh : ol.val ≤ oe.val) (os : Fin oe.val → Slot G E)
    (ne : Extent) (nl : Index) (nh : nl.val ≤ ne.val) (ns : Fin ne.val → Slot G E) :
    (recursiveCopy (.array oe ol oh os) (.array ne nl nh ns)).slots =
      recursiveArrayPrefix oe ol os ne nl nh ns (max ol.val nl.val) := rfl

/-- An unfinished array-level traversal preserves every unvisited old slot. -/
theorem recursiveArrayPrefix_unvisited {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (oe : Extent) (ol : Index) (os : Fin oe.val → Slot G E)
    (ne : Extent) (nl : Index) (nh : nl.val ≤ ne.val) (ns : Fin ne.val → Slot G E)
    (count : Nat) (i : Fin (max oe.val nl.val)) (outside : count ≤ i.val) :
    recursiveArrayPrefix oe ol os ne nl nh ns count i = oldSlot oe os i.val :=
  visit_frame _ _ _ _ outside

/-- Continuing a captured array loop never switches to mutated source reads. -/
theorem recursiveArrayPrefix_restart {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (oe : Extent) (ol : Index) (os : Fin oe.val → Slot G E)
    (ne : Extent) (nl : Index) (nh : nl.val ≤ ne.val) (ns : Fin ne.val → Slot G E)
    (first second : Nat) :
    visit (recursiveArrayTarget oe ol os ne nl nh ns) second
      (recursiveArrayPrefix oe ol os ne nl nh ns first) =
      recursiveArrayPrefix oe ol os ne nl nh ns (max first second) :=
  visit_restart _ _ _ _

/-- info: 'Solidity.Backend.StorageOps.recursiveArrayPrefix_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursiveArrayPrefix_complete
/-- info: 'Solidity.Backend.StorageOps.recursiveArrayPrefix_progress' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursiveArrayPrefix_progress
/-- info: 'Solidity.Backend.StorageOps.recursiveArrayPrefix_unvisited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursiveArrayPrefix_unvisited
/-- info: 'Solidity.Backend.StorageOps.recursiveArrayPrefix_restart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursiveArrayPrefix_restart
end Solidity.Backend.StorageOps
