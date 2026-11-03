import Solidity.Backend.StorageOps.Traversal
import Solidity.Backend.StorageOps.Lifecycle
import Solidity.Backend.StorageOps.Touched

/-! Inhabited, negative and combination controls for the V10 operation layer.
All are kernel proofs over published intrinsic values. These are not external
solc/EVM tests or claims of ordinary recursive-source admission. -/

namespace Solidity.Backend.StorageOps.Controls

open TypeGraph

private def z : Fin 1 := ⟨0, by decide⟩
private def fields : List (Name × TypeGraph.Ty 1) :=
  [("flag", .prim .bool), ("children", .array (.node z))]
private def graph : Schema 1 where
  origin := "v10-operation-controls"
  declId := fun _ => 0
  declId_injective := by intro i j _; apply Fin.ext; omega
  name := fun _ => "Node"
  fields := fun _ => fields
  rank := fun _ => 1
  nonempty := fun _ => rfl
  distinct := fun _ => rfl
  guarded := by
    intro i f hf
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> exact Nat.zero_lt_succ 0

private def i0 : Index := ⟨0, by decide⟩
private def i1 : Index := ⟨1, by decide⟩
private def i2 : Index := ⟨2, by decide⟩
private abbrev Nodes := Value graph (.array (.node z))
private abbrev Node := Value graph (.node z)
private def empty : Nodes := Value.dflt _
private def node (flag : Bool) (children : Nodes := empty) : Node :=
  .node (fun p => match p with
    | .here => .prim flag
    | .there .here => children
    | .there (.there q) => nomatch q)
private def one (v : Node) : Nodes :=
  .array ⟨1, by decide⟩ ⟨1, by decide⟩ (by decide) (fun _ => .present v)
private def flagAt (i : Index) : TypeGraph.Path graph (.array (.node z)) (.prim .bool) :=
  .cons (.index i) (.cons (.field .here) .nil)
private def childrenAt (i : Index) : TypeGraph.Path graph
    (.array (.node z)) (.array (.node z)) :=
  .cons (.index i) (.cons (.field (.there .here)) .nil)
private def old : Nodes :=
  .array ⟨3, by decide⟩ ⟨2, by decide⟩ (by decide)
    (fun _ => .present (node true (one (node true))))
private def src : Nodes := one (node false)

/-- Nonempty runtime copy transfers a live scalar. -/
theorem copies_live : (copyArray old src).observe (flagAt i0) = some false := rfl
/-- A former live element is cleared at a retained alias. -/
theorem clears_shortened : (copyArray old src).observe (flagAt i1) = some false := rfl
/-- Clearing recursively shortens the removed element's nested array. -/
theorem clears_nested : ((copyArray old src).find (childrenAt i1)).map Value.length =
    some i0 := rfl
/-- An older destination shadow remains, so clearing the entire extent would
be a semantic bug. -/
theorem keeps_old_shadow : (copyArray old src).observe (flagAt i2) = some true := rfl
/-- A retained path and a live path deliberately disagree after shrinking. -/
theorem rejects_live_tail : (flagAt i1).readLive Value.dflt (copyArray old src) = none := rfl
/-- A retained aggregate alias becomes live on regrow and keeps its identity. -/
theorem regrows_shadow : ((copyArray old src).push.bind Value.push).bind
    (fun v => (flagAt i2).readLive Value.dflt v) = some (.prim true) := rfl

private def overlap : Nodes := one (node true (one (node false)))
/-- The source is inside the destination. Reading it after overwriting the
ancestor would lose the captured child. -/
theorem overlap_snapshot : (copyAt overlap .nil (childrenAt i0)).map
    (fun v => v.observe (flagAt i0)) = some (some false) := rfl
/-- A nested out-of-extent source fails instead of silently copying a default. -/
theorem nested_source_failure : copyAt overlap .nil (childrenAt i1) = none := rfl
/-- A valid source and invalid nested destination fail with no returned root. -/
theorem nested_destination_failure : copyAt overlap (childrenAt i1) .nil = none := rfl

private def mapSlot : Slot graph (.mapping .bool (.prim .bool)) :=
  .present (.mapping (fun k => if k = true then .present (.prim true) else .absent))
private def mappings : Value graph (.array (.mapping .bool (.prim .bool))) :=
  .array ⟨2, by decide⟩ ⟨2, by decide⟩ (by decide) (fun _ => mapSlot)
private def mappingLeaf : TypeGraph.Path graph
    (.array (.mapping .bool (.prim .bool))) (.prim .bool) :=
  .cons (.index i1) (.cons (.key true) .nil)
/-- Copy clear-tail plus a dangling path keeps a mapping key. This is the
internal copy meaning; whole mapping-containing assignments need admission. -/
theorem mapping_tail_survives :
    (copyArray mappings (Value.dflt _)).observe mappingLeaf = some true := rfl

private def full : Value graph (.array (.array (.node z))) :=
  .array ⟨2 ^ 256 - 1, by decide⟩ ⟨2 ^ 256 - 1, by decide⟩ (by decide)
    (fun _ => .absent)
/-- Allocation failure is inhabited for nested aggregate elements. -/
theorem nested_capacity_failure : full.push = none := by
  apply (push_fails_iff full).2
  change 2 ^ 256 ≤ (2 ^ 256 - 1) + 1
  decide
/-- Empty pop fails rather than returning an arbitrary storage value. -/
theorem empty_pop_failure : empty.pop = none := rfl

/-- Arbitrary recursive path depth is supported by the intrinsic read-back
law; depth is a theorem parameter, never a new admission cap. -/
private def deep : Nat → TypeGraph.Path graph (.array (.node z)) (.prim .bool)
  | 0 => flagAt i0
  | d + 1 => (childrenAt i0).append (deep d)

private def tree : Nat → Nodes
  | 0 => one (node true)
  | d + 1 => one (node false (tree d))

theorem recursive_read_witness (depth : Nat) :
    ∃ root : Nodes, root.find (deep depth) = some (.prim true) := by
  refine ⟨tree depth, ?_⟩
  induction depth with
  | zero => rfl
  | succ depth ih =>
    change (tree depth).find (deep depth) = some (.prim true)
    exact ih

/-- Inhabited per-run regions for genuinely nested data/hash addresses. -/
private def hash : Solidity.Storage.Pre → Nat
  | .data 0 => 32
  | .entry 7 32 => 64
  | _ => 128
private def preimages : List Solidity.Storage.Pre := [.data 0, .entry 7 32]
private def base : Solidity.Storage.Loc := .hash 7 (.data (.root 0) 0) 0
private theorem regions : Solidity.Hash.RegionsDisjoint 256 4 hash (List.range 2) preimages :=
  by decide
/-- Transport is applied with nonempty nested hashed accesses, not vacuous
empty touched sets or an inconsistent global hash premise. -/
theorem nested_touched_transport :
    (base.add 1).word 256 hash ∈ (touched base 1 2).map (Solidity.Storage.Loc.word 256 hash) := by
  apply (touched_word_iff (N := 256) (L := 4) (R := 2) (P := preimages)
    (by intro p; cases p <;> simp only [hash] <;> split <;> decide)
    (by decide) (by decide) regions base (base.add 1) 1 2
    (by
      intro l member
      change l ∈ [base.add 0, base.add 1] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;>
        change (0 < 2 ∧ 0 < 4) ∧ _ < 4 <;> decide)
    (by decide)
    (by change (0 < 2 ∧ 0 < 4) ∧ 1 < 4; decide)
    (by decide)).2
  decide

private theorem hash_lt (p : Solidity.Storage.Pre) : hash p < 256 := by
  cases p <;> simp only [hash] <;> split <;> decide

private theorem touched_bounds : ∀ l ∈ touched base 1 2,
    Solidity.Storage.Loc.Bounded 4 2 l := by
  intro l member
  change l ∈ [base.add 0, base.add 1] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    change (0 < 2 ∧ 0 < 4) ∧ _ < 4 <;> decide

/-- Exercise the region-dependent reflection direction with a populated,
nested hashed run. -/
theorem nested_touched_reflection : base.add 1 ∈ touched base 1 2 :=
  (touched_word_iff hash_lt (by decide) (by decide) regions base (base.add 1) 1 2
    touched_bounds (by decide)
    (by change (0 < 2 ∧ 0 < 4) ∧ 1 < 4; decide) (by decide)).1 (by decide)

/-- A bounded adjacent query is outside the operation's numeric touched set;
reflection is essential to this proof. -/
theorem nested_untouched_word : (base.add 2).word 256 hash ∉
    (touched base 1 2).map (Solidity.Storage.Loc.word 256 hash) := by
  intro belongs
  have symbolic := (touched_word_iff hash_lt (by decide) (by decide) regions
    base (base.add 2) 1 2 touched_bounds (by decide)
    (by change (0 < 2 ∧ 0 < 4) ∧ 2 < 4; decide) (by decide)).1 belongs
  exact (by decide : base.add 2 ∉ touched base 1 2) symbolic

/-- Nonempty independent generated accesses carry distinct typed values;
all region/bounds/preimage premises of numeric write commutation are inhabited. -/
theorem numeric_generated_commutation :
    Slots.write (Slots.write (fun _ : Nat => (Slot.absent : Slot graph (.prim .bool)))
      ((base.add 0).word 256 hash) (.prim true))
      (((base.add 1).add 0).word 256 hash) (.prim false) =
    Slots.write (Slots.write (fun _ : Nat => (Slot.absent : Slot graph (.prim .bool)))
      (((base.add 1).add 0).word 256 hash) (.prim false))
      ((base.add 0).word 256 hash) (.prim true) :=
  generated_writes_commute hash_lt (by decide) (by decide) regions
    base (base.add 1) 1 1 1 1
    (by
      intro l member
      have equal : l = base.add 0 := List.mem_singleton.mp member
      subst l
      change (0 < 2 ∧ 0 < 4) ∧ 0 < 4
      decide)
    (by
      intro l member
      have equal : l = (base.add 1).add 0 := List.mem_singleton.mp member
      subst l
      change (0 < 2 ∧ 0 < 4) ∧ 1 < 4
      decide)
    (by decide) (by decide) (by decide)
    (base.add 0) ((base.add 1).add 0) (by decide) (by decide)
    (fun _ : Nat => (.absent : Slot graph (.prim .bool))) (.prim true) (.prim false)

/-- A zero stride really repeats addresses; nodup is not an unconditional
consequence of merely enumerating a finite operation count. -/
theorem zero_stride_duplicates : ¬ (touched base 0 2).Nodup := by decide

/-- The approved premise is inhabited even though this hash is globally
noninjective. -/
theorem hash_not_globally_injective :
    hash (.data 1) = hash (.data 2) ∧
      (Solidity.Storage.Pre.data 1) ≠ .data 2 := by
  constructor
  · rfl
  · decide

/-- Without the existing bounded-offset condition, even this run's data
preimage yields two distinct aliases to one numeric word. -/
theorem unbounded_offset_alias :
    (Solidity.Storage.Loc.data (.root 0) 0) ≠ .data (.root 0) 256 ∧
      (Solidity.Storage.Loc.data (.root 0) 0).word 256 hash =
        (Solidity.Storage.Loc.data (.root 0) 256).word 256 hash :=
  Solidity.Storage.Loc.word_data_alias 256 hash (.root 0) (by decide)

/-- Two retained (currently nonlive) aliases still obey operation commutation. -/
theorem retained_writes_commute :
    ((TypeGraph.Step.index i0).put (copyArray old empty) (node false)).bind
      (fun v => (TypeGraph.Step.index i1).put v (node true)) =
    ((TypeGraph.Step.index i1).put (copyArray old empty) (node true)).bind
      (fun v => (TypeGraph.Step.index i0).put v (node false)) :=
  array_puts_commute _ i0 (by decide) _ i0 i1 (by decide) (by decide)
    (by decide) (node false) (node true)

/-- info: 'Solidity.Backend.StorageOps.traverse_eq_overlay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms traverse_eq_overlay
/-- info: 'Solidity.Backend.StorageOps.copyAt_readback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms copyAt_readback
/-- info: 'Solidity.Backend.StorageOps.copyArray_mapping_slot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms copyArray_mapping_slot
/-- info: 'Solidity.Backend.StorageOps.generated_writes_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms generated_writes_commute
/-- info: 'Solidity.Backend.StorageOps.push_fresh_default' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms push_fresh_default
/-- info: 'Solidity.Backend.StorageOps.Controls.recursive_read_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursive_read_witness

end Solidity.Backend.StorageOps.Controls
