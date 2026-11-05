import Solidity.Backend.StorageOps.IndexedOperations

/-! Checked dynamic/fixed sibling suffix controls. Logical retained extent and
live length remain distinct; Option failure is not external world rollback. -/
namespace Solidity.Backend.StorageOps.IndexedControls
open TypeGraph
private def z : Fin 1 := ⟨0, by decide⟩
private def fs : List (Name × TypeGraph.Ty 1) := [("flag", .prim .bool), ("children", .array (.node z))]
private def graph : Schema 1 where
  origin := "v10-indexed-operation-controls"
  declId := fun _ => 0
  declId_injective := by intro i j _; apply Fin.ext; omega
  name := fun _ => "Node"
  fields := fun _ => fs
  rank := fun _ => 1
  nonempty := fun _ => rfl
  distinct := fun _ => rfl
  guarded := by
    intro i f hf
    simp only [fs, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> exact Nat.zero_lt_succ 0
private def zero : Index := ⟨0, by decide⟩
private def oneIndex : Index := ⟨1, by decide⟩
private def twoIndex : Index := ⟨2, by decide⟩
private def extent : Extent := ⟨2, by decide⟩
private def size : FixedSize := ⟨2, by decide⟩
private abbrev Nodes := Value graph (.array (.node z))
private abbrev Root := Value graph (.mapping .bool (.array (.node z)))
private def node (flag : Bool) (children : Nodes := Value.dflt _) : Value graph (.node z) :=
  .node (fun p => match p with
    | .here => .prim flag
    | .there .here => children
    | .there (.there q) => nomatch q)
private def one (v : Value graph (.node z)) : Nodes :=
  .array ⟨1, by decide⟩ oneIndex (by decide) (fun _ => .present v)
private def tree : Nat → Nodes
  | 0 => one (node true)
  | d + 1 => one (node true (tree d))
private def deepFlag : Nat → TypeGraph.Path graph (.array (.node z)) (.prim .bool)
  | 0 => .cons (.index zero) (.cons (.field .here) .nil)
  | d + 1 => .cons (.index zero) (.cons (.field (.there .here)) (deepFlag d))
private def suffix (d : Nat) : TypeGraph.Path graph (.node z) (.prim .bool) :=
  .cons (.field (.there .here)) (deepFlag d)
private def reset : Value graph (.prim .bool) → Option (Value graph (.prim .bool)) := fun _ => some (.prim false)
private def setTrue : Value graph (.prim .bool) → Option (Value graph (.prim .bool)) := fun _ => some (.prim true)
private def slots (d : Nat) (_ : Fin extent.val) : Slot graph (.node z) := .present (node true (tree d))
private def array (d : Nat) : Nodes := .array extent oneIndex (by decide) (slots d)
private def outerSlots (d : Nat) (key : PrimTy.bool.Denote) : Slot graph (.array (.node z)) :=
  .present (if key = true then array d else tree 0)
private def root (d : Nat) : Root := .mapping (outerSlots d)
private def pre : TypeGraph.Path graph (.mapping .bool (.array (.node z))) (.array (.node z)) :=
  .cons (.key true) .nil
private def left (d : Nat) := pre.append (.cons (.index zero) (suffix d))
private def right (d : Nat) := pre.append (.cons (.index oneIndex) (suffix d))
private def outside : TypeGraph.Path graph (.mapping .bool (.array (.node z))) (.prim .bool) :=
  .cons (.key false) (deepFlag 0)
private theorem tree_read (d : Nat) : (tree d).find (deepFlag d) = some (.prim true) := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih
private theorem child_update (d : Nat) : ∃ result,
    modifyAt (node true (tree d)) (suffix d) reset = some result ∧
    result.find (suffix d) = some (.prim false) := by
  have read : (node true (tree d)).find (suffix d) = some (.prim true) := tree_read d
  obtain ⟨result, saved⟩ := prefix_save_exists (suffix d) (node true (tree d)) (.prim true) (.prim false) read
  refine ⟨result, ?_, Value.find_save _ _ _ _ saved⟩
  simp only [modifyAt, read, reset, Option.bind_eq_bind, Option.bind_some]
  exact saved

theorem sibling_commutation (d : Nat) :
    (modifyAt (root d) (left d) reset).bind (fun next => modifyAt next (right d) reset) =
    (modifyAt (root d) (right d) reset).bind (fun next => modifyAt next (left d) reset) :=
  common_prefix_array_commute (root d) pre zero oneIndex (by decide) (suffix d) (suffix d) reset reset

theorem both_initially_true (d : Nat) : (root d).find (left d) = some (.prim true) ∧
    (root d).find (right d) = some (.prim true) := ⟨tree_read d, tree_read d⟩

/-- Every finite depth changes BOTH actual sibling observations, including a
retained sibling. Its live read remains absent; outside-prefix read stays true. -/
theorem sibling_success_all_depth (d : Nat) : ∃ result,
    (modifyAt (root d) (left d) reset).bind (fun next => modifyAt next (right d) reset) = some result ∧
    result.find (left d) = some (.prim false) ∧ result.find (right d) = some (.prim false) ∧
    (right d).readLive Value.dflt result = none ∧ result.find outside = some (.prim true) := by
  obtain ⟨changed, effectOK, readback⟩ := child_update d
  let a : Fin extent.val := ⟨0, by decide⟩
  let b : Fin extent.val := ⟨1, by decide⟩
  let updated : Nodes := .array extent oneIndex (by decide) (Slots.write (Slots.write (slots d) a changed) b changed)
  have childSequence :
      (modifyAt (array d) (.cons (.index zero) (suffix d)) reset).bind
        (fun next => modifyAt next (.cons (.index oneIndex) (suffix d)) reset) = some updated := by
    simp only [array, modifyAt_array_suffix, zero, oneIndex, extent, Nat.zero_lt_succ,
      Nat.lt_succ_self, dif_pos, modifySlot, slots, Slot.getD, effectOK,
      Option.map_some, Option.bind_some]
    simp only [Slots.write, Fin.mk.injEq, reduceCtorEq, if_false, slots, effectOK, Option.map_some]
    rfl
  let result : Root := .mapping (Slots.write (outerSlots d) true updated)
  refine ⟨result, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [left, right, modifyAt_append, modifyAt_sequence]
    change modifyAt (root d) pre
      (fun old => (modifyAt old (.cons (.index zero) (suffix d)) reset).bind
        (fun next => modifyAt next (.cons (.index oneIndex) (suffix d)) reset)) = some result
    simp only [root, pre, modifyAt_mapping, modifySlot, outerSlots, ite_true,
      Slot.getD, childSequence, Option.map_some]
    rfl
  · change (((Slots.write (Slots.write (slots d) a changed) b changed) a).getD (Value.dflt _)).find (suffix d) = some (.prim false)
    rw [Slots.write_other _ b a (by decide), Slots.write_self]
    exact readback
  · change changed.find (suffix d) = some (.prim false)
    exact readback
  · rfl
  · rfl

private def flag : TypeGraph.Path graph (.node z) (.prim .bool) := .cons (.field .here) .nil
private def children : TypeGraph.Path graph (.node z) (.array (.node z)) := .cons (.field (.there .here)) .nil
/-- Distinct siblings with heterogeneous endpoints: scalar clear and array push. -/
theorem heterogeneous_commutation :
    (modifyAt (root 0) (pre.append (.cons (.index zero) flag)) reset).bind
      (fun next => modifyAt next (pre.append (.cons (.index oneIndex) children)) Value.push) =
    (modifyAt (root 0) (pre.append (.cons (.index oneIndex) children)) Value.push).bind
      (fun next => modifyAt next (pre.append (.cons (.index zero) flag)) reset) :=
  common_prefix_array_commute (root 0) pre zero oneIndex (by decide) flag children reset Value.push

theorem heterogeneous_changed :
    ((modifyAt (root 0) (pre.append (.cons (.index zero) flag)) reset).bind
      (fun next => modifyAt next (pre.append (.cons (.index oneIndex) children)) Value.push)).map
        (fun result => (result.find (pre.append (.cons (.index zero) flag)),
          (result.find (pre.append (.cons (.index oneIndex) children))).map (fun value => value.length.val))) =
      some (some (.prim false), some 2) := rfl

private def fixedRoot : Value graph (.mapping .bool (.fixed (.node z) size)) :=
  .mapping (fun _ => .present (.fixed (fun _ => .present (node true (tree 0)))))
private def fixedPre : TypeGraph.Path graph (.mapping .bool (.fixed (.node z) size)) (.fixed (.node z) size) :=
  .cons (.key true) .nil

theorem fixed_commutation :
    (modifyAt fixedRoot (fixedPre.append (.cons (.fixed zero) (suffix 0))) reset).bind
      (fun next => modifyAt next (fixedPre.append (.cons (.fixed oneIndex) (suffix 0))) reset) =
    (modifyAt fixedRoot (fixedPre.append (.cons (.fixed oneIndex) (suffix 0))) reset).bind
      (fun next => modifyAt next (fixedPre.append (.cons (.fixed zero) (suffix 0))) reset) :=
  common_prefix_fixed_commute fixedRoot fixedPre zero oneIndex (by decide) (suffix 0) (suffix 0) reset reset

theorem fixed_both_changed :
    ((modifyAt fixedRoot (fixedPre.append (.cons (.fixed zero) (suffix 0))) reset).bind
      (fun next => modifyAt next (fixedPre.append (.cons (.fixed oneIndex) (suffix 0))) reset)).map
        (fun result => (result.find (fixedPre.append (.cons (.fixed zero) (suffix 0))),
          result.find (fixedPre.append (.cons (.fixed oneIndex) (suffix 0))))) =
      some (some (.prim false), some (.prim false)) := rfl

theorem out_of_extent_both_orders :
    (modifyAt (root 0) (left 0) reset).bind
      (fun next => modifyAt next (pre.append (.cons (.index twoIndex) flag)) reset) = none ∧
    (modifyAt (root 0) (pre.append (.cons (.index twoIndex) flag)) reset).bind
      (fun next => modifyAt next (left 0) reset) = none := ⟨rfl, rfl⟩

theorem fixed_out_of_bounds_both_orders :
    (modifyAt fixedRoot (fixedPre.append (.cons (.fixed zero) flag)) reset).bind
      (fun next => modifyAt next (fixedPre.append (.cons (.fixed twoIndex) flag)) reset) = none ∧
    (modifyAt fixedRoot (fixedPre.append (.cons (.fixed twoIndex) flag)) reset).bind
      (fun next => modifyAt next (fixedPre.append (.cons (.fixed zero) flag)) reset) = none := ⟨rfl, rfl⟩

theorem same_index_wrong_order :
    ((modifyAt (root 0) (left 0) reset).bind (fun next => modifyAt next (left 0) setTrue)).map
      (fun result => result.find (left 0)) = some (some (.prim true)) ∧
    ((modifyAt (root 0) (left 0) setTrue).bind (fun next => modifyAt next (left 0) reset)).map
      (fun result => result.find (left 0)) = some (some (.prim false)) := ⟨rfl, rfl⟩

private def absentRoot : Root := .mapping (fun _ => .present
  (.array extent zero (by decide) (fun _ => .absent)))
theorem absent_allocated_siblings_materialize :
    ((modifyAt absentRoot (pre.append (.cons (.index zero) flag)) setTrue).bind
      (fun next => modifyAt next (pre.append (.cons (.index oneIndex) flag)) setTrue)).map
        (fun result => (result.find (pre.append (.cons (.index zero) flag)),
          result.find (pre.append (.cons (.index oneIndex) flag)),
          (pre.append (.cons (.index zero) flag)).readLive Value.dflt result)) =
      some (some (.prim true), some (.prim true), none) := rfl

private def badSuffix : TypeGraph.Path graph (.node z) (.prim .bool) :=
  .cons (.field (.there .here)) (.cons (.index oneIndex) flag)

theorem malformed_suffix_both_orders :
    (modifyAt (root 0) (left 0) reset).bind
      (fun next => modifyAt next (pre.append (.cons (.index oneIndex) badSuffix)) reset) = none ∧
    (modifyAt (root 0) (pre.append (.cons (.index oneIndex) badSuffix)) reset).bind
      (fun next => modifyAt next (left 0) reset) = none := ⟨rfl, rfl⟩

private def emptyChild : TypeGraph.Path graph (.node z) (.array (.node z)) :=
  .cons (.field (.there .here)) (.cons (.index zero) children)
theorem local_pop_target_readable :
    (root 0).find (pre.append (.cons (.index oneIndex) emptyChild)) =
      some (Value.dflt (.array (.node z))) := rfl

theorem local_pop_target_empty : (Value.dflt _ : Nodes).pop = none := rfl

/-- The suffix is readable but its actual local pop fails, independently of
out-of-extent path failure. Both sibling orders return no result. -/
theorem local_pop_failure_both_orders :
    (modifyAt (root 0) (left 0) reset).bind
      (fun next => modifyAt next (pre.append (.cons (.index oneIndex) emptyChild)) Value.pop) = none ∧
    (modifyAt (root 0) (pre.append (.cons (.index oneIndex) emptyChild)) Value.pop).bind
      (fun next => modifyAt next (left 0) reset) = none := ⟨rfl, rfl⟩

/-- info: 'Solidity.Backend.StorageOps.modifyAt_array_suffix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms modifyAt_array_suffix
/-- info: 'Solidity.Backend.StorageOps.modifyAt_fixed_suffix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms modifyAt_fixed_suffix
/-- info: 'Solidity.Backend.StorageOps.array_suffixes_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms array_suffixes_commute
/-- info: 'Solidity.Backend.StorageOps.fixed_suffixes_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fixed_suffixes_commute
/-- info: 'Solidity.Backend.StorageOps.common_prefix_array_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms common_prefix_array_commute
/-- info: 'Solidity.Backend.StorageOps.common_prefix_fixed_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms common_prefix_fixed_commute

end Solidity.Backend.StorageOps.IndexedControls
