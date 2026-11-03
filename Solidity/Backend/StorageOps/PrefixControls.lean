import Solidity.Backend.StorageOps.CommonPrefix

/-! Inhabited shared-prefix controls over actual intrinsic operations.
No numeric representation or transaction-rollback claim is made. -/
namespace Solidity.Backend.StorageOps.PrefixControls
open TypeGraph

private def z : Fin 1 := ⟨0, by decide⟩
private def fs : List (Name × TypeGraph.Ty 1) := [("flag", .prim .bool), ("children", .array (.node z))]
private def graph : Schema 1 where
  origin := "v10-common-prefix-controls"
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
private abbrev Nodes := Value graph (.array (.node z))
private abbrev Inner := Value graph (.mapping .bool (.array (.node z)))
private abbrev Outer := Value graph (.mapping .bool (.mapping .bool (.array (.node z))))
private def node (flag : Bool) (children : Nodes := Value.dflt _) : Value graph (.node z) :=
  .node (fun p => match p with
    | .here => .prim flag
    | .there .here => children
    | .there (.there q) => nomatch q)
private def one (v : Value graph (.node z)) : Nodes :=
  .array ⟨1, by decide⟩ ⟨1, by decide⟩ (by decide) (fun _ => .present v)
private def tree : Nat → Nodes
  | 0 => one (node true)
  | d + 1 => one (node true (tree d))
private def shadow (d : Nat) : Nodes :=
  .array ⟨1, by decide⟩ zero (by decide) (fun _ => .present (node true (tree d)))
private def deepFlag : Nat → TypeGraph.Path graph (.array (.node z)) (.prim .bool)
  | 0 => .cons (.index zero) (.cons (.field .here) .nil)
  | d + 1 => .cons (.index zero) (.cons (.field (.there .here)) (deepFlag d))
private def reset : Value graph (.prim .bool) → Option (Value graph (.prim .bool)) :=
  fun _ => some (.prim false)
private def setTrue : Value graph (.prim .bool) → Option (Value graph (.prim .bool)) :=
  fun _ => some (.prim true)
private def innerSlots (d : Nat) (key : PrimTy.bool.Denote) : Slot graph (.array (.node z)) :=
  .present (if key = true then tree (d + 1) else shadow d)
private def inner (d : Nat) : Inner := .mapping (innerSlots d)
private def outerSlots (d : Nat) (key : PrimTy.bool.Denote) : Slot graph (.mapping .bool (.array (.node z))) :=
  .present (if key = true then inner d else .mapping (fun _ => .present (tree 0)))
private def root (d : Nat) : Outer := .mapping (outerSlots d)
private def pre : TypeGraph.Path graph
    (.mapping .bool (.mapping .bool (.array (.node z)))) (.mapping .bool (.array (.node z))) :=
  .cons (.key true) .nil
private def left (d : Nat) := pre.append (.cons (.key true) (deepFlag (d + 1)))
private def right (d : Nat) := pre.append (.cons (.key false) (deepFlag (d + 1)))
private def outside : TypeGraph.Path graph
    (.mapping .bool (.mapping .bool (.array (.node z)))) (.prim .bool) :=
  .cons (.key false) (.cons (.key true) (deepFlag 0))

/-- A nonempty shared mapping prefix, different keys, arbitrarily deep suffixes. -/
theorem shared_key_commutation (d : Nat) :
    (modifyAt (root d) (left d) reset).bind (fun next => modifyAt next (right d) reset) =
    (modifyAt (root d) (right d) reset).bind (fun next => modifyAt next (left d) reset) :=
  common_prefix_keys_commute (K := .bool) (root d) pre true false (by intro h; cases h)
    (deepFlag (d + 1)) (deepFlag (d + 1)) reset reset

private theorem tree_read (d : Nat) : (tree d).find (deepFlag d) = some (.prim true) := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih
private theorem tree_save (d : Nat) :
    ∃ result, (tree d).save (deepFlag d) (.prim false) = some result := by
  induction d with
  | zero => exact ⟨_, rfl⟩
  | succ d ih =>
    obtain ⟨result, saved⟩ := ih
    simp only [Value.save, deepFlag, tree, one, node, TypeGraph.Path.save, TypeGraph.Step.get,
      TypeGraph.Step.put, TypeGraph.Fields.get, Option.bind_eq_bind, Option.bind_some,
      zero, Nat.zero_lt_succ, dite_true, Slot.getD]
    rw [show (deepFlag d).save Value.dflt (tree d) (.prim false) = some result from saved]
    exact ⟨_, rfl⟩
private theorem tree_update (d : Nat) : ∃ result,
    modifyAt (tree d) (deepFlag d) reset = some result ∧
      result.find (deepFlag d) = some (.prim false) := by
  obtain ⟨result, saved⟩ := tree_save d
  refine ⟨result, ?_, Value.find_save _ _ _ _ saved⟩
  simp only [modifyAt, tree_read, reset, Option.bind_eq_bind, Option.bind_some]
  exact saved
private theorem shadow_update (d : Nat) : ∃ result,
    modifyAt (shadow d) (deepFlag (d + 1)) reset = some result ∧
      result.find (deepFlag (d + 1)) = some (.prim false) := by
  have read : (shadow d).find (deepFlag (d + 1)) = some (.prim true) := tree_read d
  obtain ⟨child, saved⟩ := tree_save d
  have canSave : ∃ result, (shadow d).save (deepFlag (d + 1)) (.prim false) = some result := by
    simp only [Value.save, shadow, deepFlag, node, TypeGraph.Path.save, TypeGraph.Step.get,
      TypeGraph.Step.put, TypeGraph.Fields.get, Option.bind_eq_bind, Option.bind_some,
      zero, Nat.zero_lt_succ, dite_true, Slot.getD]
    rw [show (deepFlag d).save Value.dflt (tree d) (.prim false) = some child from saved]
    exact ⟨_, rfl⟩
  obtain ⟨result, stored⟩ := canSave
  refine ⟨result, ?_, Value.find_save _ _ _ _ stored⟩
  simp only [modifyAt, read, reset, Option.bind_eq_bind, Option.bind_some]
  exact stored

/-- At every finite depth, BOTH targets really change after the actual sequence,
while an observation outside the shared prefix remains true. -/
theorem shared_prefix_success (d : Nat) : ∃ result,
    (modifyAt (root d) (left d) reset).bind (fun next => modifyAt next (right d) reset) = some result ∧
    result.find (left d) = some (.prim false) ∧
    result.find (right d) = some (.prim false) ∧ result.find outside = some (.prim true) := by
  obtain ⟨a, changedA, readA⟩ := tree_update (d + 1)
  obtain ⟨b, changedB, readB⟩ := shadow_update d
  let updated : Inner := .mapping (Slots.write (Slots.write (innerSlots d) true a) false b)
  have different : (true : PrimTy.bool.Denote) ≠ false := by intro h; cases h
  have childSequence :
      (modifyAt (inner d) (.cons (.key true) (deepFlag (d + 1))) reset).bind
        (fun next => modifyAt next (.cons (.key false) (deepFlag (d + 1))) reset) = some updated := by
    simp only [inner, modifyAt_key_suffix, modifySlot, innerSlots,
      ite_true, Slot.getD, changedA, Option.map_some, Option.bind_some,
      Slots.write_other _ true false (Ne.symm different), if_neg (Ne.symm different), changedB]
    rfl
  let result : Outer := .mapping (Slots.write (outerSlots d) true updated)
  refine ⟨result, ?_, ?_, ?_, ?_⟩
  · simp only [left, right, modifyAt_append, modifyAt_sequence]
    change modifyAt (root d) pre
      (fun old => (modifyAt old (.cons (.key true) (deepFlag (d + 1))) reset).bind
        (fun next => modifyAt next (.cons (.key false) (deepFlag (d + 1))) reset)) = some result
    simp only [root, pre, modifyAt_mapping, modifySlot, outerSlots, ite_true,
      Slot.getD, childSequence, Option.map_some]
    rfl
  · change (((Slots.write (Slots.write (innerSlots d) true a) false b) true).getD (Value.dflt _)).find (deepFlag (d + 1)) = some (.prim false)
    rw [Slots.write_other _ false true different, Slots.write_self]
    exact readA
  · change b.find (deepFlag (d + 1)) = some (.prim false)
    exact readB
  · rfl

/-- Source-live observation remains distinct from the successful retained read. -/
theorem retained_still_not_live :
    ((modifyAt (root 0) (left 0) reset).bind (fun next => modifyAt next (right 0) reset)).map
      (fun result => (right 0).readLive Value.dflt result) = some none := rfl

private def bad : TypeGraph.Path graph (.array (.node z)) (.prim .bool) :=
  .cons (.index ⟨1, by decide⟩) (.cons (.field .here) .nil)
theorem malformed_suffix_fails :
    (modifyAt (root 0) (left 0) reset).bind
      (fun next => modifyAt next (pre.append (.cons (.key false) bad)) reset) = none := rfl

/-- Same-target overlap destroys commutation; no unconditional alias theorem. -/
theorem same_target_wrong_order :
    ((modifyAt (root 0) (left 0) reset).bind (fun next => modifyAt next (left 0) setTrue)).map
      (fun result => result.find (left 0)) = some (some (.prim true)) ∧
    ((modifyAt (root 0) (left 0) setTrue).bind (fun next => modifyAt next (left 0) reset)).map
      (fun result => result.find (left 0)) = some (some (.prim false)) := ⟨rfl, rfl⟩

private def nodePre : TypeGraph.Path graph
    (.mapping .bool (.mapping .bool (.array (.node z)))) (.node z) :=
  pre.append (.cons (.key true) (.cons (.index zero) .nil))
/-- Genuinely heterogeneous endpoints: boolean clear versus aggregate pop. -/
theorem shared_member_heterogeneous (d : Nat) :
    (modifyAt (root d) (nodePre.append (.cons (.field .here) .nil)) reset).bind
      (fun next => modifyAt next (nodePre.append (.cons (.field (.there .here)) .nil)) Value.pop) =
    (modifyAt (root d) (nodePre.append (.cons (.field (.there .here)) .nil)) Value.pop).bind
      (fun next => modifyAt next (nodePre.append (.cons (.field .here) .nil)) reset) :=
  common_prefix_fields_commute (G := graph) (i := z) (root d) nodePre .here (.there .here)
    (by decide) .nil .nil reset Value.pop

theorem heterogeneous_changed :
    ((modifyAt (root 0) (nodePre.append (.cons (.field .here) .nil)) reset).bind
      (fun next => modifyAt next (nodePre.append (.cons (.field (.there .here)) .nil)) Value.pop)).map
        (fun result => (result.find (nodePre.append (.cons (.field .here) .nil)),
          (result.find (nodePre.append (.cons (.field (.there .here)) .nil))).map (fun v => v.length.val))) =
      some (some (.prim false), some 0) := rfl

private def retainedNodePre : TypeGraph.Path graph
    (.mapping .bool (.mapping .bool (.array (.node z)))) (.node z) :=
  pre.append (.cons (.key false) (.cons (.index zero) .nil))

theorem retained_common_prefix_changes :
    ((modifyAt (root 0) (retainedNodePre.append (.cons (.field .here) .nil)) reset).bind
      (fun next => modifyAt next (retainedNodePre.append (.cons (.field (.there .here)) .nil)) Value.pop)).map
        (fun result => (result.find (retainedNodePre.append (.cons (.field .here) .nil)),
          (result.find (retainedNodePre.append (.cons (.field (.there .here)) .nil))).map (fun v => v.length.val),
          retainedNodePre.readLive Value.dflt result)) =
      some (some (.prim false), some 0, none) := rfl

private def deepNodePre := nodePre.append (.cons (.field (.there .here)) (.cons (.index zero) .nil))
theorem member_inside_common_prefix_changes :
    ((modifyAt (root 1) (deepNodePre.append (.cons (.field .here) .nil)) reset).bind
      (fun next => modifyAt next (deepNodePre.append (.cons (.field (.there .here)) .nil)) Value.pop)).map
        (fun result => (result.find (deepNodePre.append (.cons (.field .here) .nil)),
          (result.find (deepNodePre.append (.cons (.field (.there .here)) .nil))).map (fun v => v.length.val))) =
      some (some (.prim false), some 0) := rfl

private def sizeOne : FixedSize := ⟨1, by decide⟩
private def fixedRoot : Value graph (.fixed (.node z) sizeOne) :=
  .fixed (fun _ => .present (node true (tree 0)))
private def fixedPre : TypeGraph.Path graph (.fixed (.node z) sizeOne) (.node z) :=
  .cons (.fixed zero) .nil

theorem fixed_common_prefix_changes :
    ((modifyAt fixedRoot (fixedPre.append (.cons (.field .here) .nil)) reset).bind
      (fun next => modifyAt next (fixedPre.append (.cons (.field (.there .here)) .nil)) Value.pop)).map
        (fun result => (result.find (fixedPre.append (.cons (.field .here) .nil)),
          (result.find (fixedPre.append (.cons (.field (.there .here)) .nil))).map (fun v => v.length.val))) =
      some (some (.prim false), some 0) := rfl

private def invalidPre : TypeGraph.Path graph (.fixed (.node z) sizeOne) (.node z) :=
  .cons (.fixed ⟨1, by decide⟩) .nil

theorem unreadable_common_prefix_fails :
    (modifyAt fixedRoot (invalidPre.append (.cons (.field .here) .nil)) reset).bind
      (fun next => modifyAt next (invalidPre.append (.cons (.field (.there .here)) .nil)) Value.pop) = none ∧
    (modifyAt fixedRoot (invalidPre.append (.cons (.field (.there .here)) .nil)) Value.pop).bind
      (fun next => modifyAt next (invalidPre.append (.cons (.field .here) .nil)) reset) = none := ⟨rfl, rfl⟩

private def defaults : Value graph (.mapping .bool (.mapping .bool (.prim .bool))) :=
  .mapping (fun _ => .absent)
private def defaultPre : TypeGraph.Path graph
    (.mapping .bool (.mapping .bool (.prim .bool))) (.mapping .bool (.prim .bool)) := .cons (.key true) .nil
/-- Defaulted prefix reads are usable and their materialization is preserved. -/
theorem defaulted_prefix_update : (modifyAt defaults
    (defaultPre.append (.cons (.key true) .nil)) setTrue).map
      (fun result => result.find (defaultPre.append (.cons (.key true) .nil))) = some (some (.prim true)) := rfl

/-- Read-then-write is NOT constructor identity on an absent defaulted slot. -/
theorem absent_identity_materializes : modifyAt defaults defaultPre (fun value => some value) ≠ some defaults := by
  intro equal
  change some (Value.mapping (K := .bool) (Slots.write (fun (_ : PrimTy.bool.Denote) => Slot.absent) true
    (Value.dflt (.mapping .bool (.prim .bool))))) = some defaults at equal
  have maps := Value.mapping.inj (Option.some.inj equal)
  have observed := congrFun maps true
  change Slot.present (Value.dflt (.mapping .bool (.prim .bool))) = Slot.absent at observed
  cases observed

/-- info: 'Solidity.Backend.StorageOps.step_put_exists' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms step_put_exists
/-- info: 'Solidity.Backend.StorageOps.step_put_overwrite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_put_overwrite
/-- info: 'Solidity.Backend.StorageOps.common_prefix_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms common_prefix_lift

/-- info: 'Solidity.Backend.StorageOps.prefix_save_exists' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms prefix_save_exists
/-- info: 'Solidity.Backend.StorageOps.prefix_save_overwrite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prefix_save_overwrite
/-- info: 'Solidity.Backend.StorageOps.prefix_save_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prefix_save_append
/-- info: 'Solidity.Backend.StorageOps.modifyAt_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms modifyAt_append
/-- info: 'Solidity.Backend.StorageOps.modifyAt_sequence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms modifyAt_sequence
/-- info: 'Solidity.Backend.StorageOps.common_prefix_fields_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms common_prefix_fields_commute
/-- info: 'Solidity.Backend.StorageOps.common_prefix_keys_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms common_prefix_keys_commute

end Solidity.Backend.StorageOps.PrefixControls
