import Solidity.Backend.StorageOps.LifecyclePaths

/-! Nested lifecycle, fresh/reused aliases, mapping tails and exact graph
failure controls. Modeled graph operations, not source/target world rollback. -/
namespace Solidity.Backend.StorageOps.LifecyclePathControls
open TypeGraph
private def z : Fin 1 := ⟨0, by decide⟩
private def fs : List (Name × TypeGraph.Ty 1) :=
  [("flag", .prim .bool), ("children", .array (.node z)), ("memo", .mapping .bool (.prim .bool))]
private def graph : Schema 1 where
  origin := "v10-nested-lifecycle-controls"
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
    rcases hf with rfl | rfl | rfl <;> exact Nat.zero_lt_succ 0
private def zero : Index := ⟨0, by decide⟩
private abbrev Nodes := Value graph (.array (.node z))
private abbrev Root := Value graph (.mapping .bool (.array (.node z)))
private def memo : Value graph (.mapping .bool (.prim .bool)) :=
  .mapping (fun key => if key = true then .present (.prim true) else .absent)
private def node (flag : Bool) (children : Nodes := Value.dflt _) : Value graph (.node z) :=
  .node (fun p => match p with
    | .here => .prim flag
    | .there .here => children
    | .there (.there .here) => memo
    | .there (.there (.there q)) => nomatch q)
private def one (v : Value graph (.node z)) : Nodes :=
  .array ⟨1, by decide⟩ ⟨1, by decide⟩ (by decide) (fun _ => .present v)
private def tree : Nat → Nodes
  | 0 => one (node true)
  | d + 1 => one (node true (tree d))
private def shadow (d : Nat) : Nodes :=
  .array ⟨1, by decide⟩ zero (by decide) (fun _ => .present (node true (tree d)))
private def makeRoot (target : Nodes) : Root :=
  .mapping (fun key => .present (if key = true then one (node true target) else tree 0))
private def root (d : Nat) : Root := makeRoot (shadow d)
private def pre : TypeGraph.Path graph (.mapping .bool (.array (.node z))) (.array (.node z)) :=
  .cons (.key true) (.cons (.index zero) (.cons (.field (.there .here)) .nil))
private def flagSuffix : TypeGraph.Path graph (.node z) (.prim .bool) := .cons (.field .here) .nil
private def memoSuffix : TypeGraph.Path graph (.node z) (.prim .bool) :=
  .cons (.field (.there (.there .here))) (.cons (.key true) .nil)
private def aliasFlag := pre.append (.cons (.index zero) flagSuffix)
private def aliasMemo := pre.append (.cons (.index zero) memoSuffix)
private def outside : TypeGraph.Path graph (.mapping .bool (.array (.node z))) (.prim .bool) :=
  .cons (.key false) (.cons (.index zero) flagSuffix)
private def deepFlag : Nat → TypeGraph.Path graph (.array (.node z)) (.prim .bool)
  | 0 => .cons (.index zero) flagSuffix
  | d + 1 => .cons (.index zero) (.cons (.field (.there .here)) (deepFlag d))
private theorem tree_live (d : Nat) : (deepFlag d).readLive Value.dflt (tree d) = some (.prim true) := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

/-- Every finite recursive suffix is genuinely revived by the actual nested
push. The prefix is live before push, but the element alias is not. -/
theorem revived_all_depth (d : Nat) : ∃ result,
    pushAt (root d) pre = some result ∧
    aliasFlag.readLive Value.dflt result = some (.prim true) ∧
    (pre.append (.cons (.index zero) (.cons (.field (.there .here)) (deepFlag d)))).readLive
      Value.dflt result = some (.prim true) := by
  have before : pre.readLive Value.dflt (root d) = some (shadow d) := rfl
  obtain ⟨value, pushedChild⟩ : ∃ value, (shadow d).push = some value := ⟨_, rfl⟩
  have read := prefix_live_find pre (root d) (shadow d) before
  obtain ⟨result, saved⟩ := prefix_save_exists pre (root d) (shadow d) value read
  have pushed : pushAt (root d) pre = some result := by
    simp only [pushAt, modifyAt, read, Option.bind_eq_bind, Option.bind_some, operationPush_eq_push, pushedChild]
    exact saved
  refine ⟨result, pushed, ?_, ?_⟩
  · exact pushAt_revives_live (root d) result pre (shadow d) before pushed rfl (by change 0 < 1; decide) flagSuffix
  · have revived := pushAt_revives_live (root d) result pre (shadow d) before pushed rfl
      (by change 0 < 1; decide) (.cons (.field (.there .here)) (deepFlag d))
    change (pre.append (.cons (.index zero) (.cons (.field (.there .here)) (deepFlag d)))).readLive
      Value.dflt result = (deepFlag d).readLive Value.dflt (tree d) at revived
    exact revived.trans (tree_live d)

theorem alias_initially_not_live : aliasFlag.readLive Value.dflt (root 0) = none := rfl

theorem cycle_pop_invalidates : ((pushAt (root 0) pre).bind (fun next => popAt next pre)).map
    (fun result => (aliasFlag.readLive Value.dflt result, result.find aliasMemo,
      result.find outside)) = some (none, some (.prim true), some (.prim true)) := rfl

/-- Reuse after pop sees the cleared scalar and retained mapping contents. -/
theorem cycle_regrow_reuses_cleared : (((pushAt (root 0) pre).bind (fun next => popAt next pre)).bind
    (fun next => pushAt next pre)).map
      (fun result => (aliasFlag.readLive Value.dflt result, aliasMemo.readLive Value.dflt result)) =
        some (some (.prim false), some (.prim true)) := rfl

/-- Fresh aggregate allocation defaults differ from retained aggregate reuse. -/
theorem fresh_defaults : (pushAt (makeRoot (Value.dflt _)) pre).map
    (fun result => (aliasFlag.readLive Value.dflt result, aliasMemo.readLive Value.dflt result)) =
      some (some (.prim false), some (.prim false)) := rfl

theorem delete_live_mapping_tail : (deleteAt (makeRoot (tree 0)) pre).map
    (fun result => (result.find aliasFlag, result.find aliasMemo,
      aliasFlag.readLive Value.dflt result)) = some (some (.prim false), some (.prim true), none) := rfl

/-- Deleting an empty array does not clear its older retained shadow slot. -/
theorem delete_empty_retained_unchanged : (deleteAt (root 0) pre).map
    (fun result => (result.find aliasFlag, result.find aliasMemo)) =
      some (some (.prim true), some (.prim true)) := rfl

theorem empty_pop_failure : popAt (root 0) pre = none := rfl

private def retainedParent : Root := .mapping (fun _ => .present
  (.array ⟨1, by decide⟩ zero (by decide) (fun _ => .present (node true (shadow 0)))))
/-- Retained prefix success cannot supply the missing before-live premise. -/
theorem retained_parent_not_promoted : (pushAt retainedParent pre).map
    (fun result => (result.find aliasFlag, aliasFlag.readLive Value.dflt result)) =
      some (some (.prim true), none) := rfl

private def full : Nodes := .array ⟨2 ^ 256 - 1, by omega⟩
    ⟨2 ^ 256 - 1, by omega⟩ (by omega) (fun _ => .absent)

theorem graph_capacity_failure : pushAt (makeRoot full) pre = none := by
  apply (pushAt_fails_found (makeRoot full) pre full rfl).2
  change 2 ^ 256 ≤ (2 ^ 256 - 1) + 1
  omega

private def bad : TypeGraph.Path graph (.mapping .bool (.array (.node z))) (.array (.node z)) :=
  .cons (.key true) (.cons (.index ⟨1, by decide⟩) (.cons (.field (.there .here)) .nil))

theorem malformed_lifecycle_failures : pushAt (root 0) bad = none ∧
    popAt (root 0) bad = none ∧ deleteAt (root 0) bad = none := ⟨rfl, rfl, rfl⟩

/-- A later failed pop returns no partially modified root. This Option law does
not assert rollback of the external world or compiler execution. -/
theorem late_failure_no_result : ((pushAt (root 0) pre).bind (fun next => popAt next pre)).bind
    (fun next => popAt next pre) = none := rfl

/-- info: 'Solidity.Backend.StorageOps.prefix_live_find' does not depend on any axioms -/
#guard_msgs in #print axioms prefix_live_find
/-- info: 'Solidity.Backend.StorageOps.prefix_live_save' depends on axioms: [propext] -/
#guard_msgs in #print axioms prefix_live_save
/-- info: 'Solidity.Backend.StorageOps.live_read_append' does not depend on any axioms -/
#guard_msgs in #print axioms live_read_append
/-- info: 'Solidity.Backend.StorageOps.modifyAt_failure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms modifyAt_failure
/-- info: 'Solidity.Backend.StorageOps.deleteAt_eq_delAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms deleteAt_eq_delAt
/-- info: 'Solidity.Backend.StorageOps.pushAt_result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms pushAt_result
/-- info: 'Solidity.Backend.StorageOps.popAt_result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms popAt_result
/-- info: 'Solidity.Backend.StorageOps.pushAt_reused_alias' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms pushAt_reused_alias
/-- info: 'Solidity.Backend.StorageOps.popAt_invalidates_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms popAt_invalidates_live
/-- info: 'Solidity.Backend.StorageOps.pushAt_revives_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms pushAt_revives_live

end Solidity.Backend.StorageOps.LifecyclePathControls
