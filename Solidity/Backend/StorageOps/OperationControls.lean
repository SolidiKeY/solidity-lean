import Solidity.Backend.StorageOps.OperationTransport
import Solidity.Backend.StorageOps.FieldOperations
import Solidity.Backend.StorageOps.PathOperations

/-! Inhabited partial-family, recursive-alias, failure and numeric-footprint
controls. These operate on existing graph values, not a new representation. -/

namespace Solidity.Backend.StorageOps.OperationControls

open TypeGraph

private def z : Fin 1 := ⟨0, by decide⟩
private def fs : List (Name × TypeGraph.Ty 1) :=
  [("flag", .prim .bool), ("children", .array (.node z))]
private def graph : Schema 1 where
  origin := "v10-partial-family-controls"
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
private abbrev Node := Value graph (.node z)
private abbrev Root := Value graph (.mapping .bool (.array (.node z)))
private def empty : Nodes := Value.dflt _
private def node (flag : Bool) (children : Nodes := empty) : Node :=
  .node (fun p => match p with
    | .here => .prim flag
    | .there .here => children
    | .there (.there q) => nomatch q)
private def one (v : Node) : Nodes :=
  .array ⟨1, by decide⟩ ⟨1, by decide⟩ (by decide) (fun _ => .present v)
private def live : Nodes := one (node true)
private def tree : Nat → Nodes
  | 0 => live
  | d + 1 => one (node true (tree d))
private def deepFlag : Nat → TypeGraph.Path graph (.array (.node z)) (.prim .bool)
  | 0 => .cons (.index zero) (.cons (.field .here) .nil)
  | d + 1 => .cons (.index zero) (.cons (.field (.there .here)) (deepFlag d))
private theorem tree_read (depth : Nat) : (tree depth).find (deepFlag depth) = some (.prim true) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    change (tree depth).find (deepFlag depth) = some (.prim true)
    exact ih
private def shadow (depth : Nat) : Nodes :=
  .array ⟨1, by decide⟩ zero (by decide) (fun _ => .present (node true (tree depth)))
private def slots (depth : Nat) (key : PrimTy.bool.Denote) : Slot graph (.array (.node z)) :=
  .present (if key = true then live else shadow depth)
private def keyPath (key : PrimTy.bool.Denote) : TypeGraph.Path graph
    (.mapping .bool (.array (.node z))) (.array (.node z)) := .cons (.key key) .nil
private def clear : Nodes → Option Nodes := fun value => some value.clear
private def clearTrue (root : Root) := modifyAt root (keyPath true) clear
private def pushFalse (root : Root) := modifyAt root (keyPath false) Value.push

/-- Actual source-path clear and push updates commute at different mapping keys. -/
theorem clear_push_commute (depth : Nat) :
    (clearTrue (.mapping (slots depth))).bind pushFalse =
      (pushFalse (.mapping (slots depth))).bind clearTrue :=
  modifyAt_mapping_commute (K := .bool) (slots depth) true false (by intro equal; cases equal) clear Value.push

/-- Clear affects its target while a different retained aggregate alias is
revived and passes a source-live read, not merely a retained read. -/
theorem revived_live_alias : ((clearTrue (.mapping (slots 0))).bind pushFalse).map
    (fun root => ((keyPath false).append (deepFlag 0)).readLive Value.dflt root) =
      some (some (.prim true)) := rfl

theorem cleared_other_alias : ((clearTrue (.mapping (slots 0))).bind pushFalse).map
    (fun root => root.find ((keyPath true).append (deepFlag 0))) =
      some (some (.prim false)) := rfl

/-- Every finite recursive suffix is an inhabited observation of the revived
alias after a disjoint clear/push combination. -/
theorem recursive_revived_alias (depth : Nat) :
    ((clearTrue (.mapping (slots depth))).bind pushFalse).map
      (fun root => root.find ((keyPath false).append (deepFlag (depth + 1)))) =
        some (some (.prim true)) := by
  change some ((tree depth).find (deepFlag depth)) = some (some (.prim true))
  rw [tree_read]

private def numericSlots (_ : Nat) : Slot graph (.array (.node z)) := .present live
private def pops (_ : Nat) : Nodes → Option Nodes := Value.pop
private def clears (_ : Nat) : Nodes → Option Nodes := clear

/-- Internal repetitions are retained: one pop succeeds, the second fails.
The disjoint clear family cannot turn that failure into a successful result. -/
theorem late_failure_forward :
    (modifyMany pops [0, 0] numericSlots).bind (modifyMany clears [1]) = none := rfl

theorem late_failure_reverse :
    (modifyMany clears [1] numericSlots).bind (modifyMany pops [0, 0]) = none := rfl

/-- Regression: an actual successful disjoint clear leaves the repeated-pop
failure intact at the exact produced store, not just as an outer bind result. -/
theorem late_failure_after_successful_clear :
    modifyMany pops [0, 0] (Slots.write numericSlots 1 live.clear) = none :=
  modifyMany_failure_after_disjoint numericSlots (Slots.write numericSlots 1 live.clear)
    [0, 0] [1] pops clears (by decide) rfl rfl

/-- The family scheduler is not an always-failing implementation. -/
theorem family_success : ((modifyMany pops [0] numericSlots).bind
    (modifyMany clears [1])).map
      (fun next => ((next 0).getD (Value.dflt _)).length.val) = some 0 := rfl

/-- Removing key disjointness is false: opposite final values are observable. -/
theorem same_key_order_matters :
    ((modifySlot numericSlots 0 (fun _ => some (one (node true)))).bind
      (fun next => modifySlot next 0 (fun _ => some (one (node false))))).map
        (fun next => ((next 0).getD (Value.dflt _)).observe (deepFlag 0)) =
          some (some false) ∧
    ((modifySlot numericSlots 0 (fun _ => some (one (node false)))).bind
      (fun next => modifySlot next 0 (fun _ => some (one (node true))))).map
        (fun next => ((next 0).getD (Value.dflt _)).observe (deepFlag 0)) =
          some (some true) := by
  constructor <;> rfl

private def hash : Solidity.Storage.Pre → Nat
  | .data 0 => 32
  | .entry 7 32 => 64
  | _ => 128
private def preimages : List Solidity.Storage.Pre := [.data 0, .entry 7 32]
private def base : Solidity.Storage.Loc := .hash 7 (.data (.root 0) 0) 0
private theorem hash_lt (p : Solidity.Storage.Pre) : hash p < 256 := by
  cases p <;> simp only [hash] <;> split <;> decide
private theorem regions : Solidity.Hash.RegionsDisjoint 256 4 hash (List.range 2) preimages := by
  decide

/-- Two populated, partial operation families really instantiate numeric
transport at recursive hash/data addresses under an inhabited run premise. -/
theorem numeric_families :
    (modifyMany pops ((touched base 1 1).map (Solidity.Storage.Loc.word 256 hash))
      numericSlots).bind
        (modifyMany clears ((touched (base.add 1) 1 1).map (Solidity.Storage.Loc.word 256 hash))) =
    (modifyMany clears ((touched (base.add 1) 1 1).map (Solidity.Storage.Loc.word 256 hash))
      numericSlots).bind
        (modifyMany pops ((touched base 1 1).map (Solidity.Storage.Loc.word 256 hash))) :=
  generated_families_commute hash_lt (by decide) (by decide) regions
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
    (by decide) (by decide) (by decide) numericSlots pops clears

private def popped : Nodes := live.pop.getD live
/-- A real successful pop family leaves a bounded adjacent query unchanged;
its numeric word cannot alias the generated key under this run's premise. -/
theorem numeric_untouched :
    (modifyMany pops ((touched base 1 1).map (Solidity.Storage.Loc.word 256 hash))
      numericSlots).map (fun next => next ((base.add 2).word 256 hash)) =
        some (numericSlots ((base.add 2).word 256 hash)) := by
  have performed : modifyMany pops
      ((touched base 1 1).map (Solidity.Storage.Loc.word 256 hash)) numericSlots =
        some (Slots.write numericSlots ((base.add 0).word 256 hash) popped) := rfl
  have kept := generated_family_outside hash_lt (by decide) (by decide) regions
    base (base.add 2) 1 1
    (by
      intro l member
      have equal : l = base.add 0 := List.mem_singleton.mp member
      subst l
      change (0 < 2 ∧ 0 < 4) ∧ 0 < 4
      decide)
    (by decide) (by change (0 < 2 ∧ 0 < 4) ∧ 2 < 4; decide)
    (by decide) (by decide) numericSlots _ pops performed
  rw [performed]
  exact congrArg some kept

private def members : TypeGraph.Fields graph fs :=
  fun p => match p with
    | .here => .prim true
    | .there .here => shadow 0
    | .there (.there q) => nomatch q

/-- Heterogeneous scalar clear and recursive-array push commute on real fields. -/
theorem member_clear_push_commute :
    (modifyField members .here (fun v => some v.clear)).bind
      (fun next => modifyField next (.there .here) Value.push) =
    (modifyField members (.there .here) Value.push).bind
      (fun next => modifyField next .here (fun v => some v.clear)) :=
  modifyField_commute members .here (.there .here) (by decide)
    (fun v => some v.clear) Value.push

/-- The combined operation succeeds, changes the scalar and revives the nested
array's retained element with its scalar identity intact. -/
theorem member_live_combination :
    ((modifyField members .here (fun v => some v.clear)).bind
      (fun next => modifyField next (.there .here) Value.push)).map
        (fun result => (TypeGraph.Fields.get result .here,
          (deepFlag 0).readLive Value.dflt
            (TypeGraph.Fields.get result (.there .here)))) =
      some (.prim false, some (.prim true)) := rfl

/-- The member adapter is the actual intrinsic node-path operation. -/
theorem member_path_adapter :
    modifyAt (.node members : Node) (.cons (.field (.there .here)) .nil) Value.push =
      (modifyField members (.there .here) Value.push).map Value.node :=
  modifyAt_field (G := graph) (i := z) members (.there .here) Value.push

private def reset : Value graph (.prim .bool) → Option (Value graph (.prim .bool)) :=
  fun _ => some (.prim false)

private theorem tree_save_succeeds (depth : Nat) :
    ∃ result, (deepFlag depth).save Value.dflt (tree depth) (.prim false) = some result := by
  induction depth with
  | zero => exact ⟨_, rfl⟩
  | succ depth ih =>
    obtain ⟨result, saved⟩ := ih
    simp only [deepFlag, tree, one, node, TypeGraph.Path.save, TypeGraph.Step.get,
      TypeGraph.Step.put, TypeGraph.Fields.get, Option.bind_eq_bind,
      Option.bind_some, zero, Nat.zero_lt_succ, dite_true, Slot.getD]
    rw [saved]
    exact ⟨_, rfl⟩

/-- The arbitrary-depth fixture successfully updates, rather than instantiating
the commutation theorem only at failed paths. -/
theorem arbitrary_depth_suffix_success (depth : Nat) :
    ∃ result, modifyAt (tree depth) (deepFlag depth) reset = some result ∧
      result.find (deepFlag depth) = some (.prim false) := by
  obtain ⟨result, saved⟩ := tree_save_succeeds depth
  refine ⟨result, ?_, ?_⟩
  · simp only [modifyAt, tree_read, reset, Value.save, Option.bind_eq_bind, Option.bind_some]
    exact saved
  · exact TypeGraph.Path.read_save Value.dflt (deepFlag depth) (tree depth) result (.prim false) saved

/-- Recursive suffixes need not have equal depth, and retained aliases are
not silently reclassified as live by the operation adapter. -/
theorem recursive_key_suffix_commutation (depth : Nat) :
    (modifyAt (.mapping (slots depth)) (.cons (.key true) (deepFlag 0)) reset).bind
      (fun root => modifyAt root (.cons (.key false) (deepFlag (depth + 1))) reset) =
    (modifyAt (.mapping (slots depth)) (.cons (.key false) (deepFlag (depth + 1))) reset).bind
      (fun root => modifyAt root (.cons (.key true) (deepFlag 0)) reset) :=
  recursive_keys_commute (K := .bool) (slots depth) true false (by intro equal; cases equal)
    (deepFlag 0) (deepFlag (depth + 1)) reset reset

/-- Heterogeneous outer members separate scalar clear from arbitrary-depth
recursive suffix updates within the child array. -/
theorem recursive_field_suffix_commutation (depth : Nat) :
    (modifyAt (.node members : Node) (.cons (.field .here) .nil) reset).bind
      (fun root => modifyAt root (.cons (.field (.there .here)) (deepFlag depth)) reset) =
    (modifyAt (.node members : Node) (.cons (.field (.there .here)) (deepFlag depth)) reset).bind
      (fun root => modifyAt root (.cons (.field .here) .nil) reset) :=
  recursive_fields_commute (G := graph) (i := z) members .here (.there .here)
    (by decide) .nil (deepFlag depth) reset reset

/-- Actual successful retained recursive writes in both different keys. -/
theorem recursive_suffix_changed_values :
    ((modifyAt (.mapping (slots 0)) (.cons (.key true) (deepFlag 0)) reset).bind
      (fun root => modifyAt root (.cons (.key false) (deepFlag 1)) reset)).map
        (fun result => (result.find (.cons (.key true) (deepFlag 0)),
          result.find (.cons (.key false) (deepFlag 1)))) =
      some (some (.prim false), some (.prim false)) := rfl

/-- Retained-path success does not imply a live-path observation. -/
theorem recursive_suffix_still_dangling :
    ((modifyAt (.mapping (slots 0)) (.cons (.key true) (deepFlag 0)) reset).bind
      (fun root => modifyAt root (.cons (.key false) (deepFlag 1)) reset)).map
        (fun result => ((keyPath false).append (deepFlag 1)).readLive Value.dflt result) =
      some none := rfl

private def badFlag : TypeGraph.Path graph (.array (.node z)) (.prim .bool) :=
  .cons (.index ⟨1, by decide⟩) (.cons (.field .here) .nil)

theorem recursive_suffix_failure :
    (modifyAt (.mapping (slots 0)) (.cons (.key true) (deepFlag 0)) reset).bind
      (fun root => modifyAt root (.cons (.key false) badFlag) reset) = none := rfl

/-- info: 'Solidity.Backend.StorageOps.modifyAt_field_suffix' does not depend on any axioms -/
#guard_msgs in #print axioms modifyAt_field_suffix
/-- info: 'Solidity.Backend.StorageOps.modifyAt_key_suffix' does not depend on any axioms -/
#guard_msgs in #print axioms modifyAt_key_suffix
/-- info: 'Solidity.Backend.StorageOps.recursive_fields_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursive_fields_commute
/-- info: 'Solidity.Backend.StorageOps.recursive_keys_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursive_keys_commute

/-- info: 'Solidity.Backend.StorageOps.field_writes_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms field_writes_commute
/-- info: 'Solidity.Backend.StorageOps.modifyField_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms modifyField_commute
/-- info: 'Solidity.Backend.StorageOps.modifyAt_field' does not depend on any axioms -/
#guard_msgs in #print axioms modifyAt_field

/-- info: 'Solidity.Backend.StorageOps.modifySlot_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms modifySlot_commute
/-- info: 'Solidity.Backend.StorageOps.modifyAt_mapping_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms modifyAt_mapping_commute
/-- info: 'Solidity.Backend.StorageOps.modifyMany_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms modifyMany_commute
/-- info: 'Solidity.Backend.StorageOps.modifyMany_outside' depends on axioms: [propext] -/
#guard_msgs in #print axioms modifyMany_outside
/-- info: 'Solidity.Backend.StorageOps.generated_families_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms generated_families_commute
/-- info: 'Solidity.Backend.StorageOps.generated_family_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms generated_family_outside

/-- info: 'Solidity.Backend.StorageOps.OperationControls.late_failure_after_successful_clear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms late_failure_after_successful_clear
end Solidity.Backend.StorageOps.OperationControls
