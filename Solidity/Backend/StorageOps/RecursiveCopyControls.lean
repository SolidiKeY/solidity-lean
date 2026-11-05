import Solidity.Backend.StorageOps.AbsentRootQueries
import Solidity.Backend.StorageOps.RecursiveProgress

/-! Actual recursive operation controls, independent from prior fixture verdicts. -/
namespace Solidity.Backend.StorageOps.RecursiveCopyControls
open TypeGraph
private def z : Fin 1 := ⟨0, by decide⟩
private def fs : List (Name × TypeGraph.Ty 1) :=
  [("flag", .prim .bool), ("children", .array (.node z)),
   ("memo", .mapping .bool (.prim .bool))]
private def graph : Schema 1 where
  origin := "v10-recursive-operation-controls"
  declId := fun _ => 0
  declId_injective := by intro i j _; apply Fin.ext; omega
  name := fun _ => "MemoNode"
  fields := fun _ => fs
  rank := fun _ => 1
  nonempty := fun _ => rfl
  distinct := fun _ => rfl
  guarded := by
    intro i f hf
    simp only [fs, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> exact Nat.zero_lt_succ 0

private def zero : Index := ⟨0, by decide⟩
private abbrev Map := Value graph (.mapping .bool (.prim .bool))
private abbrev Nodes := Value graph (.array (.node z))
private abbrev Node := Value graph (.node z)
private def oldMemo : Map := .mapping (fun _ => .present (.prim true))
private def srcMemo : Map := .mapping (fun _ => .present (.prim false))
private def empty : Nodes := Value.dflt _
private def node (flag : Bool) (children : Nodes) (memo : Map) : Node :=
  .node (fun p => match p with
    | .here => .prim flag
    | .there .here => children
    | .there (.there .here) => memo
    | .there (.there (.there q)) => nomatch q)
private def one (v : Node) : Nodes :=
  .array ⟨1, by decide⟩ ⟨1, by decide⟩ (by decide) (fun _ => .present v)

/-- Width is chosen independently at every recursive level. -/
private def tree (width : Nat → Index) (flag : Bool) : Nat → Nodes
  | 0 => .array ⟨(width 0).val, by have h := (width 0).isLt; omega⟩ (width 0) (Nat.le_refl _)
      (fun _ => .present (node flag empty (if flag then oldMemo else srcMemo)))
  | d + 1 => .array ⟨(width (d+1)).val, by have h := (width (d+1)).isLt; omega⟩ (width (d+1)) (Nat.le_refl _)
      (fun _ => .present (node flag (tree width flag d) (if flag then oldMemo else srcMemo)))
private def deep : Nat → TypeGraph.Path graph (.array (.node z)) (.prim .bool)
  | 0 => .cons (.index zero) (.cons (.field .here) .nil)
  | d+1 => .cons (.index zero) (.cons (.field (.there .here)) (deep d))

/-- All finite recursive depths, with independently varying old/new runtime
lengths. Both source and destination are populated, and the payload changes. -/
theorem varying_runtime_depth (ow nw : Nat → Index)
    (op : ∀ d, 0 < (ow d).val) (np : ∀ d, 0 < (nw d).val) (d : Nat) :
    (tree ow true d).find (deep d) = some (.prim true) ∧
    (recursiveCopy (tree ow true d) (tree nw false d)).find (deep d) = some (.prim false) := by
  rw [recursiveCopy_eq_overlay]
  induction d with
  | zero =>
    simp only [tree, deep, Value.find, TypeGraph.Path.read, TypeGraph.Step.get,
      Value.overlay, zero, dif_pos (op 0), dif_pos (np 0), dif_pos (show 0 < max (ow 0).val (nw 0).val by have h := op 0; omega), Slot.overlay, Slot.getD,
      Option.bind_some, node, Fields.get]
    exact ⟨True.intro, True.intro⟩
  | succ d ih =>
    simp only [tree, deep, Value.find, TypeGraph.Path.read, TypeGraph.Step.get,
      Value.overlay, zero, dif_pos (op (d+1)), dif_pos (np (d+1)), dif_pos (show 0 < max (ow (d+1)).val (nw (d+1)).val by have h := op (d+1); omega), Slot.overlay, Slot.getD,
      Option.bind_some, node, Fields.get]
    exact ih

private def deepMemo : Nat → TypeGraph.Path graph (.array (.node z)) (.mapping .bool (.prim .bool))
  | 0 => .cons (.index zero) (.cons (.field (.there (.there .here))) .nil)
  | d+1 => .cons (.index zero) (.cons (.field (.there .here)) (deepMemo d))

theorem mapping_all_depth (ow nw : Nat → Index) (op : ∀ d, 0 < (ow d).val) (d : Nat) :
    (recursiveCopy (tree ow true d) (tree nw false d)).find (deepMemo d) = some oldMemo := by
  apply recursiveCopy_mapping_read
  induction d with
  | zero =>
    simp only [tree, deepMemo, Value.find, TypeGraph.Path.read, TypeGraph.Step.get,
      zero, dif_pos (op 0), Slot.getD, Option.bind_some, node, Fields.get, if_true]
  | succ d ih =>
    simp only [tree, deepMemo, Value.find, TypeGraph.Path.read, TypeGraph.Step.get,
      zero, dif_pos (op (d+1)), Slot.getD, Option.bind_some, node, Fields.get]
    exact ih

private def i1 : Index := ⟨1, by decide⟩
private def i2 : Index := ⟨2, by decide⟩
private def child (i : Index) : TypeGraph.Path graph (.array (.node z)) (.array (.node z)) :=
  .cons (.index i) (.cons (.field (.there .here)) .nil)
private def flag (i : Index) : TypeGraph.Path graph (.array (.node z)) (.prim .bool) :=
  .cons (.index i) (.cons (.field .here) .nil)
private def memo (i : Index) : TypeGraph.Path graph (.array (.node z)) (.prim .bool) :=
  .cons (.index i) (.cons (.field (.there (.there .here))) (.cons (.key true) .nil))
private def old : Nodes := .array ⟨3, by decide⟩ i2 (by decide)
  (fun _ => .present (node true (one (node true empty oldMemo)) oldMemo))
private def src : Nodes := one (node false empty srcMemo)

/-- A live copy, stale-tail clear, and older shadow are discriminated together. -/
theorem tails_and_payload :
    (recursiveCopy old src).observe (flag zero) = some false ∧
    (recursiveCopy old src).observe (flag i1) = some false ∧
    (recursiveCopy old src).observe (flag i2) = some true := by
  constructor
  · rfl
  · constructor <;> rfl

theorem nested_tail_cleared :
    ((recursiveCopy old src).find (child i1)).map Value.length = some zero := rfl

theorem mapping_barriers :
    (recursiveCopy old src).observe (memo zero) = some true ∧
    (recursiveCopy old src).observe (memo i1) = some true := by constructor <;> rfl

theorem retained_not_live : (recursiveCopy old src).find (flag i1) = some (.prim false) ∧
    (flag i1).readLive Value.dflt (recursiveCopy old src) = none := by constructor <;> rfl

private def overlapping : Nodes := one (node true src oldMemo)
/-- Descendant source is captured before overwriting its ancestor. -/
theorem captured_overlap : (recursiveCopyAt overlapping .nil (child zero)).map
    (fun result => result.observe (flag zero)) = some (some false) := rfl

/-- Wrong order: overwriting first and re-reading the descendant loses the
source. This actual find/copy sequence disagrees with captured execution. -/
theorem captured_length : (recursiveCopyAt overlapping .nil (child zero)).map Value.length = some i1 := rfl

theorem wrong_incremental_source :
    ((recursiveCopyAt overlapping .nil (child zero)).bind
      (fun result => recursiveCopyAt result .nil (child zero))).map
      (fun result => result.observe (flag zero)) = some (some false) ∧
    ((recursiveCopyAt overlapping .nil (child zero)).bind
      (fun result => recursiveCopyAt result .nil (child zero))).map
      (fun result => result.length) = some zero := by constructor <;> rfl

theorem overlap_preserves_mapping : (recursiveCopyAt overlapping .nil (child zero)).map
    (fun result => result.observe (memo zero)) = some (some true) := rfl

private def wrongReread : Option Nodes := do
  let modified ← overlapping.save .nil overlapping.clear
  let snapshot ← modified.find (child zero)
  modified.save .nil (recursiveCopy modified snapshot)

/-- A concrete incorrect capture order loses the descendant snapshot. -/
theorem wrong_capture_order : wrongReread.map Value.length = some zero ∧
    (recursiveCopyAt overlapping .nil (child zero)).map Value.length = some i1 := by
  constructor <;> rfl

theorem inner_shadow_survives :
    (recursiveCopy (one (node true old oldMemo)) (one (node false src srcMemo))).observe
      ((child zero).append (flag i2)) = some true := rfl

private def firstFlag : TypeGraph.Path graph (.node z) (.prim .bool) := .cons (.field .here) .nil

/-- An unfinished real array loop has copied the first slot while leaving the
next old live slot unchanged; completion clears that stale tail. -/
theorem prefix_control :
    ((recursiveArrayPrefix old.extent old.length old.slots src.extent src.length
      (by decide) src.slots 1 ⟨0, by decide⟩).getD (Value.dflt _)).find firstFlag = some (.prim false) ∧
    ((recursiveArrayPrefix old.extent old.length old.slots src.extent src.length
      (by decide) src.slots 1 ⟨1, by decide⟩).getD (Value.dflt _)).find firstFlag = some (.prim true) ∧
    ((recursiveArrayPrefix old.extent old.length old.slots src.extent src.length
      (by decide) src.slots 2 ⟨1, by decide⟩).getD (Value.dflt _)).find firstFlag = some (.prim false) := by
  constructor
  · rfl
  · constructor <;> rfl

/-- An out-of-extent nested read is failure, not a default source snapshot. -/
theorem missing_nested_source : recursiveCopyAt overlapping .nil (child i1) = none := rfl

theorem missing_nested_destination : recursiveCopyAt overlapping (child i1) .nil = none := rfl

/-- Missing live source slot clears a present destination aggregate. -/
theorem absent_nested_source :
    (recursiveCopy old (.array ⟨1, by decide⟩ i1 (by decide) (fun _ => .absent))).observe
      (flag zero) = some false := rfl

/-- A present nested source copies against the default of an absent destination. -/
theorem absent_nested_destination :
    (recursiveCopy (Value.dflt (.array (.node z)))
      (one (node true src srcMemo))).observe (flag zero) = some true ∧
    (recursiveCopy (Value.dflt (.array (.node z)))
      (one (node true src srcMemo))).observe ((child zero).append (flag zero)) = some false := by
  constructor <;> rfl

/-- Fixed slots recurse through dynamic arrays instead of semantic overlay. -/
theorem fixed_nested_copy :
    (recursiveCopy (Value.fixed (m := ⟨1, by decide⟩) (fun _ => .present old))
      (Value.fixed (fun _ => .present src))).find
      (.cons (.fixed zero) (flag zero)) = some (.prim false) := rfl

/-- info: 'Solidity.Backend.StorageOps.recursiveCopy_eq_overlay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursiveCopy_eq_overlay
/-- info: 'Solidity.Backend.StorageOps.recursiveSlot_eq_overlay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursiveSlot_eq_overlay
/-- info: 'Solidity.Backend.StorageOps.recursive_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursive_prefix
/-- info: 'Solidity.Backend.StorageOps.recursiveCopyAt_eq_semantics' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursiveCopyAt_eq_semantics
/-- info: 'Solidity.Backend.StorageOps.recursiveCopyAt_readback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursiveCopyAt_readback
/-- info: 'Solidity.Backend.StorageOps.recursiveCopy_mapping_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursiveCopy_mapping_read
/-- info: 'Solidity.Backend.StorageOps.recursiveCopy_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursiveCopy_tail
/-- info: 'Solidity.Backend.StorageOps.recursiveCopy_shortened' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursiveCopy_shortened
/-- info: 'Solidity.Backend.StorageOps.RecursiveCopyControls.varying_runtime_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms varying_runtime_depth
/-- info: 'Solidity.Backend.StorageOps.recursiveCopyAt_missing_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursiveCopyAt_missing_source
/-- info: 'Solidity.Backend.StorageOps.recursiveCopyAt_missing_destination' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursiveCopyAt_missing_destination
/-- info: 'Solidity.Backend.StorageOps.RecursiveCopyControls.mapping_all_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mapping_all_depth

private def wrapNodes (v : Nodes) : Value graph (.array (.array (.node z))) :=
  .array ⟨1,by decide⟩ ⟨1,by decide⟩ (by decide) (fun _ => .present v)

/-- All finite recursive suffix depths and independently varying runtime
widths: changed successful child0 and exact failed child1 share one operation. -/
theorem missing_outer_all_depth (ow nw : Nat → Index)
    (op : ∀ d, 0 < (ow d).val) (np : ∀ d, 0 < (nw d).val) (d : Nat) :
    (recursiveCopy (wrapNodes (tree ow true d)) (wrapNodes (tree nw false d))).find
      ((.cons (.index (⟨1,by decide⟩ : Index)) .nil : TypeGraph.Path graph (.array (.array (.node z))) (.array (.node z))).append (deep d)) = none ∧
    (wrapNodes (tree ow true d)).find
      ((.cons (.index zero) .nil : TypeGraph.Path graph (.array (.array (.node z))) (.array (.node z))).append (deep d)) = some (.prim true) ∧
    (recursiveCopy (wrapNodes (tree ow true d)) (wrapNodes (tree nw false d))).find
      ((.cons (.index zero) .nil : TypeGraph.Path graph (.array (.array (.node z))) (.array (.node z))).append (deep d)) = some (.prim false) := by
  have oldChild : (wrapNodes (tree ow true d)).find (.cons (.index zero) .nil) = some (tree ow true d) := rfl
  have newChild : (recursiveCopy (wrapNodes (tree ow true d)) (wrapNodes (tree nw false d))).find
      (.cons (.index zero) .nil) = some (recursiveCopy (tree ow true d) (tree nw false d)) := by
    rw [recursiveCopy_eq_overlay,recursiveCopy_eq_overlay]
    rfl
  have changed := varying_runtime_depth ow nw op np d
  refine ⟨?_,?_,?_⟩
  · rw [recursiveCopy_eq_overlay]
    exact AbsentRootQueries.find_suffix _ _ ⟨1,by decide⟩ (deep d) (by change max 1 1 ≤ 1; decide)
  · unfold Value.find
    rw [TypeGraph.Path.read_append]
    change ((wrapNodes (tree ow true d)).find (.cons (.index zero) .nil)).bind _ = _
    rw [oldChild]
    exact changed.1
  · unfold Value.find
    rw [TypeGraph.Path.read_append]
    change ((recursiveCopy (wrapNodes (tree ow true d)) (wrapNodes (tree nw false d))).find (.cons (.index zero) .nil)).bind _ = _
    rw [newChild]
    exact changed.2

/-- info: 'Solidity.Backend.StorageOps.RecursiveCopyControls.missing_outer_all_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms missing_outer_all_depth

end Solidity.Backend.StorageOps.RecursiveCopyControls
