import Solidity.Backend.StorageOps.MappingPaths

/-! Arbitrary-depth mapping preservation and operation-combination controls.
The copy controls test internal graph semantics; they do not admit otherwise
illegal whole assignments of mapping-containing source aggregates. -/

namespace Solidity.Backend.StorageOps.MappingControls

open TypeGraph

private def z : Fin 1 := ⟨0, by decide⟩
private def fs : List (Name × TypeGraph.Ty 1) :=
  [("flag", .prim .bool), ("children", .array (.node z)),
   ("memo", .mapping .bool (.prim .bool))]
private def graph : Schema 1 where
  origin := "v10-recursive-mapping-controls"
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
private def tree : Nat → Nodes
  | 0 => one (node true empty oldMemo)
  | d + 1 => one (node true (tree d) oldMemo)
private def memoPath : Nat → TypeGraph.Path graph
    (.array (.node z)) (.mapping .bool (.prim .bool))
  | 0 => .cons (.index zero) (.cons (.field (.there (.there .here))) .nil)
  | d + 1 => .cons (.index zero) (.cons (.field (.there .here)) (memoPath d))
private def memoKey : TypeGraph.Path graph (.mapping .bool (.prim .bool)) (.prim .bool) :=
  .cons (.key true) .nil
private def flag : TypeGraph.Path graph (.array (.node z)) (.prim .bool) :=
  .cons (.index zero) (.cons (.field .here) .nil)
private def child : TypeGraph.Path graph (.array (.node z)) (.array (.node z)) :=
  .cons (.index zero) (.cons (.field (.there .here)) .nil)

private theorem old_read (depth : Nat) : (tree depth).find (memoPath depth) = some oldMemo := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    change (tree depth).find (memoPath depth) = some oldMemo
    exact ih

/-- Every finite recursive depth has an inhabited mapping lookup preserved
through deletion, despite crossing arrays whose live length becomes zero. -/
theorem clear_recursive_mapping (depth : Nat) :
    (tree depth).clear.find (memoPath depth) = some oldMemo := by
  rw [clear_mapping_read]
  exact old_read depth

/-- The retained-path law does not assert a live read after deletion. -/
theorem clear_invalidates_live (depth : Nat) :
    (memoPath depth).readLive Value.dflt (tree depth).clear = none := by
  cases depth <;> rfl

/-- Clearing the live tail by runtime copy retains mappings at arbitrary
recursive depths; no fixed-depth fixture stands in for this theorem. -/
theorem copy_recursive_mapping (depth : Nat) :
    (copyArray (tree depth) empty).find (memoPath depth) = some oldMemo :=
  copyArray_mapping_read (tree depth) empty (memoPath depth) oldMemo (old_read depth)

/-- A concrete delete operation and its appended recursive suffix inhabit
all premises of the generic delete-composition theorem. -/
theorem delete_composition (depth : Nat) :
    (tree depth).clear.find (TypeGraph.Path.nil.append (memoPath depth)) = some oldMemo :=
  delete_mapping_below (tree depth) (tree depth).clear .nil (memoPath depth)
    (tree depth) oldMemo rfl (old_read depth) rfl

private def differentSource : Nodes := one (node false empty srcMemo)
/-- Scalar contents really copy, while destination mapping contents survive. -/
theorem copies_scalar : (copyArray (tree 2) differentSource).observe flag = some false := rfl

theorem keeps_destination_mapping :
    (copyArray (tree 2) differentSource).observe ((memoPath 0).append memoKey) = some true := rfl

/-- Failed old reads cannot be preserved unconditionally: copying may make a
new mapping path readable. This discriminates the generic copy law's premise. -/
theorem newly_allocated_mapping : empty.find (memoPath 0) = none ∧
    (copyArray empty differentSource).find (memoPath 0) =
      some (Value.dflt (.mapping .bool (.prim .bool))) := by
  constructor <;> rfl

private def overlapping : Nodes := one (node true differentSource oldMemo)
/-- Overlap captures the child array before overwriting its ancestor. -/
theorem overlap_copies_scalar : (copyAt overlapping .nil child).map
    (fun result => result.observe flag) = some (some false) := rfl
/-- The descendant source mapping is false; the ancestor destination mapping
is true. Copy must keep the latter even across ancestor/descendant overlap. -/
theorem overlap_keeps_mapping : (copyAt overlapping .nil child).map
    (fun result => result.observe ((memoPath 0).append memoKey)) = some (some true) := rfl

/-- Inhabited application of the path-level mapping composition law. -/
theorem overlap_mapping_composition :
    (copyArray overlapping differentSource).find (TypeGraph.Path.nil.append (memoPath 0)) = some oldMemo :=
  copyAt_mapping_below overlapping (copyArray overlapping differentSource)
    .nil child (memoPath 0) overlapping differentSource oldMemo rfl rfl rfl rfl

/-- info: 'Solidity.Backend.StorageOps.clear_mapping_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms clear_mapping_read
/-- info: 'Solidity.Backend.StorageOps.overlay_mapping_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms overlay_mapping_read
/-- info: 'Solidity.Backend.StorageOps.delete_mapping_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms delete_mapping_below
/-- info: 'Solidity.Backend.StorageOps.copyAt_mapping_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms copyAt_mapping_below
/-- info: 'Solidity.Backend.StorageOps.MappingControls.clear_recursive_mapping' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms clear_recursive_mapping

end Solidity.Backend.StorageOps.MappingControls
