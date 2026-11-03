import Solidity.Backend.StorageOps.RecursiveSelfCopy

/-! Uncapped recursive/runtime witnesses and complete ordered graph controls.
No numeric representation, ordinary Source admission or world rollback claim. -/
namespace Solidity.Backend.StorageOps.RecursiveSelfCopyControls
open TypeGraph
private def z : Fin 1 := ⟨0, by decide⟩
private def fs : List (Name × TypeGraph.Ty 1) :=
  [("flag", .prim .bool), ("children", .array (.node z)),
   ("memo", .mapping .bool (.prim .bool))]
private def graph : Schema 1 where
  origin := "v10-recursive-self-operation-controls"
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


/-- Every finite depth and every runtime width, including empty levels. -/
theorem all_runtime_depth (width : Nat → Index) (d : Nat) :
 recursiveCopy (tree width true d) (tree width true d)=tree width true d := by
 simp only [RecursiveSelfCopy.value_self]

/-- Positive widths inhabit a payload read at the selected arbitrary depth. -/
theorem varying_readback (width : Nat → Index) (positive : ∀ d,0 < (width d).val) (d : Nat) :
 (recursiveCopy (tree width true d) (tree width true d)).find (deep d)=some (.prim true) := by
 rw [RecursiveSelfCopy.value_self]
 induction d with
 | zero =>
   simp only [tree,deep,Value.find,TypeGraph.Path.read,TypeGraph.Step.get,zero,
    dif_pos (positive 0),Slot.getD,Option.bind_some,node,Fields.get]
 | succ d ih =>
   simp only [tree,deep,Value.find,TypeGraph.Path.read,TypeGraph.Step.get,zero,
    dif_pos (positive (d+1)),Slot.getD,Option.bind_some,node,Fields.get]
   exact ih

private def idx (n : Nat) (h : n < 2^256 := by decide) : Index := ⟨n,h⟩
private def ids : List Index := [idx 0,idx 1,idx 2,idx 3]
private def flag (i : Index) : TypeGraph.Path graph (.array (.node z)) (.prim .bool) :=
 .cons (.index i) (.cons (.field .here) .nil)
private def child (i : Index) : TypeGraph.Path graph (.array (.node z)) (.array (.node z)) :=
 .cons (.index i) (.cons (.field (.there .here)) .nil)
private def memo (i : Index) : TypeGraph.Path graph (.array (.node z)) (.mapping .bool (.prim .bool)) :=
 .cons (.index i) (.cons (.field (.there (.there .here))) .nil)
private def memoFlag (i : Index) : TypeGraph.Path graph (.array (.node z)) (.prim .bool) :=
 (memo i).append (.cons (.key true) .nil)
private def inner : Nodes := .array ⟨2,by decide⟩ (idx 1) (by decide)
 (fun _ => .present (node true empty oldMemo))
private def shadowInner : Nodes := .array ⟨2,by decide⟩ (idx 2) (by decide)
 (fun _ => .present (node false empty oldMemo))
private def slots : Fin 3 → Slot graph (.node z) := fun i =>
 if i.val=1 then .absent else .present (node true (if i.val=0 then inner else shadowInner) oldMemo)
private def old : Nodes := .array ⟨3,by decide⟩ (idx 1) (by decide) slots
private def copied : Nodes := recursiveCopy old old
private def view (v : Nodes) :=
 (v.length.val,v.extent.val,ids.map (fun i => v.observe (flag i)),
 ids.map (fun i => (v.find (child i)).map (fun c => c.length.val)),
 ids.map (fun i => v.observe (memoFlag i)))
private def two : FixedSize := ⟨2,by decide⟩
private def mixed : Value graph (.fixed (.array (.node z)) two) :=
 .fixed (fun i => if i.val=0 then .present old else .absent)
private def fixedView (v : Value graph (.fixed (.array (.node z)) two)) :=
 ([idx 0,idx 1,idx 2].map (fun i => (v.find (.cons (.fixed i) .nil)).map view))

/-- Complete ordered views include live, absent, retained and malformed reads. -/
theorem ordered_observations :
 (view old,view copied,fixedView mixed,fixedView (recursiveCopy mixed mixed))=
 ((1,3,[some true,some false,some true,none],[some 1,some 0,some 2,none],[some true,some false,some true,none]),
  (1,3,[some true,some false,some true,none],[some 1,some 0,some 2,none],[some true,some false,some true,none]),
  [some (1,3,[some true,some false,some true,none],[some 1,some 0,some 2,none],[some true,some false,some true,none]),some (0,0,[none,none,none,none],[none,none,none,none],[none,none,none,none]),none],
  [some (1,3,[some true,some false,some true,none],[some 1,some 0,some 2,none],[some true,some false,some true,none]),some (0,0,[none,none,none,none],[none,none,none,none],[none,none,none,none]),none]) := by
 rw [RecursiveSelfCopy.value_self]
 rfl

/-- Actual raw absent/present slots are preserved, including the fixed wrapper. -/
theorem slot_presence :
 copied.slots ⟨1,by decide⟩=.absent ∧
 copied.slots ⟨2,by decide⟩=.present (node true shadowInner oldMemo) ∧
 recursiveSlot (Slot.absent : Slot graph (.array (.node z))) .absent=.absent ∧
 recursiveCopyAt old .nil .nil=some old := by
 simp only [copied]
 exact ⟨rfl,rfl,rfl,by simp only [recursiveCopyAt,Value.find,TypeGraph.Path.read,Option.bind_eq_bind,Option.bind_some,RecursiveSelfCopy.value_self,Value.save,TypeGraph.Path.save]⟩

private def nested : TypeGraph.Path graph (.array (.node z)) (.prim .bool) :=
 (child (idx 0)).append (flag (idx 1))
/-- Retained nested/outer aliases stay readable but are not relabeled live. -/
theorem retained_aliases :
 (old.observe nested,copied.observe nested,old.observe (flag (idx 2)),copied.observe (flag (idx 2)),
 nested.readLive Value.dflt old,nested.readLive Value.dflt copied,
 (flag (idx 2)).readLive Value.dflt old,(flag (idx 2)).readLive Value.dflt copied)=
 (some true,some true,some true,some true,none,none,none,none) := by rfl

private def wrongExtent : Nodes := .array ⟨3,by decide⟩ (idx 1) (by decide)
 (fun i => recursiveClearSlot (slots i))
/-- An incorrect whole-extent clear destroys the older shadow, unlike self-copy. -/
theorem wrong_extent :
 (view wrongExtent,view (recursiveClear old),view copied)=
 ((1,3,[some false,some false,some false,none],[some 0,some 0,some 0,none],[some true,some false,some true,none]),
  (0,3,[some false,some false,some true,none],[some 0,some 0,some 2,none],[some true,some false,some true,none]),
  (1,3,[some true,some false,some true,none],[some 1,some 0,some 2,none],[some true,some false,some true,none])) ∧
 wrongExtent.observe (flag (idx 2))≠copied.observe (flag (idx 2)) := by
 exact ⟨rfl,by change (some false : Option Bool)≠some true; decide⟩

private def erased : Map := .mapping (fun _ => .absent)
private def wrongMapping : Option Nodes := old.save (memo (idx 0)) erased
/-- Actual erroneous mapping replacement, with COMPLETE resulting observations. -/
theorem wrong_mapping :
 wrongMapping.map view=some (1,3,[some true,some false,some true,none],[some 1,some 0,some 2,none],[some false,some false,some true,none]) ∧
 wrongMapping.bind (fun v => v.observe (memoFlag (idx 0)))≠copied.observe (memoFlag (idx 0)) := by
 exact ⟨rfl,by change (some false : Option Bool)≠some true; decide⟩

/-- Out-of-extent capture fails; recursive child identity is not a failure guard. -/
theorem malformed :
 old.find (child (idx 3))=none ∧ recursiveCopyAt old (child (idx 3)) (child (idx 3))=none := by
 exact ⟨rfl,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.RecursiveSelfCopyControls.all_runtime_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms all_runtime_depth
/-- info: 'Solidity.Backend.StorageOps.RecursiveSelfCopyControls.varying_readback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms varying_readback
/-- info: 'Solidity.Backend.StorageOps.RecursiveSelfCopyControls.ordered_observations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ordered_observations
/-- info: 'Solidity.Backend.StorageOps.RecursiveSelfCopyControls.slot_presence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms slot_presence
/-- info: 'Solidity.Backend.StorageOps.RecursiveSelfCopyControls.retained_aliases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms retained_aliases
/-- info: 'Solidity.Backend.StorageOps.RecursiveSelfCopyControls.wrong_extent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms wrong_extent
/-- info: 'Solidity.Backend.StorageOps.RecursiveSelfCopyControls.wrong_mapping' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms wrong_mapping
/-- info: 'Solidity.Backend.StorageOps.RecursiveSelfCopyControls.malformed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms malformed
end Solidity.Backend.StorageOps.RecursiveSelfCopyControls
