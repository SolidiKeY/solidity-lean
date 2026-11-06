import Solidity.Backend.StorageOps.RecursiveRepeatCopy

/-! Same-captured-snapshot repeat controls, not an overlapping source re-read
law. Existing graph operations are executed directly; no target/world claim. -/
namespace Solidity.Backend.StorageOps.RecursiveRepeatCopyControls
open TypeGraph
private def z : Fin 1 := ⟨0, by decide⟩
private def fs : List (Name × TypeGraph.Ty 1) :=
  [("flag", .prim .bool), ("children", .array (.node z)),
   ("memo", .mapping .bool (.prim .bool))]
private def graph : Schema 1 where
  origin := "v10-repeat-operation-controls"
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


/-- All finite depths and independent old/source runtime widths, including zero. -/
theorem varying_runtime_depth (ow nw : Nat → Index) (d : Nat) :
 recursiveCopy (recursiveCopy (tree ow true d) (tree nw false d)) (tree nw false d)=
 recursiveCopy (tree ow true d) (tree nw false d) := by
 simp only [RecursiveRepeatCopy.value_repeat]

/-- Inhabited changed readbacks at arbitrary depth; the repeat retains the NEW payload. -/
theorem changed_depth (ow nw : Nat → Index)
 (op : ∀ d,0 < (ow d).val) (np : ∀ d,0 < (nw d).val) (d : Nat) :
 (tree ow true d).find (deep d)=some (.prim true) ∧
 (recursiveCopy (tree ow true d) (tree nw false d)).find (deep d)=some (.prim false) ∧
 (recursiveCopy (recursiveCopy (tree ow true d) (tree nw false d)) (tree nw false d)).find (deep d)=some (.prim false) := by
 rw [RecursiveRepeatCopy.value_repeat]
 suffices result : (tree ow true d).find (deep d)=some (.prim true) ∧
  (recursiveCopy (tree ow true d) (tree nw false d)).find (deep d)=some (.prim false) from
  ⟨result.1,result.2,result.2⟩
 rw [recursiveCopy_eq_overlay]
 induction d with
 | zero =>
   simp only [tree,deep,Value.find,TypeGraph.Path.read,TypeGraph.Step.get,Value.overlay,zero,
    dif_pos (op 0),dif_pos (np 0),dif_pos (show 0 < max (ow 0).val (nw 0).val by have h:=op 0; omega),Slot.overlay,Slot.getD,Option.bind_some,node,Fields.get]
   exact ⟨True.intro,True.intro⟩
 | succ d ih =>
   simp only [tree,deep,Value.find,TypeGraph.Path.read,TypeGraph.Step.get,Value.overlay,zero,
    dif_pos (op (d+1)),dif_pos (np (d+1)),dif_pos (show 0 < max (ow (d+1)).val (nw (d+1)).val by have h:=op (d+1); omega),Slot.overlay,Slot.getD,Option.bind_some,node,Fields.get]
   exact ih

private def idx (n : Nat) (h : n < 2^256 := by decide) : Index := ⟨n,h⟩
private def ids : List Index := [idx 0,idx 1,idx 2,idx 3,idx 4]
private def flag (i : Index) : TypeGraph.Path graph (.array (.node z)) (.prim .bool) :=
 .cons (.index i) (.cons (.field .here) .nil)
private def child (i : Index) : TypeGraph.Path graph (.array (.node z)) (.array (.node z)) :=
 .cons (.index i) (.cons (.field (.there .here)) .nil)
private def memo (i : Index) : TypeGraph.Path graph (.array (.node z)) (.prim .bool) :=
 .cons (.index i) (.cons (.field (.there (.there .here))) (.cons (.key true) .nil))
private def inner : Nodes := one (node true empty oldMemo)
private def old : Nodes := .array ⟨4,by decide⟩ (idx 3) (by decide)
 (fun _ => .present (node true inner oldMemo))
private def src : Nodes := .array ⟨2,by decide⟩ (idx 2) (by decide)
 (fun i => if i.val=0 then .present (node false empty srcMemo) else .absent)
private def once : Nodes := recursiveCopy old src
private def twice : Nodes := recursiveCopy once src
private def view (v : Nodes) :=
 (v.length.val,v.extent.val,ids.map (fun i => v.observe (flag i)),
 ids.map (fun i => (v.find (child i)).map (fun c => c.length.val)),
 ids.map (fun i => v.observe (memo i)))
private def two : FixedSize := ⟨2,by decide⟩
private def wrap (v : Nodes) : Value graph (.fixed (.array (.node z)) two) :=
 .fixed (fun i => if i.val=0 then .present v else .absent)
private def wrappedView (v : Value graph (.fixed (.array (.node z)) two)) :=
 ([idx 0,idx 1,idx 2].map (fun i => (v.find (.cons (.fixed i) .nil)).map view))

/-- Complete OLD/source/once/twice views, not only the selected changed cell. -/
theorem ordered_states : (view old,view src,view once,view twice)=
 ((3,4,[some true,some true,some true,some true,none],[some 1,some 1,some 1,some 1,none],[some true,some true,some true,some true,none]),
  (2,2,[some false,some false,none,none,none],[some 0,some 0,none,none,none],[some false,some false,none,none,none]),
  (2,4,[some false,some false,some false,some true,none],[some 0,some 0,some 0,some 1,none],[some true,some true,some true,some true,none]),
  (2,4,[some false,some false,some false,some true,none],[some 0,some 0,some 0,some 1,none],[some true,some true,some true,some true,none])) := by rfl

/-- Fixed slots and absent-source recursive clearing are separate concrete branches. -/
theorem fixed_and_absent :
 wrappedView (recursiveCopy (wrap old) (wrap src))=
  [some (view once),some (0,0,[none,none,none,none,none],[none,none,none,none,none],[none,none,none,none,none]),none] ∧
 wrappedView (recursiveCopy (recursiveCopy (wrap old) (wrap src)) (wrap src))=
  [some (view once),some (0,0,[none,none,none,none,none],[none,none,none,none,none],[none,none,none,none,none]),none] ∧
 view ((recursiveSlot (.present old) .absent).getD empty)=
  (0,4,[some false,some false,some false,some true,none],[some 0,some 0,some 0,some 1,none],[some true,some true,some true,some true,none]) ∧
 recursiveSlot (recursiveSlot (.present old) .absent) .absent=recursiveSlot (.present old) .absent := by
 rw [RecursiveRepeatCopy.value_repeat]
 have fixedOnce : wrappedView (recursiveCopy (wrap old) (wrap src))=
  [some (view once),some (0,0,[none,none,none,none,none],[none,none,none,none,none],[none,none,none,none,none]),none] := by rfl
 exact ⟨fixedOnce,fixedOnce,rfl,RecursiveRepeatCopy.slot_repeat _ _⟩

/-- Absent live source clears the destination slot without deallocating it;
shortened live tail stays cleared; older shadow and mappings stay exact. -/
theorem slots_and_aliases :
 src.slots ⟨1,by decide⟩=.absent ∧
 once.slots ⟨1,by decide⟩=recursiveClearSlot (old.slots ⟨1,by decide⟩) ∧
 twice.slots ⟨2,by decide⟩=recursiveClearSlot (old.slots ⟨2,by decide⟩) ∧
 twice.slots ⟨3,by decide⟩=old.slots ⟨3,by decide⟩ ∧
 (once.observe (flag (idx 3)),twice.observe (flag (idx 3)),
  (flag (idx 3)).readLive Value.dflt once,(flag (idx 3)).readLive Value.dflt twice)=
 (some true,some true,none,none) := by
 exact ⟨rfl,rfl,rfl,rfl,rfl⟩

private def overlapping : Nodes := one (node true (one (node false empty srcMemo)) oldMemo)
private def captured : Nodes := one (node false empty srcMemo)
private def first : Nodes := recursiveCopy overlapping captured
private def repeated : Nodes := recursiveCopy first captured
private def wrong : Option Nodes := do
 let result ← recursiveCopyAt overlapping .nil (child zero)
 recursiveCopyAt result .nil (child zero)

/-- Actual descendant capture and save, then repeat the original immutable snapshot. -/
theorem captured_overlap :
 overlapping.find (child zero)=some captured ∧
 recursiveCopyAt overlapping .nil (child zero)=some first ∧
 (view overlapping,view first,view repeated)=
 ((1,1,[some true,none,none,none,none],[some 1,none,none,none,none],[some true,none,none,none,none]),
  (1,1,[some false,none,none,none,none],[some 0,none,none,none,none],[some true,none,none,none,none]),
  (1,1,[some false,none,none,none,none],[some 0,none,none,none,none],[some true,none,none,none,none])) := by
 exact ⟨rfl,rfl,rfl⟩

/-- Re-reading the CURRENT overlapping source changes the header to zero.
The producer deliberately does not identify that operation with fixed capture. -/
theorem wrong_reread :
 wrong.map view=some (0,1,[some false,none,none,none,none],[some 0,none,none,none,none],[some true,none,none,none,none]) ∧
 (wrong.map (fun v => v.length.val))≠some repeated.length.val := by
 exact ⟨rfl,by change (some 0 : Option Nat)≠some 1; decide⟩

/-- A malformed captured path remains Option failure; no world rollback is inferred. -/
theorem malformed :
 old.find (child (idx 4))=none ∧
 recursiveCopyAt old .nil (child (idx 4))=none ∧
 recursiveCopyAt old (child (idx 4)) .nil=none := by
 exact ⟨rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.RecursiveRepeatCopyControls.varying_runtime_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms varying_runtime_depth
/-- info: 'Solidity.Backend.StorageOps.RecursiveRepeatCopyControls.changed_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms changed_depth
/-- info: 'Solidity.Backend.StorageOps.RecursiveRepeatCopyControls.ordered_states' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ordered_states
/-- info: 'Solidity.Backend.StorageOps.RecursiveRepeatCopyControls.fixed_and_absent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fixed_and_absent
/-- info: 'Solidity.Backend.StorageOps.RecursiveRepeatCopyControls.slots_and_aliases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms slots_and_aliases
/-- info: 'Solidity.Backend.StorageOps.RecursiveRepeatCopyControls.captured_overlap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms captured_overlap
/-- info: 'Solidity.Backend.StorageOps.RecursiveRepeatCopyControls.wrong_reread' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms wrong_reread
/-- info: 'Solidity.Backend.StorageOps.RecursiveRepeatCopyControls.malformed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms malformed
end Solidity.Backend.StorageOps.RecursiveRepeatCopyControls
