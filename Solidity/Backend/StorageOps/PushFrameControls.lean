import Solidity.Backend.StorageOps.PushFrames
import Solidity.Backend.StorageOps.CopyWriteControls

/-! Recursive runtime-query frames at every finite depth, varying live lengths,
and primitive same-target reset countercontrols. No numeric eager-loop claim. -/
namespace Solidity.Backend.StorageOps.PushFrameControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private abbrev RG := CopyWriteControls.recursiveGraph
private abbrev Nodes := Value RG (.array (.node 0))
private def ix (i : Fin 3) : Index := ⟨i.val,by have h := i.isLt; omega⟩
private def node (children : Nodes) : Value RG (.node 0) :=
  .node (Fields.set (Fields.set (fun {_} _ => Value.dflt _) .here (Value.prim (p := .bool) true)) (.there .here) children)
private def tree (width : Nat → Index) : Nat → Nodes
  | 0 => .array ⟨(width 0).val,by have h := (width 0).isLt; omega⟩ (width 0) (Nat.le_refl _) (fun _ => .present (node (Value.dflt _)))
  | d+1 => .array ⟨(width (d+1)).val,by have h := (width (d+1)).isLt; omega⟩ (width (d+1)) (Nat.le_refl _) (fun _ => .present (node (tree width d)))
private def deep : Nat → TypeGraph.Path RG (.array (.node 0)) (.prim .bool)
  | 0 => .cons (.index (ix 0)) (.cons (.field .here) .nil)
  | d+1 => .cons (.index (ix 0)) (.cons (.field (.there .here)) (deep d))
private theorem tree_read (width : Nat → Index) (positive : ∀ d, 0 < (width d).val) (d : Nat) :
    (tree width d).find (deep d) = some (.prim true) := by
  induction d with
  | zero =>
    simp only [tree,deep,ix,Fin.val_zero,Value.find,TypeGraph.Path.read,Step.get,dif_pos (positive 0),Slot.getD,
      Option.bind_some,node,Fields.get,Fields.set,Field.toNat,dif_neg (by decide : ¬ (0 = 1)),dif_pos True.intro]
    rfl
  | succ d ih =>
    simp only [tree,deep,ix,Fin.val_zero,Value.find,TypeGraph.Path.read,Step.get,dif_pos (positive (d+1)),Slot.getD,
      Option.bind_some,node,Fields.get,Fields.set,Field.toNat,dif_pos True.intro]
    exact ih
private def old (width : Nat → Index) (d : Nat) : Nodes :=
  .array ⟨2,by decide⟩ (ix 1) (by decide) (fun _ => .present (node (tree width d)))
private def result (width : Nat → Index) (d : Nat) : Nodes := (operationPush (old width d)).getD (old width d)
private def suffix (d : Nat) : Query RG (.node 0) := .word (.cons (.field (.there .here)) (deep d))

/-- Actual get/find operations and GENERAL other-index frame at every finite
recursive depth; every inner runtime live length varies independently. -/
theorem arbitrary_depth (width : Nat → Index) (positive : ∀ d, 0 < (width d).val) (d : Nat) :
    operationPush (old width d) = some (result width d) ∧
    ((suffix d).prefix (AggregatePopFrames.indexPath (ix 0))).read (old width d) = some (PrimTy.toWord (p := .bool) true) ∧
    ((suffix d).prefix (AggregatePopFrames.indexPath (ix 0))).read (result width d) = some (PrimTy.toWord (p := .bool) true) := by
  have before : ((suffix d).prefix (AggregatePopFrames.indexPath (ix 0))).read (old width d) = some (PrimTy.toWord (p := .bool) true) := by
    simp only [suffix,ix,Fin.val_zero,Query.prefix,AggregatePopFrames.indexPath,Query.read,Value.observe,Value.find,
      TypeGraph.Path.read_append,TypeGraph.Path.read,old,Step.get,dif_pos (by decide : 0 < 2),Slot.getD,
      Option.bind_some,node,Fields.get,Fields.set,Field.toNat,dif_pos True.intro]
    change (((tree width d).find (deep d)).map Value.head).map (PrimTy.toWord (p := .bool)) = some (PrimTy.toWord (p := .bool) true)
    rw [tree_read width positive d]
    rfl
  have frame := PushFrames.read_other (old width d) (result width d) rfl (ix 0) (by change (0 : Nat) ≠ 1; decide) (suffix d)
  exact ⟨rfl,before,frame.trans before⟩

private abbrev G := CopyDemandControls.graph
private def primOld : Value G (.array (.prim .bool)) := .array ⟨2,by decide⟩ (ix 1) (by decide) (fun _ => .present (.prim true))
private def primResult := (operationPush primOld).getD primOld
private def cell (i : Fin 3) : TypeGraph.Path G (.array (.prim .bool)) (.prim .bool) := .cons (.index (ix i)) .nil
private def view (v : Value G (.array (.prim .bool))) :=
  (v.length.val,v.extent.val,v.observe (cell 0),v.observe (cell 1),v.observe (cell 2),
    ((cell 0).readLive Value.dflt v).map Value.head,((cell 1).readLive Value.dflt v).map Value.head)

/-- Excluding the activated index is necessary: primitive push resets that
retained word. COMPLETE logical/raw/live observations discriminate same-target. -/
theorem same_target_negative : operationPush primOld = some primResult ∧
    (view primOld,view primResult) =
      ((1,2,some true,some true,none,some true,none),(2,2,some true,some false,none,some true,some false)) ∧
    primOld.observe (cell 1) ≠ primResult.observe (cell 1) := ⟨rfl,rfl,by change (some true : Option Bool) ≠ some false; decide⟩

/-- Actual generalized frame keeps the OTHER primitive cell, including a query
whose raw outcome fails. Neither adds a live or retained-extent requirement. -/
theorem primitive_frames :
    Step.get Value.dflt (.index (ix 0)) primResult = Step.get Value.dflt (.index (ix 0)) primOld ∧
    Step.get Value.dflt (.index (ix 2)) primResult = Step.get Value.dflt (.index (ix 2)) primOld :=
  ⟨PushFrames.get_other primOld primResult rfl (ix 0) (by decide),
   PushFrames.get_other primOld primResult rfl (ix 2) (by decide)⟩

private def flag (i : Fin 3) : Query RG (.array (.node 0)) := .word (.cons (.index (ix i)) (.cons (.field .here) .nil))
private def recursiveView (d : Nat) (v : Nodes) :=
  (v.length.val,v.extent.val,(flag 0).read v,(flag 1).read v,(flag 2).read v,
    ((suffix d).prefix (AggregatePopFrames.indexPath (ix 0))).read v,
    ((.cons (.index (ix 1)) (.cons (.field .here) .nil) : TypeGraph.Path RG (.array (.node 0)) (.prim .bool)).readLive Value.dflt v).map Value.head)

/-- COMPLETE ordered recursive fixture observations include both outer slots,
failing outside index, demanded deep leaf and retained-to-live alias. -/
theorem recursive_complete_observations (width : Nat → Index) (positive : ∀ d, 0 < (width d).val) (d : Nat) :
    (recursiveView d (old width d),recursiveView d (result width d)) =
    ((1,2,some (PrimTy.toWord (p := .bool) true),some (PrimTy.toWord (p := .bool) true),none,some (PrimTy.toWord (p := .bool) true),none),
     (2,2,some (PrimTy.toWord (p := .bool) true),some (PrimTy.toWord (p := .bool) true),none,some (PrimTy.toWord (p := .bool) true),some true)) := by
  obtain ⟨_,before,after⟩ := arbitrary_depth width positive d
  simp only [recursiveView,before,after]
  rfl
private def wrongOther : Value G (.array (.prim .bool)) := (primResult.save (cell 0) (.prim false)).getD primResult

/-- Actual wrong-target save is discriminated by COMPLETE existing primitive
raw/live observations. Source profile and correct operation stay unchanged. -/
theorem wrong_other_negative : primResult.save (cell 0) (.prim false) = some wrongOther ∧
    view wrongOther = (2,2,some false,some false,none,some false,some false) ∧
    primResult.observe (cell 0) ≠ wrongOther.observe (cell 0) :=
  ⟨rfl,rfl,by change (some true : Option Bool) ≠ some false; decide⟩

private def fixedSize : FixedSize := ⟨1,by decide⟩
private def fixedOld : Value G (.array (.fixed (.prim .bool) fixedSize)) :=
  .array ⟨1,by decide⟩ (ix 1) (by decide) (fun _ => .present (.fixed (fun _ => .present (.prim true))))
private def fixedResult := (operationPush fixedOld).getD fixedOld
private def fixedQuery (i : Fin 3) : Query G (.fixed (.prim .bool) fixedSize) := .word (.cons (.fixed (ix i)) .nil)
private def fixedView (v : Value G (.array (.fixed (.prim .bool) fixedSize))) :=
  (v.length.val,v.extent.val,((fixedQuery 0).prefix (AggregatePopFrames.indexPath (ix 0))).read v,
    ((fixedQuery 1).prefix (AggregatePopFrames.indexPath (ix 0))).read v,
    ((fixedQuery 0).prefix (AggregatePopFrames.indexPath (ix 2))).read v)

/-- A genuinely malformed fixed suffix keeps failure under the GENERAL frame.
Its unsupportedness is explicit; no numeric/owner evidence is manufactured. -/
theorem malformed_fixed_frame : operationPush fixedOld = some fixedResult ∧
    ((fixedQuery 1).prefix (AggregatePopFrames.indexPath (ix 0))).read fixedResult =
      ((fixedQuery 1).prefix (AggregatePopFrames.indexPath (ix 0))).read fixedOld ∧
    ¬ ((fixedQuery 1).prefix (AggregatePopFrames.indexPath (ix 0))).supported ∧
    (fixedView fixedOld,fixedView fixedResult) =
      ((1,1,some (PrimTy.toWord (p := .bool) true),none,none),(2,2,some (PrimTy.toWord (p := .bool) true),none,none)) := by
  refine ⟨rfl,PushFrames.read_other fixedOld fixedResult rfl (ix 0) (by decide) (fixedQuery 1),?_,rfl⟩
  change ¬ (0 < lmax ∧ (1 < 1 ∧ True))
  decide

/-- info: 'Solidity.Backend.StorageOps.PushFrameControls.arbitrary_depth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms arbitrary_depth
/-- info: 'Solidity.Backend.StorageOps.PushFrameControls.same_target_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms same_target_negative
/-- info: 'Solidity.Backend.StorageOps.PushFrameControls.primitive_frames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms primitive_frames
/-- info: 'Solidity.Backend.StorageOps.PushFrameControls.recursive_complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms recursive_complete_observations
/-- info: 'Solidity.Backend.StorageOps.PushFrameControls.wrong_other_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms wrong_other_negative
/-- info: 'Solidity.Backend.StorageOps.PushFrameControls.malformed_fixed_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms malformed_fixed_frame

end Solidity.Backend.StorageOps.PushFrameControls
