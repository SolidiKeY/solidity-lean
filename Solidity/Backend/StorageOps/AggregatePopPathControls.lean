import Solidity.Backend.StorageOps.AggregatePopPaths
import Solidity.Backend.StorageOps.AggregatePopFrameControls
import Solidity.Backend.StorageOps.PrefixLaws

/-! Actual arbitrary finite outer-prefix operations, independent old owner
witnesses and complete original observations. Prefixes add zero physical offsets;
this does not claim arbitrary recursive heap numeric realization. -/
namespace Solidity.Backend.StorageOps.AggregatePopPathControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open AggregatePopFrames AggregatePopPaths
private abbrev G := CopyDemandControls.graph
private abbrev Inner := CopyDemandControls.Inner
private abbrev Outer := CopyDemandControls.Outer
private def ix (i : Fin 4) : Index := ⟨i.val,by have h := i.isLt; omega⟩
private def word (i : Fin 4) : Query G Inner := .word (.cons (.index (ix i)) .nil)
private def leaf (i j : Fin 4) : Query G Outer := .word (.cons (.index (ix i)) (.cons (.index (ix j)) .nil))
private def header (i : Fin 4) : Query G Outer := .length (.cons (.index (ix i)) .nil)
private def selected : List (Query G Inner) := [word 0,word 1,word 2,.length .nil]
private def groups : List (Index × List (Query G Inner)) :=
  [(ix 0,selected),(ix 2,[word 0,.length .nil]),(ix 3,[word 0])]
private def popped : Value G Outer := (recursivePop CopyDemandControls.old).getD CopyDemandControls.old
private noncomputable def final : WordStore := (AggregatePop.updates CopyDemandControls.old CopyDemandControls.root).foldl
  (fun w op => writeWord w (op.1.word 128 CopyDemandControls.hash) op.2) CopyDemandControls.machine
private noncomputable def after : Store := (AggregatePop.updates CopyDemandControls.old CopyDemandControls.root).foldl
  (fun w op => write w op.1 op.2) CopyDemandControls.store
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def zero : Semantics.Word := ClearDemands.zero
private def two : Semantics.Word := lengthWord 2 (by decide)
private def seven : Semantics.Word := ⟨7,by decide⟩
private theorem targetBefore : Represented CopyDemandControls.old (AggregatePop.queries CopyDemandControls.old selected)
    CopyDemandControls.root CopyDemandControls.store := by
  intro q member
  change q ∈ [.length .nil,leaf 1 0,leaf 1 1,leaf 1 2,header 1] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (simp only [leaf,header,Query.supported,PathSupported,StepSupported]; decide)
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (intro value observed; change some one = some value at observed; cases observed; rfl)
    | (intro value observed; change some two = some value at observed; cases observed; rfl)
private theorem contextBefore : Represented CopyDemandControls.old (contexts groups)
    CopyDemandControls.root CopyDemandControls.store := by
  intro q member
  change q ∈ [leaf 0 0,leaf 0 1,leaf 0 2,header 0,leaf 2 0,header 2,leaf 3 0] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (simp only [leaf,header,Query.supported,PathSupported,StepSupported]; decide)
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (intro value observed; change some one = some value at observed; cases observed; rfl)
    | (intro value observed; change some two = some value at observed; cases observed; rfl)
    | (intro value observed; change (none : Option Semantics.Word) = some value at observed; cases observed)
private theorem targetCovered : ∀ q ∈ selected,
    q.location (AggregatePop.childBase CopyDemandControls.old CopyDemandControls.root) ∈ CopyDemandControls.locations := by
  intro q member
  simp only [selected,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide
private theorem contextCovered : ∀ q ∈ contexts groups, q.location CopyDemandControls.root ∈ CopyDemandControls.locations := by
  intro q member
  change q ∈ [leaf 0 0,leaf 0 1,leaf 0 2,header 0,leaf 2 0,header 2,leaf 3 0] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem written : ∀ q ∈ ClearDemands.slotDemands (AggregatePop.lastSlot CopyDemandControls.old),
    q.location (AggregatePop.childBase CopyDemandControls.old CopyDemandControls.root) ∈ CopyDemandControls.locations := by
  intro q member
  change q ∈ [word 0,word 1,.length .nil] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> decide
private theorem separated : ∀ q ∈ selected, ∀ d ∈ ClearDemands.slotDemands (AggregatePop.lastSlot CopyDemandControls.old),
    d.location (AggregatePop.childBase CopyDemandControls.old CopyDemandControls.root) =
      q.location (AggregatePop.childBase CopyDemandControls.old CopyDemandControls.root) → d = q := by
  intro q member d generated same
  simp only [selected,List.mem_cons,List.not_mem_nil,or_false] at member
  change d ∈ [word 0,word 1,.length .nil] at generated
  simp only [List.mem_cons,List.not_mem_nil,or_false] at generated
  rcases member with rfl | rfl | rfl | rfl <;> rcases generated with rfl | rfl | rfl
  all_goals first | rfl | cases same
private theorem headerSeparated : ∀ q ∈ selected,
    q.location (AggregatePop.childBase CopyDemandControls.old CopyDemandControls.root) ≠ CopyDemandControls.root := by
  intro q member
  simp only [selected,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide
private theorem otherIndices : ∀ group ∈ groups, group.1.val ≠ CopyDemandControls.old.length.val - 1 := by
  intro group member
  simp only [groups,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> decide
private theorem noAlias : ∀ q ∈ contexts groups, ∀ op ∈ AggregatePop.updates CopyDemandControls.old CopyDemandControls.root,
    q.location CopyDemandControls.root ≠ op.1 := by
  intro q member op generated same
  change q ∈ [leaf 0 0,leaf 0 1,leaf 0 2,header 0,leaf 2 0,header 2,leaf 3 0] at member
  change op ∈ [(leaf 1 0 |>.location CopyDemandControls.root,zero),(leaf 1 1 |>.location CopyDemandControls.root,zero),
    (header 1 |>.location CopyDemandControls.root,zero),(CopyDemandControls.root,one)] at generated
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member generated
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases generated with rfl | rfl | rfl | rfl <;> cases same


private def oneSize : FixedSize := ⟨1,by decide⟩
private def wrapTy : Nat → TypeGraph.Ty 0
  | 0 => Outer
  | d+1 => .fixed (wrapTy d) oneSize
private def wrap : (d : Nat) → Value G Outer → Value G (wrapTy d)
  | 0,v => v
  | d+1,v => .fixed (fun _ => .present (wrap d v))
private def pre : (d : Nat) → TypeGraph.Path G (wrapTy d) Outer
  | 0 => .nil
  | d+1 => .cons (.fixed ⟨0,by decide⟩) (pre d)
private theorem found (d : Nat) (v : Value G Outer) : (wrap d v).find (pre d) = some v := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change (wrap d v).find (pre d) = some v
    exact ih
private theorem supported (d : Nat) : PathSupported (pre d) := by
  induction d with
  | zero => exact True.intro
  | succ d ih =>
    change (0 < oneSize.val) ∧ PathSupported (pre d)
    exact ⟨by decide,ih⟩
private theorem location (d : Nat) (l : Solidity.Storage.Loc) : pathLoc (pre d) l = l := by
  induction d generalizing l with
  | zero => rfl
  | succ d ih =>
    change pathLoc (pre d) (l.add (0 * inlineSize G (wrapTy d))) = l
    rw [ih,Nat.zero_mul]
    cases l <;> rfl
private def observedQueries := AggregatePop.queries CopyDemandControls.old selected ++ contexts groups
private theorem arrayBefore : Represented CopyDemandControls.old observedQueries CopyDemandControls.root CopyDemandControls.store := by
  intro q member
  rcases List.mem_append.mp member with target | context
  · exact targetBefore q target
  · exact contextBefore q context
private theorem rootBefore (d : Nat) : Represented (wrap d CopyDemandControls.old)
    (observedQueries.map (Query.prefix (pre d))) CopyDemandControls.root CopyDemandControls.store := by
  apply Represented.prefix (pre d) (found d CopyDemandControls.old) (supported d)
  simpa only [location] using arrayBefore

/-- At EVERY finite outer-prefix depth, actual capture/pop/save succeeds and
ALL selected root observations agree with the SAME actual numeric operation. -/
theorem every_prefix (d : Nat) : ∃ result : Value G (wrapTy d),
    popAt (wrap d CopyDemandControls.old) (pre d) = some result ∧ result.find (pre d) = some popped ∧
    Represented result (observedQueries.map (Query.prefix (pre d))) CopyDemandControls.root after ∧
    Transport 128 CopyDemandControls.hash CopyDemandControls.locations after final := by
  obtain ⟨result,saved⟩ := prefix_save_exists (pre d) (wrap d CopyDemandControls.old) CopyDemandControls.old popped
    (found d CopyDemandControls.old)
  have actual : popAt (wrap d CopyDemandControls.old) (pre d) = some result := by
    simp only [popAt,modifyAt,Option.bind_eq_bind,found,Option.bind_some]
    change (recursivePop CopyDemandControls.old).bind (fun child => (wrap d CopyDemandControls.old).save (pre d) child) = _
    have changed : recursivePop CopyDemandControls.old = some popped := rfl
    rw [changed]
    exact saved
  obtain ⟨child,numeric,changed,readback,executed,represented,transported⟩ := complete_at
    (wrap d CopyDemandControls.old) result (pre d) CopyDemandControls.old (found d CopyDemandControls.old) actual selected groups
    CopyDemandControls.root CopyDemandControls.store CopyDemandControls.machine CopyDemandControls.run
    (rootBefore d) (fun _ _ => rfl) (by simpa only [location] using (show CopyDemandControls.root ∈ CopyDemandControls.locations by decide))
    (by simpa only [location] using targetCovered) (by simpa only [location] using contextCovered)
    (by simpa only [location] using written) (by simpa only [location] using separated)
    (by simpa only [location] using headerSeparated) otherIndices (by simpa only [location] using noAlias)
  have childEqual : child = popped := Option.some.inj (changed.symm.trans (show recursivePop CopyDemandControls.old = some popped from rfl))
  subst child
  simp only [location] at executed represented transported
  have expected : AggregatePop.execute (N := 128) CopyDemandControls.old CopyDemandControls.hash CopyDemandControls.root
      CopyDemandControls.machine = some final := rfl
  have numericEqual := Option.some.inj (executed.symm.trans expected)
  subst numeric
  exact ⟨result,actual,readback,represented,transported⟩

private def allQueries := CopyDemandControls.demands ++ CopyDemandControls.queries
private def rootView (d : Nat) (v : Value G (wrapTy d)) := allQueries.map (fun q => (q.prefix (pre d)).read v)
private def arrayView (v : Value G Outer) := allQueries.map (fun q => q.read v)
private theorem view_focus (d : Nat) (root : Value G (wrapTy d)) (child : Value G Outer)
    (read : root.find (pre d) = some child) : rootView d root = arrayView child := by
  apply List.map_congr_left
  intro q member
  exact Query.read_prefix root child (pre d) q read

/-- COMPLETE12/18 observations at every prefix depth, in the ORIGINAL order;
no old control or expected verdict is weakened. -/
theorem complete_observations (d : Nat) : ∃ result : Value G (wrapTy d),
    popAt (wrap d CopyDemandControls.old) (pre d) = some result ∧
    (rootView d (wrap d CopyDemandControls.old),rootView d result,
      CopyDemandControls.numericView CopyDemandControls.machine,CopyDemandControls.numericView final) =
    ([some one,some one,some two,some one,some one,some two,some two,some one,some one,some one,some two,none],
     [some one,some one,some two,some zero,some zero,some zero,some one,some one,some one,some one,some two,none],
     (two,two,two,two,one,one,one,one,one,one,one,one,one,seven,one,one,zero,seven),
     (one,two,zero,two,one,one,one,zero,zero,one,one,one,one,seven,one,one,zero,seven)) := by
  obtain ⟨result,actual,readback,_,_⟩ := every_prefix d
  refine ⟨result,actual,?_⟩
  rw [view_focus d _ _ (found d CopyDemandControls.old),view_focus d _ _ readback]
  exact AggregatePopControls.complete_observations

/-- The actual successful root operation exposes its existing capture/save
facts through the generic operation certificate. -/
theorem captured_operation (d : Nat) : ∃ result old child,
    popAt (wrap d CopyDemandControls.old) (pre d) = some result ∧
    (wrap d CopyDemandControls.old).find (pre d) = some old ∧ recursivePop old = some child ∧
    (wrap d CopyDemandControls.old).save (pre d) child = some result ∧ result.find (pre d) = some child := by
  obtain ⟨result,actual,_,_,_⟩ := every_prefix d
  obtain ⟨old,child,read,changed,saved,readback⟩ := captured _ _ _ actual
  exact ⟨result,old,child,actual,read,changed,saved,readback⟩

/-- Same code and shape, wrong current header: without OLD owner agreement the
numeric operation can fail while the actual captured root operation succeeds. -/
theorem changed_header_negative (d : Nat) : ∃ result,
    popAt (wrap d CopyDemandControls.old) (pre d) = some result ∧
    AggregatePop.execute (N := 128) CopyDemandControls.old CopyDemandControls.hash CopyDemandControls.root
      (writeWord CopyDemandControls.machine 0 zero) = none := by
  obtain ⟨result,actual,_,_,_⟩ := every_prefix d
  exact ⟨result,actual,rfl⟩

/-- Malformed nonempty fixed prefix fails capture; its raw numeric word is one.
This does NOT implement or claim numeric path-validation failure/rollback. -/
theorem malformed_capture :
    (wrap 1 CopyDemandControls.old).find (.cons (.fixed (ix 1)) .nil) = none ∧
    popAt (wrap 1 CopyDemandControls.old) (.cons (.fixed (ix 1)) .nil) = none ∧
    CopyDemandControls.machine 1 = one := ⟨rfl,rfl,rfl⟩


private def emptyRetained : Value G Outer :=
  .array ⟨3,by decide⟩ ⟨0,by decide⟩ (by decide) CopyDemandControls.old.slots
private def emptyMachine : WordStore := writeWord CopyDemandControls.machine 0 zero
private def emptyStore : Store := fun l => emptyMachine (l.word 128 CopyDemandControls.hash)
private theorem emptyBefore (d : Nat) : Represented (wrap d emptyRetained)
    (([.length .nil] : List (Query G Outer)).map (Query.prefix (pre d))) CopyDemandControls.root emptyStore := by
  apply Represented.prefix (pre d) (found d emptyRetained) (supported d)
  simp only [location]
  intro q member
  have same := List.mem_singleton.mp member
  subst q
  refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
  intro value observed
  change some zero = some value at observed
  cases observed
  rfl

/-- General failure_at is inhabited at EVERY prefix depth for empty arrays
with populated retained slots. It relates Option outcomes, not world rollback. -/
theorem empty_failure (d : Nat) :
    AggregatePop.execute (N := 128) emptyRetained CopyDemandControls.hash CopyDemandControls.root emptyMachine = none ∧
    popAt (wrap d emptyRetained) (pre d) = none := by
  have matched := failure_at (wrap d emptyRetained) (pre d) emptyRetained (found d emptyRetained)
    CopyDemandControls.root emptyStore emptyMachine CopyDemandControls.hash CopyDemandControls.locations
    (emptyBefore d) (fun _ _ => rfl) (by simpa only [location] using (show CopyDemandControls.root ∈ CopyDemandControls.locations by decide))
  have failed : AggregatePop.execute (N := 128) emptyRetained CopyDemandControls.hash CopyDemandControls.root emptyMachine = none := rfl
  refine ⟨failed,matched.mp ?_⟩
  simpa only [location] using failed

/-- COMPLETE initial empty-retained fixture observations. Failure returns no
postvalue; this does not reinterpret None as any world/store rollback result. -/
theorem empty_observations (d : Nat) :
    (rootView d (wrap d emptyRetained),CopyDemandControls.numericView emptyMachine) =
    ([some one,some one,some two,some one,some one,some two,some zero,some one,some one,some one,some two,none],
     (zero,two,two,two,one,one,one,one,one,one,one,one,one,seven,one,one,zero,seven)) := by
  rw [view_focus d _ _ (found d emptyRetained)]
  rfl

/-- info: 'Solidity.Backend.StorageOps.AggregatePopPathControls.every_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms every_prefix
/-- info: 'Solidity.Backend.StorageOps.AggregatePopPathControls.complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_observations
/-- info: 'Solidity.Backend.StorageOps.AggregatePopPathControls.captured_operation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms captured_operation
/-- info: 'Solidity.Backend.StorageOps.AggregatePopPathControls.changed_header_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms changed_header_negative
/-- info: 'Solidity.Backend.StorageOps.AggregatePopPathControls.malformed_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms malformed_capture
/-- info: 'Solidity.Backend.StorageOps.AggregatePopPathControls.empty_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_failure
/-- info: 'Solidity.Backend.StorageOps.AggregatePopPathControls.empty_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_observations
end Solidity.Backend.StorageOps.AggregatePopPathControls
