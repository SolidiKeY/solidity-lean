import Solidity.Backend.StorageOps.TargetFixedArrayTransport
import Solidity.Backend.StorageOps.FixedSnapshotFrames
import Solidity.Backend.StorageOps.FixedSnapshotRoot

/-! Inhabited fixed-span current-loop controls and an explicit snapshot hazard.
Shared logical headers can satisfy FiniteRun: they are not hash collisions.
No raw overlapping layout is claimed reachable in ordinary Source. -/
namespace Solidity.Backend.StorageOps.TargetFixedArrayCopyControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def graph : Schema 0 where
  origin := "v10-target-fixed-array-copy-controls"
  declId := fun i => nomatch i
  declId_injective := by intro i; exact Fin.elim0 i
  name := fun i => nomatch i
  fields := fun i => nomatch i
  rank := fun i => nomatch i
  nonempty := by intro i; exact Fin.elim0 i
  distinct := by intro i; exact Fin.elim0 i
  guarded := by intro i; exact Fin.elim0 i
private def span : FixedSize := ⟨2,by decide,by decide⟩
private def ix (i : Fin 4) : Index := ⟨i.val,by have bound := i.isLt; omega⟩
private def indices : List Index := [ix 0,ix 1,ix 2,ix 3]
private def w (i : Fin 32) : Semantics.Word := lengthWord i.val (by have bound := i.isLt; omega)
private def a : Value graph (.array (.prim .uint)) :=
  .array ⟨2,by decide⟩ ⟨1,by decide⟩ (by decide) (fun i => .present (.prim (if i.val = 0 then w 7 else w 8)))
private def b : Value graph (.array (.prim .uint)) :=
  .array ⟨2,by decide⟩ ⟨2,by decide⟩ (by decide) (fun i => .present (.prim (if i.val = 0 then w 9 else w 11)))
private def d : Value graph (.array (.prim .uint)) :=
  .array ⟨4,by decide⟩ ⟨3,by decide⟩ (by decide) (fun i => .present (.prim (if i.val = 0 then w 13 else if i.val = 1 then w 17 else if i.val = 2 then w 19 else w 23)))
private def source : Value graph (.fixed (.array (.prim .uint)) span) :=
  .fixed (fun i => if i.val = 0 then .present a else .present b)
private def old : Value graph (.fixed (.array (.prim .uint)) span) :=
  .fixed (fun i => if i.val = 0 then .present b else .present d)
private def result := old.overlay source
private def store : Store := fun l =>
  if l = .root 0 then w 1 else if l = .root 1 then w 2 else if l = .root 2 then w 3 else
  if l = .data (.root 0) 0 then w 7 else if l = .data (.root 0) 1 then w 8 else
  if l = .data (.root 1) 0 then w 9 else if l = .data (.root 1) 1 then w 11 else
  if l = .data (.root 2) 0 then w 13 else if l = .data (.root 2) 1 then w 17 else
  if l = .data (.root 2) 2 then w 19 else if l = .data (.root 2) 3 then w 23 else w 0
private def hash (p : Solidity.Storage.Pre) : Nat :=
  if p = .data 0 then 8 else if p = .data 1 then 16 else if p = .data 2 then 24 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0,.data 1,.data 2]
private def locations : List Solidity.Storage.Loc := [.root 0,.root 1,.root 2,
  .data (.root 0) 0,.data (.root 0) 1,.data (.root 0) 2,.data (.root 0) 3,
  .data (.root 1) 0,.data (.root 1) 1,.data (.root 1) 2,.data (.root 1) 3,
  .data (.root 2) 0,.data (.root 2) 1,.data (.root 2) 2,.data (.root 2) 3]
private def numeric : WordStore := fun k =>
  if k = 0 then w 1 else if k = 1 then w 2 else if k = 2 then w 3 else
  if k = 8 then w 7 else if k = 9 then w 8 else if k = 16 then w 9 else if k = 17 then w 11 else
  if k = 24 then w 13 else if k = 25 then w 17 else if k = 26 then w 19 else if k = 27 then w 23 else w 0
private theorem run : FiniteRun 64 4 3 hash preimages locations := by
  constructor
  · intro p; simp only [hash]; split <;> (first | decide | (split <;> (first | decide | (split <;> decide))))
  · decide
  · decide
  · decide
  · intro l member
    simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem initial : Transport 64 hash locations store numeric := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private def fitting : ∀ l ∈ locations, TargetOperations.KeysFit l := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
private def tail : List Evm.Word := [.val (TargetOperations.encodeWord (w 23)),.slot (.root 7)]
private def target : Evm.Machine :=
  { stack := tail,store := .ofFn (fun slot => (TargetOperations.encodeWord (store (Solidity.Storage.ofSlot slot))).val),
    mem := fun _ => .val (TargetOperations.encodeWord (w 31)),bal := fun _ => 13,bal₀ := fun _ => 17,
    self := ⟨5,by decide⟩,caller := ⟨7,by decide⟩,callvalue := ⟨11,by decide⟩,timestamp := ⟨19,by decide⟩,accepts := fun _ _ => false }
private theorem targetInitial : ∀ l (member : l ∈ locations),
    target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l) := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private def stage (n : Nat) := TargetFixedArrayCopy.prefixMachine target (.root 1) (.root 0) 0 n
private def targetSlots : List Evm.Slot := [.root 0,.root 1,.root 2,
  .data (.root 0) 0,.data (.root 0) 1,.data (.root 0) 2,.data (.root 0) 3,
  .data (.root 1) 0,.data (.root 1) 1,.data (.root 1) 2,.data (.root 1) 3,
  .data (.root 2) 0,.data (.root 2) 1,.data (.root 2) 2,.data (.root 2) 3]
private def targetView (m : Evm.Machine) := targetSlots.map (fun slot => m.store slot)
private def context (m : Evm.Machine) :=
  (m.stack,m.mem 0,m.bal ⟨0,by decide⟩,m.bal₀ ⟨0,by decide⟩,m.self,m.caller,m.callvalue,m.timestamp,m.accepts ⟨0,by decide⟩ ⟨0,by decide⟩)
private def firstNumeric := NumericTraversal.copy 64 hash (.root 1) (.root 0) numeric
private def secondNumeric := NumericTraversal.copy 64 hash (.root 2) (.root 1) firstNumeric
private def numericView (m : WordStore) :=
  [m 0,m 1,m 2,m 8,m 9,m 10,m 11,m 16,m 17,m 18,m 19,m 24,m 25,m 26,m 27]
private def lastHeader : Query graph (.fixed (.array (.prim .uint)) span) :=
  .length (TargetFixedArrayCopy.childPath span ⟨1,by decide⟩)
private def lastWord (i : Index) : Query graph (.fixed (.array (.prim .uint)) span) :=
  (PrimitivePop.elementQuery i).prefix (TargetFixedArrayCopy.childPath span ⟨1,by decide⟩)

private def path0 : TypeGraph.Path graph (.fixed (.array (.prim .uint)) span) (.array (.prim .uint)) := TargetFixedArrayCopy.childPath span ⟨0,by decide⟩
private def path1 : TypeGraph.Path graph (.fixed (.array (.prim .uint)) span) (.array (.prim .uint)) := TargetFixedArrayCopy.childPath span ⟨1,by decide⟩
private def queries : List (Query graph (.fixed (.array (.prim .uint)) span)) :=
  (PrimitivePop.queries indices).map (Query.prefix path0) ++ (PrimitivePop.queries indices).map (Query.prefix path1)

private theorem beforeA : Represented a (PrimitivePop.queries indices) (.root 0) store := by
  intro q member
  simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro observed found; change some (w 1) = some observed at found; cases found; rfl
  · refine ⟨⟨by change 0 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro observed found; change some (w 7) = some observed at found; cases found; rfl
  · refine ⟨⟨by change 1 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro observed found; change some (w 8) = some observed at found; cases found; rfl
  · refine ⟨⟨by change 2 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro observed found; change (none : Option Semantics.Word) = some observed at found; cases found
  · refine ⟨⟨by change 3 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro observed found; change (none : Option Semantics.Word) = some observed at found; cases found

private theorem beforeB : Represented b (PrimitivePop.queries indices) (.root 1) store := by
  intro q member
  simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro observed found; change some (w 2) = some observed at found; cases found; rfl
  · refine ⟨⟨by change 0 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro observed found; change some (w 9) = some observed at found; cases found; rfl
  · refine ⟨⟨by change 1 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro observed found; change some (w 11) = some observed at found; cases found; rfl
  · refine ⟨⟨by change 2 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro observed found; change (none : Option Semantics.Word) = some observed at found; cases found
  · refine ⟨⟨by change 3 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro observed found; change (none : Option Semantics.Word) = some observed at found; cases found

private theorem beforeD : Represented d (PrimitivePop.queries indices) (.root 2) store := by
  intro q member
  simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro observed found; change some (w 3) = some observed at found; cases found; rfl
  · refine ⟨⟨by change 0 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro observed found; change some (w 13) = some observed at found; cases found; rfl
  · refine ⟨⟨by change 1 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro observed found; change some (w 17) = some observed at found; cases found; rfl
  · refine ⟨⟨by change 2 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro observed found; change some (w 19) = some observed at found; cases found; rfl
  · refine ⟨⟨by change 3 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro observed found; change some (w 23) = some observed at found; cases found; rfl

private theorem beforeSource : Represented source queries (.root 0) store := by
  have first : Represented source ((PrimitivePop.queries indices).map (Query.prefix path0)) (.root 0) store :=
    Represented.prefix path0 (by rfl) (by change 0 < 2 ∧ True; decide) beforeA
  have second : Represented source ((PrimitivePop.queries indices).map (Query.prefix path1)) (.root 0) store :=
    Represented.prefix path1 (by rfl) (by change 1 < 2 ∧ True; decide) beforeB
  intro q member
  rcases List.mem_append.mp member with left | right
  · exact first q left
  · exact second q right
private theorem beforeDestination : Represented old queries (.root 1) store := by
  have first : Represented old ((PrimitivePop.queries indices).map (Query.prefix path0)) (.root 1) store :=
    Represented.prefix path0 (by rfl) (by change 0 < 2 ∧ True; decide) beforeB
  have second : Represented old ((PrimitivePop.queries indices).map (Query.prefix path1)) (.root 1) store :=
    Represented.prefix path1 (by rfl) (by change 1 < 2 ∧ True; decide) beforeD
  intro q member
  rcases List.mem_append.mp member with left | right
  · exact first q left
  · exact second q right

/-- Actual nested current loops execute and restart, but do NOT implement an
unrestricted cross-child snapshot law. This is not a hash-collision example. -/
theorem overlapping_current_source :
    FiniteRun 64 4 3 hash preimages locations ∧ Transport 64 hash locations store numeric ∧
    Represented source queries (.root 0) store ∧ Represented old queries (.root 1) store ∧
    (∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l)) ∧
    Evm.run (TargetFixedArrayCopy.code span (.root 1) (.root 0)) target = .ok (stage 2) 0 ∧
    Evm.run (TargetFixedArrayCopy.segment (.root 1) (.root 0) 1 1) (stage 1) = .ok (stage 2) 0 ∧
    (lastHeader.read result,(lastWord (ix 0)).read result,(lastWord (ix 1)).read result,(stage 2).store (.root 2)) =
      (some (w 2),some (w 9),some (w 11),1) := by
  exact ⟨run,initial,beforeSource,beforeDestination,targetInitial,TargetFixedArrayCopy.run_code _ _ _ _,
    TargetFixedArrayCopy.run_restart target (.root 1) (.root 0) 0 1 1,rfl⟩

/-- COMPLETE prefix/numeric/target/context observations preserve older23 while
future source1 is changed from header2/data9,11 to header1/data7,0. -/
theorem overlapping_current_ordered :
    (targetView target,targetView (stage 1),targetView (stage 2),numericView numeric,numericView firstNumeric,numericView secondNumeric,
      context target,context (stage 1),context (stage 2)) =
      ([1,2,3,7,8,0,0,9,11,0,0,13,17,19,23],
       [1,1,3,7,8,0,0,7,0,0,0,13,17,19,23],[1,1,1,7,8,0,0,7,0,0,0,7,0,0,23],
       [w 1,w 2,w 3,w 7,w 8,w 0,w 0,w 9,w 11,w 0,w 0,w 13,w 17,w 19,w 23],
       [w 1,w 1,w 3,w 7,w 8,w 0,w 0,w 7,w 0,w 0,w 0,w 13,w 17,w 19,w 23],
       [w 1,w 1,w 1,w 7,w 8,w 0,w 0,w 7,w 0,w 0,w 0,w 7,w 0,w 0,w 23],context target,context target,context target) := by
  rfl

/-- The missing snapshot precondition is discriminated by an ACTUAL generated
write at the exact future source header. No Source profile is restricted. -/
theorem overlapping_source_separation_fails :
    .root 1 ∈ TargetFixedArrayCopy.sourceReads target (.root 1) ∧
    .root 1 ∈ TargetFixedArrayCopy.touched target (.root 1) (.root 0) 0 1 ∧
    (stage 1).store (.root 1) ≠ target.store (.root 1) := by
  exact ⟨List.mem_cons_self,by decide,by decide⟩


private def selfStage (n : Nat) := TargetFixedArrayCopy.prefixMachine target (.root 0) (.root 0) 0 n
/-- A GOOD same-root alias runs both current child loops with different runtime
lengths1/2. All15 words and full nontrivial context remain unchanged. -/
theorem self_alias_current_prefix :
    Evm.run (TargetFixedArrayCopy.code span (.root 0) (.root 0)) target = .ok (selfStage 2) 0 ∧
    Evm.run (TargetFixedArrayCopy.segment (.root 0) (.root 0) 1 1) (selfStage 1) = .ok (selfStage 2) 0 ∧
    (targetView target,targetView (selfStage 1),targetView (selfStage 2),context (selfStage 2),
      lastHeader.read (source.overlay source),(selfStage 2).store (.root 1)) =
      ([1,2,3,7,8,0,0,9,11,0,0,13,17,19,23],[1,2,3,7,8,0,0,9,11,0,0,13,17,19,23],
       [1,2,3,7,8,0,0,9,11,0,0,13,17,19,23],context target,some (w 2),2) := by
  exact ⟨TargetFixedArrayCopy.run_code _ _ _ _,TargetFixedArrayCopy.run_restart target (.root 0) (.root 0) 0 1 1,rfl⟩

/-- Stable future current inputs are DERIVED from the exact generated set in
the self-alias run, contrasting the overlapping-current negative above. -/
theorem self_future_snapshot_inputs :
    (∀ l ∈ TargetFixedArrayCopy.sourceReads target (.root 1),
      l ∉ TargetFixedArrayCopy.touched target (.root 0) (.root 0) 0 1) ∧
    (selfStage 1).store (.root 1) = target.store (.root 1) ∧
    (∀ j < target.store (.root 1), (selfStage 1).store (.data (.root 1) j) = target.store (.data (.root 1) j)) ∧
    (targetView target,targetView (selfStage 1),context (selfStage 1)) =
      ([1,2,3,7,8,0,0,9,11,0,0,13,17,19,23],[1,2,3,7,8,0,0,9,11,0,0,13,17,19,23],context target) := by
  have reads : TargetFixedArrayCopy.sourceReads target (.root 1) = [.root 1,.data (.root 1) 0,.data (.root 1) 1] := rfl
  have writes : TargetFixedArrayCopy.touched target (.root 0) (.root 0) 0 1 = [.root 0,.data (.root 0) 0] := rfl
  have separate : ∀ l ∈ TargetFixedArrayCopy.sourceReads target (.root 1),
      l ∉ TargetFixedArrayCopy.touched target (.root 0) (.root 0) 0 1 := by
    intro l member
    rw [reads] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> rw [writes] <;> decide
  have stable := TargetFixedArrayCopy.source_snapshot_inputs target (.root 0) (.root 0) (.root 1) 0 1 separate
  exact ⟨separate,stable.1,stable.2,rfl⟩

private def empty : Value graph (.fixed (.array (.prim .uint)) span) := .fixed (fun _ => .absent)
/-- The existing defaulted child operation is reused, not a new value/state.
Absent fixed children default to zero-length arrays; source shadow8 is ignored. -/
theorem defaulted_fixed_children :
    (TargetFixedArrayCopy.child empty ⟨0,by decide⟩).length.val = 0 ∧
    (TargetFixedArrayCopy.child (empty.overlay source) ⟨0,by decide⟩).length.val = 1 ∧
    (TargetFixedArrayCopy.child (empty.overlay source) ⟨0,by decide⟩).extent.val = 1 ∧
    (TargetFixedArrayCopy.child (empty.overlay source) ⟨1,by decide⟩).length.val = 2 ∧
    lastHeader.read (empty.overlay source) = some (w 2) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- The generated frame law applies to an actual older shadow23, outside both
current child write sets, without asserting zero for a failed source query. -/
theorem older_shadow_generated_frame :
    .data (.root 2) 3 ∉ TargetFixedArrayCopy.touched target (.root 1) (.root 0) 0 2 ∧
    (stage 2).store (.data (.root 2) 3) = target.store (.data (.root 2) 3) ∧
    (target.store (.data (.root 2) 3),(stage 1).store (.data (.root 2) 3),(stage 2).store (.data (.root 2) 3)) = (23,23,23) := by
  have untouched : .data (.root 2) 3 ∉ TargetFixedArrayCopy.touched target (.root 1) (.root 0) 0 2 := by decide
  exact ⟨untouched,TargetFixedArrayCopy.prefix_outside target (.root 1) (.root 0) (.data (.root 2) 3) 0 2 untouched,rfl⟩

/-- The unrestricted evolving-current sequence has an actual all-covered-cell
finite-run transport certificate EVEN in the snapshot-discriminating overlap.
It certifies the executed sequence, not the different independent root overlay. -/
theorem overlapping_prefix_transport :
    Transport 64 hash locations (TargetFixedArrayTransport.stores store (.root 1) (.root 0) 0 2)
      (TargetFixedArrayTransport.numerics 64 hash numeric (.root 1) (.root 0) 0 2) ∧
    (∀ l (member : l ∈ locations), (stage 2).store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (TargetFixedArrayTransport.stores store (.root 1) (.root 0) 0 2 l)) := by
  apply TargetFixedArrayTransport.prefix_transport run (.root 1) (.root 0) (by trivial) (by trivial)
    store numeric target 0 2 initial fitting targetInitial
  · intro k inside
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl <;> decide
  · intro k inside j live
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl
    · change j < 1 at live
      have same : j = 0 := by omega
      subst j; decide
    · change j < 1 at live
      have same : j = 0 := by omega
      subst j; decide
  · intro k inside j visited
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl
    · change j < 2 at visited
      have casesJ : j = 0 ∨ j = 1 := by omega
      rcases casesJ with rfl | rfl <;> decide
    · change j < 3 at visited
      have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases casesJ with rfl | rfl | rfl <;> decide

/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopyControls.overlapping_current_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms overlapping_current_source
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopyControls.overlapping_current_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms overlapping_current_ordered
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopyControls.overlapping_source_separation_fails' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms overlapping_source_separation_fails
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopyControls.self_alias_current_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms self_alias_current_prefix
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopyControls.self_future_snapshot_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms self_future_snapshot_inputs
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopyControls.defaulted_fixed_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms defaulted_fixed_children
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopyControls.older_shadow_generated_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms older_shadow_generated_frame
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopyControls.overlapping_prefix_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms overlapping_prefix_transport

/-- Actual first child changes old9,11 to snapshot7,0 with a derived
independent ROOT selected owner certificate and complete prefix observations.
Later overlapping child remains the discriminating counterexample above. -/
theorem first_child_snapshot_owner :
    Transport 64 hash locations (TargetFixedArrayTransport.stores store (.root 1) (.root 0) 0 1) firstNumeric ∧
    Represented result ((PrimitivePop.queries indices).map (Query.prefix path0)) (.root 1)
      (TargetFixedArrayTransport.stores store (.root 1) (.root 0) 0 1) ∧
    (targetView (stage 1),numericView firstNumeric,context (stage 1),
      (Query.length path0).read result,(PrimitivePop.elementQuery (ix 0)).prefix path0 |>.read result) =
      ([1,1,3,7,8,0,0,7,0,0,0,13,17,19,23],
       [w 1,w 1,w 3,w 7,w 8,w 0,w 0,w 7,w 0,w 0,w 0,w 13,w 17,w 19,w 23],context target,some (w 1),some (w 7)) := by
  have actual := FixedSnapshotFrames.snapshot_child run old source ⟨0,by decide⟩ indices (.root 1) (.root 0)
    (by trivial) (by trivial) store numeric target initial fitting targetInitial
    (fun q member => beforeDestination q (List.mem_append.mpr (Or.inl member)))
    (fun q member => beforeSource q (List.mem_append.mpr (Or.inl member)))
    (by intro k inside
        change k < 1 at inside
        have same : k = 0 := by omega
        subst k
        decide)
    (by intro k inside j live
        change k < 1 at inside
        have same : k = 0 := by omega
        subst k
        change j < 1 at live
        have sameJ : j = 0 := by omega
        subst j
        decide)
    (by intro k inside j visited
        change k < 1 at inside
        have same : k = 0 := by omega
        subst k
        change j < 2 at visited
        have casesJ : j = 0 ∨ j = 1 := by omega
        rcases casesJ with rfl | rfl <;> decide)
    (by intro j member; simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide)
    (by intro j member; simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide)
    (by intro j live
        change j < 1 at live
        have same : j = 0 := by omega
        subst j
        decide)
    (by intro j visited; change j < 2 at visited; have casesJ : j = 0 ∨ j = 1 := by omega
        rcases casesJ with rfl | rfl <;> decide)
    (by intro q member op impossible; cases impossible)
    (by intro q member op impossible; cases impossible)
  exact ⟨actual.1,actual.2,rfl⟩

private theorem second_self_apart :
    ∀ q ∈ PrimitivePop.queries (G := graph) (p := .uint) indices,
      ∀ op ∈ FixedSnapshotFrames.log store (.root 0) (.root 0) 0 1, q.location (.root 1) ≠ op.1 := by
  have writes : FixedSnapshotFrames.log store (.root 0) (.root 0) 0 1 =
      [(.data (.root 0) 0,w 7),(.root 0,w 1)] := rfl
  intro q member op inside
  rw [writes] at inside
  simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
  rcases member with rfl | rfl | rfl | rfl | rfl <;> rcases inside with rfl | rfl <;> decide

/-- A later-child PUBLIC snapshot application has a genuinely NONEMPTY earlier
write log. Its exact separations are independently proved over actual writes;
all target words/context and selected root readbacks are retained. -/
theorem later_child_snapshot_owner :
    FixedSnapshotFrames.log store (.root 0) (.root 0) 0 1 ≠ [] ∧
    Transport 64 hash locations (TargetFixedArrayTransport.stores store (.root 0) (.root 0) 0 2)
      (TargetFixedArrayTransport.numerics 64 hash numeric (.root 0) (.root 0) 0 2) ∧
    Represented (source.overlay source) ((PrimitivePop.queries indices).map (Query.prefix path1)) (.root 0)
      (TargetFixedArrayTransport.stores store (.root 0) (.root 0) 0 2) ∧
    (targetView (selfStage 1),targetView (selfStage 2),context (selfStage 2),lastHeader.read (source.overlay source),
      (lastWord (ix 0)).read (source.overlay source),(lastWord (ix 1)).read (source.overlay source)) =
      ([1,2,3,7,8,0,0,9,11,0,0,13,17,19,23],[1,2,3,7,8,0,0,9,11,0,0,13,17,19,23],context target,some (w 2),some (w 9),some (w 11)) := by
  have actual := FixedSnapshotFrames.snapshot_child run source source ⟨1,by decide⟩ indices (.root 0) (.root 0)
    (by trivial) (by trivial) store numeric target initial fitting targetInitial
    (fun q member => beforeSource q (List.mem_append.mpr (Or.inr member)))
    (fun q member => beforeSource q (List.mem_append.mpr (Or.inr member)))
    (by intro k inside
        change k < 2 at inside
        have casesK : k = 0 ∨ k = 1 := by omega
        rcases casesK with rfl | rfl <;> decide)
    (by intro k inside j live
        change k < 2 at inside
        have casesK : k = 0 ∨ k = 1 := by omega
        rcases casesK with rfl | rfl
        · change j < 1 at live
          have same : j = 0 := by omega
          subst j; decide
        · change j < 2 at live
          have casesJ : j = 0 ∨ j = 1 := by omega
          rcases casesJ with rfl | rfl <;> decide)
    (by intro k inside j visited
        change k < 2 at inside
        have casesK : k = 0 ∨ k = 1 := by omega
        rcases casesK with rfl | rfl
        · change j < 1 at visited
          have same : j = 0 := by omega
          subst j; decide
        · change j < 2 at visited
          have casesJ : j = 0 ∨ j = 1 := by omega
          rcases casesJ with rfl | rfl <;> decide)
    (by intro j member; simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide)
    (by intro j member; simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide)
    (by intro j live
        change j < 2 at live
        have casesJ : j = 0 ∨ j = 1 := by omega
        rcases casesJ with rfl | rfl <;> decide)
    (by intro j visited
        change j < 2 at visited
        have casesJ : j = 0 ∨ j = 1 := by omega
        rcases casesJ with rfl | rfl <;> decide)
    second_self_apart second_self_apart
  exact ⟨by decide,actual.1,actual.2,rfl⟩

/-- The independently correct first snapshot child remains represented after
all later ACTUAL writes, even though the overlapping second child is wrong.
This distinguishes a processed-child frame from whole-root snapshot closure. -/
theorem processed_child_snapshot_frame :
    Represented result ((PrimitivePop.queries indices).map (Query.prefix path0)) (.root 1)
      (TargetFixedArrayTransport.stores store (.root 1) (.root 0) 0 2) ∧
    (targetView (stage 2),numericView secondNumeric,context (stage 2),
      (Query.length path0).read result,((PrimitivePop.elementQuery (ix 0)).prefix path0).read result,
      lastHeader.read result,(stage 2).store (.root 2)) =
      ([1,1,1,7,8,0,0,7,0,0,0,7,0,0,23],
       [w 1,w 1,w 1,w 7,w 8,w 0,w 0,w 7,w 0,w 0,w 0,w 7,w 0,w 0,w 23],context target,
       some (w 1),some (w 7),some (w 2),1) := by
  have writes : FixedSnapshotFrames.log (TargetFixedArrayTransport.stores store (.root 1) (.root 0) 0 1)
      (.root 1) (.root 0) 1 1 =
      [(.data (.root 2) 0,w 7),(.data (.root 2) 1,w 0),(.data (.root 2) 2,w 0),(.root 2,w 1)] := rfl
  have apart : ∀ q ∈ PrimitivePop.queries (G := graph) (p := .uint) indices,
      ∀ op ∈ FixedSnapshotFrames.log (TargetFixedArrayTransport.stores store (.root 1) (.root 0) 0 1)
        (.root 1) (.root 0) 1 1, q.location (.root 1) ≠ op.1 := by
    intro q member op inside
    rw [writes] at inside
    simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases member with rfl | rfl | rfl | rfl | rfl <;> rcases inside with rfl | rfl | rfl | rfl <;> decide
  have framed := FixedSnapshotFrames.represented_suffix result _ (.root 1) store (.root 1) (.root 0) 0 1 1
    first_child_snapshot_owner.2.1 (by
      intro q member op inside
      obtain ⟨suffix,suffixMember,rfl⟩ := List.mem_map.mp member
      rw [Query.location_prefix]
      exact apart suffix suffixMember op inside)
  exact ⟨framed,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopyControls.first_child_snapshot_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms first_child_snapshot_owner
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopyControls.later_child_snapshot_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms later_child_snapshot_owner
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopyControls.processed_child_snapshot_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms processed_child_snapshot_frame

private theorem two_cases (i : Fin span.val) : i = ⟨0,by decide⟩ ∨ i = ⟨1,by decide⟩ := by
  have bound := i.isLt
  change i.val < 2 at bound
  have casesI : i.val = 0 ∨ i.val = 1 := by omega
  rcases casesI with zero | one
  · exact Or.inl (Fin.ext zero)
  · exact Or.inr (Fin.ext one)
private def lowerStore (k : Nat) := TargetFixedArrayTransport.stores store (.root 0) (.root 1) 0 k
private def lowerNumeric (k : Nat) := TargetFixedArrayTransport.numerics 64 hash numeric (.root 0) (.root 1) 0 k
private def lowerStage (k : Nat) := TargetFixedArrayCopy.prefixMachine target (.root 0) (.root 1) 0 k
private def lowerResult := source.overlay old
private theorem lower_prior_log : FixedSnapshotFrames.log store (.root 0) (.root 1) 0 1 =
    [(.data (.root 0) 0,w 9),(.data (.root 0) 1,w 11),(.root 0,w 2)] := rfl
private theorem lower_suffix_log : FixedSnapshotFrames.log (lowerStore 1) (.root 0) (.root 1) 1 1 =
    [(.data (.root 1) 0,w 13),(.data (.root 1) 1,w 17),(.data (.root 1) 2,w 19),(.root 1,w 3)] := rfl
private theorem lower_before_dst (i : Fin span.val) :
    Represented source ((PrimitivePop.queries indices).map (Query.prefix (TargetFixedArrayCopy.childPath span i))) (.root 0) store := by
  rcases two_cases i with rfl | rfl
  · exact fun q member => beforeSource q (List.mem_append.mpr (Or.inl member))
  · exact fun q member => beforeSource q (List.mem_append.mpr (Or.inr member))
private theorem lower_before_src (i : Fin span.val) :
    Represented old ((PrimitivePop.queries indices).map (Query.prefix (TargetFixedArrayCopy.childPath span i))) (.root 1) store := by
  rcases two_cases i with rfl | rfl
  · exact fun q member => beforeDestination q (List.mem_append.mpr (Or.inl member))
  · exact fun q member => beforeDestination q (List.mem_append.mpr (Or.inr member))
private theorem lower_prior_apart (i : Fin span.val) :
    ∀ q ∈ PrimitivePop.queries (G := graph) (p := .uint) indices,
      ∀ op ∈ FixedSnapshotFrames.log store (.root 0) (.root 1) 0 i.val,
      q.location ((Solidity.Storage.Loc.root 0).add i.val) ≠ op.1 ∧
      q.location ((Solidity.Storage.Loc.root 1).add i.val) ≠ op.1 := by
  rcases two_cases i with rfl | rfl
  · intro q member op impossible; cases impossible
  · intro q member op inside
    rw [lower_prior_log] at inside
    simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases member with rfl | rfl | rfl | rfl | rfl <;> rcases inside with rfl | rfl | rfl <;> decide
private theorem lower_suffix_apart (i : Fin span.val) :
    ∀ q ∈ (PrimitivePop.queries indices).map (Query.prefix (TargetFixedArrayCopy.childPath (G := graph) (p := .uint) span i)),
      ∀ op ∈ FixedSnapshotFrames.log (lowerStore (i.val+1)) (.root 0) (.root 1) (i.val+1) (span.val-(i.val+1)),
      q.location (.root 0) ≠ op.1 := by
  rcases two_cases i with rfl | rfl
  · intro q member op inside
    change op ∈ FixedSnapshotFrames.log (lowerStore 1) (.root 0) (.root 1) 1 1 at inside
    rw [lower_suffix_log] at inside
    obtain ⟨suffix,suffixMember,rfl⟩ := List.mem_map.mp member
    rw [Query.location_prefix]
    simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at suffixMember
    simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases suffixMember with rfl | rfl | rfl | rfl | rfl <;> rcases inside with rfl | rfl | rfl | rfl <;> decide
  · intro q member op impossible; cases impossible

/-- TWO changed child outputs, runtime lengths1/2/3 and actual nonempty
prefix/suffix logs instantiate the whole selected ROOT snapshot theorem.
Logical overlap is safe in this direction; no blanket alias exclusion. -/
theorem lower_whole_snapshot :
    Evm.run (TargetFixedArrayCopy.code span (.root 0) (.root 1)) target = .ok (lowerStage 2) 0 ∧
    Represented lowerResult (FixedSnapshotRoot.queries span indices) (.root 0) (lowerStore 2) ∧
    Transport 64 hash locations (lowerStore 2) (lowerNumeric 2) ∧
    (∀ l (member : l ∈ locations), (lowerStage 2).store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (lowerStore 2 l)) := by
  apply FixedSnapshotRoot.complete run source old indices (.root 0) (.root 1) (by trivial) (by trivial)
    store numeric target initial fitting targetInitial lower_before_dst lower_before_src
  · intro k inside
    change k < 2 at inside
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl <;> decide
  · intro k inside j live
    change k < 2 at inside
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl
    · change j < 2 at live
      have casesJ : j = 0 ∨ j = 1 := by omega
      rcases casesJ with rfl | rfl <;> decide
    · change j < 3 at live
      have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases casesJ with rfl | rfl | rfl <;> decide
  · intro k inside j visited
    change k < 2 at inside
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl
    · change j < 2 at visited
      have casesJ : j = 0 ∨ j = 1 := by omega
      rcases casesJ with rfl | rfl <;> decide
    · change j < 3 at visited
      have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases casesJ with rfl | rfl | rfl <;> decide
  · intro i j member
    rcases two_cases i with rfl | rfl <;>
      simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl | rfl | rfl <;> decide
  · intro i j member
    rcases two_cases i with rfl | rfl <;>
      simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl | rfl | rfl <;> decide
  · intro i j live
    rcases two_cases i with rfl | rfl
    · change j < 2 at live
      have casesJ : j = 0 ∨ j = 1 := by omega
      rcases casesJ with rfl | rfl <;> decide
    · change j < 3 at live
      have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases casesJ with rfl | rfl | rfl <;> decide
  · intro i j visited
    rcases two_cases i with rfl | rfl
    · change j < 2 at visited
      have casesJ : j = 0 ∨ j = 1 := by omega
      rcases casesJ with rfl | rfl <;> decide
    · change j < 3 at visited
      have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases casesJ with rfl | rfl | rfl <;> decide
  · intro i q member op inside; exact (lower_prior_apart i q member op inside).1
  · intro i q member op inside; exact (lower_prior_apart i q member op inside).2
  · exact lower_suffix_apart

/-- COMPLETE physical/symbolic/context observations, both changed children,
newly live old shadow8→11 and ignored source older23 are all discriminated. -/
theorem lower_whole_ordered :
    (targetView target,targetView (lowerStage 1),targetView (lowerStage 2),numericView numeric,numericView (lowerNumeric 1),numericView (lowerNumeric 2),
      context target,context (lowerStage 1),context (lowerStage 2),
      (Query.length path0).read lowerResult,((PrimitivePop.elementQuery (ix 0)).prefix path0).read lowerResult,
      ((PrimitivePop.elementQuery (ix 1)).prefix path0).read lowerResult,lastHeader.read lowerResult,
      (lastWord (ix 0)).read lowerResult,(lastWord (ix 1)).read lowerResult,(lastWord (ix 2)).read lowerResult,(lastWord (ix 3)).read lowerResult) =
      ([1,2,3,7,8,0,0,9,11,0,0,13,17,19,23],[2,2,3,9,11,0,0,9,11,0,0,13,17,19,23],
       [2,3,3,9,11,0,0,13,17,19,0,13,17,19,23],
       [w 1,w 2,w 3,w 7,w 8,w 0,w 0,w 9,w 11,w 0,w 0,w 13,w 17,w 19,w 23],
       [w 2,w 2,w 3,w 9,w 11,w 0,w 0,w 9,w 11,w 0,w 0,w 13,w 17,w 19,w 23],
       [w 2,w 3,w 3,w 9,w 11,w 0,w 0,w 13,w 17,w 19,w 0,w 13,w 17,w 19,w 23],
       context target,context target,context target,some (w 2),some (w 9),some (w 11),some (w 3),some (w 13),some (w 17),some (w 19),none) := by rfl

/-- The opposite direction violates an ACTUAL earlier-source query/write
condition and fails the PUBLIC whole selected independent snapshot relation. -/
theorem upper_whole_snapshot_negative :
    (∃ op ∈ FixedSnapshotFrames.log store (.root 1) (.root 0) 0 1,
      (Query.length (G := graph) (E := .prim .uint) .nil).location (.root 1) = op.1) ∧
    ¬ Represented result (FixedSnapshotRoot.queries span indices) (.root 1)
      (TargetFixedArrayTransport.stores store (.root 1) (.root 0) 0 2) := by
  constructor
  · exact ⟨(.root 1,w 1),by decide,rfl⟩
  · intro represented
    have member : lastHeader ∈ FixedSnapshotRoot.queries (G := graph) (p := .uint) span indices := by
      apply List.mem_flatMap.mpr
      exact ⟨⟨1,by decide⟩,by decide,List.mem_map.mpr ⟨.length .nil,List.mem_cons_self,rfl⟩⟩
    have observed := (represented lastHeader member).2.2 (w 2) (by rfl)
    change w 1 = w 2 at observed
    exact (by decide : w 1 ≠ w 2) observed

/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopyControls.lower_whole_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms lower_whole_snapshot
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopyControls.lower_whole_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms lower_whole_ordered
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopyControls.upper_whole_snapshot_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms upper_whole_snapshot_negative

end Solidity.Backend.StorageOps.TargetFixedArrayCopyControls
