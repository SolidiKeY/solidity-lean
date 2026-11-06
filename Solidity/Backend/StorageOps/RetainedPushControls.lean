import Solidity.Backend.StorageOps.RetainedPush
import Solidity.Backend.StorageOps.TargetHeaderPush
import Solidity.Backend.StorageOps.CopyDemandControls

/-! Retained aggregate reuse is exercised separately from fresh allocation.
Complete old observations and actual numeric header execution are retained. -/
namespace Solidity.Backend.StorageOps.RetainedPushControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open RetainedPush
private abbrev G := CopyDemandControls.graph
private abbrev Inner := CopyDemandControls.Inner
private abbrev Outer := CopyDemandControls.Outer
private def ix (i : Fin 4) : Index := ⟨i.val,by have h := i.isLt; omega⟩
private def word (i : Fin 4) : Query G Inner := .word (.cons (.index (ix i)) .nil)
private def leaf (i j : Fin 4) : Query G Outer := .word (.cons (.index (ix i)) (.cons (.index (ix j)) .nil))
private def header (i : Fin 4) : Query G Outer := .length (.cons (.index (ix i)) .nil)
private def zero : Semantics.Word := ClearDemands.zero
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def two : Semantics.Word := lengthWord 2 (by decide)
private def three : Semantics.Word := lengthWord 3 (by decide)
private def seven : Semantics.Word := ⟨7,by decide⟩
private def groupQueries : List (Query G Inner) := [word 0,word 1,.length .nil,word 2]
private def groups : List (Index × List (Query G Inner)) :=
  [(ix 0,groupQueries),(ix 1,groupQueries),(ix 2,[word 0,.length .nil]),(ix 3,[word 0])]
private def pushed : Value G Outer := (operationPush CopyDemandControls.old).getD CopyDemandControls.old
private def final : WordStore := writeWord CopyDemandControls.machine 0 three
private def after : Store := write CopyDemandControls.store CopyDemandControls.root three
private theorem before : Represented CopyDemandControls.old (requested groups) CopyDemandControls.root CopyDemandControls.store := by
  intro q member
  change q ∈ [.length .nil,leaf 0 0,leaf 0 1,header 0,leaf 0 2,leaf 1 0,leaf 1 1,header 1,leaf 1 2,leaf 2 0,header 2,leaf 3 0] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (simp only [leaf,header,Query.supported,PathSupported,StepSupported]; decide)
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (intro value observed; change some one = some value at observed; cases observed; rfl)
    | (intro value observed; change some two = some value at observed; cases observed; rfl)
    | (intro value observed; change (none : Option Semantics.Word) = some value at observed; cases observed)
private theorem covered : ∀ q ∈ requested groups, q.location CopyDemandControls.root ∈ CopyDemandControls.locations := by
  intro q member
  change q ∈ [.length .nil,leaf 0 0,leaf 0 1,header 0,leaf 0 2,leaf 1 0,leaf 1 1,header 1,leaf 1 2,leaf 2 0,header 2,leaf 3 0] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- GENERAL retained aggregate certificate, with OLD owner and GOOD run facts
independently inhabited. Reused nonzero children are not spuriously cleared. -/
theorem nested_certificate : LifecycleNumeric.pushHeader 128 CopyDemandControls.hash CopyDemandControls.root
    CopyDemandControls.machine = some final ∧ Represented pushed (requested groups) CopyDemandControls.root after ∧
    Transport 128 CopyDemandControls.hash CopyDemandControls.locations after final := by
  obtain ⟨actual,executed,represented,transported,_,_⟩ := complete_numeric CopyDemandControls.old pushed rfl rfl (by decide)
    groups CopyDemandControls.root CopyDemandControls.store CopyDemandControls.machine CopyDemandControls.run before (fun _ _ => rfl) covered
  have expected : LifecycleNumeric.pushHeader 128 CopyDemandControls.hash CopyDemandControls.root CopyDemandControls.machine = some final := rfl
  have equal := Option.some.inj (executed.symm.trans expected)
  subst actual
  exact ⟨executed,represented,transported⟩
private def originalQueries := CopyDemandControls.demands ++ CopyDemandControls.queries
private def graphView (v : Value G Outer) := originalQueries.map (fun q => q.read v)
/-- COMPLETE original12 graph and18 numeric observations. Only the root header
changes; the formerly non-live aggregate keeps BOTH payload and inner header. -/
theorem complete_observations :
    (graphView CopyDemandControls.old,graphView pushed,CopyDemandControls.numericView CopyDemandControls.machine,CopyDemandControls.numericView final) =
    ([some one,some one,some two,some one,some one,some two,some two,some one,some one,some one,some two,none],
     [some one,some one,some two,some one,some one,some two,some three,some one,some one,some one,some two,none],
     (two,two,two,two,one,one,one,one,one,one,one,one,one,seven,one,one,zero,seven),
     (three,two,two,two,one,one,one,one,one,one,one,one,one,seven,one,one,zero,seven)) := rfl

/-- Raw retained values are unchanged while the new outer live length activates
one path. Its inner older shadow and out-of-extent failures remain non-live. -/
theorem alias_observations :
    let active : TypeGraph.Path G Outer (.prim .bool) := .cons (.index (ix 2)) (.cons (.index (ix 0)) .nil)
    let shadow : TypeGraph.Path G Outer (.prim .bool) := .cons (.index (ix 2)) (.cons (.index (ix 2)) .nil)
    (CopyDemandControls.old.length.val,CopyDemandControls.old.extent.val,pushed.length.val,pushed.extent.val,
      CopyDemandControls.old.observe active,pushed.observe active,
      (active.readLive Value.dflt CopyDemandControls.old).map Value.head,(active.readLive Value.dflt pushed).map Value.head,
      CopyDemandControls.old.observe shadow,pushed.observe shadow,(shadow.readLive Value.dflt pushed).map Value.head,
      pushed.observe (.cons (.index (ix 3)) (.cons (.index (ix 0)) .nil)),final 56) =
      (2,3,3,3,some true,some true,none,some true,some true,some true,none,none,seven) := rfl

/-- Actual derived outside frames include the failed query's unrepresented7. -/
theorem failed_word_frame : final 56 = CopyDemandControls.machine 56 := by
  obtain ⟨actual,executed,_,_,_,outside⟩ := complete_numeric CopyDemandControls.old pushed rfl rfl (by decide)
    groups CopyDemandControls.root CopyDemandControls.store CopyDemandControls.machine CopyDemandControls.run before (fun _ _ => rfl) covered
  have expected : LifecycleNumeric.pushHeader 128 CopyDemandControls.hash CopyDemandControls.root CopyDemandControls.machine = some final := rfl
  have equal := Option.some.inj (executed.symm.trans expected)
  subst actual
  exact outside 56 (by decide)
private def wrongReset : WordStore := writeWord (writeWord final 10 zero) 48 zero
/-- Wrong primitive-style reset of a retained aggregate is discriminated by
COMPLETE numeric observations, including its nonzero inner header/payload. -/
theorem wrong_reset_negative : CopyDemandControls.numericView wrongReset =
    (three,two,two,zero,one,one,one,one,one,one,zero,one,one,seven,one,one,zero,seven) := rfl


private abbrev Map : TypeGraph.Ty 0 := .mapping .bool (.prim .bool)
private def maps : Value G (.array Map) := .array ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide)
  (fun _ => .present (.mapping (fun _ => .present (.prim true))))
private def mapResult : Value G (.array Map) := (operationPush maps).getD maps
private def mapWord (key : Bool) : Query G Map := .word (.cons (.key key) .nil)
private def mapPair : List (Query G Map) := [mapWord false,mapWord true]
private def mapGroups : List (Index × List (Query G Map)) :=
  [(ix 0,mapPair),(ix 1,mapPair),(ix 2,mapPair),(ix 3,[mapWord false])]
private def mapRoot : Solidity.Storage.Loc := .root 0
private def mapLeaf (i : Fin 4) (key : Bool) : Query G (.array Map) :=
  (mapWord key).prefix (AggregatePopFrames.indexPath (ix i))
private def mapHash (p : Solidity.Storage.Pre) : Nat := if p = .data 0 then 8 else if p = .entry 0 8 then 16 else if p = .entry 1 8 then 24 else
  if p = .entry 0 9 then 32 else if p = .entry 1 9 then 40 else if p = .entry 0 10 then 48 else
  if p = .entry 1 10 then 56 else if p = .entry 0 11 then 64 else 0
private def mapP : List Solidity.Storage.Pre :=
  [.data 0,.entry 0 8,.entry 1 8,.entry 0 9,.entry 1 9,.entry 0 10,.entry 1 10,.entry 0 11]
private noncomputable def mapLocations := (requested mapGroups).map (fun q => q.location mapRoot)
private def mapMachine : WordStore := fun a => if a = 0 then two else
  if a = 16 ∨ a = 24 ∨ a = 32 ∨ a = 40 ∨ a = 48 ∨ a = 56 then one else seven
private def mapStore : Store := fun l => mapMachine (l.word 128 mapHash)
private def mapFinal : WordStore := writeWord mapMachine 0 three
private theorem mapRun : FiniteRun 128 4 1 mapHash mapP mapLocations := by
  constructor
  · intro p; simp only [mapHash]; split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> decide))))))))))))))
  · decide
  · decide
  · decide
  · intro l member
    change l ∈ [mapRoot,(mapLeaf 0 false).location mapRoot,(mapLeaf 0 true).location mapRoot,
      (mapLeaf 1 false).location mapRoot,(mapLeaf 1 true).location mapRoot,
      (mapLeaf 2 false).location mapRoot,(mapLeaf 2 true).location mapRoot,(mapLeaf 3 false).location mapRoot] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (change 0 < 1; decide)
      | (change ((0 < 1 ∧ _ < 4) ∧ 0 < 4); decide)
  · intro l member
    change l ∈ [mapRoot,(mapLeaf 0 false).location mapRoot,(mapLeaf 0 true).location mapRoot,
      (mapLeaf 1 false).location mapRoot,(mapLeaf 1 true).location mapRoot,
      (mapLeaf 2 false).location mapRoot,(mapLeaf 2 true).location mapRoot,(mapLeaf 3 false).location mapRoot] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem mapBefore : Represented maps (requested mapGroups) mapRoot mapStore := by
  intro q member
  change q ∈ [.length .nil,mapLeaf 0 false,mapLeaf 0 true,mapLeaf 1 false,mapLeaf 1 true,mapLeaf 2 false,mapLeaf 2 true,mapLeaf 3 false] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (change (_ < lmax ∧ True ∧ True); decide)
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (intro value observed; change some one = some value at observed; cases observed; rfl)
    | (intro value observed; change some two = some value at observed; cases observed; rfl)
    | (intro value observed; change (none : Option Semantics.Word) = some value at observed; cases observed)

/-- All SIX mapping keys and one supported failed read are in the GENERAL
retained certificate. Header-only execution must preserve both reactivated keys. -/
theorem mapping_certificate : LifecycleNumeric.pushHeader 128 mapHash mapRoot mapMachine = some mapFinal ∧
    Represented mapResult (requested mapGroups) mapRoot (write mapStore mapRoot three) ∧
    Transport 128 mapHash mapLocations (write mapStore mapRoot three) mapFinal := by
  obtain ⟨actual,executed,represented,transported,_,_⟩ := complete_numeric maps mapResult rfl rfl (by decide)
    mapGroups mapRoot mapStore mapMachine mapRun mapBefore (fun _ _ => rfl)
    (fun q member => List.mem_map.mpr ⟨q,member,rfl⟩)
  have expected : LifecycleNumeric.pushHeader 128 mapHash mapRoot mapMachine = some mapFinal := rfl
  have equal := Option.some.inj (executed.symm.trans expected)
  subst actual
  exact ⟨executed,represented,transported⟩
private def mapGraphView (v : Value G (.array Map)) :=
  (v.length.val,v.extent.val,[mapLeaf 0 false,mapLeaf 0 true,mapLeaf 1 false,mapLeaf 1 true,
    mapLeaf 2 false,mapLeaf 2 true,mapLeaf 3 false].map (fun q => q.read v))
private def mapNumericView (m : WordStore) := (m 0,m 8,m 9,m 10,m 16,m 24,m 32,m 40,m 48,m 56,m 64,m 127)
/-- COMPLETE mapping fixture: header/extent, six keys and failed read; twelve
numeric words include unused mapping roots and the failed query's garbage7. -/
theorem mapping_complete_observations :
    (mapGraphView maps,mapGraphView mapResult,mapNumericView mapMachine,mapNumericView mapFinal) =
    ((2,3,[some one,some one,some one,some one,some one,some one,none]),
     (3,3,[some one,some one,some one,some one,some one,some one,none]),
     (two,seven,seven,seven,one,one,one,one,one,one,seven,seven),
     (three,seven,seven,seven,one,one,one,one,one,one,seven,seven)) := rfl

theorem mapping_alias_observations :
    let active : TypeGraph.Path G (.array Map) (.prim .bool) := .cons (.index (ix 2)) (.cons (.key true) .nil)
    ((active.readLive Value.dflt maps).map Value.head,(active.readLive Value.dflt mapResult).map Value.head,
      maps.observe active,mapResult.observe active,mapMachine 10,mapFinal 10,mapMachine 64,mapFinal 64) =
      (none,some true,some true,some true,seven,seven,seven,seven) := rfl
private def wrongMapping : WordStore := writeWord (writeWord (writeWord mapFinal 48 zero) 56 zero) 10 zero
/-- Wrongly resetting reused mapping keys and its unused root is discriminated
in the COMPLETE numeric vector. -/
theorem mapping_reset_negative : mapNumericView wrongMapping =
    (three,seven,seven,zero,one,one,one,one,zero,zero,seven,seven) := rfl


private def freshOld : Value G (.array Map) := .array ⟨0,by decide⟩ (ix 0) (by decide) (fun i => nomatch i)
private def freshResult : Value G (.array Map) := (operationPush freshOld).getD freshOld
private def freshGroups : List (Index × List (Query G Map)) := [(ix 0,mapPair)]
private def freshMachine : WordStore := writeWord (writeWord mapMachine 0 zero) 16 seven
private def freshStore : Store := fun l => freshMachine (l.word 128 mapHash)
private def freshFinal : WordStore := writeWord freshMachine 0 one
private theorem freshBefore : Represented freshOld (requested freshGroups) mapRoot freshStore := by
  intro q member
  change q ∈ [.length .nil,mapLeaf 0 false,mapLeaf 0 true] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro value observed; change some zero = some value at observed; cases observed; rfl
  all_goals refine ⟨by change 0 < lmax ∧ True ∧ True; decide,True.intro,?_⟩
  all_goals intro value observed
  all_goals change (none : Option Semantics.Word) = some value at observed
  all_goals cases observed

/-- GOOD layout and OLD owner evidence do NOT supply fresh default provenance.
Old failed read/garbage7 becomes a successful default0; header-only code keeps7.
This is an OPEN fresh-allocation obligation, not a new source exclusion. -/
theorem fresh_allocation_counterexample : operationPush freshOld = some freshResult ∧
    LifecycleNumeric.pushHeader 128 mapHash mapRoot freshMachine = some freshFinal ∧
    Represented freshOld (requested freshGroups) mapRoot freshStore ∧
    (mapLeaf 0 false).read freshOld = none ∧ (mapLeaf 0 false).read freshResult = some zero ∧
    freshFinal 16 = seven ∧
    ¬ Represented freshResult (requested freshGroups) mapRoot (write freshStore mapRoot one) := by
  refine ⟨rfl,rfl,freshBefore,rfl,rfl,rfl,?_⟩
  intro wrong
  have invalid := (wrong (mapLeaf 0 false) (List.mem_cons_of_mem _ List.mem_cons_self)).2.2 zero rfl
  change seven = zero at invalid
  exact (by decide : seven ≠ zero) invalid

theorem fresh_complete_observations :
    ((freshOld.length.val,freshOld.extent.val,(mapLeaf 0 false).read freshOld,(mapLeaf 0 true).read freshOld),
     (freshResult.length.val,freshResult.extent.val,(mapLeaf 0 false).read freshResult,(mapLeaf 0 true).read freshResult),
     mapNumericView freshMachine,mapNumericView freshFinal) =
    ((0,0,none,none),(1,1,some zero,some zero),
     (zero,seven,seven,seven,seven,one,one,one,one,one,seven,seven),
     (one,seven,seven,seven,seven,one,one,one,one,one,seven,seven)) := rfl

private def maximum : Index := ⟨2 ^ 256 - 1,by decide⟩
private def huge : Value G (.array Map) := .array ⟨2 ^ 256,by decide⟩ maximum (by decide) (fun _ => .absent)
private def hugeMachine : WordStore := fun a => if a = 0 then lengthWord maximum.val maximum.isLt else seven
/-- Actual full-word capacity failure is nontrivial but lies outside the
PUBLIC lmax metadata relation. No source cap or world rollback is invented. -/
theorem capacity_failure_boundary :
    operationPush huge = none ∧ LifecycleNumeric.pushHeader 128 mapHash mapRoot hugeMachine = none ∧
    (huge.length.val,huge.extent.val,(hugeMachine 0).val.toNat) = (2 ^ 256 - 1,2 ^ 256,2 ^ 256 - 1) ∧
    ¬ (Query.length (.nil : TypeGraph.Path G (.array Map) (.array Map))).compatible huge := by
  refine ⟨rfl,rfl,rfl,?_⟩
  change ¬ (2 ^ 256 - 1 ≤ lmax ∧ 2 ^ 256 ≤ lmax)
  decide

/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.nested_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms nested_certificate
/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_observations
/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.alias_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms alias_observations
/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.failed_word_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failed_word_frame
/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.wrong_reset_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_reset_negative
/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.mapping_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mapping_certificate
/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.mapping_complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mapping_complete_observations
/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.mapping_alias_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mapping_alias_observations
/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.mapping_reset_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mapping_reset_negative
/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.fresh_allocation_counterexample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_allocation_counterexample
/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.fresh_complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_complete_observations
/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.capacity_failure_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms capacity_failure_boundary

/-- The fresh-allocation counterexample uses the SAME independently checked
GOOD regions, initial transport and covered requested keys, not a bad hash. -/
theorem fresh_run_evidence : FiniteRun 128 4 1 mapHash mapP mapLocations ∧
    Transport 128 mapHash mapLocations freshStore freshMachine ∧
    (∀ q ∈ requested freshGroups, q.location mapRoot ∈ mapLocations) := by
  refine ⟨mapRun,(fun _ _ => rfl),?_⟩
  intro q member
  change q ∈ [.length .nil,mapLeaf 0 false,mapLeaf 0 true] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> decide
/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.fresh_run_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_run_evidence

private noncomputable def target : Evm.Machine :=
  { Evm.Machine.init (fun a => if a.val = 2 then 100 else 50) ⟨2,by decide⟩ with
    store := ⟨fun slot => TargetOperations.encodeWord (CopyDemandControls.store (Solidity.Storage.ofSlot slot))⟩
    stack := [.val (TargetOperations.encodeWord seven),.slot (.root 9),.val (TargetOperations.encodeWord one)]
    mem := fun i => .val (Evm.wmod (i + 11))
    accepts := fun a _ => a.val != 3
    caller := TargetOperations.encodeWord seven
    callvalue := TargetOperations.encodeWord one
    timestamp := TargetOperations.encodeWord three }
private noncomputable def targetResult : Evm.Machine :=
  { target with store := Evm.WordStore.write target.store (.root 0) 3 }
private theorem fitting : ∀ l ∈ CopyDemandControls.locations, TargetOperations.KeysFit l := by
  intro l member
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp member
  exact TargetOperations.query_keysFit q CopyDemandControls.root True.intro
private theorem targetInitial : ∀ l (member : l ∈ CopyDemandControls.locations),
    target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (CopyDemandControls.store l) := by
  intro l member
  change TargetOperations.encodeWord (CopyDemandControls.store (Solidity.Storage.ofSlot (TargetOperations.toSlot l (fitting l member)))) = _
  rw [TargetOperations.ofSlot_toSlot]

/-- Actual guarded Instr, actual numeric operation and independent graph owner
result agree under the SAME GOOD finite run, preserving full Machine context. -/
theorem target_bridge : Evm.run (TargetHeaderPush.code (.root 0)) target = .ok targetResult 0 ∧
    LifecycleNumeric.pushHeader 128 CopyDemandControls.hash CopyDemandControls.root CopyDemandControls.machine = some final ∧
    Represented pushed (requested groups) CopyDemandControls.root after ∧
    Transport 128 CopyDemandControls.hash CopyDemandControls.locations after final ∧
    (∀ l (member : l ∈ CopyDemandControls.locations), targetResult.store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (final (l.word 128 CopyDemandControls.hash))) := by
  obtain ⟨actual,numericExecuted,executed,owner,transported,agreement⟩ := TargetHeaderPush.numeric_retained CopyDemandControls.old pushed rfl rfl (by decide)
    groups CopyDemandControls.root True.intro CopyDemandControls.store target CopyDemandControls.machine CopyDemandControls.run fitting before
    (fun _ _ => rfl) targetInitial covered
  have expected : LifecycleNumeric.pushHeader 128 CopyDemandControls.hash CopyDemandControls.root CopyDemandControls.machine = some final := rfl
  have same := Option.some.inj (numericExecuted.symm.trans expected)
  subst actual
  exact ⟨executed,numericExecuted,owner,transported,agreement⟩
private def targetSlots : List Evm.Slot := [.root 0,.data (.root 0) 0,.data (.root 0) 1,.data (.root 0) 2,
  .data (.data (.root 0) 0) 0,.data (.data (.root 0) 0) 1,.data (.data (.root 0) 0) 2,
  .data (.data (.root 0) 1) 0,.data (.data (.root 0) 1) 1,.data (.data (.root 0) 1) 2,
  .data (.data (.root 0) 2) 0,.data (.data (.root 0) 2) 1,.data (.data (.root 0) 2) 2,
  .data (.data (.root 0) 3) 0,.root 1,.data (.root 1) 0,.data (.data (.root 1) 0) 0,.root 127]
private def targetView (m : Evm.Machine) := targetSlots.map (fun slot => m.store slot)

/-- COMPLETE original12 graph/18 numeric observations plus corresponding18
symbolic target storage cells. No unchanged payload/header/shadow is omitted. -/
theorem target_complete_observations :
    (graphView CopyDemandControls.old,graphView pushed,CopyDemandControls.numericView CopyDemandControls.machine,CopyDemandControls.numericView final,
      targetView target,targetView targetResult) =
    ([some one,some one,some two,some one,some one,some two,some two,some one,some one,some one,some two,none],
     [some one,some one,some two,some one,some one,some two,some three,some one,some one,some one,some two,none],
     (two,two,two,two,one,one,one,one,one,one,one,one,one,seven,one,one,zero,seven),
     (three,two,two,two,one,one,one,one,one,one,one,one,one,seven,one,one,zero,seven),
     [2,2,2,2,1,1,1,1,1,1,1,1,1,7,1,1,0,7],[3,2,2,2,1,1,1,1,1,1,1,1,1,7,1,1,0,7]) := rfl
private def contextView (m : Evm.Machine) :=
  (m.stack,m.mem 0,m.mem 5,m.bal ⟨2,by decide⟩,m.bal ⟨3,by decide⟩,m.bal₀ ⟨2,by decide⟩,m.self,
    m.accepts ⟨3,by decide⟩ ⟨1,by decide⟩,m.caller,m.callvalue,m.timestamp)

theorem target_context : contextView targetResult = contextView target ∧
    contextView target =
    ([.val (TargetOperations.encodeWord seven),.slot (.root 9),.val (TargetOperations.encodeWord one)],
     .val ⟨11,by decide⟩,.val ⟨16,by decide⟩,100,50,100,⟨2,by decide⟩,false,
     TargetOperations.encodeWord seven,TargetOperations.encodeWord one,TargetOperations.encodeWord three) := ⟨rfl,rfl⟩
private noncomputable def changed : Evm.Machine := { target with store := Evm.WordStore.write target.store (.root 0) 6 }
private noncomputable def changedResult : Evm.Machine := { changed with store := Evm.WordStore.write changed.store (.root 0) 7 }
private noncomputable def wrongConstant : Evm.Machine := { changed with store := Evm.WordStore.write changed.store (.root 0) 3 }

/-- A changed CURRENT header drives6→7. Constant3 differs in COMPLETE target
storage observations; no old source representation is claimed for the change. -/
theorem changed_current_negative : Evm.run (TargetHeaderPush.code (.root 0)) changed = .ok changedResult 0 ∧
    Evm.run (TargetOperations.writeCode (.root 0) three) changed = .ok wrongConstant 0 ∧
    (targetView changed,targetView changedResult,targetView wrongConstant) =
      ([6,2,2,2,1,1,1,1,1,1,1,1,1,7,1,1,0,7],[7,2,2,2,1,1,1,1,1,1,1,1,1,7,1,1,0,7],
       [3,2,2,2,1,1,1,1,1,1,1,1,1,7,1,1,0,7]) := by
  refine ⟨?_,rfl,rfl⟩
  rw [TargetHeaderPush.run_current]
  rfl
private noncomputable def zeroTarget : Evm.Machine := { target with store := Evm.WordStore.write target.store (.root 0) 0 }
private noncomputable def zeroResult : Evm.Machine := { zeroTarget with store := Evm.WordStore.write zeroTarget.store (.root 0) 1 }

theorem zero_current : Evm.run (TargetHeaderPush.code (.root 0)) zeroTarget = .ok zeroResult 0 ∧
    (targetView zeroTarget,targetView zeroResult) =
      ([0,2,2,2,1,1,1,1,1,1,1,1,1,7,1,1,0,7],[1,2,2,2,1,1,1,1,1,1,1,1,1,7,1,1,0,7]) := by
  refine ⟨?_,rfl⟩
  rw [TargetHeaderPush.run_current]
  rfl
private noncomputable def maxTarget : Evm.Machine := { target with store := Evm.WordStore.write target.store (.root 0) (Evm.W - 1) }

theorem capacity_revert : operationPush huge = none ∧ Evm.run (TargetHeaderPush.code (.root 0)) maxTarget = .revert :=
  ⟨capacity_failure_boundary.1,(TargetHeaderPush.failure_matches huge (.root 0) maxTarget rfl).mpr capacity_failure_boundary.1⟩
private def uncheckedCode : List Evm.Instr := [.push (.slot (.root 0)),.sload,.push (.val ⟨1,by decide⟩),.add,.push (.slot (.root 0)),.sstore]
private noncomputable def wrapped : Evm.Machine := { maxTarget with store := Evm.WordStore.write maxTarget.store (.root 0) 0 }

/-- Wrong unguarded increment wraps the maximum header to0; the real code
reverts. This does not assert world rollback or complete ABI failure emission. -/
theorem unchecked_capacity_negative : Evm.run uncheckedCode maxTarget = .ok wrapped 0 ∧
    targetView wrapped = [0,2,2,2,1,1,1,1,1,1,1,1,1,7,1,1,0,7] ∧
    Evm.run (TargetHeaderPush.code (.root 0)) maxTarget = .revert := ⟨rfl,rfl,capacity_revert.2⟩
private noncomputable def freshTarget : Evm.Machine := { target with store :=
  ⟨fun slot => TargetOperations.encodeWord (freshStore (Solidity.Storage.ofSlot slot))⟩ }
private noncomputable def freshTargetResult : Evm.Machine := { freshTarget with store := Evm.WordStore.write freshTarget.store (.root 0) 1 }

/-- Capacity guarding alone does NOT close fresh allocation: both fresh dirty
keys remain7/1 while source defaults are0. Original C44 counter stays unchanged. -/
theorem fresh_target_counter : Evm.run (TargetHeaderPush.code (.root 0)) freshTarget = .ok freshTargetResult 0 ∧
    (freshTargetResult.store (.hash ⟨0,by decide⟩ (.data (.root 0) 0) 0),freshTargetResult.store (.hash ⟨1,by decide⟩ (.data (.root 0) 0) 0)) = (7,1) ∧
    ¬ Represented freshResult (requested freshGroups) mapRoot (write freshStore mapRoot one) := by
  refine ⟨?_,rfl,fresh_allocation_counterexample.2.2.2.2.2.2⟩
  rw [TargetHeaderPush.run_current]
  rfl

private def mapTargetSlots : List Evm.Slot := [.root 0,.data (.root 0) 0,.data (.root 0) 1,.data (.root 0) 2,
  .hash ⟨0,by decide⟩ (.data (.root 0) 0) 0,.hash ⟨1,by decide⟩ (.data (.root 0) 0) 0,
  .hash ⟨0,by decide⟩ (.data (.root 0) 1) 0,.hash ⟨1,by decide⟩ (.data (.root 0) 1) 0,
  .hash ⟨0,by decide⟩ (.data (.root 0) 2) 0,.hash ⟨1,by decide⟩ (.data (.root 0) 2) 0,
  .hash ⟨0,by decide⟩ (.data (.root 0) 3) 0,.root 127]
private def mapTargetView (m : Evm.Machine) := mapTargetSlots.map (fun slot => m.store slot)

/-- COMPLETE original fresh source and12numeric observations, extended by ALL
12corresponding target cells and unchanged nontrivial context before/after. -/
theorem fresh_target_complete_observations :
    ((freshOld.length.val,freshOld.extent.val,(mapLeaf 0 false).read freshOld,(mapLeaf 0 true).read freshOld),
     (freshResult.length.val,freshResult.extent.val,(mapLeaf 0 false).read freshResult,(mapLeaf 0 true).read freshResult),
     mapNumericView freshMachine,mapNumericView freshFinal,mapTargetView freshTarget,mapTargetView freshTargetResult,
     contextView freshTarget,contextView freshTargetResult) =
    ((0,0,none,none),(1,1,some zero,some zero),
     (zero,seven,seven,seven,seven,one,one,one,one,one,seven,seven),
     (one,seven,seven,seven,seven,one,one,one,one,one,seven,seven),
     [0,7,7,7,7,1,1,1,1,1,7,7],[1,7,7,7,7,1,1,1,1,1,7,7],contextView target,contextView target) := rfl

/-- FULL uint256 capacity witness remains outside the public metadata relation;
all18 target input/output cells and nontrivial context remain pinned. -/
theorem capacity_complete_observations :
    (huge.length.val,huge.extent.val,targetView maxTarget,targetView wrapped,
      contextView maxTarget,contextView wrapped) =
      (2 ^ 256 - 1,2 ^ 256,[Evm.W - 1,2,2,2,1,1,1,1,1,1,1,1,1,7,1,1,0,7],
       [0,2,2,2,1,1,1,1,1,1,1,1,1,7,1,1,0,7],contextView target,contextView target) ∧
    ¬ (Query.length (.nil : TypeGraph.Path G (.array Map) (.array Map))).compatible huge :=
  ⟨rfl,capacity_failure_boundary.2.2.2⟩

/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.target_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_bridge
/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.target_complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_complete_observations
/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.target_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_context
/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.changed_current_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms changed_current_negative
/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.zero_current' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms zero_current
/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.capacity_revert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms capacity_revert
/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.unchecked_capacity_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms unchecked_capacity_negative
/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.fresh_target_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_target_counter
/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.fresh_target_complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_target_complete_observations
/-- info: 'Solidity.Backend.StorageOps.RetainedPushControls.capacity_complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms capacity_complete_observations

end Solidity.Backend.StorageOps.RetainedPushControls
