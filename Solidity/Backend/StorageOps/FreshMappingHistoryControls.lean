import Solidity.Backend.StorageOps.FreshMappingHistory
import Solidity.Backend.StorageOps.TargetFreshMapping
import Solidity.Backend.StorageOps.PushFrames
import Solidity.Backend.StorageOps.CopyDemandControls

/-! Actual zero-origin push/write/push history, with independently inhabited
PUBLIC finite regions. Complete ordered observations keep old keys, unused
mapping roots, failed paths and outside words. Dirty history is discriminated. -/
namespace Solidity.Backend.StorageOps.FreshMappingHistoryControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open FreshMappingHistory
private abbrev G := CopyDemandControls.graph
private abbrev Map : TypeGraph.Ty 0 := .mapping .bool (.prim .bool)
private abbrev Array : TypeGraph.Ty 0 := .array Map
private def ix (i : Fin 3) : Index := ⟨i.val,by have h := i.isLt; omega⟩
private def root : Solidity.Storage.Loc := .root 0
private def zero : Semantics.Word := ClearDemands.zero
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def two : Semantics.Word := lengthWord 2 (by decide)
private def seven : Semantics.Word := ⟨7,by decide⟩
private def empty : Value G Array := .array ⟨0,by decide⟩ (ix 0) (by decide) (fun i => nomatch i)
private def first : Value G Array := (operationPush empty).getD empty
private def savedPath : TypeGraph.Path G Array (.prim .bool) := .cons (.index (ix 0)) (.cons (.key true) .nil)
private def old : Value G Array := (first.save savedPath (.prim true)).getD first
private def result : Value G Array := (operationPush old).getD old
private def query (i : Fin 3) (k : Bool) : Query G Array := keyQuery (ix i) k
private noncomputable def history : List (Solidity.Storage.Loc × Semantics.Word) :=
  [(root,one),((query 0 true).location root,one)]
private def hash (p : Solidity.Storage.Pre) : Nat := if p = .data 0 then 8 else if p = .entry 0 8 then 16 else
  if p = .entry 1 8 then 24 else if p = .entry 0 9 then 32 else if p = .entry 1 9 then 40 else 0
private def P : List Solidity.Storage.Pre := [.data 0,.entry 0 8,.entry 1 8,.entry 0 9,.entry 1 9]
private def queries : List (Query G Array) := [.length .nil,query 0 false,query 0 true,query 1 false,query 1 true]
private noncomputable def locations := queries.map (fun q => q.location root)
private noncomputable def machine : WordStore := numeric 128 hash history
private noncomputable def final : WordStore := writeWord machine 0 two
private noncomputable def after : Store := write (symbolic history) root two
private theorem run : FiniteRun 128 4 1 hash P locations := by
  constructor
  · intro p; simp only [hash]; split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> decide))))))))
  · decide
  · decide
  · decide
  · intro l member
    change l ∈ [root,(query 0 false).location root,(query 0 true).location root,(query 1 false).location root,(query 1 true).location root] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals first | (change 0 < 1; decide) | (change ((0 < 1 ∧ _ < 4) ∧ 0 < 4); decide)
  · intro l member
    change l ∈ [root,(query 0 false).location root,(query 0 true).location root,(query 1 false).location root,(query 1 true).location root] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
private theorem historyCovered : ∀ op ∈ history, op.1 ∈ locations := by
  intro op member
  change op ∈ [(root,one),((query 0 true).location root,one)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> decide
private theorem queryCovered : ∀ key ∈ [false,true], (keyQuery (G := G) (K := .bool) (p := .bool) old.length key).location root ∈ locations := by
  intro key _; cases key <;> decide
private theorem apart : ∀ key ∈ [false,true], ∀ op ∈ history,
    (keyQuery (G := G) (K := .bool) (p := .bool) old.length key).location root ≠ op.1 := by
  intro key _ op member
  change op ∈ [(root,one),((query 0 true).location root,one)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> cases key <;> decide
private theorem before : Represented old [.length .nil] root (symbolic history) := by
  intro q member
  have same := List.mem_singleton.mp member; subst q
  refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
  intro value observed
  change some one = some value at observed
  cases observed
  rfl

/-- BOTH source and target history entries come from actual operations: first
push, typed path save and the corresponding numeric scalar write. -/
theorem actual_history : operationPush empty = some first ∧ first.save savedPath (.prim true) = some old ∧
    LifecycleNumeric.pushHeader 128 hash root (fun _ => zero) = some (writeWord (fun _ => zero) 0 one) ∧
    writeWord (writeWord (fun _ => zero) 0 one) 24 one = machine ∧
    operationPush old = some result := ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Applies the GENERAL history-provenance certificate, not postrelation as a
premise. Both keys of the newly allocated mapping become readable default0. -/
theorem certificate : LifecycleNumeric.pushHeader 128 hash root machine = some final ∧
    Represented result (.length .nil :: [keyQuery old.length false,keyQuery old.length true]) root after ∧
    Transport 128 hash locations after final := by
  obtain ⟨actual,executed,owner,transported,_,_⟩ := complete_numeric old result rfl rfl [false,true] root run history
    historyCovered (by decide) queryCovered apart (by decide) before
  have expected : LifecycleNumeric.pushHeader 128 hash root machine = some final := rfl
  have same := Option.some.inj (executed.symm.trans expected)
  subst actual
  exact ⟨executed,owner,transported⟩
private def graphView (v : Value G Array) :=
  (v.length.val,v.extent.val,(query 0 false).read v,(query 0 true).read v,
    (query 1 false).read v,(query 1 true).read v,(query 2 false).read v)
private def numericView (m : WordStore) := (m 0,m 8,m 9,m 10,m 16,m 24,m 32,m 40,m 48,m 127)

/-- COMPLETE ordered graph/numeric observations for both pushes and the write.
The prior nonzero key survives; unused mapping roots and outside words frame. -/
theorem complete_observations :
    (graphView empty,graphView first,graphView old,graphView result,numericView (fun _ => zero),numericView (writeWord (fun _ => zero) 0 one),numericView machine,numericView final) =
    ((0,0,none,none,none,none,none),(1,1,some zero,some zero,none,none,none),
     (1,1,some zero,some one,none,none,none),(2,2,some zero,some one,some zero,some zero,none),
     (zero,zero,zero,zero,zero,zero,zero,zero,zero,zero),
     (one,zero,zero,zero,zero,zero,zero,zero,zero,zero),
     (one,zero,zero,zero,zero,one,zero,zero,zero,zero),
     (two,zero,zero,zero,zero,one,zero,zero,zero,zero)) := rfl

/-- Logical aliases distinguish old failure from fresh live default and retain
prior live payload. No heap identity or world rollback assertion is made. -/
theorem alias_observations :
    let freshPath : TypeGraph.Path G Array (.prim .bool) := .cons (.index (ix 1)) (.cons (.key true) .nil)
    (old.observe freshPath,result.observe freshPath,(freshPath.readLive Value.dflt old).map Value.head,
      (freshPath.readLive Value.dflt result).map Value.head,old.observe savedPath,result.observe savedPath,
      (savedPath.readLive Value.dflt result).map Value.head) = (none,some false,none,some false,some true,some true,some true) := rfl
private noncomputable def dirtyHistory := history ++ [((query 1 false).location root,seven)]
private noncomputable def dirty := numeric 128 hash dirtyHistory
private noncomputable def dirtyFinal := writeWord dirty 0 two
/-- The dirty negative retains the SAME independently GOOD finite run and
OLD complete selected owner/Transport evidence. Only untouched provenance fails. -/
theorem dirty_evidence : FiniteRun 128 4 1 hash P locations ∧
    Transport 128 hash locations (symbolic dirtyHistory) dirty ∧
    Represented old queries root (symbolic dirtyHistory) ∧
    ¬ (∀ key ∈ [false,true], ∀ op ∈ dirtyHistory,
      (keyQuery (G := G) (K := .bool) (p := .bool) old.length key).location root ≠ op.1) := by
  have covered : ∀ op ∈ dirtyHistory, op.1 ∈ locations := by
    intro op member
    change op ∈ history ++ [((query 1 false).location root,seven)] at member
    rcases List.mem_append.mp member with prior | last
    · exact historyCovered op prior
    · have same := List.mem_singleton.mp last; subst op; decide
  refine ⟨run,history_transport run dirtyHistory covered,?_,?_⟩
  · intro q member
    change q ∈ [.length .nil,query 0 false,query 0 true,query 1 false,query 1 true] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals refine ⟨?_,?_,?_⟩
    all_goals first
      | (change _ < lmax ∧ True ∧ True; decide)
      | exact True.intro
      | exact ⟨by decide,by decide⟩
      | (intro value observed; change some one = some value at observed; cases observed; rfl)
      | (intro value observed; change some zero = some value at observed; cases observed; rfl)
      | (intro value observed; change (none : Option Semantics.Word) = some value at observed; cases observed)
  · intro wrong
    exact wrong false (by decide) ((query 1 false).location root,seven)
      (List.mem_append.mpr (Or.inr List.mem_cons_self)) rfl

/-- Touching an old failed fresh query destroys the required provenance even
though old header/failed reads remain represented and regions stay GOOD. -/
theorem dirty_counterexample :
    LifecycleNumeric.pushHeader 128 hash root dirty = some dirtyFinal ∧
    (query 1 false).read old = none ∧ (query 1 false).read result = some zero ∧ dirtyFinal 32 = seven ∧
    ¬ Represented result [query 1 false] root (write (symbolic dirtyHistory) root two) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro wrong
  have invalid := (wrong _ List.mem_cons_self).2.2 zero rfl
  change seven = zero at invalid
  exact (by decide : seven ≠ zero) invalid

theorem dirty_complete_observations : (graphView old,graphView result,numericView dirty,numericView dirtyFinal) =
    ((1,1,some zero,some one,none,none,none),(2,2,some zero,some one,some zero,some zero,none),
     (one,zero,zero,zero,zero,one,seven,zero,zero,zero),
     (two,zero,zero,zero,zero,one,seven,zero,zero,zero)) := rfl

/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistoryControls.actual_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_history
/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistoryControls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistoryControls.complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_observations
/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistoryControls.alias_observations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms alias_observations
/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistoryControls.dirty_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms dirty_evidence
/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistoryControls.dirty_counterexample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms dirty_counterexample
/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistoryControls.dirty_complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms dirty_complete_observations


private def oldGroups : List (Index × List (Query G Map)) :=
  [(ix 0,[.word (.cons (.key false) .nil),.word (.cons (.key true) .nil)])]
private theorem oldContexts : Represented old (AggregatePopFrames.contexts oldGroups) root (symbolic history) := by
  intro q member
  change q ∈ [query 0 false,query 0 true] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  all_goals refine ⟨by change 0 < lmax ∧ True ∧ True; decide,True.intro,?_⟩
  · intro value observed; change some zero = some value at observed; cases observed; rfl
  · intro value observed; change some one = some value at observed; cases observed; rfl
private theorem combinedCovered : ∀ q ∈ (.length .nil :: [keyQuery (G := G) (K := .bool) (p := .bool) old.length false,keyQuery (G := G) (K := .bool) (p := .bool) old.length true]) ++ AggregatePopFrames.contexts oldGroups,
    q.location root ∈ locations := by
  intro q member
  change q ∈ [.length .nil,query 1 false,query 1 true,query 0 false,query 0 true] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> decide

/-- C46 ONE execution represents both new default keys AND both old keys.
The old true1 is preserved by GENERAL derived frames, not a postrelation premise. -/
theorem combined_certificate : LifecycleNumeric.pushHeader 128 hash root machine = some final ∧
    Represented result ((.length .nil :: [keyQuery (G := G) (K := .bool) (p := .bool) old.length false,keyQuery (G := G) (K := .bool) (p := .bool) old.length true]) ++ AggregatePopFrames.contexts oldGroups) root after ∧
    Transport 128 hash locations after final := by
  have other : ∀ group ∈ oldGroups, group.1.val ≠ old.length.val := by
    intro group member
    have same := List.mem_singleton.mp member; subst group; decide
  obtain ⟨actual,executed,owner,transported,_,_⟩ := PushFrames.complete_fresh old result rfl rfl [false,true] oldGroups other root run history
    historyCovered combinedCovered apart (by decide) before oldContexts
  have expected : LifecycleNumeric.pushHeader 128 hash root machine = some final := rfl
  have same := Option.some.inj (executed.symm.trans expected)
  subst actual
  exact ⟨executed,owner,transported⟩

/-- Exact other-index failure, without pretending its numeric location is
covered by this finite run. Logical failure does not constrain raw memory. -/
theorem failed_other_frame : (query 2 false).read result = (query 2 false).read old :=
  PushFrames.read_other old result rfl (ix 2) (by decide) (.word (.cons (.key false) .nil))

/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistoryControls.combined_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms combined_certificate
/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistoryControls.failed_other_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failed_other_frame

private def initialTarget : Evm.Machine :=
  { Evm.Machine.init (fun a => if a.val = 2 then 100 else 50) ⟨2,by decide⟩ with
    stack := [.val (TargetOperations.encodeWord seven),.slot (.root 9)]
    mem := fun i => .val (Evm.wmod (i + 11))
    accepts := fun a _ => a.val != 3
    caller := TargetOperations.encodeWord seven
    callvalue := TargetOperations.encodeWord one
    timestamp := TargetOperations.encodeWord two }
private def savedSlot : Evm.Slot := .hash ⟨1,by decide⟩ (.data (.root 0) 0) 0
private def firstTarget : Evm.Machine := { initialTarget with store := Evm.WordStore.write initialTarget.store (.root 0) 1 }
private def oldTarget : Evm.Machine := { firstTarget with store := Evm.WordStore.write firstTarget.store savedSlot 1 }
private def resultTarget : Evm.Machine := { oldTarget with store := Evm.WordStore.write oldTarget.store (.root 0) 2 }
private theorem targetFitting : ∀ l ∈ locations, TargetOperations.KeysFit l := by
  intro l member
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp member
  exact TargetOperations.query_keysFit q root True.intro
private theorem targetInitial : ∀ l (member : l ∈ locations), oldTarget.store.cells (TargetOperations.toSlot l (targetFitting l member)) =
    TargetOperations.encodeWord (symbolic history l) := by
  intro l member
  obtain ⟨q,inside,rfl⟩ := List.mem_map.mp member
  change q ∈ [.length .nil,query 0 false,query 0 true,query 1 false,query 1 true] at inside
  simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl | rfl <;> rfl
private def observedQueries : List (Query G Array) :=
  (.length .nil :: [keyQuery (G := G) (K := .bool) (p := .bool) old.length false,keyQuery (G := G) (K := .bool) (p := .bool) old.length true]) ++ AggregatePopFrames.contexts oldGroups

/-- Actual three-piece instruction program reaches the fixture from ZERO
storage. Source/numeric history remains independently checked by actual_history. -/
theorem actual_target_history :
    Evm.run (TargetHeaderPush.code (.root 0) ++ (TargetOperations.writeCode savedSlot one ++ TargetHeaderPush.code (.root 0))) initialTarget = .ok resultTarget 0 ∧
    Evm.run (TargetHeaderPush.code (.root 0)) initialTarget = .ok firstTarget 0 ∧
    Evm.run (TargetOperations.writeCode savedSlot one) firstTarget = .ok oldTarget 0 := by
  have firstRun : Evm.run (TargetHeaderPush.code (.root 0)) initialTarget = .ok firstTarget 0 := by
    rw [TargetHeaderPush.run_current]; rfl
  have writeRun : Evm.run (TargetOperations.writeCode savedSlot one) firstTarget = .ok oldTarget 0 := rfl
  have secondRun : Evm.run (TargetHeaderPush.code (.root 0)) oldTarget = .ok resultTarget 0 := by
    rw [TargetHeaderPush.run_current]; rfl
  refine ⟨?_,firstRun,writeRun⟩
  rw [Evm.run_append_ok firstRun,Evm.run_append_ok writeRun]
  exact secondRun

/-- GENERAL positive fresh-default/old-context owner, actual numeric Transport
and target agreement, with independent GOOD run and actual target history. -/
theorem fresh_target_bridge : Evm.run (TargetHeaderPush.code (.root 0)) oldTarget = .ok resultTarget 0 ∧
    LifecycleNumeric.pushHeader 128 hash root machine = some final ∧
    Represented result observedQueries root after ∧ Transport 128 hash locations after final ∧
    (∀ l (member : l ∈ locations), resultTarget.store.cells (TargetOperations.toSlot l (targetFitting l member)) = TargetOperations.encodeWord (final (l.word 128 hash))) := by
  have other : ∀ group ∈ oldGroups, group.1.val ≠ old.length.val := by
    intro group member; have same := List.mem_singleton.mp member; subst group; decide
  obtain ⟨actual,numericExecuted,executed,owner,transported,agreement,_⟩ := TargetFreshMapping.complete_numeric old result rfl rfl
    [false,true] oldGroups other root True.intro oldTarget run history historyCovered combinedCovered apart (by decide) before oldContexts targetFitting targetInitial
  have expected : LifecycleNumeric.pushHeader 128 hash root machine = some final := rfl
  have same := Option.some.inj (numericExecuted.symm.trans expected)
  subst actual
  exact ⟨executed,numericExecuted,owner,transported,agreement⟩

/-- ACTUAL SLOAD readbacks for EVERY successful selected source observation,
including both fresh defaults and the preserved nonzero old key. -/
theorem target_readbacks : ∀ q ∈ observedQueries, ∀ value, q.read result = some value →
    Evm.run (TargetOperations.readCode (TargetOperations.toSlot (q.location root) (TargetOperations.query_keysFit q root True.intro))) resultTarget =
      .ok { resultTarget with stack := .val (TargetOperations.encodeWord value) :: resultTarget.stack } 0 := by
  have other : ∀ group ∈ oldGroups, group.1.val ≠ old.length.val := by
    intro group member; have same := List.mem_singleton.mp member; subst group; decide
  obtain ⟨_,_,_,_,_,_,readbacks⟩ := TargetFreshMapping.complete_numeric old result rfl rfl
    [false,true] oldGroups other root True.intro oldTarget run history historyCovered combinedCovered apart (by decide) before oldContexts targetFitting targetInitial
  exact readbacks
private def targetSlots : List Evm.Slot := [.root 0,.data (.root 0) 0,.data (.root 0) 1,.data (.root 0) 2,
  .hash ⟨0,by decide⟩ (.data (.root 0) 0) 0,.hash ⟨1,by decide⟩ (.data (.root 0) 0) 0,
  .hash ⟨0,by decide⟩ (.data (.root 0) 1) 0,.hash ⟨1,by decide⟩ (.data (.root 0) 1) 0,.root 48,.root 127]
private def targetView (m : Evm.Machine) := targetSlots.map (fun slot => m.store slot)

/-- COMPLETE four-stage source/numeric history vectors stay unchanged, now
paired with all ten target cells at EACH actual executed history stage. -/
theorem target_history_complete_observations :
    (graphView empty,graphView first,graphView old,graphView result,
      numericView (fun _ => zero),numericView (writeWord (fun _ => zero) 0 one),numericView machine,numericView final,
      targetView initialTarget,targetView firstTarget,targetView oldTarget,targetView resultTarget) =
    ((0,0,none,none,none,none,none),(1,1,some zero,some zero,none,none,none),
     (1,1,some zero,some one,none,none,none),(2,2,some zero,some one,some zero,some zero,none),
     (zero,zero,zero,zero,zero,zero,zero,zero,zero,zero),(one,zero,zero,zero,zero,zero,zero,zero,zero,zero),
     (one,zero,zero,zero,zero,one,zero,zero,zero,zero),(two,zero,zero,zero,zero,one,zero,zero,zero,zero),
     [0,0,0,0,0,0,0,0,0,0],[1,0,0,0,0,0,0,0,0,0],[1,0,0,0,0,1,0,0,0,0],[2,0,0,0,0,1,0,0,0,0]) := rfl
private def contextView (m : Evm.Machine) :=
  (m.stack,m.mem 0,m.mem 5,m.bal ⟨2,by decide⟩,m.bal ⟨3,by decide⟩,m.bal₀ ⟨2,by decide⟩,m.self,
    m.accepts ⟨3,by decide⟩ ⟨1,by decide⟩,m.caller,m.callvalue,m.timestamp)

theorem target_history_context :
    (contextView firstTarget,contextView oldTarget,contextView resultTarget) =
      (contextView initialTarget,contextView initialTarget,contextView initialTarget) ∧
    contextView initialTarget =
      ([.val (TargetOperations.encodeWord seven),.slot (.root 9)],.val ⟨11,by decide⟩,.val ⟨16,by decide⟩,
       100,50,100,⟨2,by decide⟩,false,TargetOperations.encodeWord seven,TargetOperations.encodeWord one,TargetOperations.encodeWord two) := ⟨rfl,rfl⟩

/-- Unsupported physical coverage is NOT inferred from a typed failed read:
actual total SLOAD returns0 while source index2 read isNone. -/
theorem target_failed_read_boundary : (query 2 false).supported ∧ (query 2 false).read result = none ∧
    (query 2 false).location root ∉ locations ∧
    Evm.run (TargetOperations.readCode (.hash ⟨0,by decide⟩ (.data (.root 0) 2) 0)) resultTarget =
      .ok { resultTarget with stack := .val (TargetOperations.encodeWord zero) :: resultTarget.stack } 0 := ⟨by change 2 < lmax ∧ True ∧ True; decide,rfl,by decide,rfl⟩
private def dirtyTarget : Evm.Machine := { oldTarget with store := Evm.WordStore.write oldTarget.store (.hash ⟨0,by decide⟩ (.data (.root 0) 1) 0) 7 }
private def dirtyResultTarget : Evm.Machine := { dirtyTarget with store := Evm.WordStore.write dirtyTarget.store (.root 0) 2 }

/-- The original dirty-history negative survives actual guarded execution;
all10 target cells are pinned, not only the bad fresh key. -/
theorem target_dirty_history_negative : Evm.run (TargetHeaderPush.code (.root 0)) dirtyTarget = .ok dirtyResultTarget 0 ∧
    (targetView dirtyTarget,targetView dirtyResultTarget) =
      ([1,0,0,0,0,1,7,0,0,0],[2,0,0,0,0,1,7,0,0,0]) ∧
    ¬ Represented result [query 1 false] root (write (symbolic dirtyHistory) root two) := by
  refine ⟨?_,rfl,dirty_counterexample.2.2.2.2⟩
  rw [TargetHeaderPush.run_current]
  rfl

/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistoryControls.actual_target_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_target_history
/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistoryControls.fresh_target_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_target_bridge
/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistoryControls.target_readbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_readbacks
/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistoryControls.target_history_complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_history_complete_observations
/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistoryControls.target_history_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_history_context
/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistoryControls.target_failed_read_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_failed_read_boundary
/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistoryControls.target_dirty_history_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_dirty_history_negative

end Solidity.Backend.StorageOps.FreshMappingHistoryControls
