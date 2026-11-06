import Solidity.Backend.StorageOps.LifecycleSchedules

/-! Actual finite schedules with complete prefix/failure/regrowth observations.
The represented run uses the public per-run conditions. Capacity controls are
explicitly numeric-only outside the owner's smaller header metadata range. -/
namespace Solidity.Backend.StorageOps.LifecycleScheduleControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open LifecycleSchedules
private def graph : Schema 0 where
  origin := "v10-lifecycle-schedule-controls"
  declId := fun i => nomatch i
  declId_injective := by intro i; exact Fin.elim0 i
  name := fun i => nomatch i
  fields := fun i => nomatch i
  rank := fun i => nomatch i
  nonempty := by intro i; exact Fin.elim0 i
  distinct := by intro i; exact Fin.elim0 i
  guarded := by intro i; exact Fin.elim0 i
private def ix (i : Fin 4) : Index := ⟨i.val,by have bound := i.isLt; omega⟩
private def indices : List Index := [ix 0,ix 1,ix 2,ix 3]
private abbrev Elem : TypeGraph.Ty 0 := .array (.prim .bool)
private def a : Solidity.Storage.Loc := .root 0
private def b : Solidity.Storage.Loc := .root 1
private def zero : Semantics.Word := ClearDemands.zero
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def two : Semantics.Word := lengthWord 2 (by decide)
private def three : Semantics.Word := lengthWord 3 (by decide)
private def four : Semantics.Word := lengthWord 4 (by decide)
private def seven : Semantics.Word := ⟨7,by decide⟩
private def hash (p : Solidity.Storage.Pre) : Nat := if p = .data 0 then 8 else if p = .data 1 then 16 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0,.data 1]
private def locations : List Solidity.Storage.Loc := [a,b,
  .data a 0,.data a 1,.data a 2,.data a 3,.data b 0,.data b 1,.data b 2,.data b 3]
private def old : Value graph Elem := .array ⟨4,by decide⟩ ⟨1,by decide⟩ (by decide) (fun _ => .present (.prim true))
private def other : Value graph Elem := .array ⟨2,by decide⟩ ⟨0,by decide⟩ (by decide) (fun _ => .present (.prim true))
private def store : Store := fun l => if l = a then one else if l = .root 2 then seven else
  if l = .data a 0 ∨ l = .data a 1 ∨ l = .data a 2 ∨ l = .data a 3 ∨ l = .data b 0 ∨ l = .data b 1 then one else zero
private def machine : WordStore := fun n => if n = 0 then one else if n = 2 then seven else
  if n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 16 ∨ n = 17 ∨ n = 24 ∨ n = 28 then one else zero
private def view (m : WordStore) := (m 0,m 1,m 8,m 9,m 10,m 11,m 16,m 17,m 18,m 19,m 24,m 28,m 2)
private def element (i : Index) : TypeGraph.Path graph Elem (.prim .bool) := .cons (.index i) .nil
private def graphView (v : Value graph Elem) :=
  (v.length.val,v.extent.val,v.observe (element (ix 0)),v.observe (element (ix 1)),
   v.observe (element (ix 2)),v.observe (element (ix 3)),
   ((element (ix 0)).readLive Value.dflt v).map Value.head,
   ((element (ix 1)).readLive Value.dflt v).map Value.head,
   ((element (ix 2)).readLive Value.dflt v).map Value.head,
   ((element (ix 3)).readLive Value.dflt v).map Value.head)
private def bases : List Solidity.Storage.Loc := [a,a,b,a,b]
private def pushed := (pushMany 32 hash bases machine).getD machine
private def repeated := (pushMany 32 hash [a,a,a] machine).getD machine
private def popped := (popMany 32 hash [a,a] repeated).getD machine
private def regrown := (pushMany 32 hash [a,a] popped).getD machine
private theorem run : FiniteRun 32 4 2 hash preimages locations := by
  constructor
  · intro p; simp only [hash]; split <;> (first | decide | (split <;> decide))
  · decide
  · decide
  · decide
  · intro l member
    simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [a,b,Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem initial : Transport 32 hash locations store machine := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem before : Represented old (PrimitivePop.queries indices) a store := by
  intro q member
  simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 3 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
/-- All three repeated pushes change retained TRUE payloads to FALSE using
successive CURRENT headers; both other-array resets also execute. -/
theorem ordered :
    (view machine,view pushed,view repeated,view popped,view regrown) =
    ((one,zero,one,one,one,one,one,one,zero,zero,one,one,seven),
     (four,two,one,zero,zero,zero,zero,zero,zero,zero,one,one,seven),
     (four,zero,one,zero,zero,zero,one,one,zero,zero,one,one,seven),
     (two,zero,one,zero,zero,zero,one,one,zero,zero,one,one,seven),
     (four,zero,one,zero,zero,zero,one,one,zero,zero,one,one,seven)) := rfl

theorem accesses_ordered :
    (pushAccesses 32 hash bases machine,popAccesses 32 hash [a,a] repeated,
      pushAccesses 32 hash [a,a] popped) =
    ([a,.data a 1,a,.data a 2,b,.data b 0,a,.data a 3,b,.data b 1],
     [a,.data a 3,a,.data a 2],[a,.data a 2,a,.data a 3]) := rfl

theorem schedule_transport : ∃ ops, pushLog 32 hash bases machine = some ops ∧
    Transport 32 hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) store) pushed :=
  push_transport run bases store machine pushed initial rfl (by decide)

theorem repeated_bridge : ∃ result ops, graphPushes 3 old = some result ∧
    pushLog 32 hash (List.replicate 3 a) machine = some ops ∧
    Transport 32 hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) store) repeated ∧
    Represented result (PrimitivePop.queries indices) a (ops.foldl (fun w op => Representation.write w op.1 op.2) store) :=
  repeated_push_represented run 3 old indices a store machine repeated before initial rfl (by decide) (by decide)

private def gPushed := (graphPushes 3 old).getD old
private def gPopped := (graphPops 2 gPushed).getD old
private def gRegrown := (graphPushes 2 gPopped).getD old
/-- Full raw/live/shadow graph vectors: shrink invalidates live aliases while
retained reads remain; regrowth revalidates the same indices with reset values. -/
theorem graph_ordered : (graphView old,graphView gPushed,graphView gPopped,graphView gRegrown) =
    ((1,4,some true,some true,some true,some true,some true,none,none,none),
     (4,4,some true,some false,some false,some false,some true,some false,some false,some false),
     (2,4,some true,some false,some false,some false,some true,some false,none,none),
     (4,4,some true,some false,some false,some false,some true,some false,some false,some false)) := rfl

private def liveOld : Value graph Elem := .array ⟨4,by decide⟩ ⟨3,by decide⟩ (by decide) (fun _ => .present (.prim true))
private def liveMachine := writeWord (writeWord machine 0 three) 1 one
private def popPrefix := (popMany 32 hash [a,a,a] liveMachine).getD liveMachine
private def emptyGraph := (graphPops 3 liveOld).getD liveOld
/-- The first three pops execute and clear EXACT last-live indices2,1,0.
The fourth fails, so B is NOT visited. Older shadows stay TRUE. -/
theorem late_failure_ordered :
    (view liveMachine,view popPrefix,graphView emptyGraph,
      (popMany 32 hash [a,a,a,a,b] liveMachine).map view,
      popAccesses 32 hash [a,a,a,a,b] liveMachine,
      popLog 32 hash [a,a,a,a,b] liveMachine) =
    ((three,one,one,one,one,one,one,one,zero,zero,one,one,seven),
     (zero,one,zero,zero,zero,one,one,one,zero,zero,one,one,seven),
     (0,4,some false,some false,some false,some true,none,none,none,none),
     none,[a,.data a 2,a,.data a 1,a,.data a 0,a],none) := rfl

theorem actual_failed_prefix : popMany 32 hash ([a,a,a,a] ++ [b,b]) liveMachine = none :=
  pop_failed_prefix 32 hash [a,a,a,a] [b,b] liveMachine rfl

/-- Incorrect fixed-initial-header replay only resets index1 repeatedly and
increments the header ONCE; actual schedule uses1,2,3 and reaches4. -/
private def wrong := ((List.replicate 3 (NumericCommutation.pushUpdates 32 hash a machine)).flatten).foldl
  (fun m op => writeWord m (op.1.word 32 hash) op.2) machine
theorem wrong_ordered : (view wrong,view repeated) =
    ((two,zero,one,zero,one,one,one,one,zero,zero,one,one,seven),
     (four,zero,one,zero,zero,zero,one,one,zero,zero,one,one,seven)) := rfl
theorem wrong_different : wrong 10 ≠ repeated 10 ∧ wrong 0 ≠ repeated 0 := ⟨by decide,by decide⟩

private def pushedLog : List (Solidity.Storage.Loc × Semantics.Word) :=
  [(.data a 1,zero),(a,two),(.data a 2,zero),(a,three),(.data a 3,zero),(a,four)]
private def pushedStore := pushedLog.foldl (fun w op => Representation.write w op.1 op.2) store
private theorem pushedEvidence : Transport 32 hash locations pushedStore repeated ∧
    Represented gPushed (PrimitivePop.queries indices) a pushedStore := by
  obtain ⟨result,ops,graphResult,logged,transport,represented⟩ := repeated_bridge
  change some gPushed = some result at graphResult
  cases graphResult
  change some pushedLog = some ops at logged
  cases logged
  exact ⟨transport,represented⟩

theorem repeated_pop_bridge : ∃ result ops, graphPops 2 gPushed = some result ∧
    popLog 32 hash (List.replicate 2 a) repeated = some ops ∧
    Transport 32 hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) pushedStore) popped ∧
    Represented result (PrimitivePop.queries indices) a (ops.foldl (fun w op => Representation.write w op.1 op.2) pushedStore) :=
  repeated_pop_represented run 2 gPushed indices a pushedStore repeated popped
    pushedEvidence.2 pushedEvidence.1 rfl (by decide)

private def liveStore := Representation.write (Representation.write store a three) b one
private theorem liveBefore : Represented liveOld (PrimitivePop.queries indices) a liveStore := by
  intro q member
  simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word observed; change some three = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 3 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
private theorem liveTransport : Transport 32 hash locations liveStore liveMachine :=
  transport_write run (transport_write run initial a (by decide) three) b (by decide) one

theorem changed_pop_bridge : ∃ result ops, graphPops 3 liveOld = some result ∧
    popLog 32 hash (List.replicate 3 a) liveMachine = some ops ∧
    Transport 32 hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) liveStore) popPrefix ∧
    Represented result (PrimitivePop.queries indices) a (ops.foldl (fun w op => Representation.write w op.1 op.2) liveStore) :=
  repeated_pop_represented run 3 liveOld indices a liveStore liveMachine popPrefix liveBefore liveTransport rfl (by decide)

/-- Restart certificate uses the actual three-step prefix, not initial headers. -/
theorem prefix_restart : pushAccesses 32 hash ([a,a] ++ [b,a,b]) machine =
    pushAccesses 32 hash [a,a] machine ++
      pushAccesses 32 hash [b,a,b] ((pushMany 32 hash [a,a] machine).getD machine) :=
  push_accesses_append 32 hash [a,a] [b,a,b] machine _ rfl

private def near : Semantics.Word := lengthWord (2 ^ 256 - 2) (by decide)
private def full : Semantics.Word := lengthWord (2 ^ 256 - 1) (by decide)
private def capacity : WordStore := fun n => if n = 0 then near else one
private def capacityPrefix := (pushMany 32 hash [a] capacity).getD capacity
/-- Numeric-only late capacity failure, OUTSIDE owner header metadata coverage.
A successful first prefix changes word6; second failure reads only header0,
leaving the unexecuted next reset word7 TRUE. This is not world rollback. -/
theorem capacity_ordered :
    ((capacity 0,capacity 6,capacity 7,capacity 8,capacity 24),
     (capacityPrefix 0,capacityPrefix 6,capacityPrefix 7,capacityPrefix 8,capacityPrefix 24),
     (pushMany 32 hash [a,a,b] capacity).map (fun m => (m 0,m 6,m 7,m 8,m 24)),
     pushAccesses 32 hash [a,a,b] capacity,pushLog 32 hash [a,a,b] capacity) =
    ((near,one,one,one,one),(full,zero,one,one,one),none,
     [a,.data a (2 ^ 256 - 2),a],none) := rfl

private def otherPushed := (graphPushes 2 other).getD other
/-- The second array's retained/live observations also change at BOTH newly
live indices, using two actual graph pushes rather than an output oracle. -/
theorem other_graph_ordered : (graphView other,graphView otherPushed) =
    ((0,2,some true,some true,none,none,none,none,none,none),
     (2,2,some false,some false,none,none,some false,some false,none,none)) := rfl
private theorem otherBefore : Represented other (PrimitivePop.queries indices) b store := by
  intro q member
  simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word observed; change some zero = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
  · refine ⟨⟨by change 3 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
theorem other_bridge : ∃ result ops, graphPushes 2 other = some result ∧
    pushLog 32 hash (List.replicate 2 b) machine = some ops ∧
    Transport 32 hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) store)
      ((pushMany 32 hash [b,b] machine).getD machine) ∧
    Represented result (PrimitivePop.queries indices) b (ops.foldl (fun w op => Representation.write w op.1 op.2) store) :=
  repeated_push_represented run 2 other indices b store machine _ otherBefore initial rfl (by decide) (by decide)

/-- info: 'Solidity.Backend.StorageOps.LifecycleScheduleControls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.LifecycleScheduleControls.accesses_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms accesses_ordered
/-- info: 'Solidity.Backend.StorageOps.LifecycleScheduleControls.schedule_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms schedule_transport
/-- info: 'Solidity.Backend.StorageOps.LifecycleScheduleControls.repeated_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms repeated_bridge
/-- info: 'Solidity.Backend.StorageOps.LifecycleScheduleControls.graph_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms graph_ordered
/-- info: 'Solidity.Backend.StorageOps.LifecycleScheduleControls.late_failure_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms late_failure_ordered
/-- info: 'Solidity.Backend.StorageOps.LifecycleScheduleControls.actual_failed_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_failed_prefix
/-- info: 'Solidity.Backend.StorageOps.LifecycleScheduleControls.wrong_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_ordered
/-- info: 'Solidity.Backend.StorageOps.LifecycleScheduleControls.wrong_different' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_different
/-- info: 'Solidity.Backend.StorageOps.LifecycleScheduleControls.repeated_pop_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms repeated_pop_bridge
/-- info: 'Solidity.Backend.StorageOps.LifecycleScheduleControls.changed_pop_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms changed_pop_bridge
/-- info: 'Solidity.Backend.StorageOps.LifecycleScheduleControls.prefix_restart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms prefix_restart
/-- info: 'Solidity.Backend.StorageOps.LifecycleScheduleControls.capacity_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms capacity_ordered
/-- info: 'Solidity.Backend.StorageOps.LifecycleScheduleControls.other_graph_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms other_graph_ordered
/-- info: 'Solidity.Backend.StorageOps.LifecycleScheduleControls.other_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms other_bridge

end Solidity.Backend.StorageOps.LifecycleScheduleControls
