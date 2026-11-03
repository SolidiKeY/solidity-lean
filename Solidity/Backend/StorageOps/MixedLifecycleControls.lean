import Solidity.Backend.StorageOps.MixedLifecycle

/-! Actual mixed-family blocks with full ordered observations. Equal final
headers do not imply equal payload/liveness histories. No Option failure is
promoted to a world rollback or aggregate/compiler closure theorem. -/
namespace Solidity.Backend.StorageOps.MixedLifecycleControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open LifecycleSchedules MixedLifecycle
private def graph : Schema 0 where
  origin := "v10-mixed-lifecycle-controls"
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

private def liveOld : Value graph Elem := .array ⟨4,by decide⟩ ⟨3,by decide⟩ (by decide) (fun _ => .present (.prim true))
private def liveStore := Representation.write (Representation.write store a three) b one
private def liveMachine := writeWord (writeWord machine 0 three) 1 one
private def upDown := (pushPop 32 hash [a] [a,a] liveMachine).getD liveMachine
private def downUp := (popPush 32 hash [a,a] [a] liveMachine).getD liveMachine
private def graphUp := (graphPushes 1 liveOld).getD liveOld
private def graphDown := (graphPops 2 liveOld).getD liveOld
private def graphUpDown := (graphPops 2 graphUp).getD liveOld
private def graphDownUp := (graphPushes 1 graphDown).getD liveOld
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

theorem pushPop_bridge : ∃ result ops, (graphPushes 1 liveOld).bind (graphPops 2) = some result ∧
    pushPopLog 32 hash (List.replicate 1 a) (List.replicate 2 a) liveMachine = some ops ∧
    Transport 32 hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) liveStore) upDown ∧
    Represented result (PrimitivePop.queries indices) a (ops.foldl (fun w op => Representation.write w op.1 op.2) liveStore) :=
  pushPop_represented run 1 2 liveOld indices a liveStore liveMachine upDown liveBefore liveTransport rfl (by decide) (by decide)

theorem popPush_bridge : ∃ result ops, (graphPops 2 liveOld).bind (graphPushes 1) = some result ∧
    popPushLog 32 hash (List.replicate 2 a) (List.replicate 1 a) liveMachine = some ops ∧
    Transport 32 hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) liveStore) downUp ∧
    Represented result (PrimitivePop.queries indices) a (ops.foldl (fun w op => Representation.write w op.1 op.2) liveStore) :=
  popPush_represented run 2 1 liveOld indices a liveStore liveMachine downUp liveBefore liveTransport rfl (by decide) (by decide)

/-- SAME final header2/extent4, but index1/live payload and older shadow3
separate the two orders. Complete initial/intermediate/final vectors retained. -/
theorem ordered :
    (view liveMachine,view upDown,view downUp,graphView liveOld,graphView graphUp,
      graphView graphDown,graphView graphUpDown,graphView graphDownUp,
      pushPopAccesses 32 hash [a] [a,a] liveMachine,popPushAccesses 32 hash [a,a] [a] liveMachine) =
    ((three,one,one,one,one,one,one,one,zero,zero,one,one,seven),
     (two,one,one,one,zero,zero,one,one,zero,zero,one,one,seven),
     (two,one,one,zero,zero,one,one,one,zero,zero,one,one,seven),
     (3,4,some true,some true,some true,some true,some true,some true,some true,none),
     (4,4,some true,some true,some true,some false,some true,some true,some true,some false),
     (1,4,some true,some false,some false,some true,some true,none,none,none),
     (2,4,some true,some true,some false,some false,some true,some true,none,none),
     (2,4,some true,some false,some false,some true,some true,some false,none,none),
     [a,.data a 3,a,.data a 3,a,.data a 2],[a,.data a 2,a,.data a 1,a,.data a 1]) := rfl

theorem wrong_order : upDown 0 = downUp 0 ∧ upDown 9 ≠ downUp 9 ∧ upDown 11 ≠ downUp 11 := ⟨rfl,by decide,by decide⟩

private def multi := (pushPop 32 hash [a,a,b] [a,b] machine).getD machine
private def multiReverse := (popPush 32 hash [a,a,b] [a,b,a] liveMachine).getD liveMachine

theorem multi_transport : ∃ ops, pushPopLog 32 hash [a,a,b] [a,b] machine = some ops ∧
    Transport 32 hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) store) multi :=
  pushPop_transport run [a,a,b] [a,b] store machine multi initial rfl (by decide)
theorem multi_reverse_transport : ∃ ops, popPushLog 32 hash [a,a,b] [a,b,a] liveMachine = some ops ∧
    Transport 32 hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) liveStore) multiReverse :=
  popPush_transport run [a,a,b] [a,b,a] liveStore liveMachine multiReverse liveTransport rfl (by decide)

theorem multi_ordered : (view multi,view multiReverse,
    pushPopAccesses 32 hash [a,a,b] [a,b] machine,popPushAccesses 32 hash [a,a,b] [a,b,a] liveMachine) =
    ((two,zero,one,zero,zero,one,zero,one,zero,zero,one,one,seven),
     (three,one,one,zero,zero,one,zero,one,zero,zero,one,one,seven),
     [a,.data a 1,a,.data a 2,b,.data b 0,a,.data a 2,b,.data b 0],
     [a,.data a 2,a,.data a 1,b,.data b 0,a,.data a 1,b,.data b 0,a,.data a 2]) := rfl

private def firstPrefix := (pushMany 32 hash [a,a] machine).getD machine
private def secondPrefix := (popMany 32 hash [a,a,a] firstPrefix).getD machine
private def firstGraph := (graphPushes 2 old).getD old
private def secondGraph := (graphPops 3 firstGraph).getD old
/-- Late SECOND-phase failure preserves the actual successful prefix witness;
no subsequent B operation is visited, and no transactional rollback is asserted. -/
theorem second_failure_ordered :
    ((pushPop 32 hash [a,a] [a,a,a,a,b] machine).map view,
      pushPopAccesses 32 hash [a,a] [a,a,a,a,b] machine,pushPopLog 32 hash [a,a] [a,a,a,a,b] machine,
      view firstPrefix,view secondPrefix,graphView firstGraph,graphView secondGraph,
      ((graphPushes 2 old).bind (graphPops 4)).map graphView) =
    (none,[a,.data a 1,a,.data a 2,a,.data a 2,a,.data a 1,a,.data a 0,a],none,
     (three,zero,one,zero,zero,one,one,one,zero,zero,one,one,seven),
     (zero,zero,zero,zero,zero,one,one,one,zero,zero,one,one,seven),
     (3,4,some true,some false,some false,some true,some true,some false,some false,none),
     (0,4,some false,some false,some false,some true,none,none,none,none),none) := rfl

theorem first_failure : popPush 32 hash [a,a] [b,a] machine = none ∧
    popPushAccesses 32 hash [a,a] [b,a] machine = popAccesses 32 hash [a,a] machine ∧
    popPushLog 32 hash [a,a] [b,a] machine = none := popPush_failed_first 32 hash [a,a] [b,a] machine rfl

private def full : Semantics.Word := lengthWord (2 ^ 256 - 1) (by decide)
private def capacity := writeWord liveMachine 0 full
private def capacityPrefix := (popMany 32 hash [b] capacity).getD capacity
/-- SECOND-phase capacity failure is numeric-only. Its actual first-phase pop
changes B; failed A reads only its header and has no fictitious reset access. -/
theorem capacity_ordered :
    ((popPush 32 hash [b] [a,a] capacity).map view,
      popPushAccesses 32 hash [b] [a,a] capacity,popPushLog 32 hash [b] [a,a] capacity,
      view capacity,view capacityPrefix) =
    (none,[b,.data b 0,a],none,
     (full,one,one,one,one,one,one,one,zero,zero,one,one,seven),
     (full,zero,one,one,one,one,zero,one,zero,zero,one,one,seven)) := rfl

theorem empty_blocks : pushPop 32 hash [] [] machine = some machine ∧
    popPush 32 hash [] [] machine = some machine ∧
    pushPopAccesses 32 hash [] [] machine = [] ∧ popPushAccesses 32 hash [] [] machine = [] := ⟨rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.MixedLifecycleControls.pushPop_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pushPop_bridge
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycleControls.popPush_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms popPush_bridge
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycleControls.ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycleControls.wrong_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_order
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycleControls.multi_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms multi_transport
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycleControls.multi_reverse_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms multi_reverse_transport
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycleControls.multi_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms multi_ordered
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycleControls.second_failure_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms second_failure_ordered
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycleControls.first_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms first_failure
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycleControls.capacity_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms capacity_ordered
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycleControls.empty_blocks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_blocks

end Solidity.Backend.StorageOps.MixedLifecycleControls
