import Solidity.Backend.StorageOps.CopyLifecycle
import Solidity.Backend.StorageOps.PathRepresentation

/-! Copy/lifecycle components under a real represented finite run. Complete
ordered vectors distinguish safe disjoint effects, shared-read failure and good-
region interference; no compiler, eager aggregate or world closure is claimed. -/
namespace Solidity.Backend.StorageOps.CopyLifecycleControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def graph : Schema 0 where
  origin := "v10-copy-lifecycle-controls"
  declId := fun i => nomatch i
  declId_injective := by intro i; exact Fin.elim0 i
  name := fun i => nomatch i
  fields := fun i => nomatch i
  rank := fun i => nomatch i
  nonempty := by intro i; exact Fin.elim0 i
  distinct := by intro i; exact Fin.elim0 i
  guarded := by intro i; exact Fin.elim0 i
private def ix (i : Fin 4) : Index := ⟨i.val, by have bound := i.isLt; omega⟩
private def indices : List Index := [ix 0, ix 1, ix 2, ix 3]
private abbrev Elem : TypeGraph.Ty 0 := .array (.prim .bool)
private abbrev Root : TypeGraph.Ty 0 := .mapping .uint Elem
private def key (i : Fin 4) : PrimTy.uint.Denote := if i.val = 0 then ⟨0,by decide⟩ else if i.val = 1 then ⟨1,by decide⟩ else if i.val = 2 then ⟨2,by decide⟩ else ⟨3,by decide⟩
private def a : Solidity.Storage.Loc := .hash 0 (.root 0) 0
private def b : Solidity.Storage.Loc := .hash 1 (.root 0) 0
private def s : Solidity.Storage.Loc := .hash 2 (.root 0) 0
private def o : Solidity.Storage.Loc := .hash 3 (.root 0) 0
private def zero : Semantics.Word := ClearDemands.zero
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def two : Semantics.Word := lengthWord 2 (by decide)
private def three : Semantics.Word := lengthWord 3 (by decide)
private def seven : Semantics.Word := ⟨7, by decide⟩
private def hash (p : Solidity.Storage.Pre) : Nat :=
  if p = .entry 0 0 then 4 else if p = .entry 1 0 then 8 else
  if p = .entry 2 0 then 12 else if p = .entry 3 0 then 40 else
  if p = .data 4 then 16 else if p = .data 8 then 24 else
  if p = .data 12 then 32 else 0
private def preimages : List Solidity.Storage.Pre :=
  [.entry 0 0, .entry 1 0, .entry 2 0, .entry 3 0, .data 4, .data 8, .data 12]
private def locations : List Solidity.Storage.Loc := [a,b,s,o,
  .data a 0,.data a 1,.data a 2,.data a 3,
  .data b 0,.data b 1,.data b 2,.data b 3,
  .data s 0,.data s 1,.data s 2,.data s 3]
private def oldA : Value graph Elem :=
  .array ⟨4,by decide⟩ ⟨3,by decide⟩ (by decide) (fun _ => .present (.prim true))
private def oldB : Value graph Elem :=
  .array ⟨2,by decide⟩ ⟨1,by decide⟩ (by decide) (fun _ => .present (.prim true))
private def snapshot : Value graph Elem :=
  .array ⟨2,by decide⟩ ⟨2,by decide⟩ (by decide) (fun _ => .present (.prim false))
private def slots (k : PrimTy.uint.Denote) : Slot graph Elem :=
  if k = key 0 then .present oldA else if k = key 1 then .present oldB else
  if k = key 2 then .present snapshot else .absent
private def root : Value graph Root := .mapping slots
private def path (k : Fin 4) : TypeGraph.Path graph Root Elem := .cons (.key (key k)) .nil
private def element (i : Index) : TypeGraph.Path graph Elem (.prim .bool) := .cons (.index i) .nil
private def left (v : Value graph Root) := recursiveCopyAt v (path 0) (path 2)
private def pushRoot (v : Value graph Root) := pushAt v (path 1)
private def popRoot (v : Value graph Root) := popAt v (path 1)
private def store : Store := fun l => if l = a then three else if l = b then one else
  if l = s then two else if l = .root 2 then seven else
  if l = .data a 0 ∨ l = .data a 1 ∨ l = .data a 2 ∨ l = .data a 3 ∨ l = .data b 0 ∨ l = .data b 1 then one else zero
private def machine : WordStore := fun n => if n = 4 then three else if n = 8 then one else
  if n = 12 then two else if n = 2 then seven else
  if n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 24 ∨ n = 25 ∨ n = 96 ∨ n = 100 then one else zero
private def ca (m : WordStore) := NumericTraversal.copy 128 hash a s m
private def pushB (m : WordStore) := LifecycleNumeric.pushPrimitive 128 hash b m
private def popB (m : WordStore) := PrimitivePop.execute 128 hash b m
private def numericView (m : WordStore) :=
  (m 4,m 8,m 12,m 40,m 16,m 17,m 18,m 19,m 24,m 25,m 26,m 27,m 32,m 33,m 34,m 35,m 96,m 100,m 2)
private def arrayView (v : Value graph Elem) :=
  (v.length.val,v.extent.val,v.observe (element (ix 0)),v.observe (element (ix 1)),
   v.observe (element (ix 2)),v.observe (element (ix 3)),
   ((element (ix 0)).readLive Value.dflt v).map Value.head,
   ((element (ix 1)).readLive Value.dflt v).map Value.head,
   ((element (ix 2)).readLive Value.dflt v).map Value.head,
   ((element (ix 3)).readLive Value.dflt v).map Value.head)
private def rootView (v : Value graph Root) :=
  ((v.find (path 0)).map arrayView,(v.find (path 1)).map arrayView,
   (v.find (path 2)).map arrayView,(v.find (path 3)).map arrayView)
private theorem run : FiniteRun 128 4 1 hash preimages locations := by
  constructor
  · intro p; simp only [hash]
    split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide |
      (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> decide))))))))))))
  · decide
  · decide
  · decide
  · intro l member
    simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [a,b,s,o,Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem initial : Transport 128 hash locations store machine := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl


theorem copy_push_commutes : pushB (ca machine) = (pushB machine).map ca :=
  CopyLifecycle.copy_push run a s b machine (by decide) (by decide) (by decide) (by decide)
theorem copy_pop_commutes : popB (ca machine) = (popB machine).map ca :=
  CopyLifecycle.copy_pop run a s b machine (by decide) (by decide) (by decide) (by decide)

private def afterPush := (pushB (ca machine)).getD machine
private def afterPop := (popB (ca machine)).getD machine
/-- BOTH copy destination and lifecycle array change. The source, unrelated
mapping key, older shadows and sentinels retain their complete observations. -/
theorem numeric_ordered :
    (numericView machine,(pushB (ca machine)).map numericView,((pushB machine).map ca).map numericView,
     (popB (ca machine)).map numericView,((popB machine).map ca).map numericView) =
    ((three,one,two,zero,one,one,one,one,one,one,zero,zero,zero,zero,zero,zero,one,one,seven),
     some (two,two,two,zero,zero,zero,zero,one,one,zero,zero,zero,zero,zero,zero,zero,one,one,seven),
     some (two,two,two,zero,zero,zero,zero,one,one,zero,zero,zero,zero,zero,zero,zero,one,one,seven),
     some (two,zero,two,zero,zero,zero,zero,one,zero,one,zero,zero,zero,zero,zero,zero,one,one,seven),
     some (two,zero,two,zero,zero,zero,zero,one,zero,one,zero,zero,zero,zero,zero,zero,one,one,seven)) := rfl

private def copied := (left root).getD root
private def pushResult := ((left root).bind pushRoot).getD root
private def popResult := ((left root).bind popRoot).getD root
private abbrev Observations := Option (Nat × Nat × Option Bool × Option Bool × Option Bool × Option Bool × Option Bool × Option Bool × Option Bool × Option Bool) × Option (Nat × Nat × Option Bool × Option Bool × Option Bool × Option Bool × Option Bool × Option Bool × Option Bool × Option Bool) × Option (Nat × Nat × Option Bool × Option Bool × Option Bool × Option Bool × Option Bool × Option Bool × Option Bool × Option Bool) × Option (Nat × Nat × Option Bool × Option Bool × Option Bool × Option Bool × Option Bool × Option Bool × Option Bool × Option Bool)
private def beforeView : Observations :=
  (some (3,4,some true,some true,some true,some true,some true,some true,some true,none),
   some (1,2,some true,some true,none,none,some true,none,none,none),
   some (2,2,some false,some false,none,none,some false,some false,none,none),
   some (0,0,none,none,none,none,none,none,none,none))
private def pushView : Observations :=
  (some (2,4,some false,some false,some false,some true,some false,some false,none,none),
   some (2,2,some true,some false,none,none,some true,some false,none,none),
   some (2,2,some false,some false,none,none,some false,some false,none,none),
   some (0,0,none,none,none,none,none,none,none,none))
private def popView : Observations :=
  (some (2,4,some false,some false,some false,some true,some false,some false,none,none),
   some (0,2,some false,some true,none,none,none,none,none,none),
   some (2,2,some false,some false,none,none,some false,some false,none,none),
   some (0,0,none,none,none,none,none,none,none,none))

theorem graph_ordered :
    (rootView root,((left root).bind pushRoot).map rootView,((pushRoot root).bind left).map rootView,
      ((left root).bind popRoot).map rootView,((popRoot root).bind left).map rootView) =
    (beforeView,some pushView,some pushView,some popView,some popView) := rfl

theorem push_transport : Transport 128 hash locations
    ((NumericCommutation.pushUpdates 128 hash b (ca machine)).foldl
      (fun w op => Representation.write w op.1 op.2)
      ((NumericCopyCommutation.writeLog 128 hash a s machine).foldl
        (fun w op => Representation.write w op.1 op.2) store)) afterPush :=
  CopyLifecycle.copy_push_transport run a s b store machine afterPush initial rfl (by decide) (by decide)
theorem pop_transport : Transport 128 hash locations
    ((NumericCommutation.popUpdates 128 hash b (ca machine)).foldl
      (fun w op => Representation.write w op.1 op.2)
      ((NumericCopyCommutation.writeLog 128 hash a s machine).foldl
        (fun w op => Representation.write w op.1 op.2) store)) afterPop :=
  CopyLifecycle.copy_pop_transport run a s b store machine afterPop initial rfl (by decide) (by decide)

private theorem beforeA : Represented oldA (PrimitivePop.queries indices) a store := by
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
private theorem beforeB : Represented oldB (PrimitivePop.queries indices) b store := by
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
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
  · refine ⟨⟨by change 3 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
private theorem beforeS : Represented snapshot (PrimitivePop.queries indices) s store := by
  intro q member
  simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word observed; change some two = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change some zero = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change some zero = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
  · refine ⟨⟨by change 3 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
private def copyStore := CopyTransport.symbolicCopy a s store
/-- First actual typed root copy consumes BOTH old public relations. -/
theorem copy_root_bridge : Transport 128 hash locations copyStore (ca machine) ∧
    Represented copied ((PrimitivePop.queries indices).map (Query.prefix (path 0))) (.root 0) copyStore :=
  PathRepresentation.copy_at run root copied (path 0) (path 2) oldA snapshot rfl rfl rfl
    indices (.root 0) store machine
    (Represented.prefix (path 0) rfl (by change True ∧ True; trivial) beforeA)
    (Represented.prefix (path 2) rfl (by change True ∧ True; trivial) beforeS) initial
    (by decide) (by decide)
    (by
      intro i member
      simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide)
    (by
      intro i member
      simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide)
    (by intro i inside; have cases : i = 0 ∨ i = 1 := by change i < 2 at inside; omega
        rcases cases with rfl | rfl <;> decide)
    (by intro i inside; have cases : i = 0 ∨ i = 1 ∨ i = 2 := by change i < 3 at inside; omega
        rcases cases with rfl | rfl | rfl <;> decide)

private theorem bAfterCopy : Represented oldB (PrimitivePop.queries indices) b copyStore := by
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
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
  · refine ⟨⟨by change 3 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
/-- Actual second root push consumes the intermediate owner relation and
numeric Transport; postrelation is DERIVED via the unchanged owner's range iff. -/
theorem push_root_bridge : ∃ child final, pushResult.find (path 1) = some child ∧
    LifecycleNumeric.pushPrimitive 128 hash b (ca machine) = some final ∧
    let after := Representation.write (Representation.write copyStore (.data b oldB.length.val) zero)
      b (lengthWord child.length.val child.length.isLt)
    Transport 128 hash locations after final ∧
      Represented pushResult ((PrimitivePop.queries indices).map (Query.prefix (path 1))) (.root 0) after := by
  obtain ⟨child,final,found,executed,transport,iffRep⟩ :=
    PushTransport.push_at run copied pushResult (path 1) oldB rfl rfl indices (.root 0) copyStore (ca machine)
      (Represented.prefix (path 1) rfl (by change True ∧ True; trivial) bAfterCopy) copy_root_bridge.1 (by decide) (by decide)
  exact ⟨child,final,found,executed,transport,iffRep.mpr (by decide)⟩

theorem pop_root_bridge : ∃ child final, popResult.find (path 1) = some child ∧
    PrimitivePop.execute 128 hash b (ca machine) = some final ∧
    let after := Representation.write (Representation.write copyStore (.data b (oldB.length.val - 1)) zero)
      b (lengthWord child.length.val child.length.isLt)
    Transport 128 hash locations after final ∧
      Represented popResult ((PrimitivePop.queries indices).map (Query.prefix (path 1))) (.root 0) after :=
  PathRepresentation.pop_at run copied popResult (path 1) oldB rfl rfl indices (.root 0) copyStore (ca machine)
    (Represented.prefix (path 1) rfl (by change True ∧ True; trivial) bAfterCopy) copy_root_bridge.1
    (by
      intro q member
      simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide) (by decide)

private def samePush (m : WordStore) := LifecycleNumeric.pushPrimitive 128 hash a m
/-- GOOD region premises, but copying and pushing the SAME destination change
header and retained tail differently by order. -/
theorem same_destination_ordered :
    ((samePush (ca machine)).map numericView,((samePush machine).map ca).map numericView) =
    (some (three,one,two,zero,zero,zero,zero,one,one,one,zero,zero,zero,zero,zero,zero,one,one,seven),
     some (two,one,two,zero,zero,zero,zero,zero,one,one,zero,zero,zero,zero,zero,zero,one,one,seven)) := rfl
private def sourcePop (m : WordStore) := PrimitivePop.execute 128 hash s m
/-- Distinct copy/lifecycle WRITE regions alone are insufficient: pop changes
the source header read by copy. The GOOD run's region conditions still hold. -/
theorem source_interference_conditions :
    (∀ w ∈ NumericCopyCommutation.writeSet 128 hash a s machine,
      ∀ op ∈ NumericCommutation.popUpdates 128 hash s machine, w ≠ op.1) ∧
    ¬ (∀ op ∈ NumericCommutation.popUpdates 128 hash s machine,
      ∀ r ∈ NumericCopyCommutation.readSet 128 hash a s machine, op.1 ≠ r) := by decide

theorem source_interference_ordered :
    ((sourcePop (ca machine)).map numericView,((sourcePop machine).map ca).map numericView) =
    (some (two,one,one,zero,zero,zero,zero,one,one,one,zero,zero,zero,zero,zero,zero,one,one,seven),
     some (one,one,one,zero,zero,zero,zero,one,one,one,zero,zero,zero,zero,zero,zero,one,one,seven)) := rfl

private def emptyMachine := writeWord machine 12 zero
/-- Empty failed pop SHARES a source header READ with copy. Its actual write
log is empty; the theorem accepts it without excluding read/read sharing. -/
theorem shared_read_failure : sourcePop (ca emptyMachine) = (sourcePop emptyMachine).map ca :=
  CopyLifecycle.copy_pop run a s s emptyMachine (by decide) (by decide) (by decide) (by decide)
theorem shared_read_failure_ordered :
    (NumericCommutation.popTouches 128 hash s emptyMachine,
     NumericCommutation.popUpdates 128 hash s emptyMachine,
     (sourcePop (ca emptyMachine)).map numericView,((sourcePop emptyMachine).map ca).map numericView,
     numericView (ca emptyMachine)) =
    ([s],[],none,none,(zero,one,zero,zero,zero,zero,zero,one,one,one,zero,zero,zero,zero,zero,zero,one,one,seven)) := rfl

private def fullHeader : Semantics.Word := lengthWord (2 ^ 256 - 1) (by decide)
private def failureMachine := writeWord machine 8 fullHeader
/-- Numeric-only capacity fixture: no false old represented B relation. The
failed operation needs only its header, not an out-of-bounds reset location. -/
theorem capacity_failure : pushB (ca failureMachine) = (pushB failureMachine).map ca :=
  CopyLifecycle.copy_push run a s b failureMachine (by decide) (by decide) (by decide) (by decide)
theorem capacity_failure_ordered :
    (NumericCommutation.pushTouches 128 hash b failureMachine,
     NumericCommutation.pushUpdates 128 hash b failureMachine,
     (pushB (ca failureMachine)).map numericView,((pushB failureMachine).map ca).map numericView) =
    ([b],[],none,none) := rfl

private def aQueries := (PrimitivePop.queries indices).map (Query.prefix (path 0))
private def bQueries := (PrimitivePop.queries indices).map (Query.prefix (path 1))
private def pushStore := Representation.write (Representation.write copyStore (.data b 1) zero) b two
private def popStore := Representation.write (Representation.write copyStore (.data b 0) zero) b zero
private def pushedChild := (operationPush oldB).getD oldB
private def poppedChild := (recursivePop oldB).getD oldB
private theorem aApart : ∀ q ∈ aQueries, q.apart (path 1) := by
  intro q member
  obtain ⟨suffix,_,rfl⟩ := List.mem_map.mp member
  cases suffix with
  | word tail =>
    change Apart graph (.cons (.key (key 1)) .nil) (.cons (.key (key 0)) tail)
    exact .fork (.key (key 1) (key 0) (by decide)) .nil tail
  | length tail =>
    change Apart graph (.cons (.key (key 1)) .nil) (.cons (.key (key 0)) tail)
    exact .fork (.key (key 1) (key 0) (by decide)) .nil tail
private theorem aNonalias : ∀ q ∈ aQueries,
    q.location (.root 0) ≠ b ∧ q.location (.root 0) ≠ .data b 0 ∧ q.location (.root 0) ≠ .data b 1 := by
  intro q member
  simp only [aQueries,PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> decide

/-- PUBLIC graph frame theorem is applied to the ACTUAL second aggregate save;
its touched reset/header writes are separate from every selected A observation. -/
theorem push_copy_frame : Represented pushResult aQueries (.root 0) pushStore := by
  have first : Represented pushResult aQueries (.root 0)
      (Representation.write copyStore (.data b 1) zero) :=
    copy_root_bridge.2.write_frame (path 1) pushedChild rfl zero aApart
      (fun q member => (aNonalias q member).2.2)
  intro q member
  obtain ⟨supported,compatible,read⟩ := first q member
  refine ⟨supported,compatible,?_⟩
  intro word observed
  dsimp only [pushStore,popStore]
  rw [Representation.write_other _ _ _ _ (aNonalias q member).1]
  exact read word observed

theorem pop_copy_frame : Represented popResult aQueries (.root 0) popStore := by
  have first : Represented popResult aQueries (.root 0)
      (Representation.write copyStore (.data b 0) zero) :=
    copy_root_bridge.2.write_frame (path 1) poppedChild rfl zero aApart
      (fun q member => (aNonalias q member).2.1)
  intro q member
  obtain ⟨supported,compatible,read⟩ := first q member
  refine ⟨supported,compatible,?_⟩
  intro word observed
  dsimp only [pushStore,popStore]
  rw [Representation.write_other _ _ _ _ (aNonalias q member).1]
  exact read word observed

/-- Full finite BOTH-target selected postrepresentation and actual mixed
numeric Transport, not a postrelation premise or two evaluators compared. -/
theorem push_full_bridge : Transport 128 hash locations pushStore afterPush ∧
    Represented pushResult (aQueries ++ bQueries) (.root 0) pushStore := by
  obtain ⟨child,final,found,_,_,represented⟩ := push_root_bridge
  change some pushedChild = some child at found
  cases found
  refine ⟨push_transport,?_⟩
  intro q member
  rcases List.mem_append.mp member with atA | atB
  · exact push_copy_frame q atA
  · exact represented q atB

theorem pop_full_bridge : Transport 128 hash locations popStore afterPop ∧
    Represented popResult (aQueries ++ bQueries) (.root 0) popStore := by
  obtain ⟨child,final,found,_,_,represented⟩ := pop_root_bridge
  change some poppedChild = some child at found
  cases found
  refine ⟨pop_transport,?_⟩
  intro q member
  rcases List.mem_append.mp member with atA | atB
  · exact pop_copy_frame q atA
  · exact represented q atB

private def samePushRoot (v : Value graph Root) := pushAt v (path 0)
private def sourcePopRoot (v : Value graph Root) := popAt v (path 2)
/-- Complete independent graph counterparts to BOTH GOOD-region interference
negatives; headers, tails, retained/live aliases and outside keys distinguish. -/
theorem interfering_graph_ordered :
    (((left root).bind samePushRoot).map rootView,((samePushRoot root).bind left).map rootView,
      ((left root).bind sourcePopRoot).map rootView,((sourcePopRoot root).bind left).map rootView) =
    (some (some (3,4,some false,some false,some false,some true,some false,some false,some false,none),
      some (1,2,some true,some true,none,none,some true,none,none,none),
      some (2,2,some false,some false,none,none,some false,some false,none,none),
      some (0,0,none,none,none,none,none,none,none,none)),
     some (some (2,4,some false,some false,some false,some false,some false,some false,none,none),
      some (1,2,some true,some true,none,none,some true,none,none,none),
      some (2,2,some false,some false,none,none,some false,some false,none,none),
      some (0,0,none,none,none,none,none,none,none,none)),
     some (some (2,4,some false,some false,some false,some true,some false,some false,none,none),
      some (1,2,some true,some true,none,none,some true,none,none,none),
      some (1,2,some false,some false,none,none,some false,none,none,none),
      some (0,0,none,none,none,none,none,none,none,none)),
     some (some (1,4,some false,some false,some false,some true,some false,none,none,none),
      some (1,2,some true,some true,none,none,some true,none,none,none),
      some (1,2,some false,some false,none,none,some false,none,none,none),
      some (0,0,none,none,none,none,none,none,none,none))) := rfl

private def emptySource : Value graph Elem :=
  .array ⟨2,by decide⟩ ⟨0,by decide⟩ (by decide) (fun _ => .present (.prim false))
private def emptyRoot : Value graph Root :=
  .mapping (fun k => if k = key 2 then .present emptySource else slots k)
theorem shared_read_failure_graph :
    (((left emptyRoot).bind sourcePopRoot).map rootView,((sourcePopRoot emptyRoot).bind left).map rootView,
      (left emptyRoot).map rootView) =
    (none,none,some (some (0,4,some false,some false,some false,some true,none,none,none,none),
      some (1,2,some true,some true,none,none,some true,none,none,none),
      some (0,2,some false,some false,none,none,none,none,none,none),
      some (0,0,none,none,none,none,none,none,none,none))) := rfl

/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.copy_push_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copy_push_commutes
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.copy_pop_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copy_pop_commutes
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.numeric_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_ordered
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.graph_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms graph_ordered
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.push_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_transport
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.pop_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_transport
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.copy_root_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copy_root_bridge
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.push_root_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_root_bridge
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.pop_root_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_root_bridge
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.same_destination_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms same_destination_ordered
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.source_interference_conditions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_interference_conditions
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.source_interference_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_interference_ordered
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.shared_read_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shared_read_failure
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.shared_read_failure_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shared_read_failure_ordered
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.capacity_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms capacity_failure
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.capacity_failure_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms capacity_failure_ordered
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.push_copy_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_copy_frame
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.pop_copy_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_copy_frame
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.push_full_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_full_bridge
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.pop_full_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_full_bridge
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.interfering_graph_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms interfering_graph_ordered
/-- info: 'Solidity.Backend.StorageOps.CopyLifecycleControls.shared_read_failure_graph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms shared_read_failure_graph

end Solidity.Backend.StorageOps.CopyLifecycleControls
