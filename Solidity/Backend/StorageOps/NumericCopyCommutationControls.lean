import Solidity.Backend.StorageOps.NumericCopyCommutation
import Solidity.Backend.StorageOps.SnapshotCommutation
import Solidity.Backend.StorageOps.PathRepresentation

/-! Shared-source actual copies, represented inputs and ordered observations.
Read/read sharing is inhabited; the negative run has GOOD regions but interfering
read/write sets. Option graph laws do not imply reachable-world rollback. -/
namespace Solidity.Backend.StorageOps.NumericCopyCommutationControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def graph : Schema 0 where
  origin := "v10-copy-commutation-controls"
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
  .array ⟨2,by decide⟩ ⟨1,by decide⟩ (by decide) (fun i => .present (.prim (decide (i.val = 1))))
private def snapshot : Value graph Elem :=
  .array ⟨2,by decide⟩ ⟨2,by decide⟩ (by decide) (fun _ => .present (.prim false))
private def slots (k : PrimTy.uint.Denote) : Slot graph Elem :=
  if k = key 0 then .present oldA else if k = key 1 then .present oldB else
  if k = key 2 then .present snapshot else .absent
private def root : Value graph Root := .mapping slots
private def path (k : Fin 4) : TypeGraph.Path graph Root Elem := .cons (.key (key k)) .nil
private def element (i : Index) : TypeGraph.Path graph Elem (.prim .bool) := .cons (.index i) .nil
private def left (v : Value graph Root) := recursiveCopyAt v (path 0) (path 2)
private def right (v : Value graph Root) := recursiveCopyAt v (path 1) (path 2)
private def store : Store := fun l => if l = a then three else if l = b then one else
  if l = s then two else if l = .root 2 then seven else
  if l = .data a 0 ∨ l = .data a 1 ∨ l = .data a 2 ∨ l = .data a 3 ∨ l = .data b 1 then one else zero
private def machine : WordStore := fun n => if n = 4 then three else if n = 8 then one else
  if n = 12 then two else if n = 2 then seven else
  if n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 25 ∨ n = 96 ∨ n = 100 then one else zero
private def ca (m : WordStore) := NumericTraversal.copy 128 hash a s m
private def cb (m : WordStore) := NumericTraversal.copy 128 hash b s m
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

/-- This GOOD run permits a nonempty common source read set. -/
theorem shared_source_commutes : cb (ca machine) = ca (cb machine) :=
  NumericCopyCommutation.copy_copy run a s b s machine (by decide) (by decide) (by decide) (by decide)
theorem shared_read_inhabited : s ∈ NumericCopyCommutation.readSet 128 hash a s machine ∧
    s ∈ NumericCopyCommutation.readSet 128 hash b s machine ∧
    .data s 1 ∈ NumericCopyCommutation.readSet 128 hash a s machine ∧
    .data s 1 ∈ NumericCopyCommutation.readSet 128 hash b s machine := by decide

theorem graph_commutes : (left root).bind right = (right root).bind left :=
  actual_mapping_copies_commute slots (key 0) (key 2) (key 1) (key 2)
    (by decide) (by decide) (by decide) .nil .nil .nil .nil

/-- Complete raw/live/retained/defaulted observations of BOTH actual graph
orders; the unrelated absent mapping key remains defaulted, not materialized. -/
theorem graph_ordered :
    (rootView root,((left root).bind right).map rootView,((right root).bind left).map rootView) =
    ((some (3,4,some true,some true,some true,some true,some true,some true,some true,none),
      some (1,2,some false,some true,none,none,some false,none,none,none),
      some (2,2,some false,some false,none,none,some false,some false,none,none),
      some (0,0,none,none,none,none,none,none,none,none)),
     some (some (2,4,some false,some false,some false,some true,some false,some false,none,none),
      some (2,2,some false,some false,none,none,some false,some false,none,none),
      some (2,2,some false,some false,none,none,some false,some false,none,none),
      some (0,0,none,none,none,none,none,none,none,none)),
     some (some (2,4,some false,some false,some false,some true,some false,some false,none,none),
      some (2,2,some false,some false,none,none,some false,some false,none,none),
      some (2,2,some false,some false,none,none,some false,some false,none,none),
      some (0,0,none,none,none,none,none,none,none,none))) := rfl

theorem numeric_ordered : (numericView machine,numericView (cb (ca machine)),numericView (ca (cb machine))) =
    ((three,one,two,zero,one,one,one,one,zero,one,zero,zero,zero,zero,zero,zero,one,one,seven),
     (two,two,two,zero,zero,zero,zero,one,zero,zero,zero,zero,zero,zero,zero,zero,one,one,seven),
     (two,two,two,zero,zero,zero,zero,one,zero,zero,zero,zero,zero,zero,zero,zero,one,one,seven)) := rfl

theorem exact_numeric_alias : NumericTraversal.copy 128 hash a a machine = machine :=
  NumericCopyCommutation.copy_self 128 hash a machine

private def crossA (m : WordStore) := NumericTraversal.copy 128 hash a b m
private def crossB (m : WordStore) := NumericTraversal.copy 128 hash b a m
/-- Distinct destinations alone are INSUFFICIENT, despite the GOOD run. -/
theorem cross_conditions :
    (∀ x ∈ NumericCopyCommutation.writeSet 128 hash a b machine,
      ∀ y ∈ NumericCopyCommutation.writeSet 128 hash b a machine, x ≠ y) ∧
    ¬ (∀ x ∈ NumericCopyCommutation.writeSet 128 hash a b machine,
      ∀ y ∈ NumericCopyCommutation.readSet 128 hash b a machine, x ≠ y) := by decide

theorem cross_ordered : (numericView (crossB (crossA machine)),numericView (crossA (crossB machine))) =
    ((one,one,two,zero,zero,zero,zero,one,zero,one,zero,zero,zero,zero,zero,zero,one,one,seven),
     (three,three,two,zero,one,one,one,one,one,one,one,zero,zero,zero,zero,zero,one,one,seven)) := rfl
theorem cross_different : crossB (crossA machine) 4 ≠ crossA (crossB machine) 4 := by decide

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
    intro word observed; change some zero = some word at observed; cases observed; rfl
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
/-- BOTH different destination values and the shared source are represented
by the PUBLIC relation in the SAME inhabited finite run and numeric store. -/
theorem represented_inputs :
    Represented oldA (PrimitivePop.queries indices) a store ∧
    Represented oldB (PrimitivePop.queries indices) b store ∧
    Represented snapshot (PrimitivePop.queries indices) s store ∧
    Transport 128 hash locations store machine := ⟨beforeA,beforeB,beforeS,initial⟩

theorem a_bridge :
    Transport 128 hash locations (CopyTransport.symbolicCopy a s store)
      (NumericTraversal.copy 128 hash a s machine) ∧
    Represented (recursiveCopy oldA snapshot) (PrimitivePop.queries indices) a
      (CopyTransport.symbolicCopy a s store) :=
  CopyTransport.complete run oldA snapshot indices a s store machine beforeA beforeS initial
    (by decide) (by decide) (by
      intro i member
      simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide) (by
      intro i member
      simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide)
    (by intro i inside; have cases : i = 0 ∨ i = 1 := by change i < 2 at inside; omega
        rcases cases with rfl | rfl <;> decide)
    (by intro i inside; have cases : i = 0 ∨ i = 1 ∨ i = 2 := by change i < 3 at inside; omega
        rcases cases with rfl | rfl | rfl <;> decide)

theorem b_bridge :
    Transport 128 hash locations (CopyTransport.symbolicCopy b s store)
      (NumericTraversal.copy 128 hash b s machine) ∧
    Represented (recursiveCopy oldB snapshot) (PrimitivePop.queries indices) b
      (CopyTransport.symbolicCopy b s store) :=
  CopyTransport.complete run oldB snapshot indices b s store machine beforeB beforeS initial
    (by decide) (by decide) (by
      intro i member
      simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide) (by
      intro i member
      simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide)
    (by intro i inside; have cases : i = 0 ∨ i = 1 := by change i < 2 at inside; omega
        rcases cases with rfl | rfl <;> decide)
    (by intro i inside; have cases : i = 0 ∨ i = 1 := by change i < 2 at inside; omega
        rcases cases with rfl | rfl <;> decide)

/-- Actual nonempty typed root reads/save lift the published child relation. -/
theorem a_root_bridge :
    Transport 128 hash locations (CopyTransport.symbolicCopy a s store)
      (NumericTraversal.copy 128 hash a s machine) ∧
    Represented ((recursiveCopyAt root (path 0) (path 2)).getD root)
      ((PrimitivePop.queries indices).map (Query.prefix (path 0))) (.root 0)
      (CopyTransport.symbolicCopy a s store) :=
  PathRepresentation.copy_at run root _ (path 0) (path 2) oldA snapshot rfl rfl rfl
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

/-- Actual nonempty typed root reads/save lift the published child relation. -/
theorem b_root_bridge :
    Transport 128 hash locations (CopyTransport.symbolicCopy b s store)
      (NumericTraversal.copy 128 hash b s machine) ∧
    Represented ((recursiveCopyAt root (path 1) (path 2)).getD root)
      ((PrimitivePop.queries indices).map (Query.prefix (path 1))) (.root 0)
      (CopyTransport.symbolicCopy b s store) :=
  PathRepresentation.copy_at run root _ (path 1) (path 2) oldB snapshot rfl rfl rfl
    indices (.root 0) store machine
    (Represented.prefix (path 1) rfl (by change True ∧ True; trivial) beforeB)
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
    (by intro i inside; have cases : i = 0 ∨ i = 1 := by change i < 2 at inside; omega
        rcases cases with rfl | rfl <;> decide)

theorem generated_sequence :
    Transport 128 hash locations
      ((NumericCopyCommutation.writeLog 128 hash b s (ca machine)).foldl
        (fun w op => Representation.write w op.1 op.2)
        ((NumericCopyCommutation.writeLog 128 hash a s machine).foldl
          (fun w op => Representation.write w op.1 op.2) store)) (cb (ca machine)) :=
  NumericCopyCommutation.sequence_transport run a s b s store machine initial (by decide) (by decide)

private def crossLeft (v : Value graph Root) := recursiveCopyAt v (path 0) (path 1)
private def crossRight (v : Value graph Root) := recursiveCopyAt v (path 1) (path 0)
/-- The independent graph operations also observe the interfering current
source. This is an actual Option result in each order, not a world transaction. -/
theorem cross_graph_ordered :
    (((crossLeft root).bind crossRight).map rootView,((crossRight root).bind crossLeft).map rootView) =
    (some (some (1,4,some false,some false,some false,some true,some false,none,none,none),
      some (1,2,some false,some true,none,none,some false,none,none,none),
      some (2,2,some false,some false,none,none,some false,some false,none,none),
      some (0,0,none,none,none,none,none,none,none,none)),
     some (some (3,4,some true,some true,some true,some true,some true,some true,some true,none),
      some (3,3,some true,some true,some true,none,some true,some true,some true,none),
      some (2,2,some false,some false,none,none,some false,some false,none,none),
      some (0,0,none,none,none,none,none,none,none,none))) := rfl

private def badSource (v : Value graph Root) := recursiveCopyAt v
  ((path 0).append (element (ix 3))) ((path 2).append (element (ix 3)))
private def badDestination (v : Value graph Root) := recursiveCopyAt v
  ((path 1).append (element (ix 3))) ((path 2).append (element (ix 0)))
theorem malformed_orders :
    (badSource root).bind right = none ∧ (right root).bind badSource = none ∧
    (badDestination root).bind left = none ∧ (left root).bind badDestination = none := ⟨rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutationControls.shared_source_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shared_source_commutes
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutationControls.shared_read_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shared_read_inhabited
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutationControls.graph_commutes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms graph_commutes
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutationControls.graph_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms graph_ordered
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutationControls.numeric_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_ordered
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutationControls.exact_numeric_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms exact_numeric_alias
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutationControls.cross_conditions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms cross_conditions
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutationControls.cross_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms cross_ordered
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutationControls.cross_different' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms cross_different
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutationControls.represented_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_inputs
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutationControls.a_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms a_bridge
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutationControls.b_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms b_bridge
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutationControls.a_root_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms a_root_bridge
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutationControls.b_root_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms b_root_bridge
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutationControls.generated_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms generated_sequence
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutationControls.cross_graph_ordered' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms cross_graph_ordered
/-- info: 'Solidity.Backend.StorageOps.NumericCopyCommutationControls.malformed_orders' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms malformed_orders

end Solidity.Backend.StorageOps.NumericCopyCommutationControls
