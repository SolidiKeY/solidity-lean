import Solidity.Backend.StorageOps.NumericTraversal
import Solidity.Backend.StorageOps.CopyTransport
import Solidity.Backend.StorageOps.TargetCopyRepresentation
import Solidity.Backend.StorageOps.TargetCopyLifecycle
import Solidity.Backend.StorageOps.TargetCopyRead
import Solidity.Backend.StorageOps.TargetCopyWrite

/-! Actual machine-header copy controls and full ordered observations.
The raw overlapping-word counterexample is explicitly outside FiniteRun; the
represented main run and self-alias use the published per-run conditions. -/
namespace Solidity.Backend.StorageOps.NumericTraversalControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def graph : Schema 0 where
  origin := "v10-numeric-traversal-controls"
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
private def dst : Solidity.Storage.Loc := .root 0
private def srcBase : Solidity.Storage.Loc := .root 1
private def zero : Semantics.Word := ClearDemands.zero
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def three : Semantics.Word := lengthWord 3 (by decide)
private def seven : Semantics.Word := ⟨7, by decide⟩
private def hash (p : Solidity.Storage.Pre) : Nat := if p = .data 0 then 8 else if p = .data 1 then 16 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0, .data 1]
private def locations : List Solidity.Storage.Loc := [.root 0, .root 1,
  .data (.root 0) 0, .data (.root 0) 1, .data (.root 0) 2, .data (.root 0) 3,
  .data (.root 1) 0, .data (.root 1) 1, .data (.root 1) 2, .data (.root 1) 3]
private def old : Value graph (.array (.prim .bool)) :=
  .array ⟨4, by decide⟩ ⟨3, by decide⟩ (by decide) (fun _ => .present (.prim true))
private def source : Value graph (.array (.prim .bool)) :=
  .array ⟨2, by decide⟩ ⟨1, by decide⟩ (by decide)
    (fun i => .present (.prim (decide (i.val = 1))))
private def result := recursiveCopy old source
private def store : Store := fun l => if l = .root 0 then three else if l = .root 1 then one else
  if l = .root 2 then seven else if l = .data dst 0 ∨ l = .data dst 1 ∨ l = .data dst 2 ∨
    l = .data dst 3 ∨ l = .data srcBase 1 then one else zero
private def machine : WordStore := fun a => if a = 0 then three else if a = 1 then one else
  if a = 2 then seven else if a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨ a = 17 ∨ a = 20 ∨ a = 24 then one else zero
private def final := NumericTraversal.copy 32 hash dst srcBase machine
private def path (i : Index) : TypeGraph.Path graph (.array (.prim .bool)) (.prim .bool) := .cons (.index i) .nil
private def view (m : WordStore) := (m 0, m 1, m 8, m 9, m 10, m 11, m 16, m 17, m 18, m 19, m 20, m 24, m 2)
private theorem run : FiniteRun 32 4 2 hash preimages locations := by
  constructor
  · intro p; simp only [hash]; split <;> (first | decide | (split <;> decide))
  · decide
  · decide
  · decide
  · intro l member
    simp only [locations, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    simp only [locations, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem initial : Transport 32 hash locations store machine := by
  intro l member
  simp only [locations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem beforeDst : Represented old (PrimitivePop.queries indices) dst store := by
  intro q member
  simp only [PrimitivePop.queries, indices, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro, ⟨by decide, by decide⟩, ?_⟩
    intro word observed; change some three = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 3 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
private theorem beforeSrc : Represented source (PrimitivePop.queries indices) srcBase store := by
  intro q member
  simp only [PrimitivePop.queries, indices, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro, ⟨by decide, by decide⟩, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some zero = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
  · refine ⟨⟨by change 3 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
private theorem covered : ∀ i ∈ indices,
    Solidity.Storage.Loc.data dst i.val ∈ locations ∧ Solidity.Storage.Loc.data srcBase i.val ∈ locations := by
  intro i member
  simp only [indices, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide
private theorem visited : ∀ j < max old.length.val source.length.val,
    Solidity.Storage.Loc.data dst j ∈ locations := by
  intro j inside
  have cases : j = 0 ∨ j = 1 ∨ j = 2 := by change j < max 3 1 at inside; omega
  rcases cases with rfl | rfl | rfl <;> decide

/-- Actual application of BOTH owner relations, full finite run and selected
query theorem; destination and source are distinct, not a reflexive fixture. -/
theorem bridge :
    (Query.length .nil).read result = some (final (dst.word 32 hash)) ∧
    (∀ i ∈ indices, ∀ word, (PrimitivePop.elementQuery i).read result = some word →
      final ((Solidity.Storage.Loc.data dst i.val).word 32 hash) = word) ∧
    (∀ a, a ≠ dst.word 32 hash → (∀ j < max old.length.val source.length.val,
      a ≠ (Solidity.Storage.Loc.data dst j).word 32 hash) → final a = machine a) :=
  NumericTraversal.represented_observations run old source indices dst srcBase store machine beforeDst beforeSrc initial
    (by decide) (by decide) (fun i member => (covered i member).1) (fun i member => (covered i member).2) visited

/-- Source shadow is NOT copied; shortened live tail IS cleared; the older
destination shadow IS retained. Both unrelated map-key words are framed. -/
theorem ordered :
    (old.length.val, old.extent.val, source.length.val, source.extent.val,
      old.observe (path (ix 0)), old.observe (path (ix 1)), old.observe (path (ix 2)), old.observe (path (ix 3)),
      source.observe (path (ix 0)), source.observe (path (ix 1)), source.observe (path (ix 2)), source.observe (path (ix 3)),
      result.length.val, result.extent.val, result.observe (path (ix 0)), result.observe (path (ix 1)),
      result.observe (path (ix 2)), result.observe (path (ix 3)),
      ((path (ix 2)).readLive Value.dflt old).map Value.head,
      ((path (ix 2)).readLive Value.dflt result).map Value.head,
      ((path (ix 3)).readLive Value.dflt old).map Value.head,
      ((path (ix 3)).readLive Value.dflt result).map Value.head, view machine, view final) =
    (3, 4, 1, 2, some true, some true, some true, some true,
      some false, some true, none, none, 1, 4, some false, some false, some false, some true,
      some true, none, none, none,
      (three, one, one, one, one, one, zero, one, zero, zero, one, one, seven),
      (one, one, zero, zero, zero, one, zero, one, zero, zero, one, one, seven)) := rfl

private def address (i : Nat) := (Solidity.Storage.Loc.data dst i).word 32 hash
private def payload (i : Nat) := if i < 1 then machine ((Solidity.Storage.Loc.data srcBase i).word 32 hash) else zero
private def prefixState (count : Nat) := NumericTraversal.writePrefix address payload count machine
/-- Explicit progress keeps header unchanged until the final header write. -/
theorem progress_ordered : (view (prefixState 0), view (prefixState 1), view (prefixState 2), view (prefixState 3)) =
    ((three, one, one, one, one, one, zero, one, zero, zero, one, one, seven),
      (three, one, zero, one, one, one, zero, one, zero, zero, one, one, seven),
      (three, one, zero, zero, one, one, zero, one, zero, zero, one, one, seven),
      (three, one, zero, zero, zero, one, zero, one, zero, zero, one, one, seven)) := rfl
private def wrongTail := writeWord (prefixState 1) 0 one
private def wrongShadow := writeWord final 11 zero

theorem negatives : wrongTail 9 ≠ final 9 ∧ wrongShadow 11 ≠ final 11 ∧
    (PrimitivePop.elementQuery (ix 1)).read result = some zero ∧
    (PrimitivePop.elementQuery (ix 3)).read result = some one := ⟨by decide, by decide, rfl, rfl⟩
theorem wrong_ordered : (view wrongTail, view wrongShadow) =
    ((one, one, zero, one, one, one, zero, one, zero, zero, one, one, seven),
      (one, one, zero, zero, zero, zero, zero, one, zero, zero, one, one, seven)) := rfl

/-- Exact-alias copy uses the same captured source and real run; all words
stay unchanged (including source shadow, unrelated map keys and sentinel). -/
theorem self_alias_ordered : view (NumericTraversal.copy 32 hash dst dst machine) = view machine := rfl

private def growDst : Value graph (.array (.prim .bool)) :=
  .array ⟨1, by decide⟩ ⟨1, by decide⟩ (by decide) (fun _ => .present (.prim true))
private def growSrc : Value graph (.array (.prim .bool)) :=
  .array ⟨4, by decide⟩ ⟨3, by decide⟩ (by decide)
    (fun i => .present (.prim (decide (i.val = 1 ∨ i.val = 3))))
private def growResult := recursiveCopy growDst growSrc
private def growMachine : WordStore := writeWord (writeWord (writeWord machine 0 one) 1 three) 19 one
private def growFinal := NumericTraversal.copy 32 hash dst srcBase growMachine

/-- Changed actual runtime headers grow the destination extent to THREE,
not source extent FOUR; its older source shadow remains ignored. -/
theorem grow_ordered :
    (growDst.length.val, growDst.extent.val, growSrc.length.val, growSrc.extent.val,
      growDst.observe (path (ix 0)), growDst.observe (path (ix 1)), growDst.observe (path (ix 2)), growDst.observe (path (ix 3)),
      growSrc.observe (path (ix 0)), growSrc.observe (path (ix 1)), growSrc.observe (path (ix 2)), growSrc.observe (path (ix 3)),
      growResult.length.val, growResult.extent.val, growResult.observe (path (ix 0)), growResult.observe (path (ix 1)),
      growResult.observe (path (ix 2)), growResult.observe (path (ix 3)),
      ((path (ix 2)).readLive Value.dflt growDst).map Value.head,
      ((path (ix 2)).readLive Value.dflt growResult).map Value.head,
      ((path (ix 3)).readLive Value.dflt growSrc).map Value.head, view growMachine, view growFinal) =
    (1, 1, 3, 4, some true, none, none, none, some false, some true, some false, some true,
      3, 3, some false, some true, some false, none, none, some false, none,
      (one, three, one, one, one, one, zero, one, zero, one, one, one, seven),
      (three, three, zero, one, zero, one, zero, one, zero, one, one, one, seven)) := rfl

private def emptyDst : Value graph (.array (.prim .bool)) :=
  .array ⟨4, by decide⟩ ⟨0, by decide⟩ (by decide) (fun _ => .present (.prim true))
private def emptySrc : Value graph (.array (.prim .bool)) :=
  .array ⟨2, by decide⟩ ⟨0, by decide⟩ (by decide) (fun _ => .present (.prim false))
private def emptyResult := recursiveCopy emptyDst emptySrc
private def emptyMachine : WordStore := writeWord (writeWord (writeWord machine 0 zero) 1 zero) 17 zero
private def emptyFinal := NumericTraversal.copy 32 hash dst srcBase emptyMachine

theorem empty_ordered :
    (emptyDst.length.val, emptyDst.extent.val, emptySrc.length.val, emptySrc.extent.val,
      emptyResult.length.val, emptyResult.extent.val,
      emptyDst.observe (path (ix 0)), emptyDst.observe (path (ix 1)), emptyDst.observe (path (ix 2)), emptyDst.observe (path (ix 3)),
      emptySrc.observe (path (ix 0)), emptySrc.observe (path (ix 1)), emptySrc.observe (path (ix 2)), emptySrc.observe (path (ix 3)),
      emptyResult.observe (path (ix 0)), emptyResult.observe (path (ix 1)), emptyResult.observe (path (ix 2)), emptyResult.observe (path (ix 3)),
      ((path (ix 0)).readLive Value.dflt emptyResult).map Value.head, view emptyMachine, view emptyFinal) =
    (0, 4, 0, 2, 0, 4, some true, some true, some true, some true,
      some false, some false, none, none, some true, some true, some true, some true, none,
      (zero, zero, one, one, one, one, zero, zero, zero, zero, one, one, seven),
      (zero, zero, one, one, one, one, zero, zero, zero, zero, one, one, seven)) := rfl

private def absentSrc : Value graph (.array (.prim .bool)) :=
  .array ⟨2, by decide⟩ ⟨1, by decide⟩ (by decide)
    (fun i => if i.val = 0 then .absent else .present (.prim true))
private def absentDst : Value graph (.array (.prim .bool)) :=
  .array ⟨4, by decide⟩ ⟨3, by decide⟩ (by decide)
    (fun i => if i.val = 1 then .absent else .present (.prim true))
private def absentResult := recursiveCopy absentDst absentSrc
private def absentMachine : WordStore := writeWord machine 9 zero
private def absentFinal := NumericTraversal.copy 32 hash dst srcBase absentMachine

theorem absent_ordered :
    (absentDst.length.val, absentDst.extent.val, absentSrc.length.val, absentSrc.extent.val,
      absentResult.length.val, absentResult.extent.val,
      absentDst.observe (path (ix 0)), absentDst.observe (path (ix 1)), absentDst.observe (path (ix 2)), absentDst.observe (path (ix 3)),
      absentSrc.observe (path (ix 0)), absentSrc.observe (path (ix 1)), absentSrc.observe (path (ix 2)), absentSrc.observe (path (ix 3)),
      absentResult.observe (path (ix 0)), absentResult.observe (path (ix 1)), absentResult.observe (path (ix 2)), absentResult.observe (path (ix 3)),
      absentSrc.slots ⟨0, by decide⟩, absentDst.slots ⟨1, by decide⟩, absentResult.slots ⟨0, by decide⟩, absentResult.slots ⟨1, by decide⟩,
      ((path (ix 1)).readLive Value.dflt absentDst).map Value.head,
      ((path (ix 1)).readLive Value.dflt absentResult).map Value.head, view absentMachine, view absentFinal) =
    (3, 4, 1, 2, 1, 4, some true, some false, some true, some true,
      some false, some true, none, none, some false, some false, some false, some true,
      Slot.absent, Slot.absent, Slot.present (Value.prim (G := graph) (p := .bool) false), Slot.absent,
      some false, none,
      (three, one, one, zero, one, one, zero, one, zero, zero, one, one, seven),
      (one, one, zero, zero, zero, one, zero, one,zero, zero, one, one, seven)) := rfl

/-- Raw loop countercontrol ONLY: overlapping numeric word ranges here are
not asserted to satisfy the owner FiniteRun. Reading an already mutated source
changes the result; the real writePrefix uses a captured source payload. -/
private def overlapInitial : WordStore := fun a => if a = 0 ∨ a = 2 then one else if a = 4 then seven else zero
private def capturedOverlap := NumericTraversal.writePrefix (fun i => i + 1) (fun i => overlapInitial i) 3 overlapInitial
private def incremental : Nat → WordStore → WordStore
  | 0, initial => initial
  | count + 1, initial =>
    let prior := incremental count initial
    writeWord prior (count + 1) (prior count)
private def incrementalOverlap := incremental 3 overlapInitial
private def overlapView (m : WordStore) := (m 0, m 1, m 2, m 3, m 4)

theorem overlap_wrong_order : incrementalOverlap 2 ≠ capturedOverlap 2 ∧
    (overlapView overlapInitial, overlapView capturedOverlap, overlapView incrementalOverlap) =
      ((one, zero, one, zero, seven), (one, one, zero, one, seven), (one, one, one, one, seven)) := ⟨by decide, rfl⟩

theorem restart :
    NumericTraversal.writePrefix (fun i => i + 1) (fun i => overlapInitial i) 1
      (NumericTraversal.writePrefix (fun i => i + 1) (fun i => overlapInitial i) 2 overlapInitial) =
    NumericTraversal.writePrefix (fun i => i + 1) (fun i => overlapInitial i) 2 overlapInitial := by
  apply NumericTraversal.prefix_restart
  intro i _ j _ different equal
  exact different (by omega)

/-- The exact-alias control also consumes the actual represented observation
certificate under the SAME finite run; alias is not excluded by an inequality. -/
theorem self_alias_bridge : ∀ i ∈ indices, ∀ word,
    (PrimitivePop.elementQuery i).read (recursiveCopy old old) = some word →
    NumericTraversal.copy 32 hash dst dst machine ((Solidity.Storage.Loc.data dst i.val).word 32 hash) = word :=
  (NumericTraversal.represented_observations run old old indices dst dst store machine beforeDst beforeDst initial
    (by decide) (by decide) (fun i member => (covered i member).1) (fun i member => (covered i member).1)
    visited).2.1

/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bridge
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.progress_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms progress_ordered
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.negatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms negatives
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.wrong_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_ordered
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.self_alias_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms self_alias_ordered
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.grow_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms grow_ordered
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.empty_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_ordered
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.absent_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms absent_ordered
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.overlap_wrong_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms overlap_wrong_order
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.restart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms restart
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.self_alias_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms self_alias_bridge

private def afterCopy : Store := CopyTransport.symbolicCopy dst srcBase store
private def symbolicView (w : Store) :=
  (w dst, w srcBase, w (.data dst 0), w (.data dst 1), w (.data dst 2), w (.data dst 3),
    w (.data srcBase 0), w (.data srcBase 1), w (.data srcBase 2), w (.data srcBase 3), w (.root 2))

/-- The SAME nontrivial main fixture now has actual post-copy owner
representation AND full finite numeric transport, not merely point agreement. -/
theorem full_copy_bridge : Transport 32 hash locations afterCopy final ∧
    Represented result (PrimitivePop.queries indices) dst afterCopy :=
  CopyTransport.complete run old source indices dst srcBase store machine beforeDst beforeSrc initial
    (by decide) (by decide) (fun i member => (covered i member).1) (fun i member => (covered i member).2)
    (by
      intro i inside
      have equal : i = 0 := by change i < 1 at inside; omega
      subst i
      decide)
    visited

theorem full_alias_bridge :
    Transport 32 hash locations (CopyTransport.symbolicCopy dst dst store) (NumericTraversal.copy 32 hash dst dst machine) ∧
    Represented (recursiveCopy old old) (PrimitivePop.queries indices) dst (CopyTransport.symbolicCopy dst dst store) :=
  CopyTransport.complete run old old indices dst dst store machine beforeDst beforeDst initial
    (by decide) (by decide) (fun i member => (covered i member).1) (fun i member => (covered i member).1)
    (by intro i inside; exact visited i (by change i < max 3 1; change i < 3 at inside; omega)) visited

theorem symbolic_ordered : (symbolicView store, symbolicView afterCopy) =
    ((three, one, one, one, one, one, zero, one, zero, zero, seven),
      (one, one, zero, zero, zero, one, zero, one, zero, zero, seven)) := rfl

private def wrongTailStore : Store := Representation.write
  (Representation.write store (.data dst 0) zero) dst one
private def wrongShadowStore : Store := Representation.write afterCopy (.data dst 3) zero

theorem rejected_stores :
    ¬ Represented result (PrimitivePop.queries indices) dst wrongTailStore ∧
    ¬ Represented result (PrimitivePop.queries indices) dst wrongShadowStore := by
  constructor
  · intro bad
    have wrong := (bad (PrimitivePop.elementQuery (ix 1))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))).2.2 zero rfl
    exact (by decide : one ≠ zero) wrong
  · intro bad
    have wrong := (bad (PrimitivePop.elementQuery (ix 3))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))).2.2 one rfl
    exact (by decide : zero ≠ one) wrong

theorem wrong_symbolic_ordered : (symbolicView wrongTailStore, symbolicView wrongShadowStore) =
    ((one, one, zero, one, one, one, zero, one, zero, zero, seven),
      (one, one, zero, zero, zero, zero, zero, one, zero, zero, seven)) := rfl

private def badIndex : Index := ⟨4, by decide⟩
/-- The failed destination query adds NO successful numeric-cell constraint.
Positive represented reads above remain nontrivial; Option failure is explicit. -/
theorem with_failed_destination :
    Represented result (PrimitivePop.queries indices ++ [PrimitivePop.elementQuery badIndex]) dst afterCopy ∧
    ((PrimitivePop.elementQuery badIndex).read result, result.observe (path badIndex),
      ((path badIndex).readLive Value.dflt result).map Value.head, final 12, machine 12) =
      (none, none, none, zero, zero) := by
  refine ⟨?_, rfl⟩
  intro q member
  rcases List.mem_append.mp member with positive | failed
  · exact full_copy_bridge.2 q positive
  · simp only [List.mem_singleton] at failed
    subst q
    refine ⟨⟨by change 4 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed
    change (none : Option Semantics.Word) = some word at observed
    cases observed

/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.full_copy_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms full_copy_bridge
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.full_alias_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms full_alias_bridge
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.symbolic_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms symbolic_ordered
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.rejected_stores' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms rejected_stores
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.wrong_symbolic_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_symbolic_ordered
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.with_failed_destination' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms with_failed_destination


private def targetSlots : List Evm.Slot := [.root 0,.root 1,.data (.root 0) 0,.data (.root 0) 1,
  .data (.root 0) 2,.data (.root 0) 3,.data (.root 1) 0,.data (.root 1) 1,
  .data (.root 1) 2,.data (.root 1) 3,.data (.root 1) 4,.data (.root 1) 8,.root 2]
private def targetTail : List Evm.Word := [.val ⟨7,by decide⟩,.slot (.root 9)]
private def target : Evm.Machine :=
  { stack := targetTail, store := .ofFn (fun slot => if slot = .data (.root 1) 4 ∨ slot = .data (.root 1) 8 then 1 else (TargetOperations.encodeWord (store (Solidity.Storage.ofSlot slot))).val),
    mem := fun _ => .val ⟨11,by decide⟩, bal := fun _ => 13, bal₀ := fun _ => 17,
    self := ⟨19,by decide⟩,caller := ⟨23,by decide⟩,callvalue := ⟨29,by decide⟩,timestamp := ⟨31,by decide⟩,
    accepts := fun _ _ => false }
private def fitting : ∀ l ∈ locations, TargetOperations.KeysFit l := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
private theorem targetInitial : ∀ l (member : l ∈ locations),
    target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l) := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private def targetResult := TargetArrayCopyTail.afterCopy target targetTail (.root 1) (.root 0)
private def targetView (m : Evm.Machine) := targetSlots.map (fun slot => m.store slot)
private def targetContext (m : Evm.Machine) :=
  (m.stack,m.mem 0,m.bal ⟨0,by decide⟩,m.bal₀ ⟨0,by decide⟩,m.self,m.caller,m.callvalue,m.timestamp,m.accepts ⟨0,by decide⟩ ⟨0,by decide⟩)
private def graphView (v : Value graph (.array (.prim .bool))) :=
  (v.length.val,v.extent.val,v.observe (path (ix 0)),v.observe (path (ix 1)),
    v.observe (path (ix 2)),v.observe (path (ix 3)),((path (ix 1)).readLive Value.dflt v).map Value.head)

/-- Apply BOTH OLD owner relations and the GOOD published finite run to the
actual structured target copy, retaining all original selected source failures. -/
theorem actual_target_copy_bridge :
    Evm.run TargetArrayCopy.code { target with stack := .slot (.root 1) :: .slot (.root 0) :: targetTail } = .ok targetResult 0 ∧
    Represented (old.overlay source) (PrimitivePop.queries indices) dst afterCopy ∧
    Transport 32 hash locations afterCopy final ∧
    (∀ l (member : l ∈ locations), targetResult.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (final (l.word 32 hash))) ∧
    (∀ q ∈ PrimitivePop.queries (G := graph) (p := .bool) indices, ∀ word, q.read (old.overlay source) = some word → final ((q.location dst).word 32 hash) = word) :=
  TargetCopyRepresentation.complete run old source indices dst srcBase True.intro True.intro store machine target targetTail
    beforeDst beforeSrc initial (by decide) (by decide) (fun i member => (covered i member).1)
    (fun i member => (covered i member).2)
    (by intro i inside; have equal : i = 0 := by change i < 1 at inside; omega
        subst i; decide)
    visited fitting targetInitial

/-- Complete original graph/numeric observations remain unchanged; ACTUAL target
execution now has matching full ordered words and nontrivial context too. -/
theorem actual_target_copy_ordered :
    (graphView old,graphView source,graphView result,view machine,view final,targetView target,targetView targetResult,targetContext targetResult) =
      ((3,4,some true,some true,some true,some true,some true),
       (1,2,some false,some true,none,none,none),(1,4,some false,some false,some false,some true,none),
       (three,one,one,one,one,one,zero,one,zero,zero,one,one,seven),
       (one,one,zero,zero,zero,one,zero,one,zero,zero,one,one,seven),
       [3,1,1,1,1,1,0,1,0,0,1,1,7],[1,1,0,0,0,1,0,1,0,0,1,1,7],targetContext target) := by
  rfl

private def aliasTarget := TargetArrayCopyTail.afterCopy target targetTail (.root 0) (.root 0)
/-- SAME represented array is an inhabited alias, with complete target and
independent graph/numeric readbacks; no disjointness premise was inserted. -/
theorem actual_target_self_bridge :
    Evm.run TargetArrayCopy.code { target with stack := .slot (.root 0) :: .slot (.root 0) :: targetTail } = .ok aliasTarget 0 ∧
    Represented (old.overlay old) (PrimitivePop.queries indices) dst (CopyTransport.symbolicCopy dst dst store) ∧
    Transport 32 hash locations (CopyTransport.symbolicCopy dst dst store) (NumericTraversal.copy 32 hash dst dst machine) ∧
    (targetView aliasTarget,targetContext aliasTarget,graphView (old.overlay old),view (NumericTraversal.copy 32 hash dst dst machine)) =
      (targetView target,targetContext target,graphView old,view machine) := by
  have certified := TargetCopyRepresentation.complete run old old indices dst dst True.intro True.intro store machine target targetTail
    beforeDst beforeDst initial (by decide) (by decide) (fun i member => (covered i member).1)
    (fun i member => (covered i member).1)
    (by intro i inside; exact visited i (by change i < max 3 1; change i < 3 at inside; omega))
    visited fitting targetInitial
  exact ⟨certified.1,certified.2.1,certified.2.2.1,rfl⟩

private def changedTarget : Evm.Machine := { target with store := Evm.WordStore.write target.store (.data (.root 1) 0) 1 }
private def changedResult := TargetArrayCopyTail.afterCopy changedTarget targetTail (.root 1) (.root 0)
/-- ACTUAL current SLOAD sees a changed payload. The OLD source/target input
agreement then fails; replaying an old capture would incorrectly copy zero. -/
theorem actual_target_input_negative :
    Evm.run TargetArrayCopy.code { changedTarget with stack := .slot (.root 1) :: .slot (.root 0) :: targetTail } = .ok changedResult 0 ∧
    changedTarget.store.cells (.data (.root 1) 0) ≠ TargetOperations.encodeWord (store (.data srcBase 0)) ∧
    (targetView targetResult,targetView changedResult,targetContext changedResult) =
      ([1,1,0,0,0,1,0,1,0,0,1,1,7],[1,1,1,0,0,1,1,1,0,0,1,1,7],targetContext target) := by
  exact ⟨TargetArrayCopyTail.run_current _ _ _ _,by decide,rfl⟩

private def failedStore := Representation.write store (.data srcBase 2) seven
private def failedNumeric := writeWord machine 18 seven
private def failedTarget : Evm.Machine := { target with store := Evm.WordStore.write target.store (.data (.root 1) 2) 7 }
private def failedFinal := NumericTraversal.copy 32 hash dst srcBase failedNumeric
private def failedTargetResult := TargetArrayCopyTail.afterCopy failedTarget targetTail (.root 1) (.root 0)

private theorem failedBeforeDst : Represented old (PrimitivePop.queries indices) dst failedStore := by
  intro q member
  simp only [PrimitivePop.queries, indices, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro, ⟨by decide, by decide⟩, ?_⟩
    intro word observed; change some three = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 3 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl

private theorem failedBeforeSrc : Represented source (PrimitivePop.queries indices) srcBase failedStore := by
  intro q member
  simp only [PrimitivePop.queries, indices, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro, ⟨by decide, by decide⟩, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some zero = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
  · refine ⟨⟨by change 3 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed

private theorem failedInitial : Transport 32 hash locations failedStore failedNumeric := by
  intro l member
  simp only [locations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem failedTargetInitial : ∀ l (member : l ∈ locations),
    failedTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (failedStore l) := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A covered failed SOURCE query has physical word7, and BOTH OLD selected
owner relations/GOOD finite run still apply. CURRENT copy leaves that inactive
source shadow unchanged; no failed logical query was assigned numeric zero. -/
theorem actual_target_failed_source :
    Evm.run TargetArrayCopy.code { failedTarget with stack := .slot (.root 1) :: .slot (.root 0) :: targetTail } = .ok failedTargetResult 0 ∧
    Represented (old.overlay source) (PrimitivePop.queries indices) dst (CopyTransport.symbolicCopy dst srcBase failedStore) ∧
    Transport 32 hash locations (CopyTransport.symbolicCopy dst srcBase failedStore) failedFinal ∧
    (PrimitivePop.elementQuery (G := graph) (p := .bool) (ix 2)).read source = none ∧
    (graphView old,graphView source,graphView result,view failedNumeric,view failedFinal,targetView failedTarget,targetView failedTargetResult,targetContext failedTargetResult) =
      ((3,4,some true,some true,some true,some true,some true),
       (1,2,some false,some true,none,none,none),(1,4,some false,some false,some false,some true,none),
       (three,one,one,one,one,one,zero,one,seven,zero,one,one,seven),
       (one,one,zero,zero,zero,one,zero,one,seven,zero,one,one,seven),
       [3,1,1,1,1,1,0,1,7,0,1,1,7],[1,1,0,0,0,1,0,1,7,0,1,1,7],targetContext target) := by
  have certified := TargetCopyRepresentation.complete run old source indices dst srcBase True.intro True.intro failedStore failedNumeric failedTarget targetTail
    failedBeforeDst failedBeforeSrc failedInitial (by decide) (by decide) (fun i member => (covered i member).1)
    (fun i member => (covered i member).2)
    (by intro i inside; have equal : i = 0 := by change i < 1 at inside; omega
        subst i; decide)
    visited fitting failedTargetInitial
  exact ⟨certified.1,certified.2.1,certified.2.2.1,rfl,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_target_copy_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_target_copy_bridge
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_target_copy_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_target_copy_ordered
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_target_self_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_target_self_bridge
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_target_input_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_target_input_negative
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_target_failed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_target_failed_source


private def trueSource : Value graph (.array (.prim .bool)) :=
  .array ⟨2,by decide⟩ ⟨1,by decide⟩ (by decide) (fun _ => .present (.prim true))
private def trueStore := Representation.write store (.data srcBase 0) one
private def trueNumeric := writeWord machine 16 one
private def trueCopied := old.overlay trueSource
private def truePopped := (recursivePop trueCopied).getD trueCopied
private def trueRegrown := (operationPush truePopped).getD truePopped
private def trueCopyNumeric := NumericTraversal.copy 32 hash dst srcBase trueNumeric
private def truePopNumeric := (PrimitivePop.execute 32 hash dst trueCopyNumeric).getD trueCopyNumeric
private noncomputable def trueFinalNumeric := (TargetCopyLifecycle.execute 32 hash dst srcBase trueNumeric).getD trueCopyNumeric
private def truePopTarget : Evm.Machine := { changedResult with store := Evm.WordStore.write (Evm.WordStore.write changedResult.store (.root 0) 0) (.data (.root 0) 0) 0 }
private def trueFinalTarget : Evm.Machine := { truePopTarget with store := Evm.WordStore.write (Evm.WordStore.write truePopTarget.store (.root 0) 1) (.data (.root 0) 0) 0 }

private theorem trueBeforeDst : Represented old (PrimitivePop.queries indices) dst trueStore := by
  intro q member
  simp only [PrimitivePop.queries, indices, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro, ⟨by decide, by decide⟩, ?_⟩
    intro word observed; change some three = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 3 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl

private theorem trueBeforeSrc : Represented trueSource (PrimitivePop.queries indices) srcBase trueStore := by
  intro q member
  simp only [PrimitivePop.queries, indices, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro, ⟨by decide, by decide⟩, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
  · refine ⟨⟨by change 3 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed

private theorem trueInitial : Transport 32 hash locations trueStore trueNumeric :=
  transport_write run initial (.data srcBase 0) (by decide) one
private theorem trueTargetInitial : ∀ l (member : l ∈ locations),
    changedTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (trueStore l) :=
  TargetOperations.write_agreement locations fitting (.data srcBase 0) True.intro one store target targetInitial

private theorem trueRun :
    Evm.run (TargetCopyLifecycle.code (.root 0)) { changedTarget with stack := .slot (.root 1) :: .slot (.root 0) :: targetTail } = .ok trueFinalTarget 0 := by
  unfold TargetCopyLifecycle.code TargetPrimitivePopPush.code
  rw [Evm.run_append_ok (TargetArrayCopyTail.run_current changedTarget targetTail (.root 1) (.root 0))]
  have pop : Evm.run (TargetPrimitivePop.code (.root 0)) changedResult = .ok truePopTarget 0 := by
    rw [TargetPrimitivePop.run_current,if_neg (by decide)]
    rfl
  change Evm.run (TargetPrimitivePop.code (.root 0) ++ TargetPrimitivePush.code (.root 0)) changedResult = _
  rw [Evm.run_append_ok pop,TargetPrimitivePush.run_current,if_pos (by decide)]
  rfl

/-- The ACTUAL copy's derived middle owner/transport is consumed by pop/push.
No intermediate representation is supplied as a premise or replayed capture. -/
theorem actual_copy_pop_push_bridge :
    ∃ finalStore,
      Evm.run (TargetCopyLifecycle.code (.root 0)) { changedTarget with stack := .slot (.root 1) :: .slot (.root 0) :: targetTail } = .ok trueFinalTarget 0 ∧
      TargetCopyLifecycle.execute 32 hash dst srcBase trueNumeric = some trueFinalNumeric ∧
      Represented trueRegrown (PrimitivePop.queries indices) dst finalStore ∧
      Transport 32 hash locations finalStore trueFinalNumeric ∧
      (∀ l (member : l ∈ locations), trueFinalTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (trueFinalNumeric (l.word 32 hash))) := by
  obtain ⟨finalStore,finalTarget,finalNumeric,numericRun,targetRun,owner,transported,agreement⟩ :=
    TargetCopyLifecycle.complete run old trueSource truePopped trueRegrown (by rfl) (by rfl)
      indices dst srcBase True.intro True.intro trueStore trueNumeric changedTarget targetTail
      trueBeforeDst trueBeforeSrc trueInitial (by decide) (by decide) (fun i member => (covered i member).1)
      (fun i member => (covered i member).2)
      (by intro i inside; have equal : i = 0 := by change i < 1 at inside; omega
          subst i; decide)
      (by intro i inside; exact visited i inside) fitting trueTargetInitial
  have expectedNumeric : TargetCopyLifecycle.execute 32 hash dst srcBase trueNumeric = some trueFinalNumeric := rfl
  have numericEq := Option.some.inj (numericRun.symm.trans expectedNumeric)
  have targetEq := (Evm.Out.ok.inj (targetRun.symm.trans trueRun)).1
  subst finalNumeric
  subst finalTarget
  exact ⟨finalStore,trueRun,expectedNumeric,owner,transported,agreement⟩

/-- Complete FOUR stages show the copied true cell becomes nonlive and is
regrown false; older shadow3/source cells/nontrivial context stay unchanged. -/
theorem actual_copy_pop_push_ordered :
    (graphView old,graphView trueCopied,graphView truePopped,graphView trueRegrown,
      view trueNumeric,view trueCopyNumeric,view truePopNumeric,view trueFinalNumeric,
      targetView changedTarget,targetView changedResult,targetView truePopTarget,targetView trueFinalTarget,
      targetContext changedTarget,targetContext changedResult,targetContext truePopTarget,targetContext trueFinalTarget) =
      ((3,4,some true,some true,some true,some true,some true),
       (1,4,some true,some false,some false,some true,none),
       (0,4,some false,some false,some false,some true,none),
       (1,4,some false,some false,some false,some true,none),
       (three,one,one,one,one,one,one,one,zero,zero,one,one,seven),
       (one,one,one,zero,zero,one,one,one,zero,zero,one,one,seven),
       (zero,one,zero,zero,zero,one,one,one,zero,zero,one,one,seven),
       (one,one,zero,zero,zero,one,one,one,zero,zero,one,one,seven),
       [3,1,1,1,1,1,1,1,0,0,1,1,7],[1,1,1,0,0,1,1,1,0,0,1,1,7],
       [0,1,0,0,0,1,1,1,0,0,1,1,7],[1,1,0,0,0,1,1,1,0,0,1,1,7],
       targetContext target,targetContext target,targetContext target,targetContext target) := by
  rfl


private def live0 (v : Value graph (.array (.prim .bool))) := ((path (ix 0)).readLive Value.dflt v).map Value.head
/-- Shrink/regrow aliases distinguish loss of liveness from retained readback. -/
theorem actual_copy_pop_push_aliases :
    (graphView trueSource,live0 old,live0 trueCopied,live0 truePopped,live0 trueRegrown,
      truePopped.observe (path (ix 0)),trueRegrown.observe (path (ix 0))) =
      ((1,2,some true,some true,none,none,none),some true,some true,none,some false,some false,some false) := by
  rfl

private def wrongPopTarget : Evm.Machine := { changedTarget with store := Evm.WordStore.write (Evm.WordStore.write changedTarget.store (.root 0) 2) (.data (.root 0) 2) 0 }
private def wrongMiddleTarget : Evm.Machine := { wrongPopTarget with store := Evm.WordStore.write (Evm.WordStore.write wrongPopTarget.store (.root 0) 3) (.data (.root 0) 2) 0 }
private def wrongFinalTarget := TargetArrayCopyTail.afterCopy wrongMiddleTarget targetTail (.root 1) (.root 0)
private def wrongCode : List Evm.Instr := TargetPrimitivePopPush.code (.root 0) ++
  ([.push (.slot (.root 0)),.push (.slot (.root 1))] ++ TargetArrayCopy.code)
private noncomputable def wrongMiddleNumeric := (TargetPrimitivePopPush.execute 32 hash dst trueNumeric).getD trueNumeric
private noncomputable def wrongFinalNumeric := NumericTraversal.copy 32 hash dst srcBase wrongMiddleNumeric
private def wrongOldPop := (recursivePop old).getD old
private def wrongOldPush := (operationPush wrongOldPop).getD old
private def wrongGraph := wrongOldPush.overlay trueSource

/-- ACTUAL reversed program preserves the copied true payload; correct order
resets it. Both independent graph/numeric and actual target observations differ. -/
theorem actual_copy_lifecycle_wrong_order :
    Evm.run wrongCode changedTarget = .ok wrongFinalTarget 0 ∧
    (graphView wrongGraph,graphView trueRegrown,view wrongFinalNumeric,view trueFinalNumeric,
      targetView wrongFinalTarget,targetView trueFinalTarget,targetContext wrongFinalTarget) =
      ((1,4,some true,some false,some false,some true,none),
       (1,4,some false,some false,some false,some true,none),
       (one,one,one,zero,zero,one,one,one,zero,zero,one,one,seven),
       (one,one,zero,zero,zero,one,one,one,zero,zero,one,one,seven),
       [1,1,1,0,0,1,1,1,0,0,1,1,7],[1,1,0,0,0,1,1,1,0,0,1,1,7],targetContext target) := by
  refine ⟨?_,rfl⟩
  have pop : Evm.run (TargetPrimitivePop.code (.root 0)) changedTarget = .ok wrongPopTarget 0 := by
    rw [TargetPrimitivePop.run_current,if_neg (by decide)]; rfl
  have push : Evm.run (TargetPrimitivePush.code (.root 0)) wrongPopTarget = .ok wrongMiddleTarget 0 := by
    rw [TargetPrimitivePush.run_current,if_pos (by decide)]; rfl
  unfold wrongCode
  have first : Evm.run (TargetPrimitivePopPush.code (.root 0)) changedTarget = .ok wrongMiddleTarget 0 := by
    unfold TargetPrimitivePopPush.code
    rw [Evm.run_append_ok pop]; exact push
  rw [Evm.run_append_ok first]
  rw [Evm.run_append_ok (m' := { wrongMiddleTarget with stack := .slot (.root 1) :: .slot (.root 0) :: targetTail }) (by rfl)]
  exact TargetArrayCopyTail.run_current _ _ _ _

private def lateSource : Value graph (.array (.prim .bool)) :=
  .array ⟨2,by decide⟩ ⟨0,by decide⟩ (by decide) (fun i => .present (.prim (decide (i.val = 1))))
private def lateStore := Representation.write store srcBase zero
private def lateNumeric := writeWord machine 1 zero
private def lateTarget : Evm.Machine := { target with store := Evm.WordStore.write target.store (.root 1) 0 }
private def lateCopied := old.overlay lateSource
private def lateCopyNumeric := NumericTraversal.copy 32 hash dst srcBase lateNumeric
private def lateCopyTarget := TargetArrayCopyTail.afterCopy lateTarget targetTail (.root 1) (.root 0)

private theorem lateBeforeDst : Represented old (PrimitivePop.queries indices) dst lateStore := by
  intro q member
  simp only [PrimitivePop.queries, indices, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro, ⟨by decide, by decide⟩, ?_⟩
    intro word observed; change some three = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 3 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl

private theorem lateBeforeSrc : Represented lateSource (PrimitivePop.queries indices) srcBase lateStore := by
  intro q member
  simp only [PrimitivePop.queries, indices, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro, ⟨by decide, by decide⟩, ?_⟩
    intro word observed; change some zero = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some zero = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
  · refine ⟨⟨by change 3 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed

private theorem lateInitial : Transport 32 hash locations lateStore lateNumeric :=
  transport_write run initial srcBase (by decide) zero
private theorem lateTargetInitial : ∀ l (member : l ∈ locations),
    lateTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (lateStore l) :=
  TargetOperations.write_agreement locations fitting srcBase True.intro zero store target targetInitial

/-- Represented copy-to-empty really clears old live words BEFORE the actual
pop fails. Numeric None/target revert are distinct from world rollback. -/
theorem actual_copy_lifecycle_late_failure :
    Evm.run TargetArrayCopy.code { lateTarget with stack := .slot (.root 1) :: .slot (.root 0) :: targetTail } = .ok lateCopyTarget 0 ∧
    Represented lateCopied (PrimitivePop.queries indices) dst (CopyTransport.symbolicCopy dst srcBase lateStore) ∧
    Transport 32 hash locations (CopyTransport.symbolicCopy dst srcBase lateStore) lateCopyNumeric ∧
    Evm.run (TargetCopyLifecycle.code (.root 0)) { lateTarget with stack := .slot (.root 1) :: .slot (.root 0) :: targetTail } = .revert ∧
    TargetCopyLifecycle.execute 32 hash dst srcBase lateNumeric = none ∧
    (graphView old,graphView lateSource,graphView lateCopied,view lateNumeric,view lateCopyNumeric,
      targetView lateTarget,targetView lateCopyTarget,targetContext lateCopyTarget) =
      ((3,4,some true,some true,some true,some true,some true),
       (0,2,some false,some true,none,none,none),(0,4,some false,some false,some false,some true,none),
       (three,zero,one,one,one,one,zero,one,zero,zero,one,one,seven),
       (zero,zero,zero,zero,zero,one,zero,one,zero,zero,one,one,seven),
       [3,0,1,1,1,1,0,1,0,0,1,1,7],[0,0,0,0,0,1,0,1,0,0,1,1,7],targetContext target) := by
  have certified := TargetCopyRepresentation.complete run old lateSource indices dst srcBase True.intro True.intro lateStore lateNumeric lateTarget targetTail
    lateBeforeDst lateBeforeSrc lateInitial (by decide) (by decide) (fun i member => (covered i member).1)
    (fun i member => (covered i member).2) (by intro i inside; change i < 0 at inside; omega)
    (by intro i inside; exact visited i (by change i < max 3 0 at inside; change i < max 3 1; omega)) fitting lateTargetInitial
  exact ⟨certified.1,certified.2.1,certified.2.2.1,TargetCopyLifecycle.run_empty _ _ _ _ (by rfl),rfl,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_pop_push_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_pop_push_bridge
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_pop_push_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_pop_push_ordered
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_pop_push_aliases' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_pop_push_aliases
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_lifecycle_wrong_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_lifecycle_wrong_order
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_lifecycle_late_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_lifecycle_late_failure


private theorem selectedOne (v : Value graph (.array (.prim .bool))) (base : Solidity.Storage.Loc) (w : Store)
    (before : Represented v (PrimitivePop.queries indices) base w) (i : Index) (inside : i ∈ indices) :
    Represented v (PrimitivePop.queries [i]) base w := by
  intro q member
  simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
  rcases member with rfl | ⟨j,member,rfl⟩
  · exact before _ List.mem_cons_self
  · have equal : j = i := by simpa only [List.not_mem_nil,or_false] using member
    subst j
    exact before _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,inside,rfl⟩))
private def readInput (m : Evm.Machine) (i : Index) : Evm.Machine :=
  { m with stack := .slot (.root 1) :: .slot (.root 0) :: .val ⟨i.val,i.isLt⟩ :: targetTail }
private def readOutput (m : Evm.Machine) (i : Index) (word : Semantics.Word) : Evm.Machine :=
  { TargetArrayCopyTail.afterCopy m (.val ⟨i.val,i.isLt⟩ :: targetTail) (.root 1) (.root 0) with stack := .val (TargetOperations.encodeWord word) :: targetTail }
private def returnContext (word : Semantics.Word) :=
  targetContext { target with stack := .val (TargetOperations.encodeWord word) :: targetTail }

/-- SAME code and runtime index0 read changed current source false/true through
DERIVED copy certificates, not replayed old payloads or intermediate premises. -/
theorem actual_copy_read_changed :
    Evm.run (TargetCopyRead.code (.root 0)) (readInput target (ix 0)) = .ok (readOutput target (ix 0) zero) 0 ∧
    final ((Solidity.Storage.Loc.data dst 0).word 32 hash) = zero ∧
    Evm.run (TargetCopyRead.code (.root 0)) (readInput changedTarget (ix 0)) = .ok (readOutput changedTarget (ix 0) one) 0 ∧
    trueCopyNumeric ((Solidity.Storage.Loc.data dst 0).word 32 hash) = one := by
  have baseline := TargetCopyRead.complete run old source (ix 0) (.prim false) (by rfl) dst srcBase True.intro True.intro
    store machine target targetTail (selectedOne old dst store beforeDst (ix 0) (by decide))
    (selectedOne source srcBase store beforeSrc (ix 0) (by decide)) initial (by decide) (by decide) (by decide) (by decide)
    (by intro j inside; have equal : j = 0 := by change j < 1 at inside; omega
        subst j; decide) visited fitting targetInitial
  have changed := TargetCopyRead.complete run old trueSource (ix 0) (.prim true) (by rfl) dst srcBase True.intro True.intro
    trueStore trueNumeric changedTarget targetTail (selectedOne old dst trueStore trueBeforeDst (ix 0) (by decide))
    (selectedOne trueSource srcBase trueStore trueBeforeSrc (ix 0) (by decide)) trueInitial (by decide) (by decide) (by decide) (by decide)
    (by intro j inside; have equal : j = 0 := by change j < 1 at inside; omega
        subst j; decide) visited fitting trueTargetInitial
  exact ⟨baseline.1,baseline.2,changed.1,changed.2⟩

/-- Complete Source graphs and original13numeric/13target cells distinguish
changed source inputs; final stack holds payload rather than input index. -/
theorem actual_copy_read_ordered :
    (graphView old,graphView source,graphView trueSource,graphView result,graphView trueCopied,
      view machine,view final,view trueNumeric,view trueCopyNumeric,
      targetView target,targetView (readOutput target (ix 0) zero),targetView changedTarget,targetView (readOutput changedTarget (ix 0) one),
      targetContext (readOutput target (ix 0) zero),targetContext (readOutput changedTarget (ix 0) one)) =
      ((3,4,some true,some true,some true,some true,some true),
       (1,2,some false,some true,none,none,none),(1,2,some true,some true,none,none,none),
       (1,4,some false,some false,some false,some true,none),(1,4,some true,some false,some false,some true,none),
       (three,one,one,one,one,one,zero,one,zero,zero,one,one,seven),
       (one,one,zero,zero,zero,one,zero,one,zero,zero,one,one,seven),
       (three,one,one,one,one,one,one,one,zero,zero,one,one,seven),
       (one,one,one,zero,zero,one,one,one,zero,zero,one,one,seven),
       [3,1,1,1,1,1,0,1,0,0,1,1,7],[1,1,0,0,0,1,0,1,0,0,1,1,7],
       [3,1,1,1,1,1,1,1,0,0,1,1,7],[1,1,1,0,0,1,1,1,0,0,1,1,7],returnContext zero,returnContext one) := by
  rfl


private def twoRead : Semantics.Word := lengthWord 2 (by decide)
private def readSource2 : Value graph (.array (.prim .bool)) :=
  .array ⟨2,by decide⟩ ⟨2,by decide⟩ (by decide) (fun i => .present (.prim (decide (i.val = 0))))
private def readStore2 := Representation.write (Representation.write (Representation.write store srcBase twoRead) (.data srcBase 0) one) (.data srcBase 1) zero
private def readNumeric2 := writeWord (writeWord (writeWord machine 1 twoRead) 16 one) 17 zero
private def readTarget2 : Evm.Machine := { target with store := Evm.WordStore.write (Evm.WordStore.write (Evm.WordStore.write target.store (.root 1) 2) (.data (.root 1) 0) 1) (.data (.root 1) 1) 0 }
private def readCopied2 := old.overlay readSource2
private def readFinal2 := NumericTraversal.copy 32 hash dst srcBase readNumeric2

private theorem readBeforeDst2 : Represented old (PrimitivePop.queries indices) dst readStore2 := by
  intro q member
  simp only [PrimitivePop.queries, indices, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro, ⟨by decide, by decide⟩, ?_⟩
    intro word observed; change some three = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 3 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl

private theorem readBeforeSrc2 : Represented readSource2 (PrimitivePop.queries indices) srcBase readStore2 := by
  intro q member
  simp only [PrimitivePop.queries, indices, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro, ⟨by decide, by decide⟩, ?_⟩
    intro word observed; change some twoRead = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some zero = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
  · refine ⟨⟨by change 3 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed

private theorem readInitial2 : Transport 32 hash locations readStore2 readNumeric2 := by
  intro l member
  simp only [locations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem readTargetInitial2 : ∀ l (member : l ∈ locations),
    readTarget2.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (readStore2 l) := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem readSourceCovered2 : ∀ j < readSource2.length.val, Solidity.Storage.Loc.data srcBase j ∈ locations := by
  intro j inside
  have cases : j = 0 ∨ j = 1 := by change j < 2 at inside; omega
  rcases cases with rfl | rfl <;> decide

/-- The IDENTICAL instruction list receives indices0/1 from its input stack.
Payloads1/0 are opposite to those indices, rejecting an index-echo shortcut. -/
theorem actual_copy_read_runtime_indices :
    Evm.run (TargetCopyRead.code (.root 0)) (readInput readTarget2 (ix 0)) = .ok (readOutput readTarget2 (ix 0) one) 0 ∧
    readFinal2 ((Solidity.Storage.Loc.data dst 0).word 32 hash) = one ∧
    Evm.run (TargetCopyRead.code (.root 0)) (readInput readTarget2 (ix 1)) = .ok (readOutput readTarget2 (ix 1) zero) 0 ∧
    readFinal2 ((Solidity.Storage.Loc.data dst 1).word 32 hash) = zero := by
  have first := TargetCopyRead.complete run old readSource2 (ix 0) (.prim true) (by rfl) dst srcBase True.intro True.intro
    readStore2 readNumeric2 readTarget2 targetTail (selectedOne old dst readStore2 readBeforeDst2 (ix 0) (by decide))
    (selectedOne readSource2 srcBase readStore2 readBeforeSrc2 (ix 0) (by decide)) readInitial2 (by decide) (by decide) (by decide) (by decide)
    readSourceCovered2 visited fitting readTargetInitial2
  have second := TargetCopyRead.complete run old readSource2 (ix 1) (.prim false) (by rfl) dst srcBase True.intro True.intro
    readStore2 readNumeric2 readTarget2 targetTail (selectedOne old dst readStore2 readBeforeDst2 (ix 1) (by decide))
    (selectedOne readSource2 srcBase readStore2 readBeforeSrc2 (ix 1) (by decide)) readInitial2 (by decide) (by decide) (by decide) (by decide)
    readSourceCovered2 visited fitting readTargetInitial2
  exact ⟨first.1,first.2,second.1,second.2⟩

/-- Complete graph/13numeric/13target/stack/context observations at BOTH indices
also retain every older shadow and unchanged source cell. -/
theorem actual_copy_read_runtime_indices_ordered :
    (graphView old,graphView readSource2,graphView readCopied2,view readNumeric2,view readFinal2,
      targetView readTarget2,targetView (readOutput readTarget2 (ix 0) one),targetView (readOutput readTarget2 (ix 1) zero),
      targetContext (readOutput readTarget2 (ix 0) one),targetContext (readOutput readTarget2 (ix 1) zero)) =
      ((3,4,some true,some true,some true,some true,some true),
       (2,2,some true,some false,none,none,some false),(2,4,some true,some false,some false,some true,some false),
       (three,twoRead,one,one,one,one,one,zero,zero,zero,one,one,seven),
       (twoRead,twoRead,one,zero,zero,one,one,zero,zero,zero,one,one,seven),
       [3,2,1,1,1,1,1,0,0,0,1,1,7],[2,2,1,0,0,1,1,0,0,0,1,1,7],[2,2,1,0,0,1,1,0,0,0,1,1,7],
       returnContext one,returnContext zero) := by
  rfl

private def selfReadOutput : Evm.Machine :=
  { TargetArrayCopyTail.afterCopy target (.val ⟨(ix 0).val,(ix 0).isLt⟩ :: targetTail) (.root 0) (.root 0) with stack := .val (TargetOperations.encodeWord one) :: targetTail }
/-- A GOOD represented source=destination alias applies the SAME theorem;
copy preserves all observed words and the actual live read returns true. -/
theorem actual_copy_read_self_alias :
    Evm.run (TargetCopyRead.code (.root 0)) { target with stack := .slot (.root 0) :: .slot (.root 0) :: .val ⟨(ix 0).val,(ix 0).isLt⟩ :: targetTail } = .ok selfReadOutput 0 ∧
    NumericTraversal.copy 32 hash dst dst machine ((Solidity.Storage.Loc.data dst 0).word 32 hash) = one ∧
    (graphView (old.overlay old),view (NumericTraversal.copy 32 hash dst dst machine),targetView selfReadOutput,targetContext selfReadOutput) =
      (graphView old,view machine,targetView target,returnContext one) := by
  have certificate := TargetCopyRead.complete run old old (ix 0) (.prim true) (by rfl) dst dst True.intro True.intro
    store machine target targetTail (selectedOne old dst store beforeDst (ix 0) (by decide))
    (selectedOne old dst store beforeDst (ix 0) (by decide)) initial (by decide) (by decide) (by decide) (by decide)
    (by intro j inside; exact visited j (by change j < 3 at inside; change j < max 3 1; omega)) visited fitting targetInitial
  exact ⟨certificate.1,certificate.2,rfl⟩


private def absentReadDst : Value graph (.array (.prim .bool)) :=
  .array ⟨4,by decide⟩ ⟨3,by decide⟩ (by decide) (fun i => if i.val = 0 then .absent else .present (.prim true))
private def absentReadStore := Representation.write store (.data dst 0) zero
private def absentReadNumeric := writeWord machine 8 zero
private def absentReadTarget : Evm.Machine := { target with store := Evm.WordStore.write target.store (.data (.root 0) 0) 0 }
private def absentReadCopied := absentReadDst.overlay absentSrc
private def absentReadFinal := NumericTraversal.copy 32 hash dst srcBase absentReadNumeric

private theorem absentReadBeforeDst : Represented absentReadDst (PrimitivePop.queries indices) dst absentReadStore := by
  intro q member
  simp only [PrimitivePop.queries, indices, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro, ⟨by decide, by decide⟩, ?_⟩
    intro word observed; change some three = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some zero = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 3 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl

private theorem absentReadBeforeSrc : Represented absentSrc (PrimitivePop.queries indices) srcBase absentReadStore := by
  intro q member
  simp only [PrimitivePop.queries, indices, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro, ⟨by decide, by decide⟩, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some zero = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
  · refine ⟨⟨by change 3 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed

private theorem absentReadInitial : Transport 32 hash locations absentReadStore absentReadNumeric :=
  transport_write run initial (.data dst 0) (by decide) zero
private theorem absentReadTargetInitial : ∀ l (member : l ∈ locations),
    absentReadTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (absentReadStore l) :=
  TargetOperations.write_agreement locations fitting (.data dst 0) True.intro zero store target targetInitial

/-- BOTH live source/destination slots remain absent after overlay, yet their
in-extent LIVE read succeeds with the published default false. OLD successful
DEFAULT queries supply zero; this is not failed-query-zero reasoning. -/
theorem actual_copy_read_absent_default :
    Evm.run (TargetCopyRead.code (.root 0)) (readInput absentReadTarget (ix 0)) = .ok (readOutput absentReadTarget (ix 0) zero) 0 ∧
    absentReadFinal ((Solidity.Storage.Loc.data dst 0).word 32 hash) = zero ∧
    (graphView absentReadDst,graphView absentSrc,graphView absentReadCopied,
      absentReadDst.slots ⟨0,by decide⟩,absentSrc.slots ⟨0,by decide⟩,absentReadCopied.slots ⟨0,by decide⟩,
      live0 absentReadCopied,view absentReadNumeric,view absentReadFinal,targetView absentReadTarget,
      targetView (readOutput absentReadTarget (ix 0) zero),targetContext (readOutput absentReadTarget (ix 0) zero)) =
      ((3,4,some false,some true,some true,some true,some true),
       (1,2,some false,some true,none,none,none),(1,4,some false,some false,some false,some true,none),
       Slot.absent,Slot.absent,Slot.absent,some false,
       (three,one,zero,one,one,one,zero,one,zero,zero,one,one,seven),
       (one,one,zero,zero,zero,one,zero,one,zero,zero,one,one,seven),
       [3,1,0,1,1,1,0,1,0,0,1,1,7],[1,1,0,0,0,1,0,1,0,0,1,1,7],returnContext zero) := by
  have certificate := TargetCopyRead.complete run absentReadDst absentSrc (ix 0) (.prim false) (by rfl) dst srcBase True.intro True.intro
    absentReadStore absentReadNumeric absentReadTarget targetTail (selectedOne absentReadDst dst absentReadStore absentReadBeforeDst (ix 0) (by decide))
    (selectedOne absentSrc srcBase absentReadStore absentReadBeforeSrc (ix 0) (by decide)) absentReadInitial (by decide) (by decide) (by decide) (by decide)
    (by intro j inside; have equal : j = 0 := by change j < 1 at inside; omega
        subst j; decide) visited fitting absentReadTargetInitial
  exact ⟨certificate.1,certificate.2,rfl⟩

private def outsideReadIndex : Index := ⟨12,by decide⟩
private def readPrefix (m : Evm.Machine) (i : Index) :=
  TargetArrayCopyTail.afterCopy m (.val ⟨i.val,i.isLt⟩ :: targetTail) (.root 1) (.root 0)

/-- Retained cleared1, older-shadow3 and out-of-extent12 all fail LIVE after
the ACTUAL represented copy prefix, despite different raw/physical observations.
The outside query aliases physical word20=1 outside the covered run; no zero
readback or unproved transport is inferred for it. -/
theorem actual_copy_read_failed_aliases :
    Evm.run TargetArrayCopy.code (readInput target (ix 1)) = .ok (readPrefix target (ix 1)) 0 ∧
    Represented result (PrimitivePop.queries indices) dst afterCopy ∧ Transport 32 hash locations afterCopy final ∧
    Evm.run (TargetCopyRead.code (.root 0)) (readInput target (ix 1)) = .revert ∧
    Evm.run (TargetCopyRead.code (.root 0)) (readInput target (ix 3)) = .revert ∧
    Evm.run (TargetCopyRead.code (.root 0)) (readInput target outsideReadIndex) = .revert ∧
    (graphView old,graphView source,graphView result,result.observe (path (ix 1)),result.observe (path (ix 3)),result.observe (path outsideReadIndex),
      ((path (ix 1)).readLive Value.dflt result).map Value.head,((path (ix 3)).readLive Value.dflt result).map Value.head,
      ((path outsideReadIndex).readLive Value.dflt result).map Value.head,
      view machine,view final,targetView target,targetView (readPrefix target (ix 1)),targetContext (readPrefix target (ix 1)),
      final ((Solidity.Storage.Loc.data dst outsideReadIndex.val).word 32 hash),(readPrefix target outsideReadIndex).store (.data (.root 0) outsideReadIndex.val),
      decide (Solidity.Storage.Loc.data dst outsideReadIndex.val ∈ locations)) =
      ((3,4,some true,some true,some true,some true,some true),(1,2,some false,some true,none,none,none),
       (1,4,some false,some false,some false,some true,none),some false,some true,none,none,none,none,
       (three,one,one,one,one,one,zero,one,zero,zero,one,one,seven),
       (one,one,zero,zero,zero,one,zero,one,zero,zero,one,one,seven),
       [3,1,1,1,1,1,0,1,0,0,1,1,7],[1,1,0,0,0,1,0,1,0,0,1,1,7],returnContext one,one,0,false) := by
  refine ⟨TargetArrayCopyTail.run_current _ _ _ _,full_copy_bridge.2,full_copy_bridge.1,?_,?_,?_,rfl⟩
  · exact (TargetCopyRead.failure_matches old source (ix 1) target targetTail (.root 1) (.root 0) (by rfl)).mpr (by rfl)
  · exact (TargetCopyRead.failure_matches old source (ix 3) target targetTail (.root 1) (.root 0) (by rfl)).mpr (by rfl)
  · exact (TargetCopyRead.failure_matches old source outsideReadIndex target targetTail (.root 1) (.root 0) (by rfl)).mpr (by rfl)

private def omitCopyCode : List Evm.Instr := [.pop,.swap 1] ++ TargetArrayRead.code
private def omitCopyResult : Evm.Machine := { target with stack := .val (TargetOperations.encodeWord one) :: targetTail }

/-- The actual wrong program omits copy and reads old destination true.
Correct code copies current source false first and changes all stale live words. -/
theorem actual_copy_read_omitted_copy_negative :
    Evm.run omitCopyCode (readInput target (ix 0)) = .ok omitCopyResult 0 ∧
    Evm.run (TargetCopyRead.code (.root 0)) (readInput target (ix 0)) = .ok (readOutput target (ix 0) zero) 0 ∧
    (graphView old,graphView result,view machine,view final,targetView omitCopyResult,
      targetView (readOutput target (ix 0) zero),targetContext omitCopyResult,targetContext (readOutput target (ix 0) zero)) =
      ((3,4,some true,some true,some true,some true,some true),(1,4,some false,some false,some false,some true,none),
       (three,one,one,one,one,one,zero,one,zero,zero,one,one,seven),
       (one,one,zero,zero,zero,one,zero,one,zero,zero,one,one,seven),
       [3,1,1,1,1,1,0,1,0,0,1,1,7],[1,1,0,0,0,1,0,1,0,0,1,1,7],returnContext one,returnContext zero) := by
  refine ⟨?_,actual_copy_read_changed.1,rfl⟩
  unfold omitCopyCode
  rw [Evm.run_append_ok (m' := { target with stack := .val ⟨(ix 0).val,(ix 0).isLt⟩ :: .slot (.root 0) :: targetTail }) (by rfl)]
  rw [TargetArrayRead.run_current,if_pos (by decide)]
  rfl

/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_read_changed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_read_changed
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_read_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_read_ordered
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_read_runtime_indices' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_read_runtime_indices
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_read_runtime_indices_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_read_runtime_indices_ordered
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_read_self_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_read_self_alias
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_read_absent_default' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_read_absent_default
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_read_failed_aliases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_read_failed_aliases
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_read_omitted_copy_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_read_omitted_copy_negative


private def copyWriteInput (m : Evm.Machine) (i : Index) (word : Semantics.Word) : Evm.Machine :=
  { m with stack := .slot (.root 1) :: .slot (.root 0) :: .val ⟨i.val,i.isLt⟩ :: .val (TargetOperations.encodeWord word) :: targetTail }
private def copyWriteOutput (m : Evm.Machine) (i : Index) (word : Semantics.Word) : Evm.Machine :=
  { TargetArrayCopyTail.afterCopy m (.val ⟨i.val,i.isLt⟩ :: .val (TargetOperations.encodeWord word) :: targetTail) (.root 1) (.root 0) with stack := targetTail, store := Evm.WordStore.write (TargetArrayCopyTail.afterCopy m (.val ⟨i.val,i.isLt⟩ :: .val (TargetOperations.encodeWord word) :: targetTail) (.root 1) (.root 0)).store (.data (.root 0) i.val) (TargetOperations.encodeWord word).val }
private def copiedWritten := (TargetArrayWrite.writeAt (old.overlay source) (ix 0) true).getD (old.overlay source)
private def copiedWriteStore := Representation.write afterCopy (.data dst 0) one
private def copiedWriteNumeric := writeWord final 8 one

/-- Actual runtime payload true overwrites the copied false, deriving the SAME
complete selected owner/Transport and all covered target cells from OLD inputs. -/
theorem actual_copy_write_bridge :
    TargetCopyWrite.execute 32 hash dst srcBase machine (ix 0) one = some copiedWriteNumeric ∧
    Evm.run (TargetCopyWrite.code (.root 0)) (copyWriteInput target (ix 0) one) = .ok (copyWriteOutput target (ix 0) one) 0 ∧
    Represented copiedWritten (PrimitivePop.queries indices) dst copiedWriteStore ∧
    Transport 32 hash locations copiedWriteStore copiedWriteNumeric ∧
    (∀ l (member : l ∈ locations), (copyWriteOutput target (ix 0) one).store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (copiedWriteNumeric (l.word 32 hash))) ∧
    (∀ q ∈ PrimitivePop.queries (G := graph) (p := .bool) indices, ∀ word,
      q.read copiedWritten = some word → copiedWriteNumeric ((q.location dst).word 32 hash) = word) := by
  exact TargetCopyWrite.complete run old source copiedWritten (ix 0) true (by rfl) indices (by decide)
    dst srcBase True.intro True.intro store machine target targetTail beforeDst beforeSrc initial (by decide) (by decide)
    (fun j member => (covered j member).1) (fun j member => (covered j member).2)
    (by intro j inside; have equal : j = 0 := by change j < 1 at inside; omega
        subst j; decide) visited fitting targetInitial

/-- Complete THREE stages: copied source false, actual caller payload true,
with all original sibling/shadow/source/13numeric/13target/context observations. -/
theorem actual_copy_write_ordered :
    (graphView old,graphView source,graphView result,graphView copiedWritten,
      view machine,view final,view copiedWriteNumeric,targetView target,targetView targetResult,
      targetView (copyWriteOutput target (ix 0) one),targetContext (copyWriteOutput target (ix 0) one),live0 copiedWritten) =
      ((3,4,some true,some true,some true,some true,some true),(1,2,some false,some true,none,none,none),
       (1,4,some false,some false,some false,some true,none),(1,4,some true,some false,some false,some true,none),
       (three,one,one,one,one,one,zero,one,zero,zero,one,one,seven),
       (one,one,zero,zero,zero,one,zero,one,zero,zero,one,one,seven),
       (one,one,one,zero,zero,one,zero,one,zero,zero,one,one,seven),
       [3,1,1,1,1,1,0,1,0,0,1,1,7],[1,1,0,0,0,1,0,1,0,0,1,1,7],
       [1,1,1,0,0,1,0,1,0,0,1,1,7],targetContext target,some true) := by
  rfl

private def copiedWrittenFalse := (TargetArrayWrite.writeAt (old.overlay source) (ix 0) false).getD (old.overlay source)
private def copiedFalseStore := Representation.write afterCopy (.data dst 0) zero
private def copiedFalseNumeric := writeWord final 8 zero

/-- SAME code and runtime index consume changed caller payload false/true.
The false application also derives all selected owner and transport guarantees. -/
theorem actual_copy_write_runtime_values :
    Evm.run (TargetCopyWrite.code (.root 0)) (copyWriteInput target (ix 0) zero) = .ok (copyWriteOutput target (ix 0) zero) 0 ∧
    TargetCopyWrite.execute 32 hash dst srcBase machine (ix 0) zero = some copiedFalseNumeric ∧
    Represented copiedWrittenFalse (PrimitivePop.queries indices) dst copiedFalseStore ∧
    Transport 32 hash locations copiedFalseStore copiedFalseNumeric ∧
    (graphView copiedWrittenFalse,graphView copiedWritten,view copiedFalseNumeric,view copiedWriteNumeric,
      targetView (copyWriteOutput target (ix 0) zero),targetView (copyWriteOutput target (ix 0) one),
      targetContext (copyWriteOutput target (ix 0) zero),targetContext (copyWriteOutput target (ix 0) one)) =
      ((1,4,some false,some false,some false,some true,none),(1,4,some true,some false,some false,some true,none),
       (one,one,zero,zero,zero,one,zero,one,zero,zero,one,one,seven),
       (one,one,one,zero,zero,one,zero,one,zero,zero,one,one,seven),
       [1,1,0,0,0,1,0,1,0,0,1,1,7],[1,1,1,0,0,1,0,1,0,0,1,1,7],targetContext target,targetContext target) := by
  have certified := TargetCopyWrite.complete run old source copiedWrittenFalse (ix 0) false (by rfl) indices (by decide)
    dst srcBase True.intro True.intro store machine target targetTail beforeDst beforeSrc initial (by decide) (by decide)
    (fun j member => (covered j member).1) (fun j member => (covered j member).2)
    (by intro j inside; have equal : j = 0 := by change j < 1 at inside; omega
        subst j; decide) visited fitting targetInitial
  exact ⟨certified.2.1,certified.1,certified.2.2.1,certified.2.2.2.1,rfl⟩


private def uintOld : Value graph (.array (.prim .uint)) :=
  .array ⟨4,by decide⟩ ⟨3,by decide⟩ (by decide) (fun _ => .present (.prim one))
private def uintSource : Value graph (.array (.prim .uint)) :=
  .array ⟨2,by decide⟩ ⟨2,by decide⟩ (by decide) (fun i => .present (.prim (if i.val = 0 then twoRead else three)))
private def uintStore := Representation.write (Representation.write (Representation.write store srcBase twoRead) (.data srcBase 0) twoRead) (.data srcBase 1) three
private def uintNumeric := writeWord (writeWord (writeWord machine 1 twoRead) 16 twoRead) 17 three
private def uintTarget : Evm.Machine := { target with store := Evm.WordStore.write (Evm.WordStore.write (Evm.WordStore.write target.store (.root 1) 2) (.data (.root 1) 0) 2) (.data (.root 1) 1) 3 }
private def uintCopied := uintOld.overlay uintSource
private def uintCopyNumeric := NumericTraversal.copy 32 hash dst srcBase uintNumeric
private def uintWritten (i : Index) := (TargetArrayWrite.writeAt uintCopied i seven).getD uintCopied
private def uintWrittenStore (i : Index) := Representation.write (CopyTransport.symbolicCopy dst srcBase uintStore) (.data dst i.val) seven
private def uintWrittenNumeric (i : Index) := writeWord uintCopyNumeric ((Solidity.Storage.Loc.data dst i.val).word 32 hash) seven
private def uintPath (i : Index) : TypeGraph.Path graph (.array (.prim .uint)) (.prim .uint) := TargetArrayRead.path i
private def uintGraphView (v : Value graph (.array (.prim .uint))) :=
  (v.length.val,v.extent.val,v.observe (uintPath (ix 0)),v.observe (uintPath (ix 1)),
    v.observe (uintPath (ix 2)),v.observe (uintPath (ix 3)),((uintPath (ix 1)).readLive Value.dflt v).map Value.head)

private theorem uintBeforeDst : Represented uintOld (PrimitivePop.queries indices) dst uintStore := by
  intro q member
  simp only [PrimitivePop.queries, indices, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro, ⟨by decide, by decide⟩, ?_⟩
    intro word observed; change some three = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 3 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl

private theorem uintBeforeSrc : Represented uintSource (PrimitivePop.queries indices) srcBase uintStore := by
  intro q member
  simp only [PrimitivePop.queries, indices, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro, ⟨by decide, by decide⟩, ?_⟩
    intro word observed; change some twoRead = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some twoRead = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some three = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
  · refine ⟨⟨by change 3 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed

private theorem uintInitial : Transport 32 hash locations uintStore uintNumeric := by
  intro l member
  simp only [locations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem uintTargetInitial : ∀ l (member : l ∈ locations),
    uintTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (uintStore l) := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem uintSourceCovered : ∀ j < uintSource.length.val, Solidity.Storage.Loc.data srcBase j ∈ locations := by
  intro j inside
  have cases : j = 0 ∨ j = 1 := by change j < 2 at inside; omega
  rcases cases with rfl | rfl <;> decide

/-- SAME runtime program writes UINT payload7 at either input index0/1.
BOTH old/source/result certificates are applied; both selected payload changes
are nontrivial (2→7 and3→7), beyond a Boolean-only specialization. -/
theorem actual_copy_write_uint_indices :
    TargetCopyWrite.execute 32 hash dst srcBase uintNumeric (ix 0) seven = some (uintWrittenNumeric (ix 0)) ∧
    Evm.run (TargetCopyWrite.code (.root 0)) (copyWriteInput uintTarget (ix 0) seven) = .ok (copyWriteOutput uintTarget (ix 0) seven) 0 ∧
    Represented (uintWritten (ix 0)) (PrimitivePop.queries indices) dst (uintWrittenStore (ix 0)) ∧
    Transport 32 hash locations (uintWrittenStore (ix 0)) (uintWrittenNumeric (ix 0)) ∧
    TargetCopyWrite.execute 32 hash dst srcBase uintNumeric (ix 1) seven = some (uintWrittenNumeric (ix 1)) ∧
    Evm.run (TargetCopyWrite.code (.root 0)) (copyWriteInput uintTarget (ix 1) seven) = .ok (copyWriteOutput uintTarget (ix 1) seven) 0 ∧
    Represented (uintWritten (ix 1)) (PrimitivePop.queries indices) dst (uintWrittenStore (ix 1)) ∧
    Transport 32 hash locations (uintWrittenStore (ix 1)) (uintWrittenNumeric (ix 1)) := by
  have first := TargetCopyWrite.complete run uintOld uintSource (uintWritten (ix 0)) (ix 0) seven (by rfl) indices (by decide)
    dst srcBase True.intro True.intro uintStore uintNumeric uintTarget targetTail uintBeforeDst uintBeforeSrc uintInitial (by decide) (by decide)
    (fun j member => (covered j member).1) (fun j member => (covered j member).2) uintSourceCovered visited fitting uintTargetInitial
  have second := TargetCopyWrite.complete run uintOld uintSource (uintWritten (ix 1)) (ix 1) seven (by rfl) indices (by decide)
    dst srcBase True.intro True.intro uintStore uintNumeric uintTarget targetTail uintBeforeDst uintBeforeSrc uintInitial (by decide) (by decide)
    (fun j member => (covered j member).1) (fun j member => (covered j member).2) uintSourceCovered visited fitting uintTargetInitial
  exact ⟨first.1,first.2.1,first.2.2.1,first.2.2.2.1,second.1,second.2.1,second.2.2.1,second.2.2.2.1⟩

/-- Complete UINT graphs, original13numeric/13target and nontrivial contexts
show BOTH runtime indices select changed payloads with sibling/shadow frames. -/
theorem actual_copy_write_uint_ordered :
    (uintGraphView uintOld,uintGraphView uintSource,uintGraphView uintCopied,uintGraphView (uintWritten (ix 0)),uintGraphView (uintWritten (ix 1)),
      view uintNumeric,view uintCopyNumeric,view (uintWrittenNumeric (ix 0)),view (uintWrittenNumeric (ix 1)),
      targetView uintTarget,targetView (readPrefix uintTarget (ix 0)),targetView (copyWriteOutput uintTarget (ix 0) seven),targetView (copyWriteOutput uintTarget (ix 1) seven),
      targetContext (copyWriteOutput uintTarget (ix 0) seven),targetContext (copyWriteOutput uintTarget (ix 1) seven)) =
      ((3,4,some one,some one,some one,some one,some one),(2,2,some twoRead,some three,none,none,some three),
       (2,4,some twoRead,some three,some zero,some one,some three),
       (2,4,some seven,some three,some zero,some one,some three),(2,4,some twoRead,some seven,some zero,some one,some seven),
       (three,twoRead,one,one,one,one,twoRead,three,zero,zero,one,one,seven),
       (twoRead,twoRead,twoRead,three,zero,one,twoRead,three,zero,zero,one,one,seven),
       (twoRead,twoRead,seven,three,zero,one,twoRead,three,zero,zero,one,one,seven),
       (twoRead,twoRead,twoRead,seven,zero,one,twoRead,three,zero,zero,one,one,seven),
       [3,2,1,1,1,1,2,3,0,0,1,1,7],[2,2,2,3,0,1,2,3,0,0,1,1,7],
       [2,2,7,3,0,1,2,3,0,0,1,1,7],[2,2,2,7,0,1,2,3,0,0,1,1,7],targetContext target,targetContext target) := by
  rfl


private def copyWritePrefix (m : Evm.Machine) (i : Index) (word : Semantics.Word) :=
  TargetArrayCopyTail.afterCopy m (.val ⟨i.val,i.isLt⟩ :: .val (TargetOperations.encodeWord word) :: targetTail) (.root 1) (.root 0)
/-- Actual prefix preserves BOTH runtime operands for the subsequent writer;
full non-stack context and all13words accompany the explicit stack observations. -/
theorem actual_copy_write_prefix_operands :
    Evm.run TargetArrayCopy.code (copyWriteInput uintTarget (ix 0) seven) = .ok (copyWritePrefix uintTarget (ix 0) seven) 0 ∧
    Evm.run TargetArrayCopy.code (copyWriteInput uintTarget (ix 1) seven) = .ok (copyWritePrefix uintTarget (ix 1) seven) 0 ∧
    (targetView (copyWritePrefix uintTarget (ix 0) seven),targetView (copyWritePrefix uintTarget (ix 1) seven),
      targetContext (copyWritePrefix uintTarget (ix 0) seven),targetContext (copyWritePrefix uintTarget (ix 1) seven)) =
      ([2,2,2,3,0,1,2,3,0,0,1,1,7],[2,2,2,3,0,1,2,3,0,0,1,1,7],
       targetContext { target with stack := .val (TargetOperations.encodeWord zero) :: .val (TargetOperations.encodeWord seven) :: targetTail },
       targetContext { target with stack := .val (TargetOperations.encodeWord one) :: .val (TargetOperations.encodeWord seven) :: targetTail }) := by
  exact ⟨TargetArrayCopyTail.run_current _ _ _ _,TargetArrayCopyTail.run_current _ _ _ _,rfl⟩

private def absentWritten := (TargetArrayWrite.writeAt absentReadCopied (ix 0) true).getD absentReadCopied
private def absentWrittenStore := Representation.write (CopyTransport.symbolicCopy dst srcBase absentReadStore) (.data dst 0) one
private def absentWrittenNumeric := writeWord absentReadFinal 8 one
/-- Live absent/default capture is writable: the actual scalar store turns
BOTH-absent copied slot into present true without changing sibling shadows. -/
theorem actual_copy_write_absent_default :
    TargetCopyWrite.execute 32 hash dst srcBase absentReadNumeric (ix 0) one = some absentWrittenNumeric ∧
    Evm.run (TargetCopyWrite.code (.root 0)) (copyWriteInput absentReadTarget (ix 0) one) = .ok (copyWriteOutput absentReadTarget (ix 0) one) 0 ∧
    Represented absentWritten (PrimitivePop.queries indices) dst absentWrittenStore ∧
    Transport 32 hash locations absentWrittenStore absentWrittenNumeric ∧
    (graphView absentReadDst,graphView absentSrc,graphView absentReadCopied,graphView absentWritten,
      absentReadCopied.slots ⟨0,by decide⟩,absentWritten.slots ⟨0,by decide⟩,live0 absentReadCopied,live0 absentWritten,
      view absentReadNumeric,view absentReadFinal,view absentWrittenNumeric,targetView absentReadTarget,
      targetView (copyWritePrefix absentReadTarget (ix 0) one),targetView (copyWriteOutput absentReadTarget (ix 0) one),targetContext (copyWriteOutput absentReadTarget (ix 0) one)) =
      ((3,4,some false,some true,some true,some true,some true),(1,2,some false,some true,none,none,none),
       (1,4,some false,some false,some false,some true,none),(1,4,some true,some false,some false,some true,none),
       Slot.absent,Slot.present (Value.prim (G := graph) (p := .bool) true),some false,some true,
       (three,one,zero,one,one,one,zero,one,zero,zero,one,one,seven),
       (one,one,zero,zero,zero,one,zero,one,zero,zero,one,one,seven),
       (one,one,one,zero,zero,one,zero,one,zero,zero,one,one,seven),
       [3,1,0,1,1,1,0,1,0,0,1,1,7],[1,1,0,0,0,1,0,1,0,0,1,1,7],
       [1,1,1,0,0,1,0,1,0,0,1,1,7],targetContext target) := by
  have certified := TargetCopyWrite.complete run absentReadDst absentSrc absentWritten (ix 0) true (by rfl) indices (by decide)
    dst srcBase True.intro True.intro absentReadStore absentReadNumeric absentReadTarget targetTail
    absentReadBeforeDst absentReadBeforeSrc absentReadInitial (by decide) (by decide)
    (fun j member => (covered j member).1) (fun j member => (covered j member).2)
    (by intro j inside; have equal : j = 0 := by change j < 1 at inside; omega
        subst j; decide) visited fitting absentReadTargetInitial
  exact ⟨certified.1,certified.2.1,certified.2.2.1,certified.2.2.2.1,rfl⟩

private def failedWrittenStore := Representation.write (CopyTransport.symbolicCopy dst srcBase failedStore) (.data dst 0) one
private def failedWrittenNumeric := writeWord failedFinal 8 one
/-- Full ORIGINAL selected relations include failed source query2=None with
physical7; no observation is dropped. Actual copy/write preserves its raw word. -/
theorem actual_copy_write_failed_source_frame :
    TargetCopyWrite.execute 32 hash dst srcBase failedNumeric (ix 0) one = some failedWrittenNumeric ∧
    Evm.run (TargetCopyWrite.code (.root 0)) (copyWriteInput failedTarget (ix 0) one) = .ok (copyWriteOutput failedTarget (ix 0) one) 0 ∧
    Represented copiedWritten (PrimitivePop.queries indices) dst failedWrittenStore ∧
    Transport 32 hash locations failedWrittenStore failedWrittenNumeric ∧
    (PrimitivePop.elementQuery (G := graph) (p := .bool) (ix 2)).read source = none ∧
    (graphView old,graphView source,graphView result,graphView copiedWritten,view failedNumeric,view failedFinal,view failedWrittenNumeric,
      targetView failedTarget,targetView (copyWritePrefix failedTarget (ix 0) one),targetView (copyWriteOutput failedTarget (ix 0) one),targetContext (copyWriteOutput failedTarget (ix 0) one)) =
      ((3,4,some true,some true,some true,some true,some true),(1,2,some false,some true,none,none,none),
       (1,4,some false,some false,some false,some true,none),(1,4,some true,some false,some false,some true,none),
       (three,one,one,one,one,one,zero,one,seven,zero,one,one,seven),
       (one,one,zero,zero,zero,one,zero,one,seven,zero,one,one,seven),
       (one,one,one,zero,zero,one,zero,one,seven,zero,one,one,seven),
       [3,1,1,1,1,1,0,1,7,0,1,1,7],[1,1,0,0,0,1,0,1,7,0,1,1,7],
       [1,1,1,0,0,1,0,1,7,0,1,1,7],targetContext target) := by
  have certified := TargetCopyWrite.complete run old source copiedWritten (ix 0) true (by rfl) indices (by decide)
    dst srcBase True.intro True.intro failedStore failedNumeric failedTarget targetTail
    failedBeforeDst failedBeforeSrc failedInitial (by decide) (by decide)
    (fun j member => (covered j member).1) (fun j member => (covered j member).2)
    (by intro j inside; have equal : j = 0 := by change j < 1 at inside; omega
        subst j; decide) visited fitting failedTargetInitial
  exact ⟨certified.1,certified.2.1,certified.2.2.1,certified.2.2.2.1,rfl,rfl⟩

private def selfWritten := (TargetArrayWrite.writeAt (old.overlay old) (ix 0) false).getD old
private def selfWrittenStore := Representation.write (CopyTransport.symbolicCopy dst dst store) (.data dst 0) zero
private def selfWrittenNumeric := writeWord (NumericTraversal.copy 32 hash dst dst machine) 8 zero
private def selfWrittenTarget : Evm.Machine :=
  { TargetArrayCopyTail.afterCopy target (.val ⟨(ix 0).val,(ix 0).isLt⟩ :: .val (TargetOperations.encodeWord zero) :: targetTail) (.root 0) (.root 0) with stack := targetTail, store := Evm.WordStore.write (TargetArrayCopyTail.afterCopy target (.val ⟨(ix 0).val,(ix 0).isLt⟩ :: .val (TargetOperations.encodeWord zero) :: targetTail) (.root 0) (.root 0)).store (.data (.root 0) 0) 0 }
/-- Self-alias copy followed by a changed live scalar write uses the SAME
GOOD run and both OLD relations; source capture is not a disjointness premise. -/
theorem actual_copy_write_self_alias :
    TargetCopyWrite.execute 32 hash dst dst machine (ix 0) zero = some selfWrittenNumeric ∧
    Evm.run (TargetCopyWrite.code (.root 0)) { target with stack := .slot (.root 0) :: .slot (.root 0) :: .val ⟨(ix 0).val,(ix 0).isLt⟩ :: .val (TargetOperations.encodeWord zero) :: targetTail } = .ok selfWrittenTarget 0 ∧
    Represented selfWritten (PrimitivePop.queries indices) dst selfWrittenStore ∧
    Transport 32 hash locations selfWrittenStore selfWrittenNumeric ∧
    (graphView old,graphView (old.overlay old),graphView selfWritten,view machine,view selfWrittenNumeric,targetView target,targetView selfWrittenTarget,targetContext selfWrittenTarget) =
      ((3,4,some true,some true,some true,some true,some true),(3,4,some true,some true,some true,some true,some true),
       (3,4,some false,some true,some true,some true,some true),
       (three,one,one,one,one,one,zero,one,zero,zero,one,one,seven),
       (three,one,zero,one,one,one,zero,one,zero,zero,one,one,seven),
       [3,1,1,1,1,1,0,1,0,0,1,1,7],[3,1,0,1,1,1,0,1,0,0,1,1,7],targetContext target) := by
  have certified := TargetCopyWrite.complete run old old selfWritten (ix 0) false (by rfl) indices (by decide)
    dst dst True.intro True.intro store machine target targetTail beforeDst beforeDst initial (by decide) (by decide)
    (fun j member => (covered j member).1) (fun j member => (covered j member).1)
    (by intro j inside; exact visited j (by change j < 3 at inside; change j < max 3 1; omega)) visited fitting targetInitial
  exact ⟨certified.1,certified.2.1,certified.2.2.1,certified.2.2.2.1,rfl⟩


private def retainedWriteRaw := ((old.overlay source).save (path (ix 1)) (.prim true)).getD (old.overlay source)
/-- Actual copy changes retained1 to false and keeps older3 true. Typed LIVE
write and current numeric/target guards all fail, while raw retained save can
succeed. The separately executed prefix is represented; no world rollback. -/
theorem actual_copy_write_late_failures :
    Evm.run TargetArrayCopy.code (copyWriteInput target (ix 1) one) = .ok (copyWritePrefix target (ix 1) one) 0 ∧
    Represented result (PrimitivePop.queries indices) dst afterCopy ∧ Transport 32 hash locations afterCopy final ∧
    (old.overlay source).save (path (ix 1)) (.prim true) = some retainedWriteRaw ∧
    TargetArrayWrite.writeAt (old.overlay source) (ix 1) true = none ∧
    Evm.run (TargetCopyWrite.code (.root 0)) (copyWriteInput target (ix 1) one) = .revert ∧
    TargetCopyWrite.execute 32 hash dst srcBase machine (ix 1) one = none ∧
    Evm.run (TargetCopyWrite.code (.root 0)) (copyWriteInput target (ix 3) zero) = .revert ∧
    TargetCopyWrite.execute 32 hash dst srcBase machine (ix 3) zero = none ∧
    Evm.run (TargetCopyWrite.code (.root 0)) (copyWriteInput target outsideReadIndex one) = .revert ∧
    TargetCopyWrite.execute 32 hash dst srcBase machine outsideReadIndex one = none ∧
    (graphView old,graphView source,graphView result,graphView retainedWriteRaw,
      result.observe (path (ix 1)),result.observe (path (ix 3)),result.observe (path outsideReadIndex),
      view machine,view final,targetView target,targetView (copyWritePrefix target (ix 1) one),targetContext (copyWritePrefix target (ix 1) one),
      final ((Solidity.Storage.Loc.data dst outsideReadIndex.val).word 32 hash)) =
      ((3,4,some true,some true,some true,some true,some true),(1,2,some false,some true,none,none,none),
       (1,4,some false,some false,some false,some true,none),(1,4,some false,some true,some false,some true,none),
       some false,some true,none,
       (three,one,one,one,one,one,zero,one,zero,zero,one,one,seven),
       (one,one,zero,zero,zero,one,zero,one,zero,zero,one,one,seven),
       [3,1,1,1,1,1,0,1,0,0,1,1,7],[1,1,0,0,0,1,0,1,0,0,1,1,7],
       targetContext { target with stack := .val (TargetOperations.encodeWord one) :: .val (TargetOperations.encodeWord one) :: targetTail },one) := by
  refine ⟨TargetArrayCopyTail.run_current _ _ _ _,full_copy_bridge.2,full_copy_bridge.1,rfl,rfl,?_,?_,?_,?_,?_,?_,rfl⟩
  · exact (TargetCopyWrite.failure_matches old source (ix 1) true target targetTail (.root 1) (.root 0) (by rfl)).mpr (by rfl)
  · exact (TargetCopyWrite.numeric_failure_matches old source (ix 1) true hash dst srcBase machine (by rfl)).mpr (by rfl)
  · exact (TargetCopyWrite.failure_matches old source (ix 3) false target targetTail (.root 1) (.root 0) (by rfl)).mpr (by rfl)
  · exact (TargetCopyWrite.numeric_failure_matches old source (ix 3) false hash dst srcBase machine (by rfl)).mpr (by rfl)
  · exact (TargetCopyWrite.failure_matches old source outsideReadIndex true target targetTail (.root 1) (.root 0) (by rfl)).mpr (by rfl)
  · exact (TargetCopyWrite.numeric_failure_matches old source outsideReadIndex true hash dst srcBase machine (by rfl)).mpr (by rfl)

private def uncheckedCopyWriteCode : List Evm.Instr :=
  TargetArrayCopy.code ++ (TargetCopyRead.operands (.root 0) ++ (Evm.elemSlot 1 ++ [.sstore]))
private theorem unchecked_copy_write (i : Index) (word : Semantics.Word) :
    Evm.run uncheckedCopyWriteCode (copyWriteInput target i word) = .ok (copyWriteOutput target i word) 0 := by
  unfold uncheckedCopyWriteCode copyWriteInput
  rw [Evm.run_append_ok (TargetArrayCopyTail.run_current target (.val ⟨i.val,i.isLt⟩ :: .val (TargetOperations.encodeWord word) :: targetTail) (.root 1) (.root 0))]
  rw [Evm.run_append_ok (m' := { copyWritePrefix target i word with stack := .val ⟨i.val,i.isLt⟩ :: .slot (.root 0) :: .val (TargetOperations.encodeWord word) :: targetTail }) (by rfl)]
  rw [Evm.run_append_ok (Evm.elemSlot_run (copyWritePrefix target i word) (.val (TargetOperations.encodeWord word) :: targetTail) i.val 1 (.root 0) i.isLt)]
  rw [Nat.mul_one]
  rfl

/-- Actual missing-guard programs mutate retained1 or erase older3, whereas
correct code rejects both before the scalar write. Complete observations differ. -/
theorem actual_copy_write_unchecked_negative :
    Evm.run uncheckedCopyWriteCode (copyWriteInput target (ix 1) one) = .ok (copyWriteOutput target (ix 1) one) 0 ∧
    Evm.run uncheckedCopyWriteCode (copyWriteInput target (ix 3) zero) = .ok (copyWriteOutput target (ix 3) zero) 0 ∧
    (targetView (copyWritePrefix target (ix 1) one),targetView (copyWriteOutput target (ix 1) one),
      targetView (copyWriteOutput target (ix 3) zero),targetContext (copyWriteOutput target (ix 1) one),targetContext (copyWriteOutput target (ix 3) zero)) =
      ([1,1,0,0,0,1,0,1,0,0,1,1,7],[1,1,0,1,0,1,0,1,0,0,1,1,7],
       [1,1,0,0,0,0,0,1,0,0,1,1,7],targetContext target,targetContext target) := by
  exact ⟨unchecked_copy_write _ _,unchecked_copy_write _ _,rfl⟩

private def writeFirstCode : List Evm.Instr := ([.pop,.pop] ++ TargetCopyRead.operands (.root 0)) ++
  (TargetArrayWrite.code ++ ([.push (.slot (.root 0)),.push (.slot (.root 1))] ++ TargetArrayCopy.code))
private def writtenFirstTarget : Evm.Machine := { target with store := Evm.WordStore.write target.store (.data (.root 0) 0) 1 }
private def writeFirstFinal := TargetArrayCopyTail.afterCopy writtenFirstTarget targetTail (.root 1) (.root 0)
private def writtenFirstGraph := (TargetArrayWrite.writeAt old (ix 0) true).getD old
private def writeFirstGraph := writtenFirstGraph.overlay source
private def writeFirstNumeric := NumericTraversal.copy 32 hash dst srcBase (writeWord machine 8 one)

/-- Actual reversed write→copy loses the caller payload true to copied false;
correct copy→write keeps true. Independent graph/numeric/target order agrees. -/
theorem actual_copy_write_wrong_order :
    Evm.run writeFirstCode (copyWriteInput target (ix 0) one) = .ok writeFirstFinal 0 ∧
    (graphView old,graphView writeFirstGraph,graphView copiedWritten,view writeFirstNumeric,view copiedWriteNumeric,
      targetView writeFirstFinal,targetView (copyWriteOutput target (ix 0) one),
      targetContext writeFirstFinal,targetContext (copyWriteOutput target (ix 0) one)) =
      ((3,4,some true,some true,some true,some true,some true),(1,4,some false,some false,some false,some true,none),
       (1,4,some true,some false,some false,some true,none),
       (one,one,zero,zero,zero,one,zero,one,zero,zero,one,one,seven),
       (one,one,one,zero,zero,one,zero,one,zero,zero,one,one,seven),
       [1,1,0,0,0,1,0,1,0,0,1,1,7],[1,1,1,0,0,1,0,1,0,0,1,1,7],targetContext target,targetContext target) := by
  refine ⟨?_,rfl⟩
  unfold writeFirstCode
  rw [Evm.run_append_ok (m' := { target with stack := .val ⟨(ix 0).val,(ix 0).isLt⟩ :: .slot (.root 0) :: .val (TargetOperations.encodeWord one) :: targetTail }) (by rfl)]
  have written : Evm.run TargetArrayWrite.code { target with stack := .val ⟨(ix 0).val,(ix 0).isLt⟩ :: .slot (.root 0) :: .val (TargetOperations.encodeWord one) :: targetTail } = .ok writtenFirstTarget 0 := by
    rw [TargetArrayWrite.run_current,if_pos (by decide)]; rfl
  rw [Evm.run_append_ok written]
  rw [Evm.run_append_ok (m' := { writtenFirstTarget with stack := .slot (.root 1) :: .slot (.root 0) :: targetTail }) (by rfl)]
  exact TargetArrayCopyTail.run_current _ _ _ _

/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_write_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_write_bridge
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_write_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_write_ordered
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_write_runtime_values' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_write_runtime_values
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_write_uint_indices' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_write_uint_indices
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_write_uint_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_write_uint_ordered
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_write_prefix_operands' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_write_prefix_operands
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_write_absent_default' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_write_absent_default
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_write_failed_source_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_write_failed_source_frame
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_write_self_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_write_self_alias
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_write_late_failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_write_late_failures
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_write_unchecked_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_write_unchecked_negative
/-- info: 'Solidity.Backend.StorageOps.NumericTraversalControls.actual_copy_write_wrong_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copy_write_wrong_order

end Solidity.Backend.StorageOps.NumericTraversalControls
