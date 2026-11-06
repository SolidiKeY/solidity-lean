import Solidity.Backend.StorageOps.FiniteRootComposition
import Solidity.Backend.StorageOps.OutputRootComplete
import Solidity.Backend.StorageOps.OutputRootComposition
import Solidity.Backend.StorageOps.ShrinkRootComposition
import Solidity.Backend.StorageOps.MixedLiveComposition
import Solidity.Backend.StorageOps.TargetNestedArrayTransport
import Solidity.Backend.StorageOps.NestedCopyObservations
import Solidity.Backend.StorageOps.NestedSnapshotFrames
import Solidity.Backend.StorageOps.NestedRetainedCopy
import Solidity.Backend.StorageOps.NestedClearFrames
import Solidity.Backend.StorageOps.NestedLaterFrames
import Solidity.Backend.StorageOps.NestedPhaseComposition
import Solidity.Backend.StorageOps.NestedRootComposition
import Solidity.Backend.StorageOps.CopyAccess
import Solidity.Backend.StorageOps.RootCopyAccess
import Solidity.Backend.StorageOps.LaterClearFrames
import Solidity.Backend.StorageOps.NestedStaleComposition
import Solidity.Backend.StorageOps.NestedOlderComposition
import Solidity.Backend.StorageOps.NestedFreshComposition

/-! Inhabited PUBLIC finite-run and current nested numeric/target controls.
Independent graph postowner preservation is not assumed by the bridge. -/
namespace Solidity.Backend.StorageOps.TargetNestedArrayTransportControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Convert bounded natural-index coverage to the identical dependent finite
index family. Bounds remain arbitrary; this imposes no source-program cap. -/
theorem forall_bounded_pair {outer : Nat} {inner : Nat → Nat} {P : Nat → Nat → Prop}
    (finite : ∀ i : Fin outer, ∀ j : Fin (inner i.val), P i.val j.val) :
    ∀ i, i < outer → ∀ j, j < inner i → P i j :=
  fun i hi j hj => finite ⟨i, hi⟩ ⟨j, hj⟩

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.forall_bounded_pair' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms forall_bounded_pair
private def w (n : Fin 128) : Semantics.Word := lengthWord n.val (by
  have bound := n.isLt
  have wide : 128 < 2^256 := by decide
  omega)
private def w3 (n : Fin 3) : Semantics.Word := w ⟨n.val,by have bound := n.isLt; omega⟩
private def store (sourceOuter oldOuter inner : Fin 3) : Store := fun l =>
  if l = .root 0 then w3 sourceOuter else
  if l = .root 1 then w3 oldOuter else
  if l = .data (.root 0) 0 then w3 inner else
  if l = .data (.data (.root 0) 0) 0 then w 7 else
  if l = .data (.data (.root 0) 0) 1 then w 11 else
  if l = .data (.data (.root 0) 0) 2 then w 13 else
  if l = .data (.root 0) 1 then w 1 else
  if l = .data (.data (.root 0) 1) 0 then w 17 else
  if l = .data (.data (.root 0) 1) 1 then w 19 else
  if l = .data (.root 0) 2 then w 1 else
  if l = .data (.data (.root 0) 2) 0 then w 71 else
  if l = .data (.root 1) 0 then w 3 else
  if l = .data (.data (.root 1) 0) 0 then w 23 else
  if l = .data (.data (.root 1) 0) 1 then w 29 else
  if l = .data (.data (.root 1) 0) 2 then w 31 else
  if l = .data (.data (.root 1) 0) 3 then w 37 else
  if l = .data (.root 1) 1 then w 2 else
  if l = .data (.data (.root 1) 1) 0 then w 41 else
  if l = .data (.data (.root 1) 1) 1 then w 43 else
  if l = .data (.data (.root 1) 1) 2 then w 47 else
  if l = .data (.root 1) 2 then w 2 else
  if l = .data (.data (.root 1) 2) 0 then w 53 else
  if l = .data (.data (.root 1) 2) 1 then w 59 else
  if l = .data (.data (.root 1) 2) 2 then w 61 else
  if l = .root 7 then w 73 else w 0
private def numeric (sourceOuter oldOuter inner : Fin 3) : WordStore := fun address =>
  if address = 0 then w3 sourceOuter else
  if address = 1 then w3 oldOuter else
  if address = 8 then w3 inner else
  if address = 24 then w 7 else
  if address = 25 then w 11 else
  if address = 26 then w 13 else
  if address = 9 then w 1 else
  if address = 32 then w 17 else
  if address = 33 then w 19 else
  if address = 10 then w 1 else
  if address = 40 then w 71 else
  if address = 16 then w 3 else
  if address = 48 then w 23 else
  if address = 49 then w 29 else
  if address = 50 then w 31 else
  if address = 51 then w 37 else
  if address = 17 then w 2 else
  if address = 56 then w 41 else
  if address = 57 then w 43 else
  if address = 58 then w 47 else
  if address = 18 then w 2 else
  if address = 64 then w 53 else
  if address = 65 then w 59 else
  if address = 66 then w 61 else
  if address = 7 then w 73 else w 0
private def hash (p : Solidity.Storage.Pre) : Nat := if p = .data 0 then 8 else if p = .data 1 then 16 else if p = .data 8 then 24 else if p = .data 9 then 32 else if p = .data 10 then 40 else if p = .data 16 then 48 else if p = .data 17 then 56 else if p = .data 18 then 64 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0,.data 1,.data 8,.data 9,.data 10,.data 16,.data 17,.data 18]
private def locations : List Solidity.Storage.Loc := [.root 0,.root 1,.data (.root 0) 0,.data (.data (.root 0) 0) 0,.data (.data (.root 0) 0) 1,.data (.data (.root 0) 0) 2,.data (.root 0) 1,.data (.data (.root 0) 1) 0,.data (.data (.root 0) 1) 1,.data (.root 0) 2,.data (.data (.root 0) 2) 0,.data (.root 1) 0,.data (.data (.root 1) 0) 0,.data (.data (.root 1) 0) 1,.data (.data (.root 1) 0) 2,.data (.data (.root 1) 0) 3,.data (.root 1) 1,.data (.data (.root 1) 1) 0,.data (.data (.root 1) 1) 1,.data (.data (.root 1) 1) 2,.data (.root 1) 2,.data (.data (.root 1) 2) 0,.data (.data (.root 1) 2) 1,.data (.data (.root 1) 2) 2,.root 7]
private theorem run : FiniteRun 128 8 8 hash preimages locations := by
  constructor
  · intro p
    simp only [hash]
    split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> decide))))))))))))))
  · decide
  · decide
  · decide
  · intro l member
    simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem initial (sourceOuter oldOuter inner : Fin 3) : Transport 128 hash locations (store sourceOuter oldOuter inner) (numeric sourceOuter oldOuter inner) := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private def fitting : ∀ l ∈ locations, TargetOperations.KeysFit l := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
private def tail : List Evm.Word := [.val (TargetOperations.encodeWord (w 97)),.slot (.root 9)]
private def target (sourceOuter oldOuter inner : Fin 3) : Evm.Machine :=
  { stack := tail,store := .ofFn (fun slot => (TargetOperations.encodeWord (store sourceOuter oldOuter inner (Solidity.Storage.ofSlot slot))).val),
    mem := fun _ => .val (TargetOperations.encodeWord (w 79)),bal := fun _ => 13,bal₀ := fun _ => 17,
    self := ⟨5,by decide⟩,caller := ⟨7,by decide⟩,callvalue := ⟨11,by decide⟩,timestamp := ⟨19,by decide⟩,accepts := fun _ _ => false }
private theorem targetInitial (sourceOuter oldOuter inner : Fin 3) :
    ∀ l (member : l ∈ locations), (target sourceOuter oldOuter inner).store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (store sourceOuter oldOuter inner l) := by
  intro l member
  change Evm.wmod (TargetOperations.encodeWord (store sourceOuter oldOuter inner (Solidity.Storage.ofSlot (TargetOperations.toSlot l (fitting l member))))).val = _
  rw [TargetOperations.ofSlot_toSlot,Evm.wmod_of_lt (TargetOperations.encodeWord (store sourceOuter oldOuter inner l)).isLt]
private def numericView (m : WordStore) := locations.map (fun l => m (l.word 128 hash))
private def symbolicView (m : Store) := locations.map m
private def targetView (m : Evm.Machine) := locations.attach.map (fun l => m.store (TargetOperations.toSlot l.val (fitting l.val l.property)))
private def context (m : Evm.Machine) := (m.stack,m.mem,m.bal,m.bal₀,m.self,m.accepts,m.caller,m.callvalue,m.timestamp)
private def afterTarget (n o i : Fin 3) := TargetNestedArrayRuntime.afterCopy (target n o i) tail (.root 0) (.root 1)

/-- A GOOD concrete hash region inhabits every current child/header/payload
coverage premise. Both numeric/target intermediates are derived, not supplied. -/
theorem shrinking_bridge :
    FiniteRun 128 8 8 hash preimages locations ∧ Transport 128 hash locations (store 1 2 2) (numeric 1 2 2) ∧
    Evm.run TargetNestedArrayCopy.code { target 1 2 2 with stack := .slot (.root 0) :: .slot (.root 1) :: tail } = .ok (afterTarget 1 2 2) 0 ∧
    Transport 128 hash locations (TargetNestedArrayTransport.afterStore (store 1 2 2) (.root 1) (.root 0))
      (TargetNestedArrayTransport.execute 128 hash (numeric 1 2 2) (.root 1) (.root 0)) ∧
    (∀ l (member : l ∈ locations), (afterTarget 1 2 2).store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore (store 1 2 2) (.root 1) (.root 0) l)) := by
  refine ⟨run,initial 1 2 2,?_⟩
  apply TargetNestedArrayTransport.complete run (.root 1) (.root 0) (by trivial) (by trivial)
    (store 1 2 2) (numeric 1 2 2) (target 1 2 2) tail (initial 1 2 2) fitting (targetInitial 1 2 2) (by decide) (by decide)
  · intro k inside
    change k < 1 at inside
    have same : k = 0 := by omega
    subst k; decide
  · intro k inside j live
    change k < 1 at inside
    have same : k = 0 := by omega
    subst k
    change j < 2 at live
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with rfl | rfl <;> decide
  · intro k inside j visited
    change k < 1 at inside
    have same : k = 0 := by omega
    subst k
    change j < 3 at visited
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with rfl | rfl | rfl <;> decide
  · intro k inside begun
    change k < 2 at inside
    change 1 ≤ k at begun
    have same : k = 1 := by omega
    subst k; decide
  · intro k inside begun j live
    change k < 2 at inside
    change 1 ≤ k at begun
    have same : k = 1 := by omega
    subst k
    change j < 2 at live
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with rfl | rfl <;> decide

/-- COMPLETE physical numeric BEFORE/COPY/CLEAR/FINAL vectors, independent
symbolic generated-store result, all covered target words and context. -/
theorem shrinking_ordered :
    (numericView (numeric 1 2 2),
      numericView (TargetNestedArrayTransport.copyNumerics 128 hash (numeric 1 2 2) (.root 1) (.root 0) 1),
      numericView (TargetNestedArrayTransport.clearNumerics 128 hash (TargetNestedArrayTransport.copyNumerics 128 hash (numeric 1 2 2) (.root 1) (.root 0) 1) (.root 1) 1 2),
      numericView (TargetNestedArrayTransport.execute 128 hash (numeric 1 2 2) (.root 1) (.root 0)),
      symbolicView (TargetNestedArrayTransport.afterStore (store 1 2 2) (.root 1) (.root 0)),targetView (afterTarget 1 2 2),context (afterTarget 1 2 2)) =
      ([w 1,w 2,w 2,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 3,w 23,w 29,w 31,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
       [w 1,w 2,w 2,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 2,w 7,w 11,w 0,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
       [w 1,w 2,w 2,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 2,w 7,w 11,w 0,w 37,w 0,w 0,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
       [w 1,w 1,w 2,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 2,w 7,w 11,w 0,w 37,w 0,w 0,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
       [w 1,w 1,w 2,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 2,w 7,w 11,w 0,w 37,w 0,w 0,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
       [1,1,2,7,11,13,1,17,19,1,71,2,7,11,0,37,0,0,0,47,2,53,59,61,73],context (target 1 2 2)) := by rfl

/-- Both growing runtime child copies inhabit the SAME full numeric bridge;
the stale-outer coverage obligations are discharged by the actual empty suffix. -/
theorem growing_bridge :
    Evm.run TargetNestedArrayCopy.code { target 2 1 1 with stack := .slot (.root 0) :: .slot (.root 1) :: tail } = .ok (afterTarget 2 1 1) 0 ∧
    Transport 128 hash locations (TargetNestedArrayTransport.afterStore (store 2 1 1) (.root 1) (.root 0))
      (TargetNestedArrayTransport.execute 128 hash (numeric 2 1 1) (.root 1) (.root 0)) ∧
    (∀ l (member : l ∈ locations), (afterTarget 2 1 1).store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore (store 2 1 1) (.root 1) (.root 0) l)) := by
  apply TargetNestedArrayTransport.complete run (.root 1) (.root 0) (by trivial) (by trivial)
    (store 2 1 1) (numeric 2 1 1) (target 2 1 1) tail (initial 2 1 1) fitting (targetInitial 2 1 1) (by decide) (by decide)
  · intro k inside
    change k < 2 at inside
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl <;> decide
  · exact forall_bounded_pair (by decide)
  · exact forall_bounded_pair (by decide)
  · intro k inside begun
    change k < 2 at inside
    change 2 ≤ k at begun
    omega
  · intro k inside begun j live
    change k < 2 at inside
    change 2 ≤ k at begun
    omega

/-- Same-root aliases instantiate full raw transport; no blanket alias ban. -/
theorem self_bridge :
    Evm.run TargetNestedArrayCopy.code { target 1 2 2 with stack := .slot (.root 0) :: .slot (.root 0) :: tail } =
      .ok (TargetNestedArrayRuntime.afterCopy (target 1 2 2) tail (.root 0) (.root 0)) 0 ∧
    Transport 128 hash locations (TargetNestedArrayTransport.afterStore (store 1 2 2) (.root 0) (.root 0))
      (TargetNestedArrayTransport.execute 128 hash (numeric 1 2 2) (.root 0) (.root 0)) ∧
    (∀ l (member : l ∈ locations), (TargetNestedArrayRuntime.afterCopy (target 1 2 2) tail (.root 0) (.root 0)).store.cells
      (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore (store 1 2 2) (.root 0) (.root 0) l)) := by
  apply TargetNestedArrayTransport.complete run (.root 0) (.root 0) (by trivial) (by trivial)
    (store 1 2 2) (numeric 1 2 2) (target 1 2 2) tail (initial 1 2 2) fitting (targetInitial 1 2 2) (by decide) (by decide)
  · intro k inside
    change k < 1 at inside
    have same : k = 0 := by omega
    subst k; decide
  · intro k inside j live
    change k < 1 at inside
    have same : k = 0 := by omega
    subst k
    change j < 2 at live
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with rfl | rfl <;> decide
  · intro k inside j visited
    change k < 1 at inside
    have same : k = 0 := by omega
    subst k
    change j < 2 at visited
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with rfl | rfl <;> decide
  · intro k inside begun
    change k < 1 at inside
    change 1 ≤ k at begun
    omega
  · intro k inside begun j live
    change k < 1 at inside
    change 1 ≤ k at begun
    omega

/-- COMPLETE growing BEFORE/COPY/CLEAR/FINAL numeric and final symbolic/target
vectors, plus the same-root entire numeric/target/context result. -/
theorem growing_self_ordered :
    (numericView (numeric 2 1 1),numericView (TargetNestedArrayTransport.copyNumerics 128 hash (numeric 2 1 1) (.root 1) (.root 0) 2),
      numericView (TargetNestedArrayTransport.clearNumerics 128 hash (TargetNestedArrayTransport.copyNumerics 128 hash (numeric 2 1 1) (.root 1) (.root 0) 2) (.root 1) 2 2),
      numericView (TargetNestedArrayTransport.execute 128 hash (numeric 2 1 1) (.root 1) (.root 0)),
      symbolicView (TargetNestedArrayTransport.afterStore (store 2 1 1) (.root 1) (.root 0)),targetView (afterTarget 2 1 1),context (afterTarget 2 1 1),
      numericView (TargetNestedArrayTransport.execute 128 hash (numeric 1 2 2) (.root 0) (.root 0)),
      targetView (TargetNestedArrayRuntime.afterCopy (target 1 2 2) tail (.root 0) (.root 0)),
      context (TargetNestedArrayRuntime.afterCopy (target 1 2 2) tail (.root 0) (.root 0))) =
      ([w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 3,w 23,w 29,w 31,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
       [w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
       [w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
       [w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
       [w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
       [2,2,1,7,11,13,1,17,19,1,71,1,7,0,0,37,1,17,0,47,2,53,59,61,73],context (target 2 1 1),[w 1,w 2,w 2,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 3,w 23,w 29,w 31,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
       [1,2,2,7,11,13,1,17,19,1,71,3,23,29,31,37,2,41,43,47,2,53,59,61,73],context (target 1 2 2)) := by rfl

private def graph : Schema 0 where
  origin := "v10-nested-transport-logical-boundary"
  declId := fun i => nomatch i
  declId_injective := by intro i; exact Fin.elim0 i
  name := fun i => nomatch i
  fields := fun i => nomatch i
  rank := fun i => nomatch i
  nonempty := by intro i; exact Fin.elim0 i
  distinct := by intro i; exact Fin.elim0 i
  guarded := by intro i; exact Fin.elim0 i
private def innerA : Value graph (.array (.prim .uint)) := .array ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide)
  (fun i => .present (.prim (if i.val = 0 then w 7 else if i.val = 1 then w 11 else w 13)))
private def innerB : Value graph (.array (.prim .uint)) := .array ⟨2,by decide⟩ ⟨1,by decide⟩ (by decide)
  (fun i => .present (.prim (if i.val = 0 then w 17 else w 19)))
private def sourceGraph : Value graph (.array (.array (.prim .uint))) := .array ⟨2,by decide⟩ ⟨1,by decide⟩ (by decide)
  (fun i => if i.val = 0 then .present innerA else .present innerB)
private def retainedPath : TypeGraph.Path graph (.array (.array (.prim .uint))) (.array (.prim .uint)) := .cons (.index ⟨1,by decide⟩) .nil
private def missingPath : TypeGraph.Path graph (.array (.array (.prim .uint))) (.array (.prim .uint)) := .cons (.index ⟨2,by decide⟩) .nil
private def sourceQueries : List (Query graph (.array (.array (.prim .uint)))) := [.length .nil,.length retainedPath,.length missingPath]
private theorem source_selected : Represented sourceGraph sourceQueries (.root 0) (store 1 2 2) := by
  intro q member
  simp only [sourceQueries,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro observed found
    change some (w 1) = some observed at found
    cases found; rfl
  · refine ⟨by change 1 < lmax ∧ True; decide,⟨by decide,by decide⟩,?_⟩
    intro observed found
    change some (w 1) = some observed at found
    cases found; rfl
  · refine ⟨by change 2 < lmax ∧ True; decide,True.intro,?_⟩
    intro observed found
    change (none : Option Semantics.Word) = some observed at found
    cases found

/-- GOOD run/OLD PUBLIC selected owner hold while a missing path's COVERED raw
header is NONZERO. Retained logical and live reads also remain distinct. -/
theorem failed_query_nonzero_boundary :
    Represented sourceGraph sourceQueries (.root 0) (store 1 2 2) ∧
    FiniteRun 128 8 8 hash preimages locations ∧ Transport 128 hash locations (store 1 2 2) (numeric 1 2 2) ∧
    ((Query.length retainedPath).read sourceGraph,retainedPath.readLive Value.dflt sourceGraph,
      (Query.length missingPath).read sourceGraph,numeric 1 2 2 ((Solidity.Storage.Loc.data (.root 0) 2).word 128 hash),
      (target 1 2 2).store (.data (.root 0) 2),(afterTarget 1 2 2).store (.data (.root 0) 2)) =
      (some (w 1),none,none,w 1,1,1) := by
  exact ⟨source_selected,run,initial 1 2 2,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.shrinking_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shrinking_bridge
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.shrinking_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shrinking_ordered
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.growing_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms growing_bridge
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.self_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms self_bridge
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.growing_self_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms growing_self_ordered
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.failed_query_nonzero_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failed_query_nonzero_boundary

private def freshIndex (i : Fin 3) : Index := ⟨i.val,by
  have bound := i.isLt
  have wide : 3 < 2^256 := by decide
  omega⟩
private def freshIndices : List Index := [freshIndex 0,freshIndex 1,freshIndex 2]
private def firstPath : TypeGraph.Path graph (.array (.array (.prim .uint))) (.array (.prim .uint)) := NestedCopyObservations.childPath (freshIndex 0)
private def freshRoot : Value graph (.array (.array (.prim .uint))) := Value.dflt _
private def copiedRoot : Value graph (.array (.array (.prim .uint))) := sourceGraph.strip
private def freshRootQueries : List (Query graph (.array (.array (.prim .uint)))) :=
  .length .nil :: ((PrimitivePop.queries freshIndices).map (Query.prefix firstPath) ++ [.length retainedPath])
private theorem beforeInnerA : Represented innerA (PrimitivePop.queries freshIndices) (.data (.root 0) 0) (store 1 0 2) := by
  intro q member
  simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro observed found; change some (w 2) = some observed at found; cases found; rfl
  · refine ⟨by change 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro observed found; change some (w 7) = some observed at found; cases found; rfl
  · refine ⟨by change 1 < lmax ∧ True; decide,True.intro,?_⟩
    intro observed found; change some (w 11) = some observed at found; cases found; rfl
  · refine ⟨by change 2 < lmax ∧ True; decide,True.intro,?_⟩
    intro observed found; change some (w 13) = some observed at found; cases found; rfl
private theorem firstSupported : PathSupported firstPath := by change 0 < lmax ∧ True; decide
private theorem beforeFreshRoot : Represented freshRoot freshRootQueries (.root 1) (store 1 0 2) := by
  intro q member
  simp only [freshRootQueries,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at member
  rcases member with rfl | childMember | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro observed found; change some (w 0) = some observed at found; cases found; rfl
  · obtain ⟨suffix,suffixMember,rfl⟩ := List.mem_map.mp childMember
    refine ⟨(Query.supported_prefix firstPath suffix).mpr ⟨firstSupported,(beforeInnerA suffix suffixMember).1⟩,?_,?_⟩
    · cases suffix <;> exact True.intro
    · intro observed found
      cases suffix <;> change (none : Option Semantics.Word) = some observed at found <;> cases found
  · refine ⟨by change 1 < lmax ∧ True; decide,True.intro,?_⟩
    intro observed found; change (none : Option Semantics.Word) = some observed at found; cases found
private def innerCopyStore := CopyTransport.symbolicCopy (.data (.root 1) 0) (.data (.root 0) 0) (store 1 0 2)
private def innerNumeric := NumericTraversal.copy 128 hash (.data (.root 1) 0) (.data (.root 0) 0) (numeric 1 0 2)
private def innerTarget := TargetArrayCopyTail.afterCopy (target 1 0 2) tail (.data (.root 0) 0) (.data (.root 1) 0)

/-- OLD whole-root PUBLIC relation and a missing child hold while that child's
raw header is3, contradicting an initial standalone default-child relation.
The ACTUAL copy still derives the independent stripped OUTPUT relation. -/
theorem fresh_child_bridge :
    Represented freshRoot freshRootQueries (.root 1) (store 1 0 2) ∧ freshRoot.find firstPath = none ∧
    ¬ Represented (Value.dflt (G := graph) (.array (.prim .uint))) [.length .nil] (.data (.root 1) 0) (store 1 0 2) ∧
    Evm.run TargetArrayCopy.code { target 1 0 2 with stack := .slot (.data (.root 0) 0) :: .slot (.data (.root 1) 0) :: tail } = .ok innerTarget 0 ∧
    Represented innerA.strip (PrimitivePop.queries freshIndices) (.data (.root 1) 0) innerCopyStore ∧
    Transport 128 hash locations innerCopyStore innerNumeric ∧
    (∀ l (member : l ∈ locations), innerTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (innerCopyStore l)) := by
  refine ⟨beforeFreshRoot,rfl,?_,?_⟩
  · intro invalid
    have zero := (invalid (.length .nil) List.mem_cons_self).2.2 (w 0) (by rfl)
    change w 3 = w 0 at zero
    exact (by decide : w 3 ≠ w 0) zero
  · apply NestedCopyObservations.strip_complete run innerA freshIndices (.data (.root 1) 0) (.data (.root 0) 0) (by trivial) (by trivial)
      (store 1 0 2) (numeric 1 0 2) (target 1 0 2) tail beforeInnerA (initial 1 0 2) fitting (targetInitial 1 0 2) (by decide) (by decide)
    · intro i member
      simp only [freshIndices,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl <;> decide
    · intro i member
      simp only [freshIndices,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl <;> decide
    · intro j live
      change j < 2 at live
      have casesJ : j = 0 ∨ j = 1 := by omega
      rcases casesJ with rfl | rfl <;> decide
    · intro j visited
      change j < 3 at visited
      have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases casesJ with rfl | rfl | rfl <;> decide

private theorem afterInnerFinal : Represented innerA.strip (PrimitivePop.queries freshIndices) (.data (.root 1) 0)
    (TargetNestedArrayTransport.afterStore (store 1 0 2) (.root 1) (.root 0)) := by
  have old := fresh_child_bridge.2.2.2.2.1
  intro q member
  have current := old q member
  refine ⟨current.1,current.2.1,?_⟩
  intro word observed
  have value := current.2.2 word observed
  simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
  rcases member with rfl | ⟨i,inside,rfl⟩
  · change (Representation.write innerCopyStore (.root 1) (w 1)) (.data (.root 1) 0) = word
    rw [Representation.write_other _ _ _ _ (by decide)]
    exact value
  · rw [PrimitivePop.element_location] at value ⊢
    change (Representation.write innerCopyStore (.root 1) (w 1)) (.data (.data (.root 1) 0) i.val) = word
    rw [Representation.write_other _ _ _ _ (by intro impossible; cases impossible)]
    exact value

/-- Independent parent fresh overlay links the selected child certificate to
its real root OUTPUT; old/raw missing paths are not assigned default words. -/
theorem fresh_root_postowner : Represented copiedRoot freshRootQueries (.root 1)
    (TargetNestedArrayTransport.afterStore (store 1 0 2) (.root 1) (.root 0)) := by
  have found : copiedRoot.find firstPath = some innerA.strip :=
    NestedCopyObservations.strip_child sourceGraph (freshIndex 0) (by decide)
  have children := Represented.prefix firstPath found firstSupported afterInnerFinal
  intro q member
  simp only [freshRootQueries,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at member
  rcases member with rfl | childMember | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro observed read
    change some (w 1) = some observed at read
    cases read; rfl
  · exact children q childMember
  · refine ⟨by change 1 < lmax ∧ True; decide,True.intro,?_⟩
    intro observed read
    change (none : Option Semantics.Word) = some observed at read
    cases read

private def freshSourceQueries : List (Query graph (.array (.array (.prim .uint)))) :=
  .length .nil :: (PrimitivePop.queries freshIndices).map (Query.prefix firstPath)
private theorem beforeFreshSource : Represented sourceGraph freshSourceQueries (.root 0) (store 1 0 2) := by
  have children := Represented.prefix firstPath (by rfl : sourceGraph.find firstPath = some innerA) firstSupported beforeInnerA
  intro q member
  rcases List.mem_cons.mp member with rfl | childMember
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro observed found; change some (w 1) = some observed at found; cases found; rfl
  · exact children q childMember

/-- WHOLE fresh-root witness applies the actual C65/C66 runtime bridge and
retains BOTH OLD root relations and the independent copied-OUTPUT relation.
This is one inhabited allocation case, not general recursive compiler closure. -/
theorem fresh_root_runtime :
    Represented freshRoot freshRootQueries (.root 1) (store 1 0 2) ∧
    Represented sourceGraph freshSourceQueries (.root 0) (store 1 0 2) ∧
    Evm.run TargetNestedArrayCopy.code { target 1 0 2 with stack := .slot (.root 0) :: .slot (.root 1) :: tail } = .ok (afterTarget 1 0 2) 0 ∧
    Represented copiedRoot freshRootQueries (.root 1) (TargetNestedArrayTransport.afterStore (store 1 0 2) (.root 1) (.root 0)) ∧
    Transport 128 hash locations (TargetNestedArrayTransport.afterStore (store 1 0 2) (.root 1) (.root 0))
      (TargetNestedArrayTransport.execute 128 hash (numeric 1 0 2) (.root 1) (.root 0)) ∧
    (∀ l (member : l ∈ locations), (afterTarget 1 0 2).store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore (store 1 0 2) (.root 1) (.root 0) l)) := by
  have actual : Evm.run TargetNestedArrayCopy.code { target 1 0 2 with stack := .slot (.root 0) :: .slot (.root 1) :: tail } = .ok (afterTarget 1 0 2) 0 ∧
      Transport 128 hash locations (TargetNestedArrayTransport.afterStore (store 1 0 2) (.root 1) (.root 0))
        (TargetNestedArrayTransport.execute 128 hash (numeric 1 0 2) (.root 1) (.root 0)) ∧
      (∀ l (member : l ∈ locations), (afterTarget 1 0 2).store.cells (TargetOperations.toSlot l (fitting l member)) =
        TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore (store 1 0 2) (.root 1) (.root 0) l)) := by
    apply TargetNestedArrayTransport.complete run (.root 1) (.root 0) (by trivial) (by trivial)
      (store 1 0 2) (numeric 1 0 2) (target 1 0 2) tail (initial 1 0 2) fitting (targetInitial 1 0 2) (by decide) (by decide)
    · intro k inside
      change k < 1 at inside
      have same : k = 0 := by omega
      subst k; decide
    · intro k inside j live
      change k < 1 at inside
      have same : k = 0 := by omega
      subst k
      change j < 2 at live
      have casesJ : j = 0 ∨ j = 1 := by omega
      rcases casesJ with rfl | rfl <;> decide
    · intro k inside j visited
      change k < 1 at inside
      have same : k = 0 := by omega
      subst k
      change j < 3 at visited
      have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases casesJ with rfl | rfl | rfl <;> decide
    · intro k inside begun
      change k < 1 at inside
      change 1 ≤ k at begun
      omega
    · intro k inside begun j live
      change k < 1 at inside
      change 1 ≤ k at begun
      omega
  exact ⟨beforeFreshRoot,beforeFreshSource,actual.1,fresh_root_postowner,actual.2.1,actual.2.2⟩

/-- COMPLETE physical BEFORE/INNER/CLEAR/FINAL and symbolic/target/context
observations accompany the independent parent/child Option and word outcomes. -/
theorem fresh_case_ordered :
    (numericView (numeric 1 0 2),numericView innerNumeric,
      numericView (TargetNestedArrayTransport.clearNumerics 128 hash innerNumeric (.root 1) 1 1),
      numericView (TargetNestedArrayTransport.execute 128 hash (numeric 1 0 2) (.root 1) (.root 0)),
      symbolicView innerCopyStore,symbolicView (TargetNestedArrayTransport.afterStore (store 1 0 2) (.root 1) (.root 0)),
      targetView innerTarget,targetView (afterTarget 1 0 2),context innerTarget,context (afterTarget 1 0 2),
      freshRoot.find firstPath,copiedRoot.find firstPath,
      (PrimitivePop.elementQuery (freshIndex 2)).read innerA.strip,
      (PrimitivePop.elementQuery (⟨3,by decide⟩ : Index)).read innerA.strip,(Query.length retainedPath).read copiedRoot,
      (target 1 0 2).store (.data (.root 1) 0),(afterTarget 1 0 2).store (.data (.root 1) 1)) =
      ([w 1,w 0,w 2,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 3,w 23,w 29,w 31,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
       [w 1,w 0,w 2,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 2,w 7,w 11,w 0,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
       [w 1,w 0,w 2,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 2,w 7,w 11,w 0,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
       [w 1,w 1,w 2,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 2,w 7,w 11,w 0,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
       [w 1,w 0,w 2,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 2,w 7,w 11,w 0,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
       [w 1,w 1,w 2,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 2,w 7,w 11,w 0,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
       [1,0,2,7,11,13,1,17,19,1,71,2,7,11,0,37,2,41,43,47,2,53,59,61,73],[1,1,2,7,11,13,1,17,19,1,71,2,7,11,0,37,2,41,43,47,2,53,59,61,73],context (target 1 0 2),context (target 1 0 2),
       none,some innerA.strip,none,none,none,3,2) := by rfl

/-- None implies NEITHER a physical frame NOR zero. Successful source-only
postowner certification never hides the actual extra raw clear of old31. -/
theorem invalid_none_physical_frames :
    ((PrimitivePop.elementQuery (freshIndex 2)).read innerA.strip,
      (PrimitivePop.elementQuery (⟨3,by decide⟩ : Index)).read innerA.strip,
      store 1 0 2 (.data (.data (.root 1) 0) 2),innerCopyStore (.data (.data (.root 1) 0) 2),
      innerCopyStore (.data (.data (.root 1) 0) 3)) = (none,none,w 31,w 0,w 37) ∧
    ¬ (∀ q ∈ PrimitivePop.queries (G := graph) (p := .uint) freshIndices, q.read innerA.strip = none →
      innerCopyStore (q.location (.data (.root 1) 0)) = store 1 0 2 (q.location (.data (.root 1) 0))) ∧
    ¬ (∀ i : Index, (PrimitivePop.elementQuery i).read innerA.strip = none →
      innerCopyStore (.data (.data (.root 1) 0) i.val) = ClearDemands.zero) := by
  refine ⟨rfl,?_,?_⟩
  · intro invalid
    have member : PrimitivePop.elementQuery (G := graph) (p := .uint) (freshIndex 2) ∈ PrimitivePop.queries freshIndices :=
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨freshIndex 2,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),rfl⟩)
    have unchanged := invalid _ member (by rfl)
    change w 0 = w 31 at unchanged
    exact (by decide : w 0 ≠ w 31) unchanged
  · intro invalid
    have zero := invalid ⟨3,by decide⟩ (by rfl)
    change w 37 = w 0 at zero
    exact (by decide : w 37 ≠ w 0) zero

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.fresh_child_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_child_bridge
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.fresh_root_postowner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_root_postowner
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.fresh_root_runtime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_root_runtime
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.fresh_case_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_case_ordered
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.invalid_none_physical_frames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms invalid_none_physical_frames


private def retainedChild : Value graph (.array (.prim .uint)) := .array ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide)
  (fun i => .present (.prim (if i.val = 0 then w 41 else if i.val = 1 then w 43 else w 47)))
private def retainedRoot : Value graph (.array (.array (.prim .uint))) := .array ⟨3,by decide⟩ ⟨1,by decide⟩ (by decide)
  (fun i => if i.val = 1 then .present retainedChild else .absent)
private theorem beforeRetained : Represented retainedChild (PrimitivePop.queries freshIndices) (.data (.root 1) 1) (store 2 1 1) := by
  intro q member
  simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro observed found; change some (w 2) = some observed at found; cases found; rfl
  · refine ⟨by change 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro observed found; change some (w 41) = some observed at found; cases found; rfl
  · refine ⟨by change 1 < lmax ∧ True; decide,True.intro,?_⟩
    intro observed found; change some (w 43) = some observed at found; cases found; rfl
  · refine ⟨by change 2 < lmax ∧ True; decide,True.intro,?_⟩
    intro observed found; change some (w 47) = some observed at found; cases found; rfl

/-- Nonempty actual runtime prefix preserves the retained next child's OLD
owner. The next copy can consume this evidence; no intermediate owner premise. -/
theorem retained_prefix_owner : Represented retainedChild (PrimitivePop.queries freshIndices) (.data (.root 1) 1)
    (TargetNestedArrayTransport.copyStores (store 2 1 1) (.root 1) (.root 0) 1) := by
  refine NestedSnapshotFrames.represented_copy_frame run (.root 1) (.root 0) (by trivial) (by trivial)
    (store 2 1 1) (numeric 2 1 1) (target 2 1 1) 1 (initial 2 1 1) fitting (targetInitial 2 1 1)
    ?_ ?_ ?_ retainedChild (PrimitivePop.queries freshIndices) (.data (.root 1) 1) beforeRetained ?_ ?_
  · intro k inside
    have same : k = 0 := by omega
    subst k; decide
  · intro k inside j live
    have same : k = 0 := by omega
    subst k
    change j < 1 at live
    have same : j = 0 := by omega
    subst j; decide
  · intro k inside j live
    have same : k = 0 := by omega
    subst k
    change j < 3 at live
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with rfl | rfl | rfl <;> decide
  · intro q member
    simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  · intro q member
    simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · change Evm.Slot.data (.root 1) 1 ∉ TargetNestedArrayCopyLoop.touched (target 2 1 1) (.root 0) (.root 1) 1
      decide
    · change Evm.Slot.data (.data (.root 1) 1) 0 ∉ TargetNestedArrayCopyLoop.touched (target 2 1 1) (.root 0) (.root 1) 1
      decide
    · change Evm.Slot.data (.data (.root 1) 1) 1 ∉ TargetNestedArrayCopyLoop.touched (target 2 1 1) (.root 0) (.root 1) 1
      decide
    · change Evm.Slot.data (.data (.root 1) 1) 2 ∉ TargetNestedArrayCopyLoop.touched (target 2 1 1) (.root 0) (.root 1) 1
      decide

/-- COMPLETE prefix observations retain the next child header/live payload and
its older shadow47, while the previous child has changed. -/
theorem retained_prefix_ordered :
    (symbolicView (store 2 1 1),
      symbolicView (TargetNestedArrayTransport.copyStores (store 2 1 1) (.root 1) (.root 0) 1),
      targetView (TargetNestedArrayCopyLoop.prefixMachine (target 2 1 1) (.root 0) (.root 1) 1),
      context (TargetNestedArrayCopyLoop.prefixMachine (target 2 1 1) (.root 0) (.root 1) 1),
      retainedRoot.find retainedPath,retainedPath.readLive Value.dflt retainedRoot) =
    ([w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 3,w 23,w 29,w 31,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
     [2,1,1,7,11,13,1,17,19,1,71,1,7,0,0,37,2,41,43,47,2,53,59,61,73],
     context (target 2 1 1),some retainedChild,none) := by rfl

/-- The exact access guard is discriminating: a visited header is NOT framed,
and absence of that guard would give the false header3=header1 claim. -/
theorem visited_frame_negative :
    Evm.Slot.data (.root 1) 0 ∈ TargetNestedArrayCopyLoop.touched (target 2 1 1) (.root 0) (.root 1) 1 ∧
    TargetNestedArrayTransport.copyStores (store 2 1 1) (.root 1) (.root 0) 1 (.data (.root 1) 0) ≠
      store 2 1 1 (.data (.root 1) 0) := by decide

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.retained_prefix_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms retained_prefix_owner
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.retained_prefix_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms retained_prefix_ordered
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.visited_frame_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms visited_frame_negative


private def retainedIndices : List Index := [freshIndex 0,freshIndex 1]
private def sourceTwo : Value graph (.array (.array (.prim .uint))) := .array ⟨2,by decide⟩ ⟨2,by decide⟩ (by decide)
  (fun i => if i.val = 0 then .present innerA else .present innerB)
private def retainedQueries : List (Query graph (.array (.array (.prim .uint)))) :=
  (PrimitivePop.queries retainedIndices).map (Query.prefix retainedPath)
private theorem beforeRetainedRoot : Represented retainedRoot retainedQueries (.root 1) (store 2 1 1) := by
  apply Represented.prefix retainedPath (by rfl) (by change 1 < lmax ∧ True; decide)
  intro q member
  apply beforeRetained q
  simp only [PrimitivePop.queries,retainedIndices,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
  rcases member with rfl | rfl | rfl <;> simp only [true_or,or_true]
private theorem beforeSourceTwo : Represented sourceTwo retainedQueries (.root 0) (store 2 1 1) := by
  apply Represented.prefix retainedPath (by rfl) (by change 1 < lmax ∧ True; decide)
  intro q member
  simp only [PrimitivePop.queries,retainedIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro observed found; change some (w 1) = some observed at found; cases found; rfl
  · refine ⟨by change 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro observed found; change some (w 17) = some observed at found; cases found; rfl
  · refine ⟨by change 1 < lmax ∧ True; decide,True.intro,?_⟩
    intro observed found; change some (w 19) = some observed at found; cases found; rfl

/-- APPLY the general retained snapshot theorem after a changed nonempty
prefix; both CURRENT child owners are derived from OLD root observations. -/
theorem retained_copied_root :
    Represented (retainedRoot.overlay sourceTwo) retainedQueries (.root 1)
      (TargetNestedArrayTransport.copyStores (store 2 1 1) (.root 1) (.root 0) 2) ∧
    Transport 128 hash locations (TargetNestedArrayTransport.copyStores (store 2 1 1) (.root 1) (.root 0) 2)
      (TargetNestedArrayTransport.copyNumerics 128 hash (numeric 2 1 1) (.root 1) (.root 0) 2) ∧
    (∀ l (member : l ∈ locations),
      (TargetNestedArrayCopyLoop.prefixMachine (target 2 1 1) (.root 0) (.root 1) 2).store.cells
        (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (TargetNestedArrayTransport.copyStores (store 2 1 1) (.root 1) (.root 0) 2 l)) := by
  refine NestedRetainedCopy.copied_child run retainedRoot sourceTwo (freshIndex 1) retainedIndices (by decide) (by decide)
    (.root 1) (.root 0) (by trivial) (by trivial) (store 2 1 1) (numeric 2 1 1) (target 2 1 1)
    (initial 2 1 1) fitting (targetInitial 2 1 1) beforeRetainedRoot beforeSourceTwo ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k inside
    change k < 2 at inside
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl <;> decide
  · exact forall_bounded_pair (by decide)
  · exact forall_bounded_pair (by decide)
  · intro j member
    simp only [retainedIndices,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> decide
  · intro j member
    simp only [retainedIndices,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> decide
  · intro j live
    change j < 1 at live
    have same : j = 0 := by omega
    subst j; decide
  · intro j live
    change j < 2 at live
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with rfl | rfl <;> decide
  · intro q member
    simp only [PrimitivePop.queries,retainedIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · change Evm.Slot.data (.root 1) 1 ∉ TargetNestedArrayCopyLoop.touched (target 2 1 1) (.root 0) (.root 1) 1
      decide
    · change Evm.Slot.data (.data (.root 1) 1) 0 ∉ TargetNestedArrayCopyLoop.touched (target 2 1 1) (.root 0) (.root 1) 1
      decide
    · change Evm.Slot.data (.data (.root 1) 1) 1 ∉ TargetNestedArrayCopyLoop.touched (target 2 1 1) (.root 0) (.root 1) 1
      decide
  · intro q member
    simp only [PrimitivePop.queries,retainedIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · change Evm.Slot.data (.root 0) 1 ∉ TargetNestedArrayCopyLoop.touched (target 2 1 1) (.root 0) (.root 1) 1
      decide
    · change Evm.Slot.data (.data (.root 0) 1) 0 ∉ TargetNestedArrayCopyLoop.touched (target 2 1 1) (.root 0) (.root 1) 1
      decide
    · change Evm.Slot.data (.data (.root 0) 1) 1 ∉ TargetNestedArrayCopyLoop.touched (target 2 1 1) (.root 0) (.root 1) 1
      decide

/-- COMPLETE two-prefix symbolic/numeric/target/context observations preserve
older47 while replacing live41->17 and stale43->0, and retain extent3. -/
theorem retained_copy_ordered :
    (symbolicView (TargetNestedArrayTransport.copyStores (store 2 1 1) (.root 1) (.root 0) 2),
      numericView (TargetNestedArrayTransport.copyNumerics 128 hash (numeric 2 1 1) (.root 1) (.root 0) 2),
      targetView (TargetNestedArrayCopyLoop.prefixMachine (target 2 1 1) (.root 0) (.root 1) 2),
      context (TargetNestedArrayCopyLoop.prefixMachine (target 2 1 1) (.root 0) (.root 1) 2),
      (NestedCopyObservations.child (retainedRoot.overlay sourceTwo) (freshIndex 1)).extent.val,
      (PrimitivePop.elementQuery (freshIndex 0)).read (retainedChild.overlay innerB),
      (PrimitivePop.elementQuery (freshIndex 1)).read (retainedChild.overlay innerB),
      (PrimitivePop.elementQuery (freshIndex 2)).read (retainedChild.overlay innerB)) =
    ([w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
     [2,1,1,7,11,13,1,17,19,1,71,1,7,0,0,37,1,17,0,47,2,53,59,61,73],
     context (target 2 1 1),3,some (w 17),some (w 0),some (w 47)) := by rfl

/-- Substituting fresh strip is wrong: the retained shadow is a successful
read after overlay but None in strip, even though both live headers are1. -/
theorem retained_strip_negative :
    (PrimitivePop.elementQuery (freshIndex 2)).read (retainedChild.overlay innerB) = some (w 47) ∧
    (PrimitivePop.elementQuery (freshIndex 2)).read innerB.strip = none ∧
    retainedChild.overlay innerB ≠ innerB.strip := by
  refine ⟨rfl,rfl,?_⟩
  intro same
  have observed := congrArg (fun v => (PrimitivePop.elementQuery (freshIndex 2)).read v) same
  change some (w 47) = none at observed
  cases observed

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.retained_copied_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms retained_copied_root
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.retained_copy_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms retained_copy_ordered
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.retained_strip_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms retained_strip_negative

private theorem shrinkingSource : Represented innerA (PrimitivePop.queries freshIndices) (.data (.root 0) 0) (store 1 2 2) := by
  intro q member
  simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro observed found; change some (w 2) = some observed at found; cases found; rfl
  · refine ⟨by change 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro observed found; change some (w 7) = some observed at found; cases found; rfl
  · refine ⟨by change 1 < lmax ∧ True; decide,True.intro,?_⟩
    intro observed found; change some (w 11) = some observed at found; cases found; rfl
  · refine ⟨by change 2 < lmax ∧ True; decide,True.intro,?_⟩
    intro observed found; change some (w 13) = some observed at found; cases found; rfl

/-- Actual nonempty stale clearing and final header write preserve the selected
independent copied child output. No destination-default header is inferred. -/
theorem shrinking_copied_owner : Represented innerA.strip (PrimitivePop.queries freshIndices) (.data (.root 1) 0)
    (TargetNestedArrayTransport.afterStore (store 1 2 2) (.root 1) (.root 0)) := by
  have copied := NestedCopyObservations.strip_postowner run innerA freshIndices (.data (.root 1) 0) (.data (.root 0) 0)
    (store 1 2 2) (numeric 1 2 2) shrinkingSource (initial 1 2 2) (by decide) (by decide)
    (by intro i member; simp only [freshIndices,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl <;> decide)
    (by intro i member; simp only [freshIndices,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl <;> decide)
    (by intro j live; change j < 2 at live
        have casesJ : j = 0 ∨ j = 1 := by omega
        rcases casesJ with rfl | rfl <;> decide)
    (by intro j live; change j < 3 at live
        have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
        rcases casesJ with rfl | rfl | rfl <;> decide)
  have copiedPrefix := TargetNestedArrayTransport.copy_prefix run (.root 1) (.root 0) (by trivial) (by trivial)
    (store 1 2 2) (numeric 1 2 2) (target 1 2 2) 1 (initial 1 2 2) fitting (targetInitial 1 2 2)
    (by intro k live; have same : k = 0 := by omega
        subst k; decide)
    (by intro k live j bound; have same : k = 0 := by omega
        subst k; change j < 2 at bound
        have casesJ : j = 0 ∨ j = 1 := by omega
        rcases casesJ with rfl | rfl <;> decide)
    (by intro k live j bound; have same : k = 0 := by omega
        subst k; change j < 3 at bound
        have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
        rcases casesJ with rfl | rfl | rfl <;> decide)
  change Represented innerA.strip (PrimitivePop.queries freshIndices) (.data (.root 1) 0)
    (Representation.write (TargetNestedArrayTransport.clearStores
      (TargetNestedArrayTransport.copyStores (store 1 2 2) (.root 1) (.root 0) 1) (.root 1) 1 2) (.root 1) (store 1 2 2 (.root 0)))
  apply NestedClearFrames.header_child_owner
  refine NestedClearFrames.clear_child_owner run (.root 1) (by trivial)
    (TargetNestedArrayTransport.copyStores (store 1 2 2) (.root 1) (.root 0) 1)
    (TargetNestedArrayTransport.copyNumerics 128 hash (numeric 1 2 2) (.root 1) (.root 0) 1)
    (TargetNestedArrayCopyLoop.prefixMachine (target 1 2 2) (.root 0) (.root 1) 1) 1 2 copiedPrefix.1 fitting copiedPrefix.2
    ?_ ?_ innerA.strip freshIndices 0 (Or.inl (by decide)) copied.1 ?_
  · intro k live begun
    have same : k = 1 := by omega
    subst k; decide
  · intro k live begun j bound
    have same : k = 1 := by omega
    subst k
    change j < 2 at bound
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with rfl | rfl <;> decide
  · intro q member
    simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide

/-- COMPLETE unchanged shrinking fixture plus new independent-output link.
Stale child1 is cleared, copied child0 and older children/shadows are retained. -/
theorem shrinking_clear_output :
    Represented innerA.strip (PrimitivePop.queries freshIndices) (.data (.root 1) 0)
      (TargetNestedArrayTransport.afterStore (store 1 2 2) (.root 1) (.root 0)) ∧
    Evm.run TargetNestedArrayCopy.code { target 1 2 2 with stack := .slot (.root 0) :: .slot (.root 1) :: tail } = .ok (afterTarget 1 2 2) 0 ∧
    (symbolicView (TargetNestedArrayTransport.copyStores (store 1 2 2) (.root 1) (.root 0) 1),
      symbolicView (TargetNestedArrayTransport.clearStores (TargetNestedArrayTransport.copyStores (store 1 2 2) (.root 1) (.root 0) 1) (.root 1) 1 2),
      symbolicView (TargetNestedArrayTransport.afterStore (store 1 2 2) (.root 1) (.root 0)),
      targetView (afterTarget 1 2 2),context (afterTarget 1 2 2),
      (PrimitivePop.elementQuery (freshIndex 0)).read innerA.strip,
      (PrimitivePop.elementQuery (freshIndex 1)).read innerA.strip,
      (PrimitivePop.elementQuery (freshIndex 2)).read innerA.strip) =
    ([w 1,w 2,w 2,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 2,w 7,w 11,w 0,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 1,w 2,w 2,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 2,w 7,w 11,w 0,w 37,w 0,w 0,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 1,w 1,w 2,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 2,w 7,w 11,w 0,w 37,w 0,w 0,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
     [1,1,2,7,11,13,1,17,19,1,71,2,7,11,0,37,0,0,0,47,2,53,59,61,73],context (target 1 2 2),some (w 7),some (w 11),none) := by
  exact ⟨shrinking_copied_owner,shrinking_bridge.2.2.1,rfl⟩

/-- A misplaced final outer-header write into the live child's header breaks
its represented output, despite otherwise correct traversal. -/
theorem wrong_header_negative : ¬ Represented innerA.strip (PrimitivePop.queries freshIndices) (.data (.root 1) 0)
    (Representation.write (TargetNestedArrayTransport.afterStore (store 1 2 2) (.root 1) (.root 0)) (.data (.root 1) 0) (w 1)) := by
  intro bad
  have observed := (bad (.length .nil) List.mem_cons_self).2.2 (w 2) (by rfl)
  change w 1 = w 2 at observed
  have unequal : w 1 ≠ w 2 := by decide
  exact unequal observed

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.shrinking_copied_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shrinking_copied_owner
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.shrinking_clear_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shrinking_clear_output
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.wrong_header_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_header_negative


private def firstRetained : Value graph (.array (.prim .uint)) := .array ⟨4,by decide⟩ ⟨3,by decide⟩ (by decide)
  (fun i => .present (.prim (if i.val = 0 then w 23 else if i.val = 1 then w 29 else if i.val = 2 then w 31 else w 37)))
private def firstSource : Value graph (.array (.prim .uint)) := .array ⟨3,by decide⟩ ⟨1,by decide⟩ (by decide)
  (fun i => .present (.prim (if i.val = 0 then w 7 else if i.val = 1 then w 11 else w 13)))
private theorem beforeFirstRetained : Represented firstRetained (PrimitivePop.queries freshIndices) (.data (.root 1) 0) (store 2 1 1) := by
  intro q member
  simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 3) = some word at found; cases found; rfl
  · refine ⟨by change 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 23) = some word at found; cases found; rfl
  · refine ⟨by change 1 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 29) = some word at found; cases found; rfl
  · refine ⟨by change 2 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 31) = some word at found; cases found; rfl
private theorem beforeFirstSource : Represented firstSource (PrimitivePop.queries freshIndices) (.data (.root 0) 0) (store 2 1 1) := by
  intro q member
  simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 1) = some word at found; cases found; rfl
  · refine ⟨by change 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 7) = some word at found; cases found; rfl
  · refine ⟨by change 1 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 11) = some word at found; cases found; rfl
  · refine ⟨by change 2 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 13) = some word at found; cases found; rfl
private theorem firstCopied : Represented (firstRetained.overlay firstSource) (PrimitivePop.queries freshIndices) (.data (.root 1) 0)
    (TargetNestedArrayTransport.copyStores (store 2 1 1) (.root 1) (.root 0) 1) := by
  have copied := CopyTransport.complete run firstRetained firstSource freshIndices (.data (.root 1) 0) (.data (.root 0) 0)
    (store 2 1 1) (numeric 2 1 1) beforeFirstRetained beforeFirstSource (initial 2 1 1) (by decide) (by decide)
    (by intro i member; simp only [freshIndices,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl <;> decide)
    (by intro i member; simp only [freshIndices,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl <;> decide)
    (by intro j live; change j < 1 at live
        have same : j = 0 := by omega
        subst j; decide)
    (by intro j live; change j < 3 at live
        have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
        rcases casesJ with rfl | rfl | rfl <;> decide)
  simpa only [recursiveCopy_eq_overlay,TargetNestedArrayTransport.copyStores] using copied.2

/-- APPLY the interval certificate to independently derived changed child0
output, while the later actual child1 copy also changes stored values. -/
theorem later_copied_owner : Represented (firstRetained.overlay firstSource) (PrimitivePop.queries freshIndices) (.data (.root 1) 0)
    (TargetNestedArrayTransport.copyStores (store 2 1 1) (.root 1) (.root 0) 2) := by
  refine NestedLaterFrames.owner_interval run (.root 1) (.root 0) (by trivial) (by trivial)
    (store 2 1 1) (numeric 2 1 1) (target 2 1 1) 1 1 0 (initial 2 1 1) fitting (targetInitial 2 1 1)
    ?_ ?_ ?_ (firstRetained.overlay firstSource) freshIndices (by decide) firstCopied ?_
  · intro k inside
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl <;> decide
  · intro k inside j live
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl <;> change j < 1 at live
    all_goals have same : j = 0 := by omega
    all_goals subst j; decide
  · intro k inside j live
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl
    · change j < 3 at live
      have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases casesJ with rfl | rfl | rfl <;> decide
    · change j < 2 at live
      have casesJ : j = 0 ∨ j = 1 := by omega
      rcases casesJ with rfl | rfl <;> decide
  · intro q member
    simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide

/-- This growing run has no active stale suffix; the actual header-last phase
then preserves the already-copied independent retained output. -/
theorem later_finished_owner : Represented (firstRetained.overlay firstSource) (PrimitivePop.queries freshIndices) (.data (.root 1) 0)
    (TargetNestedArrayTransport.afterStore (store 2 1 1) (.root 1) (.root 0)) := by
  change Represented (firstRetained.overlay firstSource) (PrimitivePop.queries freshIndices) (.data (.root 1) 0)
    (Representation.write (TargetNestedArrayTransport.copyStores (store 2 1 1) (.root 1) (.root 0) 2) (.root 1) (store 2 1 1 (.root 0)))
  exact NestedClearFrames.header_child_owner _ _ _ _ _ _ later_copied_owner

/-- COMPLETE observations connect OLD, first-copy, later-copy, header-last,
numeric execution and actual target. Both independent overlay tails survive. -/
theorem later_output_ordered :
    (symbolicView (store 2 1 1),
      symbolicView (TargetNestedArrayTransport.copyStores (store 2 1 1) (.root 1) (.root 0) 1),
      symbolicView (TargetNestedArrayTransport.copyStores (store 2 1 1) (.root 1) (.root 0) 2),
      symbolicView (TargetNestedArrayTransport.afterStore (store 2 1 1) (.root 1) (.root 0)),
      numericView (TargetNestedArrayTransport.execute 128 hash (numeric 2 1 1) (.root 1) (.root 0)),
      targetView (afterTarget 2 1 1),context (afterTarget 2 1 1),
      (firstRetained.overlay firstSource).extent.val,
      (PrimitivePop.elementQuery (freshIndex 0)).read (firstRetained.overlay firstSource),
      (PrimitivePop.elementQuery (freshIndex 1)).read (firstRetained.overlay firstSource),
      (PrimitivePop.elementQuery (freshIndex 2)).read (firstRetained.overlay firstSource)) =
    ([w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 3,w 23,w 29,w 31,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],[w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],[w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],[w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],[w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],[2,2,1,7,11,13,1,17,19,1,71,1,7,0,0,37,1,17,0,47,2,53,59,61,73],
      context (target 2 1 1),4,some (w 7),some (w 0),some (w 0)) := by rfl

/-- Without earlier<first the future child changes; the already-processed
child also differs from OLD, so an initial-to-final frame would be false. -/
theorem future_frame_negative :
    (TargetNestedArrayCopyLoop.prefixMachine (target 2 1 1) (.root 0) (.root 1) 2).store (.data (.root 1) 1) ≠
      (TargetNestedArrayCopyLoop.prefixMachine (target 2 1 1) (.root 0) (.root 1) 1).store (.data (.root 1) 1) ∧
    (TargetNestedArrayCopyLoop.prefixMachine (target 2 1 1) (.root 0) (.root 1) 2).store (.data (.root 1) 0) ≠
      (target 2 1 1).store (.data (.root 1) 0) := by decide

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.later_copied_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms later_copied_owner
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.later_finished_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms later_finished_owner
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.later_output_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms later_output_ordered
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.future_frame_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms future_frame_negative


private def bothStore : Store := Representation.write (store 2 1 1) (.root 1) (w 3)
private def bothNumeric : WordStore := writeWord (numeric 2 1 1) ((Solidity.Storage.Loc.root 1).word 128 hash) (w 3)
private def bothTarget : Evm.Machine := { target 2 1 1 with store := Evm.WordStore.write (target 2 1 1).store (.root 1) (TargetOperations.encodeWord (w 3)).val }
private def bothAfter := TargetNestedArrayRuntime.afterCopy bothTarget tail (.root 0) (.root 1)
private theorem bothInitial : Transport 128 hash locations bothStore bothNumeric :=
  transport_write run (initial 2 1 1) (.root 1) (by decide) (w 3)
private theorem bothTargetInitial : ∀ l (member : l ∈ locations),
    bothTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (bothStore l) :=
  TargetOperations.write_agreement locations fitting (.root 1) (by trivial) (w 3) (store 2 1 1) (target 2 1 1) (targetInitial 2 1 1)
private theorem beforeBothRetained : Represented firstRetained (PrimitivePop.queries freshIndices) (.data (.root 1) 0) bothStore := by
  intro q member
  simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 3) = some word at found; cases found; rfl
  · refine ⟨by change 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 23) = some word at found; cases found; rfl
  · refine ⟨by change 1 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 29) = some word at found; cases found; rfl
  · refine ⟨by change 2 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 31) = some word at found; cases found; rfl
private theorem beforeBothSource : Represented firstSource (PrimitivePop.queries freshIndices) (.data (.root 0) 0) bothStore := by
  intro q member
  simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 1) = some word at found; cases found; rfl
  · refine ⟨by change 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 7) = some word at found; cases found; rfl
  · refine ⟨by change 1 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 11) = some word at found; cases found; rfl
  · refine ⟨by change 2 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 13) = some word at found; cases found; rfl
private theorem bothFirstCopied : Represented (firstRetained.overlay firstSource) (PrimitivePop.queries freshIndices) (.data (.root 1) 0)
    (TargetNestedArrayTransport.copyStores bothStore (.root 1) (.root 0) 1) := by
  have copied := CopyTransport.complete run firstRetained firstSource freshIndices (.data (.root 1) 0) (.data (.root 0) 0)
    bothStore bothNumeric beforeBothRetained beforeBothSource bothInitial (by decide) (by decide)
    (by intro i member; simp only [freshIndices,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl <;> decide)
    (by intro i member; simp only [freshIndices,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl <;> decide)
    (by intro j live; change j < 1 at live
        have same : j = 0 := by omega
        subst j; decide)
    (by intro j live; change j < 3 at live
        have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
        rcases casesJ with rfl | rfl | rfl <;> decide)
  simpa only [recursiveCopy_eq_overlay,TargetNestedArrayTransport.copyStores] using copied.2


/-- A single instantiated certificate performs TWO changed copies, THEN a
NONEMPTY stale clear, THEN header-last; no first-prefix postowner oracle. -/
theorem both_phase_bridge :
    Evm.run TargetNestedArrayCopy.code { bothTarget with stack := .slot (.root 0) :: .slot (.root 1) :: tail } = .ok bothAfter 0 ∧
    Represented (firstRetained.overlay firstSource) (PrimitivePop.queries freshIndices) (.data (.root 1) 0)
      (TargetNestedArrayTransport.afterStore bothStore (.root 1) (.root 0)) ∧
    Transport 128 hash locations (TargetNestedArrayTransport.afterStore bothStore (.root 1) (.root 0))
      (TargetNestedArrayTransport.execute 128 hash bothNumeric (.root 1) (.root 0)) ∧
    (∀ l (member : l ∈ locations), bothAfter.store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore bothStore (.root 1) (.root 0) l)) := by
  refine NestedPhaseComposition.finish_child run (.root 1) (.root 0) (by trivial) (by trivial)
    bothStore bothNumeric bothTarget tail bothInitial fitting bothTargetInitial (by decide) (by decide)
    ?_ ?_ ?_ ?_ ?_ (firstRetained.overlay firstSource) freshIndices 1 0 (by decide) (by decide) bothFirstCopied ?_
  · intro k inside
    change k < 2 at inside
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl <;> decide
  · exact forall_bounded_pair (by decide)
  · exact forall_bounded_pair (by decide)
  · intro k inside begun
    change k < 3 at inside
    change 2 ≤ k at begun
    have same : k = 2 := by omega
    subst k; decide
  · intro k inside begun j live
    change k < 3 at inside
    change 2 ≤ k at begun
    have same : k = 2 := by omega
    subst k
    change j < 2 at live
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with rfl | rfl <;> decide
  · intro q member
    simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide

/-- COMPLETE ordered observations: first child changes, later child changes,
stale child2 clears only its live words; all older shadows/context remain. -/
theorem both_phase_ordered :
    (symbolicView bothStore,
      symbolicView (TargetNestedArrayTransport.copyStores bothStore (.root 1) (.root 0) 1),
      symbolicView (TargetNestedArrayTransport.copyStores bothStore (.root 1) (.root 0) 2),
      symbolicView (TargetNestedArrayTransport.clearStores (TargetNestedArrayTransport.copyStores bothStore (.root 1) (.root 0) 2) (.root 1) 2 3),
      symbolicView (TargetNestedArrayTransport.afterStore bothStore (.root 1) (.root 0)),
      numericView (TargetNestedArrayTransport.execute 128 hash bothNumeric (.root 1) (.root 0)),
      targetView bothAfter,context bothAfter,
      (firstRetained.overlay firstSource).extent.val,
      (PrimitivePop.elementQuery (freshIndex 0)).read (firstRetained.overlay firstSource),
      (PrimitivePop.elementQuery (freshIndex 1)).read (firstRetained.overlay firstSource),
      (PrimitivePop.elementQuery (freshIndex 2)).read (firstRetained.overlay firstSource)) =
    ([w 2,w 3,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 3,w 23,w 29,w 31,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],[w 2,w 3,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],[w 2,w 3,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],[w 2,w 3,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 0,w 0,w 0,w 61,w 73],[w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 0,w 0,w 0,w 61,w 73],[w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 0,w 0,w 0,w 61,w 73],[2,2,1,7,11,13,1,17,19,1,71,1,7,0,0,37,1,17,0,47,0,0,0,61,73],
      context bothTarget,4,some (w 7),some (w 0),some (w 0)) := by rfl

/-- Re-clearing the newly live prefix destroys the proved independent output;
correct stale-tail clearing starts at the captured NEW outer length2. -/
theorem repeated_live_clear_negative : ¬ Represented (firstRetained.overlay firstSource)
    (PrimitivePop.queries freshIndices) (.data (.root 1) 0)
    (Representation.write (TargetNestedArrayTransport.clearStores
      (TargetNestedArrayTransport.copyStores bothStore (.root 1) (.root 0) 2) (.root 1) 0 3) (.root 1) (w 2)) := by
  intro bad
  have observed := (bad (.length .nil) List.mem_cons_self).2.2 (w 1) (by rfl)
  change w 0 = w 1 at observed
  have unequal : w 0 ≠ w 1 := by decide
  exact unequal observed

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.both_phase_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms both_phase_bridge
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.both_phase_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms both_phase_ordered
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.repeated_live_clear_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms repeated_live_clear_negative


private def staleChild : Value graph (.array (.prim .uint)) := .array ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide)
  (fun i => .present (.prim (if i.val = 0 then w 53 else if i.val = 1 then w 59 else w 61)))
private def sourceOlderChild : Value graph (.array (.prim .uint)) := .array ⟨1,by decide⟩ ⟨1,by decide⟩ (by decide)
  (fun _ => .present (.prim (w 71)))
private def bothOldRoot : Value graph (.array (.array (.prim .uint))) := .array ⟨3,by decide⟩ ⟨3,by decide⟩ (by decide)
  (fun i => if i.val = 0 then .present firstRetained else if i.val = 1 then .present retainedChild else .present staleChild)
private def bothSourceRoot : Value graph (.array (.array (.prim .uint))) := .array ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide)
  (fun i => if i.val = 0 then .present firstSource else if i.val = 1 then .present innerB else .present sourceOlderChild)
private def rootChildren : List Index := [freshIndex 0,freshIndex 1]
private def rootIndices (_ : Index) : List Index := retainedIndices
private def selectedRootQueries : List (Query graph (.array (.array (.prim .uint)))) := NestedRootComposition.rootQueries rootChildren rootIndices
private theorem beforeBothOldRoot : Represented bothOldRoot selectedRootQueries (.root 1) bothStore := by
  intro q member
  simp only [selectedRootQueries,NestedRootComposition.rootQueries,rootChildren,rootIndices,PrimitivePop.queries,retainedIndices,
    List.flatMap_cons,List.flatMap_nil,List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | (rfl | rfl | rfl) | (rfl | rfl | rfl)
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 3) = some word at found; cases found; rfl
  · refine ⟨by change 0 < lmax ∧ True; decide,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 3) = some word at found; cases found; rfl
  · refine ⟨by change 0 < lmax ∧ 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 23) = some word at found; cases found; rfl
  · refine ⟨by change 0 < lmax ∧ 1 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 29) = some word at found; cases found; rfl
  · refine ⟨by change 1 < lmax ∧ True; decide,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 2) = some word at found; cases found; rfl
  · refine ⟨by change 1 < lmax ∧ 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 41) = some word at found; cases found; rfl
  · refine ⟨by change 1 < lmax ∧ 1 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 43) = some word at found; cases found; rfl
private theorem beforeBothSourceRoot : Represented bothSourceRoot selectedRootQueries (.root 0) bothStore := by
  intro q member
  simp only [selectedRootQueries,NestedRootComposition.rootQueries,rootChildren,rootIndices,PrimitivePop.queries,retainedIndices,
    List.flatMap_cons,List.flatMap_nil,List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | (rfl | rfl | rfl) | (rfl | rfl | rfl)
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 2) = some word at found; cases found; rfl
  · refine ⟨by change 0 < lmax ∧ True; decide,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 1) = some word at found; cases found; rfl
  · refine ⟨by change 0 < lmax ∧ 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 7) = some word at found; cases found; rfl
  · refine ⟨by change 0 < lmax ∧ 1 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 11) = some word at found; cases found; rfl
  · refine ⟨by change 1 < lmax ∧ True; decide,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 1) = some word at found; cases found; rfl
  · refine ⟨by change 1 < lmax ∧ 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 17) = some word at found; cases found; rfl
  · refine ⟨by change 1 < lmax ∧ 1 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 19) = some word at found; cases found; rfl

/-- APPLY the full selected ROOT union to BOTH old root representations.
No per-child prefix/postowner is an input: all are derived by the generic law. -/
theorem selected_root_bridge :
    Evm.run TargetNestedArrayCopy.code { bothTarget with stack := .slot (.root 0) :: .slot (.root 1) :: tail } = .ok bothAfter 0 ∧
    Represented (bothOldRoot.overlay bothSourceRoot) selectedRootQueries (.root 1)
      (TargetNestedArrayTransport.afterStore bothStore (.root 1) (.root 0)) ∧
    Transport 128 hash locations (TargetNestedArrayTransport.afterStore bothStore (.root 1) (.root 0))
      (TargetNestedArrayTransport.execute 128 hash bothNumeric (.root 1) (.root 0)) ∧
    (∀ l (member : l ∈ locations), bothAfter.store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore bothStore (.root 1) (.root 0) l)) := by
  refine NestedRootComposition.live_root run bothOldRoot bothSourceRoot rootChildren rootIndices ?_
    (.root 1) (.root 0) (by trivial) (by trivial) bothStore bothNumeric bothTarget tail bothInitial fitting bothTargetInitial
    beforeBothOldRoot beforeBothSourceRoot (by decide) (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i member
    simp only [rootChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> decide
  · intro k inside
    change k < 2 at inside
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl <;> decide
  · exact forall_bounded_pair (by decide)
  · exact forall_bounded_pair (by decide)
  · intro k inside begun
    change k < 3 at inside
    change 2 ≤ k at begun
    have same : k = 2 := by omega
    subst k; decide
  · intro k inside begun j live
    change k < 3 at inside
    change 2 ≤ k at begun
    have same : k = 2 := by omega
    subst k
    change j < 2 at live
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with rfl | rfl <;> decide
  · intro i member j inside
    simp only [rootChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    simp only [rootIndices,retainedIndices,List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases member with rfl | rfl <;> rcases inside with rfl | rfl <;> decide
  · intro i member j inside
    simp only [rootChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    simp only [rootIndices,retainedIndices,List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases member with rfl | rfl <;> rcases inside with rfl | rfl <;> decide
  · intro i member j live
    simp only [rootChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> change j < 1 at live
    all_goals have same : j = 0 := by omega
    all_goals subst j; decide
  · intro i member j live
    simp only [rootChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · change j < 3 at live
      have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases casesJ with rfl | rfl | rfl <;> decide
    · change j < 2 at live
      have casesJ : j = 0 ∨ j = 1 := by omega
      rcases casesJ with rfl | rfl <;> decide
  · intro i member q observation
    simp only [rootChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    simp only [rootIndices,PrimitivePop.queries,retainedIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at observation
    rcases member with rfl | rfl
    · rcases observation with rfl | rfl | rfl <;> exact List.not_mem_nil
    · rcases observation with rfl | rfl | rfl
      · change Evm.Slot.data (.root 1) 1 ∉ TargetNestedArrayCopyLoop.touched bothTarget (.root 0) (.root 1) 1
        decide
      · change Evm.Slot.data (.data (.root 1) 1) 0 ∉ TargetNestedArrayCopyLoop.touched bothTarget (.root 0) (.root 1) 1
        decide
      · change Evm.Slot.data (.data (.root 1) 1) 1 ∉ TargetNestedArrayCopyLoop.touched bothTarget (.root 0) (.root 1) 1
        decide
  · intro i member q observation
    simp only [rootChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    simp only [rootIndices,PrimitivePop.queries,retainedIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at observation
    rcases member with rfl | rfl
    · rcases observation with rfl | rfl | rfl <;> exact List.not_mem_nil
    · rcases observation with rfl | rfl | rfl
      · change Evm.Slot.data (.root 0) 1 ∉ TargetNestedArrayCopyLoop.touched bothTarget (.root 0) (.root 1) 1
        decide
      · change Evm.Slot.data (.data (.root 0) 1) 0 ∉ TargetNestedArrayCopyLoop.touched bothTarget (.root 0) (.root 1) 1
        decide
      · change Evm.Slot.data (.data (.root 0) 1) 1 ∉ TargetNestedArrayCopyLoop.touched bothTarget (.root 0) (.root 1) 1
        decide

/-- COMPLETE physical output and all selected independent ROOT observations.
Separate stale/older graph reads are recorded without extending the owner list. -/
theorem selected_root_observations :
    (symbolicView bothStore,symbolicView (TargetNestedArrayTransport.afterStore bothStore (.root 1) (.root 0)),
      numericView (TargetNestedArrayTransport.execute 128 hash bothNumeric (.root 1) (.root 0)),
      targetView bothAfter,context bothAfter,
      selectedRootQueries.map (fun q => q.read (bothOldRoot.overlay bothSourceRoot)),
      (Query.length missingPath).read (bothOldRoot.overlay bothSourceRoot),
      missingPath.readLive Value.dflt (bothOldRoot.overlay bothSourceRoot)) =
    ([w 2,w 3,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 3,w 23,w 29,w 31,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],[w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 0,w 0,w 0,w 61,w 73],[w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 0,w 0,w 0,w 61,w 73],[2,2,1,7,11,13,1,17,19,1,71,1,7,0,0,37,1,17,0,47,0,0,0,61,73],context bothTarget,
      [some (w 2),some (w 1),some (w 7),some (w 0),some (w 1),some (w 17),some (w 0)],some (w 0),none) := by rfl

/-- Correct outer header alone cannot rescue an incorrectly re-cleared live
child: the selected ROOT certificate detects the wrong child header. -/
theorem selected_root_wrong_clear : ¬ Represented (bothOldRoot.overlay bothSourceRoot) selectedRootQueries (.root 1)
    (Representation.write (TargetNestedArrayTransport.clearStores
      (TargetNestedArrayTransport.copyStores bothStore (.root 1) (.root 0) 2) (.root 1) 0 3) (.root 1) (w 2)) := by
  intro bad
  have member : Query.length firstPath ∈ selectedRootQueries := by
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨freshIndex 0,by simp only [rootChildren,List.mem_cons,true_or],
      List.mem_map.mpr ⟨Query.length .nil,List.mem_cons_self,rfl⟩⟩)
  have observed := (bad (.length firstPath) member).2.2 (w 1) (by rfl)
  change w 0 = w 1 at observed
  have unequal : w 0 ≠ w 1 := by decide
  exact unequal observed

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.selected_root_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms selected_root_bridge
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.selected_root_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms selected_root_observations
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.selected_root_wrong_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms selected_root_wrong_clear


private def shadowIndex : Index := ⟨3,by decide⟩
private def accessIndices : List Index := [freshIndex 0,freshIndex 1,freshIndex 2,shadowIndex]
private def accessSourceLocation : Solidity.Storage.Loc := .data (.data (.root 0) 0) 3
private def accessStore : Store := Representation.write (store 2 1 1) accessSourceLocation (w 83)
private def accessNumeric : WordStore := writeWord (numeric 2 1 1) (accessSourceLocation.word 128 hash) (w 83)
private def accessTarget : Evm.Machine := { target 2 1 1 with store := .ofFn (fun slot => (TargetOperations.encodeWord (accessStore (Solidity.Storage.ofSlot slot))).val) }
private def accessAfter := TargetArrayCopyTail.afterCopy accessTarget tail (.data (.root 0) 0) (.data (.root 1) 0)
private def accessAfterStore := CopyTransport.symbolicCopy (.data (.root 1) 0) (.data (.root 0) 0) accessStore
private def accessAfterNumeric := NumericTraversal.copy 128 hash (.data (.root 1) 0) (.data (.root 0) 0) accessNumeric
private theorem accessInitial : Transport 128 hash locations accessStore accessNumeric := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem accessTargetInitial : ∀ l (member : l ∈ locations),
    accessTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (accessStore l) := by
  intro l member
  change Evm.wmod (TargetOperations.encodeWord (accessStore (Solidity.Storage.ofSlot (TargetOperations.toSlot l (fitting l member))))).val = _
  rw [TargetOperations.ofSlot_toSlot,Evm.wmod_of_lt (TargetOperations.encodeWord (accessStore l)).isLt]
private theorem accessBeforeDst : Represented firstRetained (PrimitivePop.queries accessIndices) (.data (.root 1) 0) accessStore := by
  intro q member
  simp only [PrimitivePop.queries,accessIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 3) = some word at found; cases found; rfl
  · refine ⟨by change 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 23) = some word at found; cases found; rfl
  · refine ⟨by change 1 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 29) = some word at found; cases found; rfl
  · refine ⟨by change 2 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 31) = some word at found; cases found; rfl
  · refine ⟨by change 3 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 37) = some word at found; cases found; rfl
private theorem accessBeforeSrc : Represented firstSource (PrimitivePop.queries accessIndices) (.data (.root 0) 0) accessStore := by
  intro q member
  simp only [PrimitivePop.queries,accessIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 1) = some word at found; cases found; rfl
  · refine ⟨by change 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 7) = some word at found; cases found; rfl
  · refine ⟨by change 1 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 11) = some word at found; cases found; rfl
  · refine ⟨by change 2 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 13) = some word at found; cases found; rfl
  · refine ⟨by change 3 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change (none : Option Semantics.Word) = some word at found; cases found

/-- The ORIGINAL finite run does not cover the unread source query, whose raw
symbolic/numeric/target value is83 despite logical None. It covers all real
reads/writes and the retained destination observation37. APPLY the new bridge. -/
theorem precise_access_bridge :
    accessSourceLocation ∉ locations ∧
    ¬ (∀ i ∈ accessIndices, Solidity.Storage.Loc.data (.data (.root 0) 0) i.val ∈ locations) ∧
    (PrimitivePop.elementQuery shadowIndex).read firstSource = none ∧
    Evm.run TargetArrayCopy.code { accessTarget with stack := .slot (.data (.root 0) 0) :: .slot (.data (.root 1) 0) :: tail } = .ok accessAfter 0 ∧
    Represented (firstRetained.overlay firstSource) (PrimitivePop.queries accessIndices) (.data (.root 1) 0) accessAfterStore ∧
    Transport 128 hash locations accessAfterStore accessAfterNumeric ∧
    (∀ l (member : l ∈ locations), accessAfter.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (accessAfterStore l)) := by
  refine ⟨by decide,?_,rfl,?_⟩
  · intro covered
    have wrong := covered shadowIndex (by simp only [accessIndices,List.mem_cons,true_or,or_true])
    exact (by decide : accessSourceLocation ∉ locations) wrong

  · refine CopyAccess.complete run firstRetained firstSource accessIndices (.data (.root 1) 0) (.data (.root 0) 0)
      (by trivial) (by trivial) accessStore accessNumeric accessTarget tail accessBeforeDst (CopyAccess.read_queries_from_full _ _ _ _ accessBeforeSrc) accessInitial (by decide) (by decide)
      ?_ ?_ ?_ fitting accessTargetInitial
    · intro i member
      simp only [accessIndices,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    · intro j live
      change j < 1 at live
      have same : j = 0 := by omega
      subst j; decide
    · intro j live
      change j < 3 at live
      have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases casesJ with rfl | rfl | rfl <;> decide


/-- APPLY successful-observation framing; Source None requires neither coverage
nor a physical frame. Every Some observation has an actual separated address. -/
theorem precise_snapshot_frame : Represented firstSource (PrimitivePop.queries accessIndices) (.data (.root 0) 0)
    (TargetNestedArrayTransport.copyStores accessStore (.root 1) (.root 0) 1) := by
  refine CopyAccess.observed_frame run (.root 1) (.root 0) (by trivial) (by trivial) accessStore accessNumeric accessTarget 1
    accessInitial fitting accessTargetInitial ?_ ?_ ?_ firstSource (PrimitivePop.queries accessIndices) (.data (.root 0) 0) accessBeforeSrc ?_ ?_
  · intro k live
    have same : k = 0 := by omega
    subst k; decide
  · intro k live j bound
    have same : k = 0 := by omega
    subst k
    change j < 1 at bound
    have same : j = 0 := by omega
    subst j; decide
  · intro k live j bound
    have same : k = 0 := by omega
    subst k
    change j < 3 at bound
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with rfl | rfl | rfl <;> decide
  · intro q member word observed
    simp only [PrimitivePop.queries,accessIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · change (none : Option Semantics.Word) = some word at observed
      cases observed
  · intro q member word observed
    simp only [PrimitivePop.queries,accessIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · change Evm.Slot.data (.root 0) 0 ∉ TargetNestedArrayCopyLoop.touched accessTarget (.root 0) (.root 1) 1
      decide
    · change Evm.Slot.data (.data (.root 0) 0) 0 ∉ TargetNestedArrayCopyLoop.touched accessTarget (.root 0) (.root 1) 1
      decide
    · change Evm.Slot.data (.data (.root 0) 0) 1 ∉ TargetNestedArrayCopyLoop.touched accessTarget (.root 0) (.root 1) 1
      decide
    · change Evm.Slot.data (.data (.root 0) 0) 2 ∉ TargetNestedArrayCopyLoop.touched accessTarget (.root 0) (.root 1) 1
      decide
    · change (none : Option Semantics.Word) = some word at observed
      cases observed

/-- COMPLETE covered vectors plus the explicitly UNcovered unread source83.
The retained destination37 is a successful member of the NEW owner query set. -/
theorem precise_access_ordered :
    (symbolicView accessStore,symbolicView accessAfterStore,numericView accessAfterNumeric,targetView accessAfter,context accessAfter,
      accessStore accessSourceLocation,accessAfterStore accessSourceLocation,
      accessNumeric (accessSourceLocation.word 128 hash),accessAfterNumeric (accessSourceLocation.word 128 hash),
      accessTarget.store (.data (.data (.root 0) 0) 3),accessAfter.store (.data (.data (.root 0) 0) 3),
      (PrimitivePop.queries accessIndices).map (fun q => q.read (firstRetained.overlay firstSource))) =
    ([w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 3,w 23,w 29,w 31,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],[w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],[w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],[2,1,1,7,11,13,1,17,19,1,71,1,7,0,0,37,2,41,43,47,2,53,59,61,73],context accessTarget,w 83,w 83,w 83,w 83,83,83,
      [some (w 1),some (w 7),some (w 0),some (w 0),some (w 37)]) := by rfl

/-- Incorrectly copying the unread raw83 over the older destination37 breaks
the independent selected output. None never authorizes an extra source read. -/
theorem unread_source_copy_negative : ¬ Represented (firstRetained.overlay firstSource) (PrimitivePop.queries accessIndices) (.data (.root 1) 0)
    (Representation.write accessAfterStore (.data (.data (.root 1) 0) 3) (accessStore accessSourceLocation)) := by
  intro bad
  have member : PrimitivePop.elementQuery shadowIndex ∈ PrimitivePop.queries (G := graph) (p := .uint) accessIndices :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨shadowIndex,by simp only [accessIndices,List.mem_cons,true_or,or_true],rfl⟩)
  have observed := (bad _ member).2.2 (w 37) (by rfl)
  change w 83 = w 37 at observed
  have unequal : w 83 ≠ w 37 := by decide
  exact unequal observed

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.precise_access_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms precise_access_bridge
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.precise_snapshot_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms precise_snapshot_frame
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.precise_access_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms precise_access_ordered
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.unread_source_copy_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms unread_source_copy_negative


/-- Actual extra SLOAD/SSTORE reads raw83 and overwrites the observed retained
word37. This executable negative agrees with the symbolic wrong-copy control. -/
theorem unread_source_target_negative :
    Evm.run (TargetOperations.copyCode (.data (.data (.root 1) 0) 3) (.data (.data (.root 0) 0) 3)) accessAfter =
      .ok { accessAfter with store := Evm.WordStore.write accessAfter.store (.data (.data (.root 1) 0) 3) 83 } 0 ∧
    (Evm.WordStore.write accessAfter.store (.data (.data (.root 1) 0) 3) 83).cells (.data (.data (.root 1) 0) 3) ≠
      TargetOperations.encodeWord (w 37) := by
  refine ⟨?_,?_⟩
  · exact TargetOperations.run_copy _ _ _
  · decide

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.unread_source_target_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms unread_source_target_negative


private def retainedSourceShadow : Value graph (.array (.prim .uint)) := .array ⟨4,by decide⟩ ⟨1,by decide⟩ (by decide)
  (fun i => .present (.prim (if i.val = 0 then w 7 else if i.val = 1 then w 11 else if i.val = 2 then w 13 else w 83)))
private def sourceShadowPath : TypeGraph.Path graph (.array (.prim .uint)) (.prim .uint) := .cons (.index shadowIndex) .nil
private theorem retainedSourceReads : Represented retainedSourceShadow (CopyAccess.readQueries retainedSourceShadow accessIndices)
    (.data (.root 0) 0) accessStore := by
  change Represented retainedSourceShadow [Query.length .nil,PrimitivePop.elementQuery (freshIndex 0)] (.data (.root 0) 0) accessStore
  intro q member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 1) = some word at found; cases found; rfl
  · refine ⟨by change 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 7) = some word at found; cases found; rfl
private theorem retainedSourceBridge :
    Evm.run TargetArrayCopy.code { accessTarget with stack := .slot (.data (.root 0) 0) :: .slot (.data (.root 1) 0) :: tail } = .ok accessAfter 0 ∧
    Represented (firstRetained.overlay retainedSourceShadow) (PrimitivePop.queries accessIndices) (.data (.root 1) 0) accessAfterStore ∧
    Transport 128 hash locations accessAfterStore accessAfterNumeric ∧
    (∀ l (member : l ∈ locations), accessAfter.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (accessAfterStore l)) := by
  refine CopyAccess.complete run firstRetained retainedSourceShadow accessIndices (.data (.root 1) 0) (.data (.root 0) 0)
    (by trivial) (by trivial) accessStore accessNumeric accessTarget tail accessBeforeDst retainedSourceReads accessInitial (by decide) (by decide)
    ?_ ?_ ?_ fitting accessTargetInitial
  · intro i member
    simp only [accessIndices,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  · intro j live
    change j < 1 at live
    have same : j = 0 := by omega
    subst j; decide
  · intro j live
    change j < 3 at live
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with rfl | rfl | rfl <;> decide

/-- An inhabited RETAINED source read Some83 is also ignored outside LIVE.
The source demand slice contains only header+live index0. The destination's
older Some37 stays represented; both logical/live distinctions are pinned. -/
theorem ignored_retained_source :
    ((PrimitivePop.elementQuery shadowIndex).read retainedSourceShadow,
      sourceShadowPath.readLive Value.dflt retainedSourceShadow,
      (PrimitivePop.elementQuery shadowIndex).read (firstRetained.overlay retainedSourceShadow),
      sourceShadowPath.readLive Value.dflt (firstRetained.overlay retainedSourceShadow),
      symbolicView accessStore,symbolicView accessAfterStore,numericView accessAfterNumeric,targetView accessAfter,context accessAfter) =
    (some (w 83),none,some (w 37),none,[w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 3,w 23,w 29,w 31,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],[w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],[w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],[2,1,1,7,11,13,1,17,19,1,71,1,7,0,0,37,2,41,43,47,2,53,59,61,73],context accessTarget) ∧
    Evm.run TargetArrayCopy.code { accessTarget with stack := .slot (.data (.root 0) 0) :: .slot (.data (.root 1) 0) :: tail } = .ok accessAfter 0 ∧
    Represented (firstRetained.overlay retainedSourceShadow) (PrimitivePop.queries accessIndices) (.data (.root 1) 0) accessAfterStore ∧
    Transport 128 hash locations accessAfterStore accessAfterNumeric ∧
    (∀ l (member : l ∈ locations), accessAfter.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (accessAfterStore l)) := by
  exact ⟨rfl,retainedSourceBridge⟩

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.ignored_retained_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ignored_retained_source

private def accessOldRoot : Value graph (.array (.array (.prim .uint))) := .array ⟨3,by decide⟩ ⟨1,by decide⟩ (by decide)
  (fun i => if i.val = 0 then .present firstRetained else if i.val = 1 then .present retainedChild else .present staleChild)
private def accessSourceRoot : Value graph (.array (.array (.prim .uint))) := .array ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide)
  (fun i => if i.val = 0 then .present retainedSourceShadow else if i.val = 1 then .present innerB else .present sourceOlderChild)
private def accessChildren : List Index := [freshIndex 0]
private def accessRootIndices (_ : Index) : List Index := accessIndices
private def accessRootQueries := NestedRootComposition.rootQueries (G := graph) (p := .uint) accessChildren accessRootIndices
private def accessRootReads := RootCopyAccess.sourceQueries accessSourceRoot accessChildren accessRootIndices
private def accessRootAfter := TargetNestedArrayRuntime.afterCopy accessTarget tail (.root 0) (.root 1)
private theorem accessOldOwner : Represented accessOldRoot accessRootQueries (.root 1) accessStore := by
  intro q member
  change q ∈ Query.length .nil :: (PrimitivePop.queries accessIndices).map (Query.prefix firstPath) at member
  rcases List.mem_cons.mp member with rfl | inside
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 1) = some word at found; cases found; rfl
  · exact (Represented.prefix firstPath (by rfl : accessOldRoot.find firstPath = some firstRetained)
      (by change 0 < lmax ∧ True; decide) accessBeforeDst) q inside
private theorem accessSourceOwner : Represented accessSourceRoot accessRootReads (.root 0) accessStore := by
  intro q member
  change q ∈ Query.length .nil :: (CopyAccess.readQueries retainedSourceShadow accessIndices).map (Query.prefix firstPath) at member
  rcases List.mem_cons.mp member with rfl | inside
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 2) = some word at found; cases found; rfl
  · exact (Represented.prefix firstPath (by rfl : accessSourceRoot.find firstPath = some retainedSourceShadow)
      (by change 0 < lmax ∧ True; decide) retainedSourceReads) q inside

/-- Full actual nested runtime copy with a six-observation ROOT owner but only
three source demands. Unread source83 is outside the finite run; retained37
remains an explicit successful destination observation. -/
theorem precise_root_bridge :
    Evm.run TargetNestedArrayCopy.code { accessTarget with stack := .slot (.root 0) :: .slot (.root 1) :: tail } = .ok accessRootAfter 0 ∧
    Represented (accessOldRoot.overlay accessSourceRoot) accessRootQueries (.root 1)
      (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0)) ∧
    Transport 128 hash locations (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0))
      (TargetNestedArrayTransport.execute 128 hash accessNumeric (.root 1) (.root 0)) ∧
    (∀ l (member : l ∈ locations), accessRootAfter.store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0) l)) := by
  refine RootCopyAccess.live_root run accessOldRoot accessSourceRoot accessChildren accessRootIndices ?_
    (.root 1) (.root 0) (by trivial) (by trivial) accessStore accessNumeric accessTarget tail accessInitial fitting accessTargetInitial
    accessOldOwner accessSourceOwner (by decide) (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i member
    have same := List.mem_singleton.mp member; subst i; decide
  · intro k inside
    change k < 2 at inside
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl <;> decide
  · exact forall_bounded_pair (by decide)
  · exact forall_bounded_pair (by decide)
  · intro k inside begun
    change k < 2 at inside
    change 2 ≤ k at begun
    omega
  · intro k inside begun j live
    change k < 2 at inside
    change 2 ≤ k at begun
    omega
  · intro i member j inside
    have same := List.mem_singleton.mp member; subst i
    simp only [accessRootIndices,accessIndices,List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl | rfl | rfl | rfl <;> decide
  · intro i member j live
    have same := List.mem_singleton.mp member; subst i
    change j < 1 at live
    have same : j = 0 := by omega
    subst j; decide
  · intro i member j live
    have same := List.mem_singleton.mp member; subst i
    change j < 3 at live
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with rfl | rfl | rfl <;> decide
  · intro i member q observation
    have same := List.mem_singleton.mp member; subst i
    exact List.not_mem_nil
  · intro i member q observation
    have same := List.mem_singleton.mp member; subst i
    exact List.not_mem_nil

/-- Complete covered before/first/final vectors, numeric/target output, context,
all six destination and three source demands, plus the uncovered source shadow. -/
theorem precise_root_ordered :
    (symbolicView accessStore,symbolicView accessAfterStore,
      symbolicView (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0)),
      numericView (TargetNestedArrayTransport.execute 128 hash accessNumeric (.root 1) (.root 0)),
      targetView accessRootAfter,context accessRootAfter,
      accessRootQueries.map (fun q => q.read (accessOldRoot.overlay accessSourceRoot)),
      accessRootReads.map (fun q => q.read accessSourceRoot),
      accessRootAfter.store (.data (.data (.root 0) 0) 3),
      (PrimitivePop.elementQuery shadowIndex).read retainedSourceShadow,
      sourceShadowPath.readLive Value.dflt retainedSourceShadow) =
    ([w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 3,w 23,w 29,w 31,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
     [2,2,1,7,11,13,1,17,19,1,71,1,7,0,0,37,1,17,0,47,2,53,59,61,73],context accessTarget,
     [some (w 2),some (w 1),some (w 7),some (w 0),some (w 0),some (w 37)],
     [some (w 2),some (w 1),some (w 7)],83,some (w 83),none) := by rfl

/-- An extra read of the retained source shadow is executable but falsifies
this ROOT owner, despite a correct root header and all live payloads. -/
theorem precise_root_wrong_copy : ¬ Represented (accessOldRoot.overlay accessSourceRoot) accessRootQueries (.root 1)
    (Representation.write (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0))
      (.data (.data (.root 1) 0) 3) (w 83)) := by
  intro bad
  have member : Query.prefix firstPath (PrimitivePop.elementQuery shadowIndex) ∈ accessRootQueries := by
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨freshIndex 0,List.mem_cons_self,
      List.mem_map.mpr ⟨PrimitivePop.elementQuery shadowIndex,
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨shadowIndex,by change shadowIndex ∈ accessIndices; simp only [accessIndices,List.mem_cons,true_or,or_true],rfl⟩),rfl⟩⟩)
  have observed := (bad _ member).2.2 (w 37) (by rfl)
  change w 83 = w 37 at observed
  exact (by decide : w 83 ≠ w 37) observed

/-- Actual forbidden extra SLOAD/SSTORE agrees with the ROOT counterexample. -/
theorem precise_root_target_wrong_copy :
    Evm.run (TargetOperations.copyCode (.data (.data (.root 1) 0) 3) (.data (.data (.root 0) 0) 3)) accessRootAfter =
      .ok { accessRootAfter with store := Evm.WordStore.write accessRootAfter.store (.data (.data (.root 1) 0) 3) 83 } 0 ∧
    (Evm.WordStore.write accessRootAfter.store (.data (.data (.root 1) 0) 3) 83).cells (.data (.data (.root 1) 0) 3) ≠
      TargetOperations.encodeWord (w 37) := by
  refine ⟨TargetOperations.run_copy _ _ _,?_⟩
  decide

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.precise_root_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms precise_root_bridge

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.precise_root_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms precise_root_ordered

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.precise_root_wrong_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms precise_root_wrong_copy

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.precise_root_target_wrong_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms precise_root_target_wrong_copy

private def laterChildren : List Index := [freshIndex 1]
private def laterIndices (_ : Index) : List Index := freshIndices
private def laterQueries := NestedRootComposition.rootQueries (G := graph) (p := .uint) laterChildren laterIndices
private def laterReads := RootCopyAccess.sourceQueries accessSourceRoot laterChildren laterIndices
private theorem laterBeforeDst : Represented retainedChild (PrimitivePop.queries freshIndices) (.data (.root 1) 1) accessStore := by
  intro q member
  simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 2) = some word at found; cases found; rfl
  · refine ⟨by change 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 41) = some word at found; cases found; rfl
  · refine ⟨by change 1 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 43) = some word at found; cases found; rfl
  · refine ⟨by change 2 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 47) = some word at found; cases found; rfl
private theorem laterBeforeSrc : Represented innerB (CopyAccess.readQueries innerB freshIndices) (.data (.root 0) 1) accessStore := by
  change Represented innerB [Query.length .nil,PrimitivePop.elementQuery (freshIndex 0)] (.data (.root 0) 1) accessStore
  intro q member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 1) = some word at found; cases found; rfl
  · refine ⟨by change 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 17) = some word at found; cases found; rfl
private theorem laterOldOwner : Represented accessOldRoot laterQueries (.root 1) accessStore := by
  intro q member
  change q ∈ Query.length .nil :: (PrimitivePop.queries freshIndices).map (Query.prefix retainedPath) at member
  rcases List.mem_cons.mp member with rfl | inside
  · exact accessOldOwner _ List.mem_cons_self
  · exact (Represented.prefix retainedPath (by rfl : accessOldRoot.find retainedPath = some retainedChild)
      (by change 1 < lmax ∧ True; decide) laterBeforeDst) q inside
private theorem laterSourceOwner : Represented accessSourceRoot laterReads (.root 0) accessStore := by
  intro q member
  change q ∈ Query.length .nil :: (CopyAccess.readQueries innerB freshIndices).map (Query.prefix retainedPath) at member
  rcases List.mem_cons.mp member with rfl | inside
  · exact accessSourceOwner _ List.mem_cons_self
  · exact (Represented.prefix retainedPath (by rfl : accessSourceRoot.find retainedPath = some innerB)
      (by change 1 < lmax ∧ True; decide) laterBeforeSrc) q inside

/-- Later selected child: CURRENT owner derived after nonempty actual writes.
Retained outer path becomes live; retained inner shadow47 survives. -/
theorem later_precise_root_bridge :
    Evm.run TargetNestedArrayCopy.code { accessTarget with stack := .slot (.root 0) :: .slot (.root 1) :: tail } = .ok accessRootAfter 0 ∧
    Represented (accessOldRoot.overlay accessSourceRoot) laterQueries (.root 1)
      (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0)) ∧
    Transport 128 hash locations (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0))
      (TargetNestedArrayTransport.execute 128 hash accessNumeric (.root 1) (.root 0)) ∧
    (∀ l (member : l ∈ locations), accessRootAfter.store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0) l)) := by
  refine RootCopyAccess.live_root run accessOldRoot accessSourceRoot laterChildren laterIndices ?_
    (.root 1) (.root 0) (by trivial) (by trivial) accessStore accessNumeric accessTarget tail accessInitial fitting accessTargetInitial
    laterOldOwner laterSourceOwner (by decide) (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i member
    have same := List.mem_singleton.mp member; subst i; decide
  · intro k inside
    change k < 2 at inside
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl <;> decide
  · exact forall_bounded_pair (by decide)
  · exact forall_bounded_pair (by decide)
  · intro k inside begun
    change k < 2 at inside
    change 2 ≤ k at begun
    omega
  · intro k inside begun j live
    change k < 2 at inside
    change 2 ≤ k at begun
    omega
  · intro i member j inside
    have same := List.mem_singleton.mp member; subst i
    simp only [laterIndices,freshIndices,List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl | rfl | rfl <;> decide
  · intro i member j live
    have same := List.mem_singleton.mp member; subst i
    change j < 1 at live
    have same : j = 0 := by omega
    subst j; decide
  · intro i member j live
    have same := List.mem_singleton.mp member; subst i
    change j < 2 at live
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with rfl | rfl <;> decide
  · intro i member q observation
    have same := List.mem_singleton.mp member; subst i
    simp only [laterIndices,PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at observation
    rcases observation with rfl | rfl | rfl | rfl
    · change Evm.Slot.data (.root 1) 1 ∉ TargetNestedArrayCopyLoop.touched accessTarget (.root 0) (.root 1) 1
      decide
    · change Evm.Slot.data (.data (.root 1) 1) 0 ∉ TargetNestedArrayCopyLoop.touched accessTarget (.root 0) (.root 1) 1
      decide
    · change Evm.Slot.data (.data (.root 1) 1) 1 ∉ TargetNestedArrayCopyLoop.touched accessTarget (.root 0) (.root 1) 1
      decide
    · change Evm.Slot.data (.data (.root 1) 1) 2 ∉ TargetNestedArrayCopyLoop.touched accessTarget (.root 0) (.root 1) 1
      decide
  · intro i member q observation
    have same := List.mem_singleton.mp member; subst i
    change q ∈ [Query.length .nil,PrimitivePop.elementQuery (freshIndex 0)] at observation
    rcases List.mem_cons.mp observation with rfl | inside
    · change Evm.Slot.data (.root 0) 1 ∉ TargetNestedArrayCopyLoop.touched accessTarget (.root 0) (.root 1) 1
      decide
    · have same := List.mem_singleton.mp inside; subst q
      change Evm.Slot.data (.data (.root 0) 1) 0 ∉ TargetNestedArrayCopyLoop.touched accessTarget (.root 0) (.root 1) 1
      decide

/-- Complete ordered physical and selected-query observations after earlier writes. -/
theorem later_precise_root_ordered :
    (symbolicView accessStore,symbolicView accessAfterStore,
      symbolicView (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0)),
      numericView (TargetNestedArrayTransport.execute 128 hash accessNumeric (.root 1) (.root 0)),
      targetView accessRootAfter,context accessRootAfter,
      laterQueries.map (fun q => q.read (accessOldRoot.overlay accessSourceRoot)),
      laterReads.map (fun q => q.read accessSourceRoot),
      accessRootAfter.store (.data (.data (.root 0) 0) 3),
      (PrimitivePop.elementQuery shadowIndex).read retainedSourceShadow,
      sourceShadowPath.readLive Value.dflt retainedSourceShadow) =
    ([w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 3,w 23,w 29,w 31,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
     [2,2,1,7,11,13,1,17,19,1,71,1,7,0,0,37,1,17,0,47,2,53,59,61,73],context accessTarget,
     [some (w 2),some (w 1),some (w 17),some (w 0),some (w 47)],
     [some (w 2),some (w 1),some (w 17)],83,some (w 83),none) := by rfl

/-- Both exact finite-region demand and alias states discriminate live from
retained. The prior prefix really changes child0, while child1 is preserved. -/
theorem later_alias_and_prefix :
    (retainedPath.readLive Value.dflt accessOldRoot).isSome = false ∧
    (retainedPath.readLive Value.dflt (accessOldRoot.overlay accessSourceRoot)).isSome = true ∧
    accessAfterStore (.data (.data (.root 1) 0) 0) = w 7 ∧
    accessStore (.data (.data (.root 1) 0) 0) = w 23 ∧
    (PrimitivePop.elementQuery (freshIndex 2)).read innerB = none ∧
    (.data (.data (.root 0) 1) 2 : Solidity.Storage.Loc) ∉ locations ∧
    (PrimitivePop.elementQuery (freshIndex 2)).read (retainedChild.overlay innerB) = some (w 47) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,by decide,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.later_precise_root_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms later_precise_root_bridge

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.later_precise_root_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms later_precise_root_ordered

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.later_alias_and_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms later_alias_and_prefix

/-- Reading a missing source index as an extra physical zero destroys the
successful retained destination observation; None never supplies that zero. -/
theorem later_wrong_shadow_copy : ¬ Represented (accessOldRoot.overlay accessSourceRoot) laterQueries (.root 1)
    (Representation.write (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0))
      (.data (.data (.root 1) 1) 2) (w 0)) := by
  intro bad
  have member : Query.prefix retainedPath (PrimitivePop.elementQuery (freshIndex 2)) ∈ laterQueries := by
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨freshIndex 1,List.mem_cons_self,
      List.mem_map.mpr ⟨PrimitivePop.elementQuery (freshIndex 2),
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨freshIndex 2,by change freshIndex 2 ∈ freshIndices; simp only [freshIndices,List.mem_cons,true_or,or_true],rfl⟩),rfl⟩⟩)
  have observed := (bad _ member).2.2 (w 47) (by rfl)
  change w 0 = w 47 at observed
  exact (by decide : w 0 ≠ w 47) observed

/-- The fixture's unobserved raw zero is proved separately from logical None.
Its extra SLOAD/SSTORE is executable and violates represented retained47. -/
theorem later_wrong_shadow_target :
    Evm.run (TargetOperations.copyCode (.data (.data (.root 1) 1) 2) (.data (.data (.root 0) 1) 2)) accessRootAfter =
      .ok { accessRootAfter with store := Evm.WordStore.write accessRootAfter.store (.data (.data (.root 1) 1) 2) 0 } 0 ∧
    (Evm.WordStore.write accessRootAfter.store (.data (.data (.root 1) 1) 2) 0).cells (.data (.data (.root 1) 1) 2) ≠
      TargetOperations.encodeWord (w 47) := by
  refine ⟨TargetOperations.run_copy _ _ _,?_⟩
  decide

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.later_wrong_shadow_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms later_wrong_shadow_copy

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.later_wrong_shadow_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms later_wrong_shadow_target

private def clearFirst := TargetNestedArrayTransport.clearStores bothStore (.root 1) 0 1
private def clearFinal := TargetNestedArrayTransport.clearStores bothStore (.root 1) 0 3
private def clearFinalTarget := TargetNestedArrayClearLoop.prefixMachine bothTarget (.root 1) 0 3
private theorem clearOldInputs : Represented firstRetained (TargetClearRepresentation.oldQueries firstRetained accessIndices)
    (.data (.root 1) 0) bothStore := by
  change Represented firstRetained [Query.length .nil,PrimitivePop.elementQuery shadowIndex] (.data (.root 1) 0) bothStore
  intro q member
  rcases List.mem_cons.mp member with rfl | inside
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 3) = some word at found; cases found; rfl
  · have same := List.mem_singleton.mp inside; subst q
    refine ⟨by change 3 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 37) = some word at found; cases found; rfl
private theorem clearFirstOwner : Represented firstRetained.clear (PrimitivePop.queries accessIndices) (.data (.root 1) 0) clearFirst := by
  change Represented firstRetained.clear (PrimitivePop.queries accessIndices) (.data (.root 1) 0)
    (TargetClearRepresentation.afterStore firstRetained (.data (.root 1) 0) bothStore)
  exact TargetClearRepresentation.represented_spec firstRetained accessIndices (.data (.root 1) 0) bothStore clearOldInputs
private theorem clearHeaders : ∀ k < 3, 0 ≤ k → Solidity.Storage.Loc.data (.root 1) k ∈ locations := by
  intro k inside begun
  have casesK : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases casesK with rfl | rfl | rfl <;> decide
private theorem clearWrites : ∀ k < 3, 0 ≤ k →
    ∀ j < ((TargetNestedArrayTransport.clearStores bothStore (.root 1) 0 k) (.data (.root 1) k)).val.toNat,
      Solidity.Storage.Loc.data (.data (.root 1) k) j ∈ locations := by
  intro k inside begun j live
  have casesK : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases casesK with rfl | rfl | rfl
  · change j < 3 at live
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with rfl | rfl | rfl <;> decide
  · change j < 2 at live
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with rfl | rfl <;> decide
  · change j < 2 at live
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with rfl | rfl <;> decide

/-- The first changed clear owner, derived from OLD header+retained37, survives
TWO later nonempty stale-child iterations under the original finite region. -/
theorem cleared_child_interval :
    Represented firstRetained.clear (PrimitivePop.queries accessIndices) (.data (.root 1) 0) clearFinal ∧
    Transport 128 hash locations clearFinal (TargetNestedArrayTransport.clearNumerics 128 hash bothNumeric (.root 1) 0 3) ∧
    (∀ l (member : l ∈ locations), clearFinalTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (clearFinal l)) := by
  refine ⟨?_,TargetNestedArrayTransport.clear_prefix run (.root 1) (by trivial) bothStore bothNumeric bothTarget 0 3
    bothInitial fitting bothTargetInitial clearHeaders clearWrites⟩
  refine LaterClearFrames.owner_interval run (.root 1) (by trivial) bothStore bothNumeric bothTarget 0 1 2 0
    bothInitial fitting bothTargetInitial clearHeaders clearWrites firstRetained.clear accessIndices (by decide) clearFirstOwner ?_
  intro q member
  simp only [PrimitivePop.queries,accessIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Actual structured loop executes all three child clear operations. It does
not write the root header; that separate final phase remains explicit. -/
theorem cleared_child_actual_loop :
    Evm.run [.loop TargetArrayClear.condition TargetNestedArrayCopy.clearBody]
      { bothTarget with stack := .val ⟨0,by decide⟩ :: .val ⟨3,by decide⟩ :: .slot (.root 1) :: .val ⟨0,by decide⟩ :: tail } =
      .ok (TargetNestedArrayClearLoop.iterationMachine bothTarget tail (.root 1) 0 ⟨0,by decide⟩ ⟨3,by decide⟩ ⟨3,by decide⟩) 0 := by
  exact TargetNestedArrayClearLoop.run_loop bothTarget tail (.root 1) ⟨0,by decide⟩ ⟨3,by decide⟩

/-- Complete ordered observations: changed first prefix, later stale siblings,
all older shadows37/47/61, numeric/target/context and all selected owner reads. -/
theorem cleared_child_interval_ordered :
    (symbolicView bothStore,symbolicView clearFirst,symbolicView clearFinal,
      numericView (TargetNestedArrayTransport.clearNumerics 128 hash bothNumeric (.root 1) 0 3),
      targetView clearFinalTarget,context clearFinalTarget,
      (PrimitivePop.queries accessIndices).map (fun q => q.read firstRetained.clear)) =
    ([w 2,w 3,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 3,w 23,w 29,w 31,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 3,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 0,w 0,w 0,w 0,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 3,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 0,w 0,w 0,w 0,w 37,w 0,w 0,w 0,w 47,w 0,w 0,w 0,w 61,w 73],
     [w 2,w 3,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 0,w 0,w 0,w 0,w 37,w 0,w 0,w 0,w 47,w 0,w 0,w 0,w 61,w 73],
     [2,3,1,7,11,13,1,17,19,1,71,0,0,0,0,37,0,0,0,47,0,0,0,61,73],context bothTarget,
     [some (w 0),some (w 0),some (w 0),some (w 0),some (w 37)]) := by rfl

/-- Framing the OLD owner after its live slots were cleared would be false;
the interval theorem deliberately takes the changed first-prefix owner. -/
theorem cleared_child_old_owner_negative : ¬ Represented firstRetained (PrimitivePop.queries accessIndices) (.data (.root 1) 0) clearFinal := by
  intro bad
  have observed := (bad (.length .nil) List.mem_cons_self).2.2 (w 3) (by rfl)
  change w 0 = w 3 at observed
  exact (by decide : w 0 ≠ w 3) observed

/-- Clearing the entire retained extent, rather than the old live prefix,
falsifies the actual retained shadow observation. -/
theorem cleared_child_whole_extent_negative : ¬ Represented firstRetained.clear (PrimitivePop.queries accessIndices) (.data (.root 1) 0)
    (Representation.write clearFinal (.data (.data (.root 1) 0) 3) (w 0)) := by
  intro bad
  have member : PrimitivePop.elementQuery shadowIndex ∈ PrimitivePop.queries (G := graph) (p := .uint) accessIndices :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨shadowIndex,by simp only [accessIndices,List.mem_cons,true_or,or_true],rfl⟩)
  have observed := (bad _ member).2.2 (w 37) (by rfl)
  change w 0 = w 37 at observed
  exact (by decide : w 0 ≠ w 37) observed

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.cleared_child_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms cleared_child_interval

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.cleared_child_actual_loop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms cleared_child_actual_loop

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.cleared_child_interval_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms cleared_child_interval_ordered

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.cleared_child_old_owner_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms cleared_child_old_owner_negative

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.cleared_child_whole_extent_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms cleared_child_whole_extent_negative

private def staleRootQueries : List (Query graph (.array (.array (.prim .uint)))) :=
  (PrimitivePop.queries freshIndices).map (Query.prefix missingPath)
private theorem staleOldLeaf : Represented staleChild (TargetClearRepresentation.oldQueries staleChild freshIndices) (.data (.root 1) 2) bothStore := by
  change Represented staleChild [Query.length .nil,PrimitivePop.elementQuery (freshIndex 2)] (.data (.root 1) 2) bothStore
  intro q member
  rcases List.mem_cons.mp member with rfl | inside
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 2) = some word at found; cases found; rfl
  · have same := List.mem_singleton.mp inside; subst q
    refine ⟨by change 2 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 61) = some word at found; cases found; rfl
private theorem beforeStaleRoot : Represented bothOldRoot
    ((TargetClearRepresentation.oldQueries (NestedCopyObservations.child bothOldRoot (freshIndex 2)) freshIndices).map
      (Query.prefix (NestedCopyObservations.childPath (freshIndex 2)))) (.root 1) bothStore := by
  exact Represented.prefix missingPath (by rfl : bothOldRoot.find missingPath = some staleChild)
    (by change 2 < lmax ∧ True; decide) staleOldLeaf
private theorem staleOldRootHeader : Represented bothOldRoot [.length .nil] (.root 1) bothStore := by
  intro q member
  have same := List.mem_singleton.mp member; subst q
  exact beforeBothOldRoot _ List.mem_cons_self
private theorem staleSourceRootHeader : Represented bothSourceRoot [.length .nil] (.root 0) bothStore := by
  intro q member
  have same := List.mem_singleton.mp member; subst q
  exact beforeBothSourceRoot _ List.mem_cons_self

/-- APPLY the full derived stale-child ROOT transport. OLD root header plus
OLD child header/retained61 suffice; no current owner or source-child premise. -/
theorem stale_root_bridge :
    Evm.run TargetNestedArrayCopy.code { bothTarget with stack := .slot (.root 0) :: .slot (.root 1) :: tail } = .ok bothAfter 0 ∧
    Represented (bothOldRoot.overlay bothSourceRoot) staleRootQueries (.root 1)
      (TargetNestedArrayTransport.afterStore bothStore (.root 1) (.root 0)) ∧
    Transport 128 hash locations (TargetNestedArrayTransport.afterStore bothStore (.root 1) (.root 0))
      (TargetNestedArrayTransport.execute 128 hash bothNumeric (.root 1) (.root 0)) ∧
    (∀ l (member : l ∈ locations), bothAfter.store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore bothStore (.root 1) (.root 0) l)) := by
  refine NestedStaleComposition.stale_child run bothOldRoot bothSourceRoot (freshIndex 2) freshIndices (by decide) (by decide)
    (.root 1) (.root 0) (by trivial) (by trivial) bothStore bothNumeric bothTarget tail bothInitial fitting bothTargetInitial
    beforeStaleRoot staleOldRootHeader staleSourceRootHeader (by decide) (by decide) ?_ ?_ ?_ ?_ ?_ ?_
  · intro k inside
    change k < 2 at inside
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl <;> decide
  · exact forall_bounded_pair (by decide)
  · exact forall_bounded_pair (by decide)
  · intro k inside begun
    change k < 3 at inside
    change 2 ≤ k at begun
    have same : k = 2 := by omega
    subst k; decide
  · intro k inside begun j live
    change k < 3 at inside
    change 2 ≤ k at begun
    have same : k = 2 := by omega
    subst k
    change j < 2 at live
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with rfl | rfl <;> decide
  · intro q member
    simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide

/-- Complete old/copy-prefix/final physical observations, selected stale ROOT
queries, logical retained success and non-live path distinction. -/
theorem stale_root_ordered :
    (symbolicView bothStore,symbolicView (TargetNestedArrayTransport.copyStores bothStore (.root 1) (.root 0) 2),
      symbolicView (TargetNestedArrayTransport.afterStore bothStore (.root 1) (.root 0)),
      numericView (TargetNestedArrayTransport.execute 128 hash bothNumeric (.root 1) (.root 0)),
      targetView bothAfter,context bothAfter,
      staleRootQueries.map (fun q => q.read (bothOldRoot.overlay bothSourceRoot)),
      (Query.length missingPath).read (bothOldRoot.overlay bothSourceRoot),
      (missingPath.readLive Value.dflt (bothOldRoot.overlay bothSourceRoot)).isSome,
      (PrimitivePop.elementQuery (freshIndex 0)).read sourceOlderChild) =
    ([w 2,w 3,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 3,w 23,w 29,w 31,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 3,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 0,w 0,w 0,w 61,w 73],
     [w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 0,w 0,w 0,w 61,w 73],
     [2,2,1,7,11,13,1,17,19,1,71,1,7,0,0,37,1,17,0,47,0,0,0,61,73],context bothTarget,
     [some (w 0),some (w 0),some (w 0),some (w 61)],some (w 0),false,some (w 71)) := by rfl

/-- Copying the source's retained OUTER child beyond its LIVE length wrongly
replaces a cleared stale payload with71 and invalidates the selected ROOT. -/
theorem stale_root_wrong_source_tail : ¬ Represented (bothOldRoot.overlay bothSourceRoot) staleRootQueries (.root 1)
    (Representation.write (TargetNestedArrayTransport.afterStore bothStore (.root 1) (.root 0))
      (.data (.data (.root 1) 2) 0) (w 71)) := by
  intro bad
  have member : Query.prefix missingPath (PrimitivePop.elementQuery (freshIndex 0)) ∈ staleRootQueries :=
    List.mem_map.mpr ⟨_,List.mem_cons_of_mem _ (List.mem_map.mpr ⟨freshIndex 0,List.mem_cons_self,rfl⟩),rfl⟩
  have observed := (bad _ member).2.2 (w 0) (by rfl)
  change w 71 = w 0 at observed
  exact (by decide : w 71 ≠ w 0) observed

/-- The extra retained-source read/write is actual executable code, not an
inference from a failed logical read or a new source profile rule. -/
theorem stale_root_wrong_source_target :
    Evm.run (TargetOperations.copyCode (.data (.data (.root 1) 2) 0) (.data (.data (.root 0) 2) 0)) bothAfter =
      .ok { bothAfter with store := Evm.WordStore.write bothAfter.store (.data (.data (.root 1) 2) 0) 71 } 0 ∧
    (Evm.WordStore.write bothAfter.store (.data (.data (.root 1) 2) 0) 71).cells (.data (.data (.root 1) 2) 0) ≠
      TargetOperations.encodeWord (w 0) := by
  refine ⟨TargetOperations.run_copy _ _ _,?_⟩
  decide

/-- Whole-extent stale clearing would erase older61, which is part of the
MAIN represented ROOT query family, not merely an extra graph-only read. -/
theorem stale_root_whole_extent_negative : ¬ Represented (bothOldRoot.overlay bothSourceRoot) staleRootQueries (.root 1)
    (Representation.write (TargetNestedArrayTransport.afterStore bothStore (.root 1) (.root 0))
      (.data (.data (.root 1) 2) 2) (w 0)) := by
  intro bad
  have member : Query.prefix missingPath (PrimitivePop.elementQuery (freshIndex 2)) ∈ staleRootQueries :=
    List.mem_map.mpr ⟨_,List.mem_cons_of_mem _ (List.mem_map.mpr ⟨freshIndex 2,
      by simp only [freshIndices,List.mem_cons,true_or,or_true],rfl⟩),rfl⟩
  have observed := (bad _ member).2.2 (w 61) (by rfl)
  change w 0 = w 61 at observed
  exact (by decide : w 0 ≠ w 61) observed

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.stale_root_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms stale_root_bridge

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.stale_root_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms stale_root_ordered

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.stale_root_wrong_source_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms stale_root_wrong_source_tail

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.stale_root_wrong_source_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms stale_root_wrong_source_target

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.stale_root_whole_extent_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms stale_root_whole_extent_negative

private def shadowMemo : Value graph (.mapping .uint (.prim .uint)) := .mapping (fun _ => .present (.prim (w 91)))
private def shadowMapOld : Value graph (.array (.mapping .uint (.prim .uint))) :=
  .array ⟨2,by decide⟩ ⟨1,by decide⟩ (by decide) (fun i => if i.val = 0 then .present shadowMemo else .absent)
private def shadowMapSource : Value graph (.array (.mapping .uint (.prim .uint))) :=
  .array ⟨3,by decide⟩ ⟨0,by decide⟩ (by decide) (fun _ => .present (.mapping (fun _ => .present (.prim (w 42)))))
private def shadowMapPath (i : Index) : TypeGraph.Path graph (.array (.mapping .uint (.prim .uint))) (.mapping .uint (.prim .uint)) :=
  .cons (.index i) .nil
private def shadowMapWord (i : Index) : Query graph (.array (.mapping .uint (.prim .uint))) :=
  .word (.cons (.index i) (.cons (.key (w 5)) .nil))

/-- Generic endpoint laws have inhabited mapping/absent/default/failing controls.
Source retained42 is ignored; stale mapping91 survives the barrier. An absent
OLDER slot defaults logically, while out-of-extent failure remains None. This
internal meaning does not admit Solidity whole mapping assignments. -/
theorem stale_mapping_options :
    (shadowMapOld.overlay shadowMapSource).find (shadowMapPath (freshIndex 0)) = some shadowMemo ∧
    (shadowMapOld.overlay shadowMapSource).find (shadowMapPath (freshIndex 1)) = shadowMapOld.find (shadowMapPath (freshIndex 1)) ∧
    (shadowMapOld.overlay shadowMapSource).find (shadowMapPath shadowIndex) = none ∧
    (shadowMapWord (freshIndex 0)).read (shadowMapOld.overlay shadowMapSource) = some (w 91) ∧
    (shadowMapWord (freshIndex 1)).read (shadowMapOld.overlay shadowMapSource) = some (w 0) ∧
    (shadowMapWord shadowIndex).read (shadowMapOld.overlay shadowMapSource) = none ∧
    ((shadowMapPath (freshIndex 0)).readLive Value.dflt (shadowMapOld.overlay shadowMapSource)).isSome = false := by
  refine ⟨?_,?_,?_,rfl,rfl,rfl,rfl⟩
  · exact NestedStaleComposition.find_stale shadowMapOld shadowMapSource (freshIndex 0) (by decide) (by decide)
  · exact NestedStaleComposition.find_older shadowMapOld shadowMapSource (freshIndex 1) (by decide) (by decide)
  · exact (NestedStaleComposition.find_older shadowMapOld shadowMapSource shadowIndex (by decide) (by decide)).trans rfl

/-- Erasing the stale mapping would replace successful91 with default0.
Mapping barriers, rather than any raw default or Source-admission premise,
explain the correct retained observation. -/
theorem stale_mapping_erasure_negative :
    (shadowMapWord (freshIndex 0)).read
      (Value.array (G := graph) ⟨2,by decide⟩ ⟨0,by decide⟩ (by decide) (fun _ => .absent)) ≠
    (shadowMapWord (freshIndex 0)).read (shadowMapOld.overlay shadowMapSource) := by
  change some (w 0) ≠ some (w 91)
  decide

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.stale_mapping_options' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms stale_mapping_options
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.stale_mapping_erasure_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms stale_mapping_erasure_negative

private def olderHash (p : Solidity.Storage.Pre) : Nat := if p = .data 19 then 72 else hash p
private def olderPreimages := preimages ++ [Solidity.Storage.Pre.data 19]
private def olderLocations := locations ++ [Solidity.Storage.Loc.data (.root 1) 3,
  .data (.data (.root 1) 3) 0,.data (.data (.root 1) 3) 1,.data (.data (.root 1) 3) 2]
private theorem olderRun : FiniteRun 128 8 8 olderHash olderPreimages olderLocations := by
  constructor
  · intro p
    by_cases newPre : p = .data 19
    · simp only [olderHash,if_pos newPre]; decide
    · simp only [olderHash,if_neg newPre]; exact run.1 p
  · decide
  · decide
  · decide
  · intro l member
    simp only [olderLocations,locations,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with ( rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl ) | ( rfl | rfl | rfl | rfl ) <;> simp only [Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    simp only [olderLocations,locations,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with ( rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl ) | ( rfl | rfl | rfl | rfl ) <;> decide
private def olderUncovered : Solidity.Storage.Loc := .data (.root 0) 3
private def olderStore : Store := fun l =>
  if l = olderUncovered then w 99 else
  if l = .data (.root 1) 3 then w 1 else
  if l = .data (.data (.root 1) 3) 0 then w 91 else
  if l = .data (.data (.root 1) 3) 1 then w 93 else
  if l = .data (.data (.root 1) 3) 2 then w 95 else bothStore l
private def olderNumeric : WordStore := fun address =>
  if address = 11 then w 99 else
  if address = 19 then w 1 else
  if address = 72 then w 91 else
  if address = 73 then w 93 else
  if address = 74 then w 95 else bothNumeric address
private theorem olderInitial : Transport 128 olderHash olderLocations olderStore olderNumeric := by
  intro l member
  simp only [olderLocations,locations,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ( rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl ) | ( rfl | rfl | rfl | rfl ) <;> rfl
private def olderFitting : ∀ l ∈ olderLocations, TargetOperations.KeysFit l := by
  intro l member
  simp only [olderLocations,locations,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ( rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl ) | ( rfl | rfl | rfl | rfl ) <;> trivial
private def olderTarget : Evm.Machine := { bothTarget with
  store := .ofFn (fun slot => (TargetOperations.encodeWord (olderStore (Solidity.Storage.ofSlot slot))).val) }
private theorem olderTargetInitial : ∀ l (member : l ∈ olderLocations),
    olderTarget.store.cells (TargetOperations.toSlot l (olderFitting l member)) = TargetOperations.encodeWord (olderStore l) := by
  intro l member
  change Evm.wmod (TargetOperations.encodeWord (olderStore (Solidity.Storage.ofSlot (TargetOperations.toSlot l (olderFitting l member))))).val = _
  rw [TargetOperations.ofSlot_toSlot,Evm.wmod_of_lt (TargetOperations.encodeWord (olderStore l)).isLt]
private def olderArray : Value graph (.array (.prim .uint)) := .array ⟨3,by decide⟩ ⟨1,by decide⟩ (by decide)
  (fun i => .present (.prim (if i.val = 0 then w 91 else if i.val = 1 then w 93 else w 95)))
private def olderRoot : Value graph (.array (.array (.prim .uint))) := .array ⟨4,by decide⟩ ⟨3,by decide⟩ (by decide)
  (fun i => if i.val = 0 then .present firstRetained else if i.val = 1 then .present retainedChild else
    if i.val = 2 then .present staleChild else .present olderArray)
private def olderPath : TypeGraph.Path graph (.array (.array (.prim .uint))) (.array (.prim .uint)) :=
  NestedCopyObservations.childPath shadowIndex
private def olderQueries : List (Query graph (.array (.array (.prim .uint)))) :=
  (PrimitivePop.queries freshIndices).map (Query.prefix olderPath)
private theorem olderLeafOwner : Represented olderArray (PrimitivePop.queries freshIndices) (.data (.root 1) 3) olderStore := by
  intro q member
  simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 1) = some word at found; cases found; rfl
  · refine ⟨by change 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 91) = some word at found; cases found; rfl
  · refine ⟨by change 1 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 93) = some word at found; cases found; rfl
  · refine ⟨by change 2 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 95) = some word at found; cases found; rfl
private theorem olderBeforeRoot : Represented olderRoot olderQueries (.root 1) olderStore :=
  Represented.prefix olderPath (by rfl) (by change 3 < lmax ∧ True; decide) olderLeafOwner
private theorem olderHeader : Represented olderRoot [.length .nil] (.root 1) olderStore := by
  intro q member
  have same := List.mem_singleton.mp member; subst q
  refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
  intro word found; change some (w 3) = some word at found; cases found; rfl
private theorem olderSourceHeader : Represented bothSourceRoot [.length .nil] (.root 0) olderStore := by
  intro q member
  have same := List.mem_singleton.mp member; subst q
  refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
  intro word found; change some (w 2) = some word at found; cases found; rfl
private def olderAfter := TargetNestedArrayRuntime.afterCopy olderTarget tail (.root 0) (.root 1)

/-- Actual OLD and NEW finite regions are inhabited separately. This is an
explicit local model extension, never global hash injectivity or an inferred
extension of the original25-location run. Missing source child raw99 is outside. -/
theorem older_region_witness :
    FiniteRun 128 8 8 olderHash olderPreimages olderLocations ∧
    Transport 128 olderHash olderLocations olderStore olderNumeric ∧
    olderUncovered ∉ olderLocations ∧ olderStore olderUncovered = w 99 := by
  exact ⟨olderRun,olderInitial,by decide,rfl⟩

/-- Full actual runtime program preserves a selected OUTER older child with
live inner payload91 and retained93/95. Source child3 is absent logically; no
source-child relation or raw-default premise is supplied to the theorem. -/
theorem older_root_bridge :
    Evm.run TargetNestedArrayCopy.code { olderTarget with stack := .slot (.root 0) :: .slot (.root 1) :: tail } = .ok olderAfter 0 ∧
    Represented (olderRoot.overlay bothSourceRoot) olderQueries (.root 1)
      (TargetNestedArrayTransport.afterStore olderStore (.root 1) (.root 0)) ∧
    Transport 128 olderHash olderLocations (TargetNestedArrayTransport.afterStore olderStore (.root 1) (.root 0))
      (TargetNestedArrayTransport.execute 128 olderHash olderNumeric (.root 1) (.root 0)) ∧
    (∀ l (member : l ∈ olderLocations), olderAfter.store.cells (TargetOperations.toSlot l (olderFitting l member)) =
      TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore olderStore (.root 1) (.root 0) l)) := by
  refine NestedOlderComposition.older_child olderRun olderRoot bothSourceRoot shadowIndex freshIndices (by decide) (by decide) (by decide)
    (.root 1) (.root 0) (by trivial) (by trivial) olderStore olderNumeric olderTarget tail olderInitial olderFitting olderTargetInitial
    olderBeforeRoot olderHeader olderSourceHeader (by decide) (by decide) ?_ ?_ ?_ ?_ ?_ ?_
  · intro k inside
    change k < 2 at inside
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl <;> decide
  · exact forall_bounded_pair (by decide)
  · exact forall_bounded_pair (by decide)
  · intro k inside begun
    change k < 3 at inside
    change 2 ≤ k at begun
    have same : k = 2 := by omega
    subst k; decide
  · intro k inside begun j live
    change k < 3 at inside
    change 2 ≤ k at begun
    have same : k = 2 := by omega
    subst k
    change j < 2 at live
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with rfl | rfl <;> decide
  · intro q member
    simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.older_region_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms older_region_witness
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.older_root_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms older_root_bridge

private def olderSymbolicView (m : Store) := olderLocations.map m
private def olderNumericView (m : WordStore) := olderLocations.map (fun l => m (l.word 128 olderHash))
private def olderTargetView (m : Evm.Machine) := olderLocations.attach.map (fun l => m.store (TargetOperations.toSlot l.val (olderFitting l.val l.property)))

/-- COMPLETE new29-location vectors and the explicitly uncovered source99.
ALL selected older header/live/shadow queries stay successful, while Source
absence and retained non-live path observations remain distinct. -/
theorem older_root_ordered :
    (olderSymbolicView olderStore,
      olderSymbolicView (TargetNestedArrayTransport.copyStores olderStore (.root 1) (.root 0) 2),
      olderSymbolicView (TargetNestedArrayTransport.afterStore olderStore (.root 1) (.root 0)),
      olderNumericView (TargetNestedArrayTransport.execute 128 olderHash olderNumeric (.root 1) (.root 0)),
      olderTargetView olderAfter,context olderAfter,
      olderQueries.map (fun q => q.read olderRoot),olderQueries.map (fun q => q.read (olderRoot.overlay bothSourceRoot)),
      (olderRoot.find olderPath).isSome,(bothSourceRoot.find olderPath).isSome,
      (olderPath.readLive Value.dflt olderRoot).isSome,(olderPath.readLive Value.dflt (olderRoot.overlay bothSourceRoot)).isSome,
      olderStore olderUncovered,TargetNestedArrayTransport.afterStore olderStore (.root 1) (.root 0) olderUncovered,
      olderNumeric (olderUncovered.word 128 olderHash),TargetNestedArrayTransport.execute 128 olderHash olderNumeric (.root 1) (.root 0) (olderUncovered.word 128 olderHash),
      olderTarget.store (.data (.root 0) 3),olderAfter.store (.data (.root 0) 3)) =
    ([w 2,w 3,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 3,w 23,w 29,w 31,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73,w 1,w 91,w 93,w 95],
     [w 2,w 3,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73,w 1,w 91,w 93,w 95],
     [w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 0,w 0,w 0,w 61,w 73,w 1,w 91,w 93,w 95],
     [w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 0,w 0,w 0,w 61,w 73,w 1,w 91,w 93,w 95],
     [2,2,1,7,11,13,1,17,19,1,71,1,7,0,0,37,1,17,0,47,0,0,0,61,73,1,91,93,95],context olderTarget,
     [some (w 1),some (w 91),some (w 93),some (w 95)],[some (w 1),some (w 91),some (w 93),some (w 95)],
     true,false,false,false,w 99,w 99,w 99,w 99,99,99) := by rfl

/-- Treating the absent source child as permission to read its raw99 would
corrupt the unchanged older destination header, despite correct root header2. -/
theorem older_wrong_source_copy : ¬ Represented (olderRoot.overlay bothSourceRoot) olderQueries (.root 1)
    (Representation.write (TargetNestedArrayTransport.afterStore olderStore (.root 1) (.root 0)) (.data (.root 1) 3) (w 99)) := by
  intro bad
  have member : Query.prefix olderPath (.length .nil) ∈ olderQueries := List.mem_map.mpr ⟨_,List.mem_cons_self,rfl⟩
  have observed := (bad _ member).2.2 (w 1) (by rfl)
  change w 99 = w 1 at observed
  exact (by decide : w 99 ≠ w 1) observed

/-- The wrong extra SLOAD/SSTORE reads an actual nonzero raw word outside the
certified run. Its executable result is NOT a certified numeric/frame premise. -/
theorem older_wrong_source_target :
    Evm.run (TargetOperations.copyCode (.data (.root 1) 3) (.data (.root 0) 3)) olderAfter =
      .ok { olderAfter with store := Evm.WordStore.write olderAfter.store (.data (.root 1) 3) 99 } 0 ∧
    (Evm.WordStore.write olderAfter.store (.data (.root 1) 3) 99).cells (.data (.root 1) 3) ≠ TargetOperations.encodeWord (w 1) := by
  refine ⟨TargetOperations.run_copy _ _ _,?_⟩
  decide

/-- Clearing past OLD live length into the older OUTER extent is wrong even
if that child has a live inner prefix. Its OLD header1 is a selected ROOT read. -/
theorem older_wrong_outer_clear_owner : ¬ Represented (olderRoot.overlay bothSourceRoot) olderQueries (.root 1)
    (TargetNestedArrayTransport.clearStore (TargetNestedArrayTransport.afterStore olderStore (.root 1) (.root 0)) (.data (.root 1) 3)) := by
  intro bad
  have member : Query.prefix olderPath (.length .nil) ∈ olderQueries := List.mem_map.mpr ⟨_,List.mem_cons_self,rfl⟩
  have observed := (bad _ member).2.2 (w 1) (by rfl)
  change w 0 = w 1 at observed
  exact (by decide : w 0 ≠ w 1) observed

/-- Actual extra child clear changes the older header/live91, while its inner
shadows remain. This distinguishes wrong OUTER live extent from inner extent. -/
theorem older_wrong_outer_clear_target :
    Evm.run TargetArrayClear.code { olderAfter with stack := .slot (.data (.root 1) 3) :: tail } =
      .ok (TargetArrayClear.afterClear olderAfter tail (.data (.root 1) 3)) 0 ∧
    ((TargetArrayClear.afterClear olderAfter tail (.data (.root 1) 3)).store (.data (.root 1) 3),
      (TargetArrayClear.afterClear olderAfter tail (.data (.root 1) 3)).store (.data (.data (.root 1) 3) 0),
      (TargetArrayClear.afterClear olderAfter tail (.data (.root 1) 3)).store (.data (.data (.root 1) 3) 1),
      (TargetArrayClear.afterClear olderAfter tail (.data (.root 1) 3)).store (.data (.data (.root 1) 3) 2)) = (0,0,93,95) := by
  exact ⟨TargetArrayClear.run_current olderAfter tail (.data (.root 1) 3),rfl⟩

/-- Erasing inner older95 also falsifies a MAIN represented ROOT query. -/
theorem older_wrong_retained_clear : ¬ Represented (olderRoot.overlay bothSourceRoot) olderQueries (.root 1)
    (Representation.write (TargetNestedArrayTransport.afterStore olderStore (.root 1) (.root 0)) (.data (.data (.root 1) 3) 2) (w 0)) := by
  intro bad
  have member : Query.prefix olderPath (PrimitivePop.elementQuery (freshIndex 2)) ∈ olderQueries :=
    List.mem_map.mpr ⟨_,List.mem_cons_of_mem _ (List.mem_map.mpr ⟨freshIndex 2,
      by simp only [freshIndices,List.mem_cons,true_or,or_true],rfl⟩),rfl⟩
  have observed := (bad _ member).2.2 (w 95) (by rfl)
  change w 0 = w 95 at observed
  exact (by decide : w 0 ≠ w 95) observed

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.older_root_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms older_root_ordered

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.older_wrong_source_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms older_wrong_source_copy

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.older_wrong_source_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms older_wrong_source_target

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.older_wrong_outer_clear_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms older_wrong_outer_clear_owner

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.older_wrong_outer_clear_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms older_wrong_outer_clear_target

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.older_wrong_retained_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms older_wrong_retained_clear

private def freshExtraSource : Solidity.Storage.Loc := .data (.data (.root 0) 1) 2
private def freshStore : Store := Representation.write (Representation.write accessStore (.root 1) (w 0)) freshExtraSource (w 89)
private def freshNumeric : WordStore := writeWord (writeWord accessNumeric 1 (w 0)) 34 (w 89)
private theorem freshInitial : Transport 128 hash locations freshStore freshNumeric := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private def freshTarget : Evm.Machine := { accessTarget with
  store := .ofFn (fun slot => (TargetOperations.encodeWord (freshStore (Solidity.Storage.ofSlot slot))).val) }
private theorem freshTargetInitial : ∀ l (member : l ∈ locations),
    freshTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (freshStore l) := by
  intro l member
  change Evm.wmod (TargetOperations.encodeWord (freshStore (Solidity.Storage.ofSlot (TargetOperations.toSlot l (fitting l member))))).val = _
  rw [TargetOperations.ofSlot_toSlot,Evm.wmod_of_lt (TargetOperations.encodeWord (freshStore l)).isLt]
private def freshOldRoot : Value graph (.array (.array (.prim .uint))) := Value.dflt _
private def freshSourceB : Value graph (.array (.prim .uint)) := .array ⟨3,by decide⟩ ⟨1,by decide⟩ (by decide)
  (fun i => .present (.prim (if i.val = 0 then w 17 else if i.val = 1 then w 19 else w 89)))
private def freshSourceRoot : Value graph (.array (.array (.prim .uint))) := .array ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide)
  (fun i => if i.val = 0 then .present retainedSourceShadow else if i.val = 1 then .present freshSourceB else .present sourceOlderChild)
private theorem freshOldHeader : Represented freshOldRoot [.length .nil] (.root 1) freshStore := by
  intro q member
  have same := List.mem_singleton.mp member; subst q
  refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
  intro word found; change some (w 0) = some word at found; cases found; rfl
private theorem freshSourceHeader : Represented freshSourceRoot [.length .nil] (.root 0) freshStore := by
  intro q member
  have same := List.mem_singleton.mp member; subst q
  refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
  intro word found; change some (w 2) = some word at found; cases found; rfl
private theorem freshSourceReads : Represented freshSourceB (CopyAccess.readQueries freshSourceB freshIndices) (.data (.root 0) 1) freshStore := by
  change Represented freshSourceB [Query.length .nil,PrimitivePop.elementQuery (freshIndex 0)] (.data (.root 0) 1) freshStore
  intro q member
  rcases List.mem_cons.mp member with rfl | inside
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 1) = some word at found; cases found; rfl
  · have same := List.mem_singleton.mp inside; subst q
    refine ⟨by change 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 17) = some word at found; cases found; rfl
private theorem freshBeforeSource : Represented freshSourceRoot
    ((CopyAccess.readQueries (NestedCopyObservations.child freshSourceRoot (freshIndex 1)) freshIndices).map
      (Query.prefix (NestedCopyObservations.childPath (freshIndex 1)))) (.root 0) freshStore :=
  Represented.prefix retainedPath (by rfl) (by change 1 < lmax ∧ True; decide) freshSourceReads
private def freshQueries := NestedRootComposition.rootQueries (G := graph) (p := .uint) [freshIndex 1] (fun _ => freshIndices)
private def freshPrefix := TargetNestedArrayTransport.copyStores freshStore (.root 1) (.root 0) 1
private def freshPrefixTarget := TargetNestedArrayCopyLoop.prefixMachine freshTarget (.root 0) (.root 1) 1
private def freshAfter := TargetNestedArrayRuntime.afterCopy freshTarget tail (.root 0) (.root 1)

private theorem freshChildBridge :
    Evm.run TargetNestedArrayCopy.code { freshTarget with stack := .slot (.root 0) :: .slot (.root 1) :: tail } = .ok freshAfter 0 ∧
    Represented (freshOldRoot.overlay freshSourceRoot) ((PrimitivePop.queries freshIndices).map (Query.prefix retainedPath)) (.root 1)
      (TargetNestedArrayTransport.afterStore freshStore (.root 1) (.root 0)) ∧
    Transport 128 hash locations (TargetNestedArrayTransport.afterStore freshStore (.root 1) (.root 0))
      (TargetNestedArrayTransport.execute 128 hash freshNumeric (.root 1) (.root 0)) ∧
    (∀ l (member : l ∈ locations), freshAfter.store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore freshStore (.root 1) (.root 0) l)) := by
  refine NestedFreshComposition.fresh_child run freshOldRoot freshSourceRoot (freshIndex 1) freshIndices (by decide) (by decide)
    (.root 1) (.root 0) (by trivial) (by trivial) freshStore freshNumeric freshTarget tail freshInitial fitting freshTargetInitial
    freshBeforeSource ?_ ?_ ?_ ?_ ?_ ?_ ?_ freshSourceHeader (by decide) (by decide) ?_ ?_ ?_
  · intro k inside
    change k < 2 at inside
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl <;> decide
  · exact forall_bounded_pair (by decide)
  · exact forall_bounded_pair (by decide)
  · intro j member
    simp only [freshIndices,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro j live
    change j < 1 at live
    have same : j = 0 := by omega
    subst j; decide
  · intro j live
    change j < 2 at live
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with rfl | rfl <;> decide
  · intro q member
    simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · trivial
    · change 0 < lmax ∧ True; decide
    · change 1 < lmax ∧ True; decide
    · change 2 < lmax ∧ True; decide
  · intro k inside begun
    change k < 2 at inside
    change 2 ≤ k at begun
    omega
  · intro k inside begun j live
    change k < 2 at inside
    change 2 ≤ k at begun
    omega
  · intro q member
    change q ∈ [Query.length .nil,PrimitivePop.elementQuery (freshIndex 0)] at member
    rcases List.mem_cons.mp member with rfl | inside
    · change Evm.Slot.data (.root 0) 1 ∉ TargetNestedArrayCopyLoop.touched freshTarget (.root 0) (.root 1) 1
      decide
    · have same := List.mem_singleton.mp inside; subst q
      change Evm.Slot.data (.data (.root 0) 1) 0 ∉ TargetNestedArrayCopyLoop.touched freshTarget (.root 0) (.root 1) 1
      decide

/-- A fresh copied child and the independently derived root header give a
MAIN ROOT owner; no initial destination default/zero relation is used. -/
theorem fresh_root_bridge :
    Evm.run TargetNestedArrayCopy.code { freshTarget with stack := .slot (.root 0) :: .slot (.root 1) :: tail } = .ok freshAfter 0 ∧
    Represented (freshOldRoot.overlay freshSourceRoot) freshQueries (.root 1)
      (TargetNestedArrayTransport.afterStore freshStore (.root 1) (.root 0)) ∧
    Transport 128 hash locations (TargetNestedArrayTransport.afterStore freshStore (.root 1) (.root 0))
      (TargetNestedArrayTransport.execute 128 hash freshNumeric (.root 1) (.root 0)) ∧
    (∀ l (member : l ∈ locations), freshAfter.store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore freshStore (.root 1) (.root 0) l)) := by
  refine ⟨freshChildBridge.1,?_,freshChildBridge.2.2⟩
  intro q member
  change q ∈ Query.length .nil :: (PrimitivePop.queries freshIndices).map (Query.prefix retainedPath) at member
  rcases List.mem_cons.mp member with rfl | inside
  · exact NestedRootComposition.root_header freshOldRoot freshSourceRoot (.root 1) (.root 0) freshStore freshOldHeader freshSourceHeader _ List.mem_cons_self
  · exact freshChildBridge.2.1 q inside

/-- Logical absence with a NONZERO current raw header refutes manufacturing
an OLD full default-child relation; the new actual certificate needs none. -/
theorem fresh_not_old_default :
    freshOldRoot.find retainedPath = none ∧ freshPrefix (.data (.root 1) 1) = w 2 ∧
    freshExtraSource ∉ locations ∧
    (PrimitivePop.elementQuery (freshIndex 2)).read freshSourceB = some (w 89) ∧
    ¬ Represented (Value.dflt (.array (.prim .uint)) : Value graph _) [.length .nil] (.data (.root 1) 1) freshPrefix := by
  refine ⟨rfl,rfl,by decide,rfl,?_⟩
  intro bad
  have observed := (bad (.length .nil) List.mem_cons_self).2.2 (w 0) (by rfl)
  change w 2 = w 0 at observed
  exact (by decide : w 2 ≠ w 0) observed

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.fresh_root_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_root_bridge
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.fresh_not_old_default' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_not_old_default

private theorem freshPrefixInput :
    Transport 128 hash locations freshPrefix (TargetNestedArrayTransport.copyNumerics 128 hash freshNumeric (.root 1) (.root 0) 1) ∧
    (∀ l (member : l ∈ locations), freshPrefixTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (freshPrefix l)) := by
  refine TargetNestedArrayTransport.copy_prefix run (.root 1) (.root 0) (by trivial) (by trivial)
    freshStore freshNumeric freshTarget 1 freshInitial fitting freshTargetInitial ?_ ?_ ?_
  · intro k inside
    have same : k = 0 := by omega
    subst k; decide
  · intro k inside j live
    have same : k = 0 := by omega
    subst k
    change j < 1 at live
    have same : j = 0 := by omega
    subst j; decide
  · intro k inside j live
    have same : k = 0 := by omega
    subst k
    change j < 3 at live
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with rfl | rfl | rfl <;> decide
private theorem freshSnapshot : Represented freshSourceB (CopyAccess.readQueries freshSourceB freshIndices) (.data (.root 0) 1) freshPrefix := by
  change Represented freshSourceB [Query.length .nil,PrimitivePop.elementQuery (freshIndex 0)] (.data (.root 0) 1) freshPrefix
  intro q member
  rcases List.mem_cons.mp member with rfl | inside
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 1) = some word at found; cases found; rfl
  · have same := List.mem_singleton.mp inside; subst q
    refine ⟨by change 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 17) = some word at found; cases found; rfl
private def freshPrimitiveAfter := TargetArrayCopyTail.afterCopy freshPrefixTarget tail (.data (.root 0) 1) (.data (.root 1) 1)

/-- APPLY the headline primitive complete certificate to the actual changed
prefix inputs; no OLD destination default owner is constructible here. -/
theorem fresh_primitive_bridge :
    Evm.run TargetArrayCopy.code { freshPrefixTarget with stack := .slot (.data (.root 0) 1) :: .slot (.data (.root 1) 1) :: tail } = .ok freshPrimitiveAfter 0 ∧
    Represented freshSourceB.strip (PrimitivePop.queries freshIndices) (.data (.root 1) 1)
      (CopyTransport.symbolicCopy (.data (.root 1) 1) (.data (.root 0) 1) freshPrefix) ∧
    Transport 128 hash locations (CopyTransport.symbolicCopy (.data (.root 1) 1) (.data (.root 0) 1) freshPrefix)
      (NumericTraversal.copy 128 hash (.data (.root 1) 1) (.data (.root 0) 1)
        (TargetNestedArrayTransport.copyNumerics 128 hash freshNumeric (.root 1) (.root 0) 1)) ∧
    (∀ l (member : l ∈ locations), freshPrimitiveAfter.store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (CopyTransport.symbolicCopy (.data (.root 1) 1) (.data (.root 0) 1) freshPrefix l)) := by
  refine FreshCopyAccess.complete run freshSourceB freshIndices (.data (.root 1) 1) (.data (.root 0) 1)
    (by trivial) (by trivial) freshPrefix (TargetNestedArrayTransport.copyNumerics 128 hash freshNumeric (.root 1) (.root 0) 1)
    freshPrefixTarget tail freshSnapshot ?_ freshPrefixInput.1 fitting freshPrefixInput.2 (by decide) (by decide) ?_ ?_ ?_
  · intro q member
    simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · trivial
    · change 0 < lmax ∧ True; decide
    · change 1 < lmax ∧ True; decide
    · change 2 < lmax ∧ True; decide
  · intro i member
    simp only [freshIndices,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro j live
    change j < 1 at live
    have same : j = 0 := by omega
    subst j; decide
  · intro j live
    change j < 2 at live
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with rfl | rfl <;> decide

/-- COMPLETE25-point old/first/final physical observations plus BOTH unread
source tails83/89. Logical fresh None coexists with physical older47; no
initial zero/default relation or None=>rawzero/frame inference is used. -/
theorem fresh_root_ordered :
    (symbolicView freshStore,symbolicView freshPrefix,
      symbolicView (TargetNestedArrayTransport.afterStore freshStore (.root 1) (.root 0)),
      numericView (TargetNestedArrayTransport.execute 128 hash freshNumeric (.root 1) (.root 0)),
      targetView freshAfter,context freshAfter,
      freshQueries.map (fun q => q.read freshOldRoot),freshQueries.map (fun q => q.read (freshOldRoot.overlay freshSourceRoot)),
      (retainedPath.readLive Value.dflt freshOldRoot).isSome,(retainedPath.readLive Value.dflt (freshOldRoot.overlay freshSourceRoot)).isSome,
      (PrimitivePop.elementQuery (freshIndex 2)).read freshSourceB,
      freshStore accessSourceLocation,TargetNestedArrayTransport.afterStore freshStore (.root 1) (.root 0) accessSourceLocation,
      freshNumeric (accessSourceLocation.word 128 hash),TargetNestedArrayTransport.execute 128 hash freshNumeric (.root 1) (.root 0) (accessSourceLocation.word 128 hash),
      freshTarget.store (.data (.data (.root 0) 0) 3),freshAfter.store (.data (.data (.root 0) 0) 3),
      freshStore freshExtraSource,TargetNestedArrayTransport.afterStore freshStore (.root 1) (.root 0) freshExtraSource,
      freshNumeric (freshExtraSource.word 128 hash),TargetNestedArrayTransport.execute 128 hash freshNumeric (.root 1) (.root 0) (freshExtraSource.word 128 hash),
      freshTarget.store (.data (.data (.root 0) 1) 2),freshAfter.store (.data (.data (.root 0) 1) 2)) =
    ([w 2,w 0,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 3,w 23,w 29,w 31,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 0,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
     [2,2,1,7,11,13,1,17,19,1,71,1,7,0,0,37,1,17,0,47,2,53,59,61,73],context freshTarget,
     [some (w 0),none,none,none,none],[some (w 2),some (w 1),some (w 17),none,none],false,true,some (w 89),
     w 83,w 83,w 83,w 83,83,83,w 89,w 89,w 89,w 89,89,89) := by rfl

private def freshWrongSkip : Evm.Machine :=
  { freshPrefixTarget with
    store := Evm.WordStore.write
      (Evm.WordStore.write freshPrefixTarget.store (.data (.data (.root 1) 1) 0) 17) (.data (.root 1) 1) 1 }

/-- Pretending OLD raw header0 skips the necessary physical tail clear. This
wrong executable code has correct NEW header/live17 but leaves43 instead of0. -/
theorem fresh_wrong_skip_clear :
    Evm.run (TargetOperations.copyCode (.data (.data (.root 1) 1) 0) (.data (.data (.root 0) 1) 0) ++
      TargetOperations.writeCode (.data (.root 1) 1) (w 1)) freshPrefixTarget = .ok freshWrongSkip 0 ∧
    (freshWrongSkip.store (.data (.root 1) 1),freshWrongSkip.store (.data (.data (.root 1) 1) 0),
      freshWrongSkip.store (.data (.data (.root 1) 1) 1),freshPrimitiveAfter.store (.data (.data (.root 1) 1) 1)) = (1,17,43,0) := by
  exact ⟨rfl,rfl⟩

/-- An extra actual read of source89 wrongly replaces physical older47. The
logical output query is None, so this counterexample concerns the explicit
physical operation contract, not a manufactured represented word at None. -/
theorem fresh_wrong_extra_tail :
    Evm.run (TargetOperations.copyCode (.data (.data (.root 1) 1) 2) (.data (.data (.root 0) 1) 2)) freshAfter =
      .ok { freshAfter with store := Evm.WordStore.write freshAfter.store (.data (.data (.root 1) 1) 2) 89 } 0 ∧
    (freshAfter.store (.data (.data (.root 1) 1) 2),
      (Evm.WordStore.write freshAfter.store (.data (.data (.root 1) 1) 2) 89) (.data (.data (.root 1) 1) 2)) = (47,89) := by
  exact ⟨TargetOperations.run_copy _ _ _,rfl⟩

/-- PUBLIC selected representation alone does not pin a failed query's raw
word. Even wrong raw89 at this fresh None query satisfies that relation;
the separate numeric/target operation certificate rejects the extra write. -/
theorem fresh_none_does_not_pin_raw_tail : Represented (freshOldRoot.overlay freshSourceRoot) freshQueries (.root 1)
    (Representation.write (TargetNestedArrayTransport.afterStore freshStore (.root 1) (.root 0)) (.data (.data (.root 1) 1) 2) (w 89)) := by
  intro q member
  have before := fresh_root_bridge.2.1 q member
  refine ⟨before.1,before.2.1,?_⟩
  intro word observed
  change q ∈ Query.length .nil :: (PrimitivePop.queries freshIndices).map (Query.prefix retainedPath) at member
  simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · rw [Representation.write_other _ _ _ _ (by decide)]
    exact before.2.2 word observed
  · rw [Representation.write_other _ _ _ _ (by decide)]
    exact before.2.2 word observed
  · rw [Representation.write_other _ _ _ _ (by decide)]
    exact before.2.2 word observed
  · change (none : Option Semantics.Word) = some word at observed
    cases observed
  · change (none : Option Semantics.Word) = some word at observed
    cases observed

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.fresh_primitive_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_primitive_bridge

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.fresh_root_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_root_ordered

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.fresh_wrong_skip_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_wrong_skip_clear

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.fresh_wrong_extra_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_wrong_extra_tail

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.fresh_none_does_not_pin_raw_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_none_does_not_pin_raw_tail

/-- Retained Source Some89 is not live; fresh logical None coexists with raw47.
These distinct observations rule out both Source-tail copying and raw-zero
claims based solely on failed logical queries. -/
theorem fresh_live_retained_distinction :
    (PrimitivePop.elementQuery (freshIndex 2)).read freshSourceB = some (w 89) ∧
    ((.cons (.index (freshIndex 2)) .nil : TypeGraph.Path graph (.array (.prim .uint)) (.prim .uint)).readLive Value.dflt freshSourceB) = none ∧
    (PrimitivePop.elementQuery (freshIndex 2)).read freshSourceB.strip = none ∧
    freshPrimitiveAfter.store (.data (.data (.root 1) 1) 2) = 47 := by
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.fresh_live_retained_distinction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_live_retained_distinction


-- C81: a single growth run has retained child0 AND genuinely missing child1.
private def mixedOldRoot : Value graph (.array (.array (.prim .uint))) :=
  .array ⟨1,by decide⟩ ⟨1,by decide⟩ (by decide) (fun _ => .present firstRetained)
private def mixedChildren : List Index := [freshIndex 0,freshIndex 1]
private def mixedIndices (i : Index) : List Index := if i.val = 0 then accessIndices else freshIndices
private def mixedQueries := NestedRootComposition.rootQueries (G := graph) (p := .uint) mixedChildren mixedIndices
private def mixedReads := RootCopyAccess.sourceQueries accessSourceRoot mixedChildren mixedIndices
private theorem mixedHeader : Represented mixedOldRoot [.length .nil] (.root 1) accessStore := by
  intro q member
  have same := List.mem_singleton.mp member; subst q
  refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
  intro word found; change some (w 1) = some word at found; cases found; rfl
private theorem mixedSourceOwner : Represented accessSourceRoot mixedReads (.root 0) accessStore := by
  intro q member
  change q ∈ Query.length .nil ::
    ((CopyAccess.readQueries retainedSourceShadow accessIndices).map (Query.prefix firstPath) ++
     (CopyAccess.readQueries innerB freshIndices).map (Query.prefix retainedPath)) at member
  rcases List.mem_cons.mp member with rfl | inside
  · exact accessSourceOwner _ List.mem_cons_self
  · rcases List.mem_append.mp inside with left | right
    · exact (Represented.prefix firstPath (by rfl : accessSourceRoot.find firstPath = some retainedSourceShadow)
        (by change 0 < lmax ∧ True; decide) retainedSourceReads) q left
    · exact (Represented.prefix retainedPath (by rfl : accessSourceRoot.find retainedPath = some innerB)
        (by change 1 < lmax ∧ True; decide) laterBeforeSrc) q right

/-- A non-vacuous combined owner: OLD extent1 separates retained child0 from
fresh child1; actual raw child1 header2/41/43/47 needs real stale-tail clearing. -/
theorem mixed_growth_bridge :
    Evm.run TargetNestedArrayCopy.code { accessTarget with stack := .slot (.root 0) :: .slot (.root 1) :: tail } = .ok accessRootAfter 0 ∧
    Represented (mixedOldRoot.overlay accessSourceRoot) mixedQueries (.root 1)
      (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0)) ∧
    Transport 128 hash locations (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0))
      (TargetNestedArrayTransport.execute 128 hash accessNumeric (.root 1) (.root 0)) ∧
    (∀ l (member : l ∈ locations), accessRootAfter.store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0) l)) := by
  refine MixedLiveComposition.live_root run mixedOldRoot accessSourceRoot mixedChildren mixedIndices ?_
    (.root 1) (.root 0) (by trivial) (by trivial) accessStore accessNumeric accessTarget tail accessInitial fitting accessTargetInitial
    mixedHeader ?_ mixedSourceOwner (by decide) (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i member
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> decide
  · intro i member retained
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Represented.prefix firstPath (by rfl : mixedOldRoot.find firstPath = some firstRetained)
        (by change 0 < lmax ∧ True; decide) accessBeforeDst
    · change 1 < 1 at retained; omega
  · intro k inside
    change k < 2 at inside
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl <;> decide
  · exact forall_bounded_pair (by decide)
  · exact forall_bounded_pair (by decide)
  · intro k inside begun
    change k < 2 at inside; change 2 ≤ k at begun; omega
  · intro k inside begun j live
    change k < 2 at inside; change 2 ≤ k at begun; omega
  · intro i member j inside
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · change j ∈ accessIndices at inside
      simp only [accessIndices,List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl <;> decide
    · change j ∈ freshIndices at inside
      simp only [freshIndices,List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with rfl | rfl | rfl <;> decide
  · intro i member j live
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> change j < 1 at live
    all_goals have same : j = 0 := by omega
    all_goals subst j; decide
  · intro i member retained j live
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · change j < 3 at live
      have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases casesJ with rfl | rfl | rfl <;> decide
    · change 1 < 1 at retained; omega
  · intro i member missing j live
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · change 1 ≤ 0 at missing; omega
    · change j < 2 at live
      have casesJ : j = 0 ∨ j = 1 := by omega
      rcases casesJ with rfl | rfl <;> decide
  · intro i member missing q observation
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · change 1 ≤ 0 at missing; omega
    · change q ∈ PrimitivePop.queries freshIndices at observation
      simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at observation
      rcases observation with rfl | rfl | rfl | rfl
      · trivial
      · change 0 < lmax ∧ True; decide
      · change 1 < lmax ∧ True; decide
      · change 2 < lmax ∧ True; decide
  · intro i member retained q observation
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact List.not_mem_nil
    · change 1 < 1 at retained; omega
  · intro i member q observation
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact List.not_mem_nil
    · change q ∈ [Query.length .nil,PrimitivePop.elementQuery (freshIndex 0)] at observation
      rcases List.mem_cons.mp observation with rfl | inside
      · change Evm.Slot.data (.root 0) 1 ∉ TargetNestedArrayCopyLoop.touched accessTarget (.root 0) (.root 1) 1
        decide
      · have same := List.mem_singleton.mp inside; subst q
        change Evm.Slot.data (.data (.root 0) 1) 0 ∉ TargetNestedArrayCopyLoop.touched accessTarget (.root 0) (.root 1) 1
        decide

/-- Complete ordered old/prefix/final symbolic/numeric/target vectors/context,
all old/output/source query outcomes, and both actual branch witnesses. -/
theorem mixed_growth_ordered :
    (symbolicView accessStore,symbolicView accessAfterStore,
      symbolicView (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0)),
      numericView (TargetNestedArrayTransport.execute 128 hash accessNumeric (.root 1) (.root 0)),
      targetView accessRootAfter,context accessRootAfter,
      mixedQueries.map (fun q => q.read mixedOldRoot),
      mixedQueries.map (fun q => q.read (mixedOldRoot.overlay accessSourceRoot)),
      mixedReads.map (fun q => q.read accessSourceRoot),
      (freshIndex 0).val < mixedOldRoot.extent.val,mixedOldRoot.extent.val ≤ (freshIndex 1).val,
      mixedOldRoot.find retainedPath,accessStore (.data (.root 1) 1)) =
    ([w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 3,w 23,w 29,w 31,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
     [2,2,1,7,11,13,1,17,19,1,71,1,7,0,0,37,1,17,0,47,2,53,59,61,73],context accessTarget,
     [some (w 1),some (w 3),some (w 23),some (w 29),some (w 31),some (w 37),none,none,none,none],
     [some (w 2),some (w 1),some (w 7),some (w 0),some (w 0),some (w 37),some (w 1),some (w 17),none,none],
     [some (w 2),some (w 1),some (w 7),some (w 1),some (w 17)],True,True,none,w 2) := by
  have retained : ((freshIndex 0).val < mixedOldRoot.extent.val) = True := propext ⟨fun _ => True.intro,fun _ => by decide⟩
  have missing : (mixedOldRoot.extent.val ≤ (freshIndex 1).val) = True := propext ⟨fun _ => True.intro,fun _ => by decide⟩
  rw [retained,missing]
  rfl

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.mixed_growth_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mixed_growth_bridge
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.mixed_growth_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mixed_growth_ordered


/-- Misclassifying retained child0 as fresh erases its successful shadow37. -/
theorem mixed_wrong_fresh : ¬ Represented (mixedOldRoot.overlay accessSourceRoot) mixedQueries (.root 1)
    (Representation.write (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0))
      (.data (.data (.root 1) 0) 3) (w 0)) := by
  intro bad
  have member : Query.prefix firstPath (PrimitivePop.elementQuery shadowIndex) ∈ mixedQueries := by
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨freshIndex 0,List.mem_cons_self,
      List.mem_map.mpr ⟨PrimitivePop.elementQuery shadowIndex,
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨shadowIndex,by change shadowIndex ∈ accessIndices; simp only [accessIndices,List.mem_cons,true_or,or_true],rfl⟩),rfl⟩⟩)
  have observed := (bad _ member).2.2 (w 37) (by rfl)
  change w 0 = w 37 at observed
  exact (by decide : w 0 ≠ w 37) observed

/-- Misclassifying fresh child1 as OLD default ownership fails at raw header2.
This is an initial-relation failure, not Option failure implying rollback. -/
theorem mixed_not_old_default :
    mixedOldRoot.find retainedPath = none ∧
    ¬ Represented (NestedCopyObservations.child mixedOldRoot (freshIndex 1)) [.length .nil]
      (.data (.root 1) 1) accessStore := by
  refine ⟨rfl,?_⟩
  intro bad
  have observed := (bad (.length .nil) List.mem_cons_self).2.2 (w 0) (by rfl)
  change w 2 = w 0 at observed
  exact (by decide : w 2 ≠ w 0) observed

/-- Actual wrong post-copy SSTORE erases the retained shadow. -/
theorem mixed_wrong_target :
    Evm.run (TargetOperations.writeCode (.data (.data (.root 1) 0) 3) (w 0)) accessRootAfter =
      .ok { accessRootAfter with store := Evm.WordStore.write accessRootAfter.store (.data (.data (.root 1) 0) 3) 0 } 0 ∧
    (Evm.WordStore.write accessRootAfter.store (.data (.data (.root 1) 0) 3) 0).cells (.data (.data (.root 1) 0) 3) ≠
      TargetOperations.encodeWord (w 37) := by
  refine ⟨TargetOperations.run_write _ _ _,?_⟩
  decide

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.mixed_wrong_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mixed_wrong_fresh
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.mixed_not_old_default' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mixed_not_old_default
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.mixed_wrong_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mixed_wrong_target


-- C82 combines LIVE, shortened former-live and older retained children.
private def shrinkChildren : List Index := [freshIndex 0,freshIndex 2,shadowIndex]
private def shrinkIndices (i : Index) : List Index := if i.val = 0 then accessIndices else freshIndices
private def shrinkQueries := NestedRootComposition.rootQueries (G := graph) (p := .uint) shrinkChildren shrinkIndices
private def shrinkReads := RootCopyAccess.sourceQueries bothSourceRoot [freshIndex 0] shrinkIndices
private theorem shrinkFirstOld : Represented firstRetained (PrimitivePop.queries accessIndices) (.data (.root 1) 0) olderStore := by
  intro q member
  simp only [PrimitivePop.queries,accessIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 3) = some word at found; cases found; rfl
  · refine ⟨by change 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 23) = some word at found; cases found; rfl
  · refine ⟨by change 1 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 29) = some word at found; cases found; rfl
  · refine ⟨by change 2 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 31) = some word at found; cases found; rfl
  · refine ⟨by change 3 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 37) = some word at found; cases found; rfl
private theorem shrinkFirstSource : Represented firstSource (CopyAccess.readQueries firstSource accessIndices) (.data (.root 0) 0) olderStore := by
  change Represented firstSource [Query.length .nil,PrimitivePop.elementQuery (freshIndex 0)] (.data (.root 0) 0) olderStore
  intro q member
  rcases List.mem_cons.mp member with rfl | inside
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 1) = some word at found; cases found; rfl
  · have same := List.mem_singleton.mp inside; subst q
    refine ⟨by change 0 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 7) = some word at found; cases found; rfl
private theorem shrinkStaleOld : Represented staleChild (TargetClearRepresentation.oldQueries staleChild freshIndices) (.data (.root 1) 2) olderStore := by
  change Represented staleChild [Query.length .nil,PrimitivePop.elementQuery (freshIndex 2)] (.data (.root 1) 2) olderStore
  intro q member
  rcases List.mem_cons.mp member with rfl | inside
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word found; change some (w 2) = some word at found; cases found; rfl
  · have same := List.mem_singleton.mp inside; subst q
    refine ⟨by change 2 < lmax ∧ True; decide,True.intro,?_⟩
    intro word found; change some (w 61) = some word at found; cases found; rfl

/-- Actual shrink combines all three branches, with OLD owners only where
needed and no Sourcechild owner for stale2 or older3/uncovered raw99. -/
theorem shrink_root_bridge :
    Evm.run TargetNestedArrayCopy.code { olderTarget with stack := .slot (.root 0) :: .slot (.root 1) :: tail } = .ok olderAfter 0 ∧
    Represented (olderRoot.overlay bothSourceRoot) shrinkQueries (.root 1)
      (TargetNestedArrayTransport.afterStore olderStore (.root 1) (.root 0)) ∧
    Transport 128 olderHash olderLocations (TargetNestedArrayTransport.afterStore olderStore (.root 1) (.root 0))
      (TargetNestedArrayTransport.execute 128 olderHash olderNumeric (.root 1) (.root 0)) ∧
    (∀ l (member : l ∈ olderLocations), olderAfter.store.cells (TargetOperations.toSlot l (olderFitting l member)) =
      TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore olderStore (.root 1) (.root 0) l)) := by
  refine ShrinkRootComposition.retained_root olderRun olderRoot bothSourceRoot shrinkChildren shrinkIndices ?_
    (.root 1) (.root 0) (by trivial) (by trivial) olderStore olderNumeric olderTarget tail olderInitial olderFitting olderTargetInitial
    olderHeader ?_ olderSourceHeader ?_ ?_ ?_ (by decide) (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i member
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro i member live
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Represented.prefix firstPath (by rfl : olderRoot.find firstPath = some firstRetained)
        (by change 0 < lmax ∧ True; decide) shrinkFirstOld
    · change 2 < 2 at live; omega
    · change 3 < 2 at live; omega
  · intro i member live
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Represented.prefix firstPath (by rfl : bothSourceRoot.find firstPath = some firstSource)
        (by change 0 < lmax ∧ True; decide) shrinkFirstSource
    · change 2 < 2 at live; omega
    · change 3 < 2 at live; omega
  · intro i member pastNew oldLive
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · change 2 ≤ 0 at pastNew; omega
    · exact Represented.prefix missingPath (by rfl : olderRoot.find missingPath = some staleChild)
        (by change 2 < lmax ∧ True; decide) shrinkStaleOld
    · change 3 < 3 at oldLive; omega
  · intro i member pastNew pastOld
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · change 2 ≤ 0 at pastNew; omega
    · change 3 ≤ 2 at pastOld; omega
    · exact olderBeforeRoot
  · intro k inside
    change k < 2 at inside
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl <;> decide
  · exact forall_bounded_pair (by decide)
  · exact forall_bounded_pair (by decide)
  · intro k inside begun
    change k < 3 at inside; change 2 ≤ k at begun
    have same : k = 2 := by omega
    subst k; decide
  · intro k inside begun j live
    change k < 3 at inside; change 2 ≤ k at begun
    have same : k = 2 := by omega
    subst k; change j < 2 at live
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with rfl | rfl <;> decide
  · intro i member j inside
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · change j ∈ accessIndices at inside
      simp only [accessIndices,List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl <;> decide
    · change j ∈ freshIndices at inside
      simp only [freshIndices,List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with rfl | rfl | rfl <;> decide
    · change j ∈ freshIndices at inside
      simp only [freshIndices,List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with rfl | rfl | rfl <;> decide
  · intro i member live j inside
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · change j < 1 at inside
      have same : j = 0 := by omega
      subst j; decide
    · change 2 < 2 at live; omega
    · change 3 < 2 at live; omega
  · intro i member live j inside
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · change j < 3 at inside
      have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases casesJ with rfl | rfl | rfl <;> decide
    · change 2 < 2 at live; omega
    · change 3 < 2 at live; omega
  · intro i member
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro i member live q observation
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact List.not_mem_nil
    · change 2 < 2 at live; omega
    · change 3 < 2 at live; omega
  · intro i member live q observation
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact List.not_mem_nil
    · change 2 < 2 at live; omega
    · change 3 < 2 at live; omega

/-- COMPLETE29-location old/copy/final vectors across logical/numeric/target,
all fourteen old/outputqueries, exact Source demands and both nonlive classes. -/
theorem shrink_root_ordered :
    (olderSymbolicView olderStore,
      olderSymbolicView (TargetNestedArrayTransport.copyStores olderStore (.root 1) (.root 0) 2),
      olderSymbolicView (TargetNestedArrayTransport.afterStore olderStore (.root 1) (.root 0)),
      olderNumericView (TargetNestedArrayTransport.execute 128 olderHash olderNumeric (.root 1) (.root 0)),
      olderTargetView olderAfter,context olderAfter,
      shrinkQueries.map (fun q => q.read olderRoot),shrinkQueries.map (fun q => q.read (olderRoot.overlay bothSourceRoot)),
      shrinkReads.map (fun q => q.read bothSourceRoot),
      shrinkChildren.map (fun i => (decide (i.val < bothSourceRoot.length.val),decide (i.val < olderRoot.length.val))),
      (missingPath.readLive Value.dflt olderRoot).isSome,(missingPath.readLive Value.dflt (olderRoot.overlay bothSourceRoot)).isSome,
      (olderPath.readLive Value.dflt olderRoot).isSome,(olderPath.readLive Value.dflt (olderRoot.overlay bothSourceRoot)).isSome,
      olderStore olderUncovered,TargetNestedArrayTransport.afterStore olderStore (.root 1) (.root 0) olderUncovered,
      olderNumeric (olderUncovered.word 128 olderHash),TargetNestedArrayTransport.execute 128 olderHash olderNumeric (.root 1) (.root 0) (olderUncovered.word 128 olderHash),
      olderTarget.store (.data (.root 0) 3),olderAfter.store (.data (.root 0) 3),
      (bothSourceRoot.find olderPath).isSome) =
    ([w 2,w 3,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 3,w 23,w 29,w 31,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73,w 1,w 91,w 93,w 95],
     [w 2,w 3,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73,w 1,w 91,w 93,w 95],
     [w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 0,w 0,w 0,w 61,w 73,w 1,w 91,w 93,w 95],
     [w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 0,w 0,w 0,w 61,w 73,w 1,w 91,w 93,w 95],
     [2,2,1,7,11,13,1,17,19,1,71,1,7,0,0,37,1,17,0,47,0,0,0,61,73,1,91,93,95],context olderTarget,
     [some (w 3),some (w 3),some (w 23),some (w 29),some (w 31),some (w 37),some (w 2),some (w 53),some (w 59),some (w 61),some (w 1),some (w 91),some (w 93),some (w 95)],
     [some (w 2),some (w 1),some (w 7),some (w 0),some (w 0),some (w 37),some (w 0),some (w 0),some (w 0),some (w 61),some (w 1),some (w 91),some (w 93),some (w 95)],
     [some (w 2),some (w 1),some (w 7)],[(true,true),(false,true),(false,false)],true,false,false,false,w 99,w 99,w 99,w 99,99,99,false) := by rfl

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.shrink_root_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shrink_root_bridge
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.shrink_root_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shrink_root_ordered


private theorem shrinkMember (i : Index) (member : i ∈ shrinkChildren)
    (q : Query graph (.array (.prim .uint))) (inside : q ∈ PrimitivePop.queries (shrinkIndices i)) :
    Query.prefix (NestedCopyObservations.childPath i) q ∈ shrinkQueries :=
  List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨i,member,List.mem_map.mpr ⟨q,inside,rfl⟩⟩)

/-- Each wrong class falsifies a successful observation in the SAME combined
owner: stale-as-older, older-as-stale, and retained-as-fresh, respectively. -/
theorem shrink_wrong_classes :
    (¬ Represented (olderRoot.overlay bothSourceRoot) shrinkQueries (.root 1)
      (Representation.write (TargetNestedArrayTransport.afterStore olderStore (.root 1) (.root 0)) (.data (.root 1) 2) (w 2))) ∧
    (¬ Represented (olderRoot.overlay bothSourceRoot) shrinkQueries (.root 1)
      (Representation.write (TargetNestedArrayTransport.afterStore olderStore (.root 1) (.root 0)) (.data (.root 1) 3) (w 0))) ∧
    (¬ Represented (olderRoot.overlay bothSourceRoot) shrinkQueries (.root 1)
      (Representation.write (TargetNestedArrayTransport.afterStore olderStore (.root 1) (.root 0)) (.data (.data (.root 1) 0) 3) (w 0))) := by
  refine ⟨?_,?_,?_⟩
  · intro bad
    have member := shrinkMember (freshIndex 2) (List.mem_cons_of_mem _ List.mem_cons_self) (.length .nil) List.mem_cons_self
    have observed := (bad _ member).2.2 (w 0) (by rfl)
    change w 2 = w 0 at observed
    exact (by decide : w 2 ≠ w 0) observed
  · intro bad
    have member := shrinkMember shadowIndex (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (.length .nil) List.mem_cons_self
    have observed := (bad _ member).2.2 (w 1) (by rfl)
    change w 0 = w 1 at observed
    exact (by decide : w 0 ≠ w 1) observed
  · intro bad
    have member := shrinkMember (freshIndex 0) List.mem_cons_self (PrimitivePop.elementQuery shadowIndex)
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨shadowIndex,
        by change shadowIndex ∈ accessIndices; simp only [accessIndices,List.mem_cons,true_or,or_true],rfl⟩))
    have observed := (bad _ member).2.2 (w 37) (by rfl)
    change w 0 = w 37 at observed
    exact (by decide : w 0 ≠ w 37) observed

private def shrinkWrongCode : List Evm.Instr := TargetArrayCopy.setup ++
  [.loop TargetArrayCopy.condition TargetNestedArrayCopy.copyBody] ++ TargetArrayCopy.transition ++ TargetArrayCopy.finish
private def shrinkCopiedTarget := TargetNestedArrayCopyLoop.prefixMachine olderTarget (.root 0) (.root 1) 2
private def shrinkWrongAfter : Evm.Machine :=
  { shrinkCopiedTarget with
    stack := tail
    store := Evm.WordStore.write shrinkCopiedTarget.store (.root 1) 2 }

/-- Actual uncapped nested copy loop followed by header write, omitting the
stale outer clear loop. It terminates successfully with the wrong stale child. -/
theorem shrink_wrong_skip_runtime :
    Evm.run shrinkWrongCode { olderTarget with stack := .slot (.root 0) :: .slot (.root 1) :: tail } = .ok shrinkWrongAfter 0 := by
  have copied := TargetNestedArrayCopyLoop.run_loop_from olderTarget tail (.root 0) (.root 1)
    ⟨3,by decide⟩ ⟨2,by decide⟩ ⟨0,by decide⟩ (by decide)
  unfold shrinkWrongCode
  simp only [List.append_assoc]
  rw [Evm.run_append_ok (TargetArrayCopy.run_setup olderTarget tail (.root 0) (.root 1))]
  change Evm.run _ (TargetNestedArrayCopyLoop.iterationMachine olderTarget tail (.root 0) (.root 1)
    ⟨3,by decide⟩ ⟨2,by decide⟩ ⟨0,by decide⟩) = _
  rw [Evm.run_append_ok copied]
  change Evm.run _ ({ shrinkCopiedTarget with stack := (.val ⟨2,by decide⟩ :: .val ⟨2,by decide⟩ :: .slot (.root 0) :: .slot (.root 1) :: .val ⟨3,by decide⟩ :: tail) } : Evm.Machine) = _
  rw [Evm.run_append_ok (TargetArrayCopyTail.run_transition shrinkCopiedTarget tail (.root 0) (.root 1) ⟨2,by decide⟩ ⟨3,by decide⟩)]
  exact TargetArrayCopyTail.run_finish shrinkCopiedTarget tail (.root 1) ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨2,by decide⟩

/-- COMPLETE wrong-program target vector/context. Correct outer/live-child
headers do not excuse stale53/59 surviving; older91/93/95 must still survive. -/
theorem shrink_wrong_skip_ordered :
    (olderTargetView shrinkWrongAfter,context shrinkWrongAfter,
      shrinkWrongAfter.store (.data (.root 0) 3),
      (shrinkWrongAfter.store (.data (.root 1) 2),olderAfter.store (.data (.root 1) 2))) =
    ([2,2,1,7,11,13,1,17,19,1,71,1,7,0,0,37,1,17,0,47,2,53,59,61,73,1,91,93,95],
     context olderTarget,99,(2,0)) := by rfl

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.shrink_wrong_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shrink_wrong_classes
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.shrink_wrong_skip_runtime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shrink_wrong_skip_runtime
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.shrink_wrong_skip_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shrink_wrong_skip_ordered


/-- Apply the UNIFIED theorem to inhabited growth; no old postowner is reused. -/
theorem output_growth_bridge :
    Evm.run TargetNestedArrayCopy.code { accessTarget with stack := .slot (.root 0) :: .slot (.root 1) :: tail } = .ok accessRootAfter 0 ∧
    Represented (mixedOldRoot.overlay accessSourceRoot) mixedQueries (.root 1)
      (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0)) ∧
    Transport 128 hash locations (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0))
      (TargetNestedArrayTransport.execute 128 hash accessNumeric (.root 1) (.root 0)) ∧
    (∀ l (member : l ∈ locations), accessRootAfter.store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0) l)) := by
  have sourceHeader : Represented accessSourceRoot [.length .nil] (.root 0) accessStore := by
    intro q member
    have same := List.mem_singleton.mp member; subst q
    exact accessSourceOwner _ List.mem_cons_self
  refine OutputRootComposition.root run mixedOldRoot accessSourceRoot mixedChildren mixedIndices ?_
    (.root 1) (.root 0) (by trivial) (by trivial) accessStore accessNumeric accessTarget tail accessInitial fitting accessTargetInitial
    mixedHeader ?_ sourceHeader ?_ ?_ ?_ (by decide) (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i member
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> decide
  · intro i member retained active
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Represented.prefix firstPath (by rfl : mixedOldRoot.find firstPath = some firstRetained)
        (by change 0 < lmax ∧ True; decide) accessBeforeDst
    · change 1 < 1 at retained; omega
  · intro i member live q observation
    exact mixedSourceOwner q (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨i,member,observation⟩))
  · intro i member pastNew unused
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · change 2 ≤ 0 at pastNew; omega
    · change 2 ≤ 1 at pastNew; omega
  · intro i member pastNew unused
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · change 2 ≤ 0 at pastNew; omega
    · change 2 ≤ 1 at pastNew; omega
  · intro k inside
    change k < 2 at inside
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl <;> decide
  · exact forall_bounded_pair (by decide)
  · exact forall_bounded_pair (by decide)
  · intro k inside begun
    change k < 2 at inside; change 2 ≤ k at begun; omega
  · intro k inside begun j live
    change k < 2 at inside; change 2 ≤ k at begun; omega
  · intro i member j inside
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · change j ∈ accessIndices at inside
      simp only [accessIndices,List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl <;> decide
    · change j ∈ freshIndices at inside
      simp only [freshIndices,List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with rfl | rfl | rfl <;> decide
  · intro i member active j live
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> change j < 1 at live
    all_goals have same : j = 0 := by omega
    all_goals subst j; decide
  · intro i member retained active j live
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · change j < 3 at live
      have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases casesJ with rfl | rfl | rfl <;> decide
    · change 1 < 1 at retained; omega
  · intro i member
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> decide
  · intro i member missing j live
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · change 1 ≤ 0 at missing; omega
    · change j < 2 at live
      have casesJ : j = 0 ∨ j = 1 := by omega
      rcases casesJ with rfl | rfl <;> decide
  · intro i member missing q observation
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · change 1 ≤ 0 at missing; omega
    · change q ∈ PrimitivePop.queries freshIndices at observation
      simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at observation
      rcases observation with rfl | rfl | rfl | rfl
      · trivial
      · change 0 < lmax ∧ True; decide
      · change 1 < lmax ∧ True; decide
      · change 2 < lmax ∧ True; decide
  · intro i member retained active q observation
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact List.not_mem_nil
    · change 1 < 1 at retained; omega
  · intro i member active q observation
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact List.not_mem_nil
    · change q ∈ [Query.length .nil,PrimitivePop.elementQuery (freshIndex 0)] at observation
      rcases List.mem_cons.mp observation with rfl | inside
      · change Evm.Slot.data (.root 0) 1 ∉ TargetNestedArrayCopyLoop.touched accessTarget (.root 0) (.root 1) 1
        decide
      · have same := List.mem_singleton.mp inside; subst q
        change Evm.Slot.data (.data (.root 0) 1) 0 ∉ TargetNestedArrayCopyLoop.touched accessTarget (.root 0) (.root 1) 1
        decide

/-- Apply the SAME UNIFIED theorem to inhabited shrink, including all three retained classes. -/
theorem output_shrink_bridge :
    Evm.run TargetNestedArrayCopy.code { olderTarget with stack := .slot (.root 0) :: .slot (.root 1) :: tail } = .ok olderAfter 0 ∧
    Represented (olderRoot.overlay bothSourceRoot) shrinkQueries (.root 1)
      (TargetNestedArrayTransport.afterStore olderStore (.root 1) (.root 0)) ∧
    Transport 128 olderHash olderLocations (TargetNestedArrayTransport.afterStore olderStore (.root 1) (.root 0))
      (TargetNestedArrayTransport.execute 128 olderHash olderNumeric (.root 1) (.root 0)) ∧
    (∀ l (member : l ∈ olderLocations), olderAfter.store.cells (TargetOperations.toSlot l (olderFitting l member)) =
      TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore olderStore (.root 1) (.root 0) l)) := by
  refine OutputRootComposition.root olderRun olderRoot bothSourceRoot shrinkChildren shrinkIndices ?_
    (.root 1) (.root 0) (by trivial) (by trivial) olderStore olderNumeric olderTarget tail olderInitial olderFitting olderTargetInitial
    olderHeader ?_ olderSourceHeader ?_ ?_ ?_ (by decide) (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i member
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro i member retained live
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Represented.prefix firstPath (by rfl : olderRoot.find firstPath = some firstRetained)
        (by change 0 < lmax ∧ True; decide) shrinkFirstOld
    · change 2 < 2 at live; omega
    · change 3 < 2 at live; omega
  · intro i member live
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Represented.prefix firstPath (by rfl : bothSourceRoot.find firstPath = some firstSource)
        (by change 0 < lmax ∧ True; decide) shrinkFirstSource
    · change 2 < 2 at live; omega
    · change 3 < 2 at live; omega
  · intro i member pastNew oldLive
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · change 2 ≤ 0 at pastNew; omega
    · exact Represented.prefix missingPath (by rfl : olderRoot.find missingPath = some staleChild)
        (by change 2 < lmax ∧ True; decide) shrinkStaleOld
    · change 3 < 3 at oldLive; omega
  · intro i member pastNew pastOld
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · change 2 ≤ 0 at pastNew; omega
    · change 3 ≤ 2 at pastOld; omega
    · exact olderBeforeRoot
  · intro k inside
    change k < 2 at inside
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl <;> decide
  · exact forall_bounded_pair (by decide)
  · exact forall_bounded_pair (by decide)
  · intro k inside begun
    change k < 3 at inside; change 2 ≤ k at begun
    have same : k = 2 := by omega
    subst k; decide
  · intro k inside begun j live
    change k < 3 at inside; change 2 ≤ k at begun
    have same : k = 2 := by omega
    subst k; change j < 2 at live
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with rfl | rfl <;> decide
  · intro i member j inside
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · change j ∈ accessIndices at inside
      simp only [accessIndices,List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl <;> decide
    · change j ∈ freshIndices at inside
      simp only [freshIndices,List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with rfl | rfl | rfl <;> decide
    · change j ∈ freshIndices at inside
      simp only [freshIndices,List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with rfl | rfl | rfl <;> decide
  · intro i member live j inside
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · change j < 1 at inside
      have same : j = 0 := by omega
      subst j; decide
    · change 2 < 2 at live; omega
    · change 3 < 2 at live; omega
  · intro i member retained live j inside
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · change j < 3 at inside
      have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases casesJ with rfl | rfl | rfl <;> decide
    · change 2 < 2 at live; omega
    · change 3 < 2 at live; omega
  · intro i member
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro i member missing
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · change 4 ≤ 0 at missing
      have impossible : False := by omega
      exact False.elim impossible
    · change 4 ≤ 2 at missing
      have impossible : False := by omega
      exact False.elim impossible
    · change 4 ≤ 3 at missing
      have impossible : False := by omega
      exact False.elim impossible
  · intro i member missing
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · change 4 ≤ 0 at missing
      have impossible : False := by omega
      exact False.elim impossible
    · change 4 ≤ 2 at missing
      have impossible : False := by omega
      exact False.elim impossible
    · change 4 ≤ 3 at missing
      have impossible : False := by omega
      exact False.elim impossible
  · intro i member retained live q observation
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact List.not_mem_nil
    · change 2 < 2 at live; omega
    · change 3 < 2 at live; omega
  · intro i member live q observation
    simp only [shrinkChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact List.not_mem_nil
    · change 2 < 2 at live; omega
    · change 3 < 2 at live; omega

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.output_growth_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms output_growth_bridge

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.output_shrink_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms output_shrink_bridge


-- C84: a genuinely missing OUTER result child has covered nonzero raw cells.
private def completeQueries := mixedQueries ++ (PrimitivePop.queries freshIndices).map (Query.prefix missingPath)

/-- Actual successful plus failed ROOT query composition from OLD evidence.
Numeric and ALL covered target contracts still cover the nonzero absent child. -/
theorem complete_growth_bridge :
    Evm.run TargetNestedArrayCopy.code { accessTarget with stack := .slot (.root 0) :: .slot (.root 1) :: tail } = .ok accessRootAfter 0 ∧
    Represented (mixedOldRoot.overlay accessSourceRoot) completeQueries (.root 1)
      (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0)) ∧
    Transport 128 hash locations (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0))
      (TargetNestedArrayTransport.execute 128 hash accessNumeric (.root 1) (.root 0)) ∧
    (∀ l (member : l ∈ locations), accessRootAfter.store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0) l)) := by
  have sourceHeader : Represented accessSourceRoot [.length .nil] (.root 0) accessStore := by
    intro q member
    have same := List.mem_singleton.mp member; subst q
    exact accessSourceOwner _ List.mem_cons_self
  refine OutputRootComplete.complete run mixedOldRoot accessSourceRoot mixedChildren mixedIndices ?_
    (freshIndex 2) (by decide) (PrimitivePop.queries freshIndices) ?_
    (.root 1) (.root 0) (by trivial) (by trivial) accessStore accessNumeric accessTarget tail accessInitial fitting accessTargetInitial
    mixedHeader ?_ sourceHeader ?_ ?_ ?_ (by decide) (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i member
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> decide
  · intro q member
    simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · change 2 < lmax ∧ True; decide
    · change 2 < lmax ∧ (0 < lmax ∧ True); decide
    · change 2 < lmax ∧ (1 < lmax ∧ True); decide
    · change 2 < lmax ∧ (2 < lmax ∧ True); decide
  · intro i member retained active
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Represented.prefix firstPath (by rfl : mixedOldRoot.find firstPath = some firstRetained)
        (by change 0 < lmax ∧ True; decide) accessBeforeDst
    · change 1 < 1 at retained; omega
  · intro i member live q observation
    exact mixedSourceOwner q (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨i,member,observation⟩))
  · intro i member pastNew unused
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · change 2 ≤ 0 at pastNew; omega
    · change 2 ≤ 1 at pastNew; omega
  · intro i member pastNew unused
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · change 2 ≤ 0 at pastNew; omega
    · change 2 ≤ 1 at pastNew; omega
  · intro k inside
    change k < 2 at inside
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl <;> decide
  · exact forall_bounded_pair (by decide)
  · exact forall_bounded_pair (by decide)
  · intro k inside begun
    change k < 2 at inside; change 2 ≤ k at begun; omega
  · intro k inside begun j live
    change k < 2 at inside; change 2 ≤ k at begun; omega
  · intro i member j inside
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · change j ∈ accessIndices at inside
      simp only [accessIndices,List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl <;> decide
    · change j ∈ freshIndices at inside
      simp only [freshIndices,List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with rfl | rfl | rfl <;> decide
  · intro i member active j live
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> change j < 1 at live
    all_goals have same : j = 0 := by omega
    all_goals subst j; decide
  · intro i member retained active j live
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · change j < 3 at live
      have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases casesJ with rfl | rfl | rfl <;> decide
    · change 1 < 1 at retained; omega
  · intro i member
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> decide
  · intro i member missing j live
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · change 1 ≤ 0 at missing; omega
    · change j < 2 at live
      have casesJ : j = 0 ∨ j = 1 := by omega
      rcases casesJ with rfl | rfl <;> decide
  · intro i member missing q observation
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · change 1 ≤ 0 at missing; omega
    · change q ∈ PrimitivePop.queries freshIndices at observation
      simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at observation
      rcases observation with rfl | rfl | rfl | rfl
      · trivial
      · change 0 < lmax ∧ True; decide
      · change 1 < lmax ∧ True; decide
      · change 2 < lmax ∧ True; decide
  · intro i member retained active q observation
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact List.not_mem_nil
    · change 1 < 1 at retained; omega
  · intro i member active q observation
    simp only [mixedChildren,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact List.not_mem_nil
    · change q ∈ [Query.length .nil,PrimitivePop.elementQuery (freshIndex 0)] at observation
      rcases List.mem_cons.mp observation with rfl | inside
      · change Evm.Slot.data (.root 0) 1 ∉ TargetNestedArrayCopyLoop.touched accessTarget (.root 0) (.root 1) 1
        decide
      · have same := List.mem_singleton.mp inside; subst q
        change Evm.Slot.data (.data (.root 0) 1) 0 ∉ TargetNestedArrayCopyLoop.touched accessTarget (.root 0) (.root 1) 1
        decide

/-- COMPLETE ordered25 old/prefix/final symbolic/numeric/target/context,
all14 old/output ROOT queries, Source demands and logical/physical mismatch. -/
theorem complete_growth_ordered :
    (symbolicView accessStore,symbolicView accessAfterStore,
      symbolicView (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0)),
      numericView (TargetNestedArrayTransport.execute 128 hash accessNumeric (.root 1) (.root 0)),
      targetView accessRootAfter,context accessRootAfter,
      completeQueries.map (fun q => q.read mixedOldRoot),
      completeQueries.map (fun q => q.read (mixedOldRoot.overlay accessSourceRoot)),
      mixedReads.map (fun q => q.read accessSourceRoot),
      (Query.prefix missingPath (Query.length .nil)).read accessSourceRoot,
      (Query.prefix missingPath (PrimitivePop.elementQuery (freshIndex 0))).read accessSourceRoot,
      (mixedOldRoot.find missingPath).isSome,((mixedOldRoot.overlay accessSourceRoot).find missingPath).isSome,
      ((missingPath.readLive Value.dflt (mixedOldRoot.overlay accessSourceRoot))).isSome) =
    ([w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 3,w 23,w 29,w 31,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
     [2,2,1,7,11,13,1,17,19,1,71,1,7,0,0,37,1,17,0,47,2,53,59,61,73],context accessTarget,
     [some (w 1),some (w 3),some (w 23),some (w 29),some (w 31),some (w 37),none,none,none,none,none,none,none,none],
     [some (w 2),some (w 1),some (w 7),some (w 0),some (w 0),some (w 37),some (w 1),some (w 17),none,none,none,none,none,none],
     [some (w 2),some (w 1),some (w 7),some (w 1),some (w 17)],some (w 1),some (w 71),false,false,false) := by rfl

/-- Four failed queries coexist with certified nonzero raw header2/53/59/61.
No Option failure implies physical default initialization or world rollback. -/
theorem complete_not_raw_default :
    ((PrimitivePop.queries (G := graph) (p := .uint) freshIndices).map
      (fun q => (Query.prefix missingPath q).read (mixedOldRoot.overlay accessSourceRoot))) = [none,none,none,none] ∧
    (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0) (.data (.root 1) 2),
      TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0) (.data (.data (.root 1) 2) 0),
      accessRootAfter.store (.data (.root 1) 2),accessRootAfter.store (.data (.data (.root 1) 2) 0)) = (w 2,w 53,2,53) := by
  exact ⟨rfl,rfl⟩

/-- Actual forbidden extra copy from a retained nonlive Source child corrupts
raw53->71 despite every added graph query failing. Physical contract matters. -/
theorem complete_wrong_source_tail :
    Evm.run (TargetOperations.copyCode (.data (.data (.root 1) 2) 0) (.data (.data (.root 0) 2) 0)) accessRootAfter =
      .ok { accessRootAfter with store := Evm.WordStore.write accessRootAfter.store (.data (.data (.root 1) 2) 0) 71 } 0 ∧
    (Evm.WordStore.write accessRootAfter.store (.data (.data (.root 1) 2) 0) 71).cells (.data (.data (.root 1) 2) 0) ≠
      TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0) (.data (.data (.root 1) 2) 0)) := by
  refine ⟨TargetOperations.run_copy _ _ _,?_⟩
  decide

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.complete_growth_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_growth_bridge
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.complete_growth_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_growth_ordered
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.complete_not_raw_default' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_not_raw_default
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.complete_wrong_source_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_wrong_source_tail


-- C85: observations are deliberately reordered and repeat an absent child.
private def finiteChildren : List Index := [freshIndex 2,freshIndex 1,freshIndex 0,freshIndex 2]
private def finiteQueries := NestedRootComposition.rootQueries (G := graph) (p := .uint) finiteChildren mixedIndices
private def finiteReads := RootCopyAccess.sourceQueries accessSourceRoot
  (finiteChildren.filter (fun i => decide (i.val < accessSourceRoot.length.val))) mixedIndices
private theorem finiteLiveCases (i : Index) (live : i.val < accessSourceRoot.length.val) :
    i = freshIndex 0 ∨ i = freshIndex 1 := by
  change i.val < 2 at live
  have casesI : i.val = 0 ∨ i.val = 1 := by omega
  rcases casesI with left | right
  · exact Or.inl (Fin.ext left)
  · exact Or.inr (Fin.ext right)
private theorem finiteOutsideIndex (i : Index) (member : i ∈ finiteChildren)
    (outside : max mixedOldRoot.extent.val accessSourceRoot.length.val ≤ i.val) : i = freshIndex 2 := by
  simp only [finiteChildren,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · rfl
  · change 2 ≤ 1 at outside; omega
  · change 2 ≤ 0 at outside; omega
  · rfl

/-- A single unpartitioned, reordered, duplicate observation list is checked
from OLD evidence. No prior desired postowner or outside physical premise. -/
theorem finite_root_bridge :
    Evm.run TargetNestedArrayCopy.code { accessTarget with stack := .slot (.root 0) :: .slot (.root 1) :: tail } = .ok accessRootAfter 0 ∧
    Represented (mixedOldRoot.overlay accessSourceRoot) finiteQueries (.root 1)
      (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0)) ∧
    Transport 128 hash locations (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0))
      (TargetNestedArrayTransport.execute 128 hash accessNumeric (.root 1) (.root 0)) ∧
    (∀ l (member : l ∈ locations), accessRootAfter.store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0) l)) := by
  have sourceHeader : Represented accessSourceRoot [.length .nil] (.root 0) accessStore := by
    intro q member
    have same := List.mem_singleton.mp member; subst q
    exact accessSourceOwner _ List.mem_cons_self
  refine FiniteRootComposition.root run mixedOldRoot accessSourceRoot finiteChildren mixedIndices
    (.root 1) (.root 0) (by trivial) (by trivial) accessStore accessNumeric accessTarget tail accessInitial fitting accessTargetInitial
    mixedHeader ?_ sourceHeader ?_ ?_ ?_ (by decide) (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i member oldInside live
    change i.val < 1 at oldInside
    have same : i = freshIndex 0 := Fin.ext (by change i.val = 0; omega)
    subst i
    exact Represented.prefix firstPath (by rfl : mixedOldRoot.find firstPath = some firstRetained)
      (by change 0 < lmax ∧ True; decide) accessBeforeDst
  · intro i member live
    rcases finiteLiveCases i live with rfl | rfl
    · exact Represented.prefix firstPath (by rfl : accessSourceRoot.find firstPath = some retainedSourceShadow)
        (by change 0 < lmax ∧ True; decide) retainedSourceReads
    · exact Represented.prefix retainedPath (by rfl : accessSourceRoot.find retainedPath = some innerB)
        (by change 1 < lmax ∧ True; decide) laterBeforeSrc
  · intro i member pastNew oldLive
    change 2 ≤ i.val at pastNew; change i.val < 1 at oldLive; omega
  · intro i member oldInside pastNew pastOld
    change i.val < 1 at oldInside; change 2 ≤ i.val at pastNew; omega
  · intro k inside
    change k < 2 at inside
    have casesK : k = 0 ∨ k = 1 := by omega
    rcases casesK with rfl | rfl <;> decide
  · exact forall_bounded_pair (by decide)
  · exact forall_bounded_pair (by decide)
  · intro k inside begun
    change k < 2 at inside; change 2 ≤ k at begun; omega
  · intro k inside begun j live
    change k < 2 at inside; change 2 ≤ k at begun; omega
  · intro i member inside j selected
    rcases finiteLiveCases i inside with rfl | rfl
    · change j ∈ accessIndices at selected
      simp only [accessIndices,List.mem_cons,List.not_mem_nil,or_false] at selected
      rcases selected with rfl | rfl | rfl | rfl <;> decide
    · change j ∈ freshIndices at selected
      simp only [freshIndices,List.mem_cons,List.not_mem_nil,or_false] at selected
      rcases selected with rfl | rfl | rfl <;> decide
  · intro i member live j inside
    rcases finiteLiveCases i live with rfl | rfl <;> change j < 1 at inside
    all_goals have same : j = 0 := by omega
    all_goals subst j; decide
  · intro i member oldInside live j inside
    change i.val < 1 at oldInside
    have same : i = freshIndex 0 := Fin.ext (by change i.val = 0; omega)
    subst i; change j < 3 at inside
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases casesJ with rfl | rfl | rfl <;> decide
  · intro i member inside
    rcases finiteLiveCases i inside with rfl | rfl <;> decide
  · intro i member inside missing j live
    change i.val < 2 at inside; change 1 ≤ i.val at missing
    have same : i = freshIndex 1 := Fin.ext (by change i.val = 1; omega)
    subst i; change j < 2 at live
    have casesJ : j = 0 ∨ j = 1 := by omega
    rcases casesJ with rfl | rfl <;> decide
  · intro i member inside missing q selected
    change i.val < 2 at inside; change 1 ≤ i.val at missing
    have same : i = freshIndex 1 := Fin.ext (by change i.val = 1; omega)
    subst i
    change q ∈ PrimitivePop.queries freshIndices at selected
    simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at selected
    rcases selected with rfl | rfl | rfl | rfl
    · trivial
    · change 0 < lmax ∧ True; decide
    · change 1 < lmax ∧ True; decide
    · change 2 < lmax ∧ True; decide
  · intro i member outside q selected
    have same := finiteOutsideIndex i member outside
    subst i
    change q ∈ PrimitivePop.queries freshIndices at selected
    simp only [PrimitivePop.queries,freshIndices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at selected
    rcases selected with rfl | rfl | rfl | rfl
    · change 2 < lmax ∧ True; decide
    · change 2 < lmax ∧ (0 < lmax ∧ True); decide
    · change 2 < lmax ∧ (1 < lmax ∧ True); decide
    · change 2 < lmax ∧ (2 < lmax ∧ True); decide
  · intro i member oldInside live q selected
    change i.val < 1 at oldInside
    have same : i = freshIndex 0 := Fin.ext (by change i.val = 0; omega)
    subst i
    exact List.not_mem_nil
  · intro i member live q selected
    rcases finiteLiveCases i live with rfl | rfl
    · exact List.not_mem_nil
    · change q ∈ [Query.length .nil,PrimitivePop.elementQuery (freshIndex 0)] at selected
      rcases List.mem_cons.mp selected with rfl | rest
      · change Evm.Slot.data (.root 0) 1 ∉ TargetNestedArrayCopyLoop.touched accessTarget (.root 0) (.root 1) 1
        decide
      · have same := List.mem_singleton.mp rest; subst q
        change Evm.Slot.data (.data (.root 0) 1) 0 ∉ TargetNestedArrayCopyLoop.touched accessTarget (.root 0) (.root 1) 1
        decide

/-- COMPLETE ordered25 phase vectors/context and all18 OLD/output queries.
Observers [2,1,0,2] differ from actual copy turns [0,1], with duplicate failures. -/
theorem finite_root_ordered :
    (symbolicView accessStore,symbolicView accessAfterStore,
      symbolicView (TargetNestedArrayTransport.afterStore accessStore (.root 1) (.root 0)),
      numericView (TargetNestedArrayTransport.execute 128 hash accessNumeric (.root 1) (.root 0)),
      targetView accessRootAfter,context accessRootAfter,
      finiteQueries.map (fun q => q.read mixedOldRoot),finiteQueries.map (fun q => q.read (mixedOldRoot.overlay accessSourceRoot)),
      finiteReads.map (fun q => q.read accessSourceRoot),finiteChildren.map Fin.val,
      (accessRootAfter.store (.data (.root 1) 2),accessRootAfter.store (.data (.data (.root 1) 2) 0))) =
    ([w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 3,w 23,w 29,w 31,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 1,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 2,w 41,w 43,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
     [w 2,w 2,w 1,w 7,w 11,w 13,w 1,w 17,w 19,w 1,w 71,w 1,w 7,w 0,w 0,w 37,w 1,w 17,w 0,w 47,w 2,w 53,w 59,w 61,w 73],
     [2,2,1,7,11,13,1,17,19,1,71,1,7,0,0,37,1,17,0,47,2,53,59,61,73],context accessTarget,
     [some (w 1),none,none,none,none,none,none,none,none,some (w 3),some (w 23),some (w 29),some (w 31),some (w 37),none,none,none,none],
     [some (w 2),none,none,none,none,some (w 1),some (w 17),none,none,some (w 1),some (w 7),some (w 0),some (w 0),some (w 37),none,none,none,none],
     [some (w 2),some (w 1),some (w 17),some (w 1),some (w 7)],[2,1,0,2],(2,53)) := by rfl

private def finiteWrongAfter := TargetArrayCopyTail.afterCopy accessRootAfter tail (.data (.root 0) 2) (.data (.root 1) 2)
/-- Executing an observed NONLIVE child as though observers drove copy turns
runs actual inner loops and corrupts the separate physical operation contract. -/
theorem finite_wrong_observer_copy :
    Evm.run TargetArrayCopy.code { accessRootAfter with stack := .slot (.data (.root 0) 2) :: .slot (.data (.root 1) 2) :: tail } = .ok finiteWrongAfter 0 ∧
    (targetView finiteWrongAfter,context finiteWrongAfter) =
      ([2,2,1,7,11,13,1,17,19,1,71,1,7,0,0,37,1,17,0,47,1,71,0,61,73],context accessTarget) := by
  exact ⟨TargetArrayCopyTail.run_current _ _ _ _,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.finite_root_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms finite_root_bridge
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.finite_root_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms finite_root_ordered
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.finite_wrong_observer_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms finite_wrong_observer_copy

end Solidity.Backend.StorageOps.TargetNestedArrayTransportControls
