import Solidity.Backend.StorageOps.TargetFixedArrayTransport

/-! Exact generated update-log frames for fixed-child snapshot composition.
This module adapts existing Store/Represented operations; no new relation/state. -/
namespace Solidity.Backend.StorageOps.FixedSnapshotFrames
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def log (initial : Store) (dst src : Solidity.Storage.Loc) (start : Nat) : Nat → List (Solidity.Storage.Loc × Semantics.Word)
  | 0 => []
  | count+1 => log initial dst src start count ++
      CopyTransport.updates (dst.add (start+count)) (src.add (start+count))
        (TargetFixedArrayTransport.stores initial dst src start count)

theorem stores_log (initial : Store) (dst src : Solidity.Storage.Loc) (start count : Nat) :
    TargetFixedArrayTransport.stores initial dst src start count =
      (log initial dst src start count).foldl (fun w op => Representation.write w op.1 op.2) initial := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [log,List.foldl_append,← ih]
    rfl

/-- A generated-store frame includes successful and failed logical queries:
only actual stored words are framed, and no failed read is assigned zero. -/
theorem fold_outside (operations : List (Solidity.Storage.Loc × Semantics.Word))
    (initial : Store) (observer : Solidity.Storage.Loc)
    (outside : ∀ op ∈ operations, observer ≠ op.1) :
    operations.foldl (fun w op => Representation.write w op.1 op.2) initial observer = initial observer := by
  induction operations generalizing initial with
  | nil => rfl
  | cons op rest ih =>
    change rest.foldl (fun w pair => Representation.write w pair.1 pair.2)
      (Representation.write initial op.1 op.2) observer = _
    rw [ih _ (fun pair inside => outside pair (List.mem_cons_of_mem _ inside))]
    exact Representation.write_other _ _ _ _ (outside op List.mem_cons_self)

theorem prefix_outside (initial : Store) (dst src observer : Solidity.Storage.Loc) (start count : Nat)
    (outside : ∀ op ∈ log initial dst src start count, observer ≠ op.1) :
    TargetFixedArrayTransport.stores initial dst src start count observer = initial observer := by
  rw [stores_log]
  exact fold_outside _ _ _ outside

/-- The PUBLIC owner relation itself is reused. Every selected observation is
framed from its OLD evidence and exact generated write-address nonaliasing. -/
theorem represented_prefix {n : Nat} {G : Schema n} {A : TypeGraph.Ty n}
    (value : Value G A) (queries : List (Query G A)) (base : Solidity.Storage.Loc)
    (initial : Store) (dst src : Solidity.Storage.Loc) (start count : Nat)
    (before : Represented value queries base initial)
    (outside : ∀ q ∈ queries, ∀ op ∈ log initial dst src start count, q.location base ≠ op.1) :
    Represented value queries base (TargetFixedArrayTransport.stores initial dst src start count) := by
  intro q member
  obtain ⟨supported,compatible,observed⟩ := before q member
  refine ⟨supported,compatible,?_⟩
  intro word read
  rw [prefix_outside initial dst src (q.location base) start count (outside q member)]
  exact observed word read

/-- The next CURRENT child copy realizes the ORIGINAL independent fixed-root
snapshot observation when earlier generated writes avoid BOTH selected OLD
child observation sets. Neither intermediate owner relation is a premise. -/
theorem snapshot_child {n N L R : Nat} {G : Schema n} {p : PrimTy} {m : FixedSize}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (old source : Value G (.fixed (.array (.prim p)) m)) (i : Fin m.val) (indices : List Index)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (beforeDst : Represented old ((PrimitivePop.queries indices).map (Query.prefix (TargetFixedArrayCopy.childPath m i))) dst store)
    (beforeSrc : Represented source ((PrimitivePop.queries indices).map (Query.prefix (TargetFixedArrayCopy.childPath m i))) src store)
    (headers : ∀ k < i.val+1, dst.add k ∈ locations ∧ src.add k ∈ locations)
    (reads : ∀ k < i.val+1, ∀ j < ((TargetFixedArrayTransport.stores store dst src 0 k) (src.add k)).val.toNat,
      Solidity.Storage.Loc.data (src.add k) j ∈ locations)
    (writes : ∀ k < i.val+1, ∀ j < max ((TargetFixedArrayTransport.stores store dst src 0 k) (dst.add k)).val.toNat
        ((TargetFixedArrayTransport.stores store dst src 0 k) (src.add k)).val.toNat,
      Solidity.Storage.Loc.data (dst.add k) j ∈ locations)
    (dstCovered : ∀ j ∈ indices, Solidity.Storage.Loc.data (dst.add i.val) j.val ∈ locations)
    (srcCovered : ∀ j ∈ indices, Solidity.Storage.Loc.data (src.add i.val) j.val ∈ locations)
    (sourceCovered : ∀ j < (TargetFixedArrayCopy.child source i).length.val, Solidity.Storage.Loc.data (src.add i.val) j ∈ locations)
    (visitedCovered : ∀ j < max (TargetFixedArrayCopy.child old i).length.val (TargetFixedArrayCopy.child source i).length.val,
      Solidity.Storage.Loc.data (dst.add i.val) j ∈ locations)
    (dstApart : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, ∀ op ∈ log store dst src 0 i.val,
      q.location (dst.add i.val) ≠ op.1)
    (srcApart : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, ∀ op ∈ log store dst src 0 i.val,
      q.location (src.add i.val) ≠ op.1) :
    Transport N hash locations (TargetFixedArrayTransport.stores store dst src 0 (i.val+1))
      (TargetFixedArrayTransport.numerics N hash numeric dst src 0 (i.val+1)) ∧
    Represented (old.overlay source) ((PrimitivePop.queries indices).map (Query.prefix (TargetFixedArrayCopy.childPath m i))) dst
      (TargetFixedArrayTransport.stores store dst src 0 (i.val+1)) := by
  have oldChild : Represented (TargetFixedArrayCopy.child old i) (PrimitivePop.queries indices) (dst.add i.val) store := by
    simpa only [TargetFixedArrayCopy.child_location] using PathRepresentation.focus old _ _ (TargetFixedArrayCopy.find_child old i) _ dst store beforeDst
  have sourceChild : Represented (TargetFixedArrayCopy.child source i) (PrimitivePop.queries indices) (src.add i.val) store := by
    simpa only [TargetFixedArrayCopy.child_location] using PathRepresentation.focus source _ _ (TargetFixedArrayCopy.find_child source i) _ src store beforeSrc
  have previous := TargetFixedArrayTransport.prefix_transport run dst src dstFits srcFits store numeric target 0 i.val initial fitting targetInitial
    (by simpa only [Nat.zero_add] using fun k h => headers k (Nat.lt_trans h (Nat.lt_succ_self i.val)))
    (by simpa only [Nat.zero_add] using fun k h => reads k (Nat.lt_trans h (Nat.lt_succ_self i.val)))
    (by simpa only [Nat.zero_add] using fun k h => writes k (Nat.lt_trans h (Nat.lt_succ_self i.val)))
  have oldCurrent := represented_prefix _ _ (dst.add i.val) store dst src 0 i.val oldChild dstApart
  have sourceCurrent := represented_prefix _ _ (src.add i.val) store dst src 0 i.val sourceChild srcApart
  have result := CopyTransport.complete run (TargetFixedArrayCopy.child old i) (TargetFixedArrayCopy.child source i) indices
    (dst.add i.val) (src.add i.val) (TargetFixedArrayTransport.stores store dst src 0 i.val)
    (TargetFixedArrayTransport.numerics N hash numeric dst src 0 i.val) oldCurrent sourceCurrent previous.1
    (headers i.val (Nat.lt_succ_self i.val)).1 (headers i.val (Nat.lt_succ_self i.val)).2
    dstCovered srcCovered sourceCovered visitedCovered
  refine ⟨?_,?_⟩
  · simpa only [TargetFixedArrayTransport.stores,TargetFixedArrayTransport.numerics,Nat.zero_add] using result.1
  · have represented : Represented (TargetFixedArrayCopy.child (old.overlay source) i) (PrimitivePop.queries indices)
        (pathLoc (TargetFixedArrayCopy.childPath (G := G) (p := p) m i) dst) (TargetFixedArrayTransport.stores store dst src 0 (i.val+1)) := by
      simpa only [TargetFixedArrayCopy.child_overlay,TargetFixedArrayCopy.child_location,
        recursiveCopy_eq_overlay,TargetFixedArrayTransport.stores,Nat.zero_add] using result.2
    apply Represented.prefix (TargetFixedArrayCopy.childPath m i) (TargetFixedArrayCopy.find_child (old.overlay source) i) _ represented
    exact ⟨i.isLt,True.intro⟩

/-- Exact evolving-store restart uses the SAME current child operations. -/
theorem stores_append (initial : Store) (dst src : Solidity.Storage.Loc) (start count rest : Nat) :
    TargetFixedArrayTransport.stores initial dst src start (count+rest) =
      TargetFixedArrayTransport.stores (TargetFixedArrayTransport.stores initial dst src start count) dst src (start+count) rest := by
  induction rest with
  | zero => rfl
  | succ rest ih =>
    change CopyTransport.symbolicCopy (dst.add (start+(count+rest))) (src.add (start+(count+rest)))
      (TargetFixedArrayTransport.stores initial dst src start (count+rest)) =
      CopyTransport.symbolicCopy (dst.add ((start+count)+rest)) (src.add ((start+count)+rest))
        (TargetFixedArrayTransport.stores (TargetFixedArrayTransport.stores initial dst src start count) dst src (start+count) rest)
    rw [ih,Nat.add_assoc]

/-- Processed child owner observations survive the remaining actual generated
writes. Together with snapshot_child this supplies old/done/unvisited frames;
nonaliasing is checked on the actual suffix log, not assumed postpreservation. -/
theorem represented_suffix {n : Nat} {G : Schema n} {A : TypeGraph.Ty n}
    (value : Value G A) (queries : List (Query G A)) (base : Solidity.Storage.Loc)
    (initial : Store) (dst src : Solidity.Storage.Loc) (start count rest : Nat)
    (before : Represented value queries base (TargetFixedArrayTransport.stores initial dst src start count))
    (outside : ∀ q ∈ queries, ∀ op ∈ log (TargetFixedArrayTransport.stores initial dst src start count) dst src (start+count) rest,
      q.location base ≠ op.1) :
    Represented value queries base (TargetFixedArrayTransport.stores initial dst src start (count+rest)) := by
  rw [stores_append]
  exact represented_prefix value queries base _ dst src (start+count) rest before outside

/-- info: 'Solidity.Backend.StorageOps.FixedSnapshotFrames.log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms log
/-- info: 'Solidity.Backend.StorageOps.FixedSnapshotFrames.stores_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stores_log
/-- info: 'Solidity.Backend.StorageOps.FixedSnapshotFrames.fold_outside' does not depend on any axioms -/
#guard_msgs in #print axioms fold_outside
/-- info: 'Solidity.Backend.StorageOps.FixedSnapshotFrames.prefix_outside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms prefix_outside
/-- info: 'Solidity.Backend.StorageOps.FixedSnapshotFrames.represented_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_prefix
/-- info: 'Solidity.Backend.StorageOps.FixedSnapshotFrames.snapshot_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms snapshot_child
/-- info: 'Solidity.Backend.StorageOps.FixedSnapshotFrames.stores_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms stores_append
/-- info: 'Solidity.Backend.StorageOps.FixedSnapshotFrames.represented_suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_suffix

end Solidity.Backend.StorageOps.FixedSnapshotFrames
