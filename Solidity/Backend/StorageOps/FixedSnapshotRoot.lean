import Solidity.Backend.StorageOps.FixedSnapshotFrames

/-! Whole selected fixed-root observation composition under explicit generated
access conditions. Independent snapshot semantics remains Value.overlay. -/
namespace Solidity.Backend.StorageOps.FixedSnapshotRoot
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def queries {n : Nat} {G : Schema n} {p : PrimTy} (m : FixedSize) (indices : List Index) :
    List (Query G (.fixed (.array (.prim p)) m)) :=
  (List.finRange m.val).flatMap (fun i => (PrimitivePop.queries indices).map
    (Query.prefix (TargetFixedArrayCopy.childPath m i)))

/-- All intermediate child and processed-suffix relations are DERIVED from
original owner evidence and generated access conditions. This does not assert
those conditions for arbitrary overlapping Source layouts. -/
theorem complete {n N L R : Nat} {G : Schema n} {p : PrimTy} {m : FixedSize}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (old source : Value G (.fixed (.array (.prim p)) m)) (indices : List Index)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (beforeDst : ∀ i : Fin m.val, Represented old ((PrimitivePop.queries indices).map (Query.prefix (TargetFixedArrayCopy.childPath m i))) dst store)
    (beforeSrc : ∀ i : Fin m.val, Represented source ((PrimitivePop.queries indices).map (Query.prefix (TargetFixedArrayCopy.childPath m i))) src store)
    (headers : ∀ k < m.val, dst.add k ∈ locations ∧ src.add k ∈ locations)
    (reads : ∀ k < m.val, ∀ j < ((TargetFixedArrayTransport.stores store dst src 0 k) (src.add k)).val.toNat,
      Solidity.Storage.Loc.data (src.add k) j ∈ locations)
    (writes : ∀ k < m.val, ∀ j < max ((TargetFixedArrayTransport.stores store dst src 0 k) (dst.add k)).val.toNat
        ((TargetFixedArrayTransport.stores store dst src 0 k) (src.add k)).val.toNat,
      Solidity.Storage.Loc.data (dst.add k) j ∈ locations)
    (dstCovered : ∀ i : Fin m.val, ∀ j ∈ indices, Solidity.Storage.Loc.data (dst.add i.val) j.val ∈ locations)
    (srcCovered : ∀ i : Fin m.val, ∀ j ∈ indices, Solidity.Storage.Loc.data (src.add i.val) j.val ∈ locations)
    (sourceCovered : ∀ i : Fin m.val, ∀ j < (TargetFixedArrayCopy.child source i).length.val, Solidity.Storage.Loc.data (src.add i.val) j ∈ locations)
    (visitedCovered : ∀ i : Fin m.val, ∀ j < max (TargetFixedArrayCopy.child old i).length.val (TargetFixedArrayCopy.child source i).length.val,
      Solidity.Storage.Loc.data (dst.add i.val) j ∈ locations)
    (dstApart : ∀ i : Fin m.val, ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, ∀ op ∈ FixedSnapshotFrames.log store dst src 0 i.val,
      q.location (dst.add i.val) ≠ op.1)
    (srcApart : ∀ i : Fin m.val, ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, ∀ op ∈ FixedSnapshotFrames.log store dst src 0 i.val,
      q.location (src.add i.val) ≠ op.1)
    (suffixApart : ∀ i : Fin m.val, ∀ q ∈ (PrimitivePop.queries indices).map (Query.prefix (TargetFixedArrayCopy.childPath (G := G) (p := p) m i)),
      ∀ op ∈ FixedSnapshotFrames.log (TargetFixedArrayTransport.stores store dst src 0 (i.val+1)) dst src (i.val+1) (m.val-(i.val+1)),
        q.location dst ≠ op.1) :
    Evm.run (TargetFixedArrayCopy.code m (TargetOperations.toSlot dst dstFits) (TargetOperations.toSlot src srcFits)) target =
      .ok (TargetFixedArrayCopy.prefixMachine target (TargetOperations.toSlot dst dstFits) (TargetOperations.toSlot src srcFits) 0 m.val) 0 ∧
    Represented (old.overlay source) (queries m indices) dst (TargetFixedArrayTransport.stores store dst src 0 m.val) ∧
    Transport N hash locations (TargetFixedArrayTransport.stores store dst src 0 m.val)
      (TargetFixedArrayTransport.numerics N hash numeric dst src 0 m.val) ∧
    (∀ l (member : l ∈ locations),
      (TargetFixedArrayCopy.prefixMachine target (TargetOperations.toSlot dst dstFits) (TargetOperations.toSlot src srcFits) 0 m.val).store.cells
        (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (TargetFixedArrayTransport.stores store dst src 0 m.val l)) := by
  have current := TargetFixedArrayTransport.prefix_transport run dst src dstFits srcFits store numeric target 0 m.val initial fitting targetInitial
    (by simpa only [Nat.zero_add] using headers)
    (by simpa only [Nat.zero_add] using reads)
    (by simpa only [Nat.zero_add] using writes)
  refine ⟨TargetFixedArrayCopy.run_code _ _ _ _,?_,current.1,current.2⟩
  intro q member
  obtain ⟨i,_,inside⟩ := List.mem_flatMap.mp member
  have earlier : ∀ k < i.val+1, k < m.val := by
    intro k bound
    have limit := i.isLt
    omega
  have child := FixedSnapshotFrames.snapshot_child run old source i indices dst src dstFits srcFits store numeric target initial fitting targetInitial
    (beforeDst i) (beforeSrc i) (fun k bound => headers k (earlier k bound))
    (fun k bound => reads k (earlier k bound)) (fun k bound => writes k (earlier k bound))
    (dstCovered i) (srcCovered i) (sourceCovered i) (visitedCovered i) (dstApart i) (srcApart i)
  have finalChild := FixedSnapshotFrames.represented_suffix (old.overlay source)
    ((PrimitivePop.queries indices).map (Query.prefix (TargetFixedArrayCopy.childPath m i))) dst store dst src 0 (i.val+1) (m.val-(i.val+1))
    child.2 (by simpa only [Nat.zero_add] using suffixApart i)
  have total : i.val+1 + (m.val-(i.val+1)) = m.val := by
    have limit := i.isLt
    omega
  rw [total] at finalChild
  exact finalChild q inside

/-- info: 'Solidity.Backend.StorageOps.FixedSnapshotRoot.queries' does not depend on any axioms -/
#guard_msgs in #print axioms queries
/-- info: 'Solidity.Backend.StorageOps.FixedSnapshotRoot.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete

end Solidity.Backend.StorageOps.FixedSnapshotRoot
