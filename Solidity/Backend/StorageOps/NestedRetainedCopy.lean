import Solidity.Backend.StorageOps.NestedSnapshotFrames
import Solidity.Backend.StorageOps.NestedCopyObservations
import Solidity.Backend.StorageOps.PathRepresentation

/-! Retained-child snapshot composition for an actual runtime nested prefix.
OLD root observations and exact generated access separation derive BOTH current
child owners; no desired copy postcondition is supplied as a premise. -/
namespace Solidity.Backend.StorageOps.NestedRetainedCopy
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

theorem child_location {n : Nat} {G : Schema n} {p : PrimTy} (i : Index) (base : Solidity.Storage.Loc) :
    pathLoc (NestedCopyObservations.childPath (G := G) (p := p) i) base = .data base i.val := by
  simp only [NestedCopyObservations.childPath,pathLoc,stepLoc,inlineSize_array,Nat.mul_one]

private theorem selected_covered {n : Nat} {G : Schema n} {p : PrimTy} (indices : List Index)
    (base : Solidity.Storage.Loc) (locations : List Solidity.Storage.Loc)
    (header : base ∈ locations)
    (dataCovered : ∀ i ∈ indices, Solidity.Storage.Loc.data base i.val ∈ locations) :
    ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, q.location base ∈ locations := by
  intro q member
  simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
  rcases member with rfl | ⟨i,inside,rfl⟩
  · exact header
  · rw [PrimitivePop.element_location]; exact dataCovered i inside

/-- Preserved retained extents and independent snapshot payloads, at ANY runtime
outer index. Complete CURRENT generated accesses are covered by the original
finite run. Nonalias is local to selected original queries versus actual writes. -/
theorem copied_child {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (old source : Value G (.array (.array (.prim p)))) (i : Index) (indices : List Index)
    (oldInside : i.val < old.extent.val) (live : i.val < source.length.val)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (beforeDst : Represented old ((PrimitivePop.queries indices).map (Query.prefix (NestedCopyObservations.childPath i))) dst store)
    (beforeSrc : Represented source ((PrimitivePop.queries indices).map (Query.prefix (NestedCopyObservations.childPath i))) src store)
    (headers : ∀ k < i.val+1, Solidity.Storage.Loc.data dst k ∈ locations ∧ Solidity.Storage.Loc.data src k ∈ locations)
    (reads : ∀ k < i.val+1, ∀ j < ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data src k) j ∈ locations)
    (writes : ∀ k < i.val+1, ∀ j < max ((TargetNestedArrayTransport.copyStores store dst src k) (.data dst k)).val.toNat
        ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    (dstCovered : ∀ j ∈ indices, Solidity.Storage.Loc.data (.data dst i.val) j.val ∈ locations)
    (srcCovered : ∀ j ∈ indices, Solidity.Storage.Loc.data (.data src i.val) j.val ∈ locations)
    (sourceCovered : ∀ j < (NestedCopyObservations.child source i).length.val,
      Solidity.Storage.Loc.data (.data src i.val) j ∈ locations)
    (visitedCovered : ∀ j < max (NestedCopyObservations.child old i).length.val (NestedCopyObservations.child source i).length.val,
      Solidity.Storage.Loc.data (.data dst i.val) j ∈ locations)
    (dstApart : ∀ q (member : q ∈ PrimitivePop.queries (G := G) (p := p) indices),
      TargetOperations.toSlot (q.location (.data dst i.val))
        (fitting _ (selected_covered indices (.data dst i.val) locations (headers i.val (Nat.lt_succ_self _)).1 dstCovered q member)) ∉
      TargetNestedArrayCopyLoop.touched target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) i.val)
    (srcApart : ∀ q (member : q ∈ PrimitivePop.queries (G := G) (p := p) indices),
      TargetOperations.toSlot (q.location (.data src i.val))
        (fitting _ (selected_covered indices (.data src i.val) locations (headers i.val (Nat.lt_succ_self _)).2 srcCovered q member)) ∉
      TargetNestedArrayCopyLoop.touched target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) i.val) :
    Represented (old.overlay source) ((PrimitivePop.queries indices).map (Query.prefix (NestedCopyObservations.childPath i))) dst
      (TargetNestedArrayTransport.copyStores store dst src (i.val+1)) ∧
    Transport N hash locations (TargetNestedArrayTransport.copyStores store dst src (i.val+1))
      (TargetNestedArrayTransport.copyNumerics N hash numeric dst src (i.val+1)) ∧
    (∀ l (member : l ∈ locations),
      (TargetNestedArrayCopyLoop.prefixMachine target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) (i.val+1)).store.cells
        (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (TargetNestedArrayTransport.copyStores store dst src (i.val+1) l)) := by
  have sourceInside : i.val < source.extent.val := Nat.lt_of_lt_of_le live (by cases source; assumption)
  have oldChild : Represented (NestedCopyObservations.child old i) (PrimitivePop.queries indices) (.data dst i.val) store := by
    simpa only [child_location] using PathRepresentation.focus old _ _ (NestedCopyObservations.find_child old i oldInside) _ dst store beforeDst
  have sourceChild : Represented (NestedCopyObservations.child source i) (PrimitivePop.queries indices) (.data src i.val) store := by
    simpa only [child_location] using PathRepresentation.focus source _ _ (NestedCopyObservations.find_child source i sourceInside) _ src store beforeSrc
  have previousHeaders := fun k (inside : k < i.val) => headers k (Nat.lt_trans inside (Nat.lt_succ_self i.val))
  have previousReads := fun k (inside : k < i.val) => reads k (Nat.lt_trans inside (Nat.lt_succ_self i.val))
  have previousWrites := fun k (inside : k < i.val) => writes k (Nat.lt_trans inside (Nat.lt_succ_self i.val))
  have previous := TargetNestedArrayTransport.copy_prefix run dst src dstFits srcFits store numeric target i.val initial fitting targetInitial previousHeaders previousReads previousWrites
  have currentHeaders := headers i.val (Nat.lt_succ_self _)
  have oldCurrent := NestedSnapshotFrames.represented_copy_frame run dst src dstFits srcFits store numeric target i.val initial fitting targetInitial
    previousHeaders previousReads previousWrites _ _ _ oldChild (selected_covered indices _ locations currentHeaders.1 dstCovered) dstApart
  have sourceCurrent := NestedSnapshotFrames.represented_copy_frame run dst src dstFits srcFits store numeric target i.val initial fitting targetInitial
    previousHeaders previousReads previousWrites _ _ _ sourceChild (selected_covered indices _ locations currentHeaders.2 srcCovered) srcApart
  have copied := CopyTransport.complete run (NestedCopyObservations.child old i) (NestedCopyObservations.child source i) indices
    (.data dst i.val) (.data src i.val) (TargetNestedArrayTransport.copyStores store dst src i.val)
    (TargetNestedArrayTransport.copyNumerics N hash numeric dst src i.val) oldCurrent sourceCurrent previous.1
    currentHeaders.1 currentHeaders.2 dstCovered srcCovered sourceCovered visitedCovered
  have result : Represented ((NestedCopyObservations.child old i).overlay (NestedCopyObservations.child source i))
      (PrimitivePop.queries indices) (pathLoc (NestedCopyObservations.childPath (G := G) (p := p) i) dst)
      (TargetNestedArrayTransport.copyStores store dst src (i.val+1)) := by
    simpa only [recursiveCopy_eq_overlay,child_location,TargetNestedArrayTransport.copyStores] using copied.2
  have supported : PathSupported (NestedCopyObservations.childPath (G := G) (p := p) i) :=
    ((Query.supported_prefix _ (.length .nil)).mp
      (beforeDst _ (List.mem_map.mpr ⟨_,List.mem_cons_self,rfl⟩)).1).1
  have final := TargetNestedArrayTransport.copy_prefix run dst src dstFits srcFits store numeric target (i.val+1) initial fitting targetInitial headers reads writes
  exact ⟨Represented.prefix _ (NestedCopyObservations.overlay_find_live old source i live) supported result,final⟩

/-- info: 'Solidity.Backend.StorageOps.NestedRetainedCopy.child_location' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms child_location
/-- info: 'Solidity.Backend.StorageOps.NestedRetainedCopy.copied_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copied_child
end Solidity.Backend.StorageOps.NestedRetainedCopy
