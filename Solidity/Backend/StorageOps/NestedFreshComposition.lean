import Solidity.Backend.StorageOps.FreshCopyAccess
import Solidity.Backend.StorageOps.RootCopyAccess

/-! Fresh selected ROOT output with precise source demands, even with nonzero
unrepresented raw destination child history. Existing intrinsic graph/target
interfaces only; no default-world initialization or source admission claim. -/
namespace Solidity.Backend.StorageOps.NestedFreshComposition
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Logical missing extent yields the existing graph default, not a physical
zero header, allocation provenance or a full default representation relation. -/
theorem child_of_missing {n : Nat} {G : Schema n} {p : PrimTy}
    (old : Value G (.array (.array (.prim p)))) (i : Index) (missing : old.extent.val ≤ i.val) :
    NestedCopyObservations.child old i = Value.dflt _ := by
  cases old with
  | array extent length bound slots =>
    change extent.val ≤ i.val at missing
    simp only [NestedCopyObservations.child,NestedCopyObservations.childPath,Value.find,TypeGraph.Path.read,Step.get,
      dif_neg (Nat.not_lt_of_ge missing),Option.bind_none,Option.getD_none]

/-- Derive actual full-program selected FRESH ROOT output from OLD precise
source evidence and all actual accesses. No destination child owner/default
header/current/postowner is supplied. Output query support remains PUBLIC. -/
theorem fresh_child {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (old source : Value G (.array (.array (.prim p)))) (i : Index) (indices : List Index)
    (oldMissing : old.extent.val ≤ i.val) (live : i.val < source.length.val)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (tail : List Evm.Word)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (beforeSrc : Represented source ((CopyAccess.readQueries (NestedCopyObservations.child source i) indices).map (Query.prefix (NestedCopyObservations.childPath i))) src store)
    (headers : ∀ k < source.length.val, Solidity.Storage.Loc.data dst k ∈ locations ∧ Solidity.Storage.Loc.data src k ∈ locations)
    (reads : ∀ k < source.length.val, ∀ j < ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data src k) j ∈ locations)
    (writes : ∀ k < source.length.val, ∀ j < max ((TargetNestedArrayTransport.copyStores store dst src k) (.data dst k)).val.toNat
        ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    (dstCovered : ∀ j ∈ indices, Solidity.Storage.Loc.data (.data dst i.val) j.val ∈ locations)
    (sourceCovered : ∀ j < (NestedCopyObservations.child source i).length.val,
      Solidity.Storage.Loc.data (.data src i.val) j ∈ locations)
    (visitedCovered : ∀ j < max ((TargetNestedArrayTransport.copyStores store dst src i.val) (.data dst i.val)).val.toNat (NestedCopyObservations.child source i).length.val,
      Solidity.Storage.Loc.data (.data dst i.val) j ∈ locations)

    (outputSupported : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, q.supported)
    (sourceHeaderOwner : Represented source [.length .nil] src store)
    (dstHeader : dst ∈ locations) (srcHeader : src ∈ locations)
    (clearHeaders : ∀ k < max source.length.val (store dst).val.toNat, source.length.val ≤ k → Solidity.Storage.Loc.data dst k ∈ locations)
    (clearWrites : ∀ k < max source.length.val (store dst).val.toNat, source.length.val ≤ k →
      ∀ j < ((TargetNestedArrayTransport.clearStores
        (TargetNestedArrayTransport.copyStores store dst src source.length.val) dst source.length.val k) (.data dst k)).val.toNat,
        Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    (srcApart : ∀ q ∈ CopyAccess.readQueries (NestedCopyObservations.child source i) indices,
      TargetOperations.toSlot (q.location (.data src i.val)) (TargetOperations.query_keysFit q (.data src i.val) srcFits) ∉
      TargetNestedArrayCopyLoop.touched target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) i.val) :
    Evm.run TargetNestedArrayCopy.code { target with stack := .slot (TargetOperations.toSlot src srcFits) :: .slot (TargetOperations.toSlot dst dstFits) :: tail } =
      .ok (TargetNestedArrayRuntime.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)) 0 ∧
    Represented (old.overlay source) ((PrimitivePop.queries indices).map (Query.prefix (NestedCopyObservations.childPath i))) dst
      (TargetNestedArrayTransport.afterStore store dst src) ∧
    Transport N hash locations (TargetNestedArrayTransport.afterStore store dst src) (TargetNestedArrayTransport.execute N hash numeric dst src) ∧
    (∀ l (member : l ∈ locations),
      (TargetNestedArrayRuntime.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store.cells
        (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore store dst src l)) := by
  have captured : store src = lengthWord source.length.val source.length.isLt :=
    (sourceHeaderOwner (.length .nil) List.mem_cons_self).2.2 _ (by cases source; rfl)
  have countKnown : (store src).val.toNat = source.length.val := by rw [captured]; rfl
  have sourceInside : i.val < source.extent.val := Nat.lt_of_lt_of_le live (by cases source; assumption)
  have sourceChild : Represented (NestedCopyObservations.child source i)
      (CopyAccess.readQueries (NestedCopyObservations.child source i) indices) (.data src i.val) store := by
    simpa only [NestedRetainedCopy.child_location] using
      PathRepresentation.focus source _ _ (NestedCopyObservations.find_child source i sourceInside) _ src store beforeSrc
  have partialHeaders := fun k (inside : k < i.val) => headers k (by omega)
  have partialReads := fun k (inside : k < i.val) => reads k (by omega)
  have partialWrites := fun k (inside : k < i.val) => writes k (by omega)
  have previous := TargetNestedArrayTransport.copy_prefix run dst src dstFits srcFits store numeric target i.val initial fitting targetInitial partialHeaders partialReads partialWrites
  have srcQueries : ∀ q ∈ CopyAccess.readQueries (NestedCopyObservations.child source i) indices,
      q.location (.data src i.val) ∈ locations := by
    intro q member
    simp only [CopyAccess.readQueries,List.mem_cons,List.mem_map] at member
    rcases member with rfl | ⟨j,filtered,rfl⟩
    · exact (headers i.val live).2
    · rw [PrimitivePop.element_location]
      exact sourceCovered j.val (by simpa only [decide_eq_true_eq] using (List.mem_filter.mp filtered).2)
  have sourceCurrent := NestedSnapshotFrames.represented_copy_frame run dst src dstFits srcFits store numeric target i.val initial fitting targetInitial
    partialHeaders partialReads partialWrites _ _ _ sourceChild srcQueries srcApart
  have copied := FreshCopyAccess.represented run (NestedCopyObservations.child source i) indices
    (.data dst i.val) (.data src i.val) (TargetNestedArrayTransport.copyStores store dst src i.val)
    (TargetNestedArrayTransport.copyNumerics N hash numeric dst src i.val) sourceCurrent outputSupported previous.1
    (headers i.val live).1 (headers i.val live).2 dstCovered sourceCovered visitedCovered
  have childOwner : Represented (NestedCopyObservations.child source i).strip (PrimitivePop.queries indices) (.data dst i.val)
      (TargetNestedArrayTransport.copyStores store dst src (i.val+1)) := copied.1
  have finished := NestedPhaseComposition.finish_child run dst src dstFits srcFits store numeric target tail initial fitting targetInitial
    dstHeader srcHeader (by simpa only [countKnown] using headers) (by simpa only [countKnown] using reads)
    (by simpa only [countKnown] using writes) (by simpa only [countKnown] using clearHeaders) (by simpa only [countKnown] using clearWrites)
    (NestedCopyObservations.child source i).strip indices (i.val+1) i.val (by omega) (by omega) childOwner (by
      intro q member
      simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
      rcases member with rfl | ⟨j,inside,rfl⟩
      · exact (headers i.val live).1
      · rw [PrimitivePop.element_location]; exact dstCovered j inside)
  have supported : PathSupported (NestedCopyObservations.childPath (G := G) (p := p) i) :=
    ((Query.supported_prefix _ (.length .nil)).mp
      (beforeSrc _ (List.mem_map.mpr ⟨_,List.mem_cons_self,rfl⟩)).1).1
  have found : (old.overlay source).find (NestedCopyObservations.childPath i) = some (NestedCopyObservations.child source i).strip := by
    simpa only [child_of_missing old i oldMissing,Value.strip] using NestedCopyObservations.overlay_find_live old source i live
  have leaf : Represented (NestedCopyObservations.child source i).strip (PrimitivePop.queries indices)
      (pathLoc (NestedCopyObservations.childPath (G := G) (p := p) i) dst) (TargetNestedArrayTransport.afterStore store dst src) := by
    simpa only [NestedRetainedCopy.child_location] using finished.2.1
  exact ⟨finished.1,Represented.prefix _ found supported leaf,finished.2.2⟩

/-- info: 'Solidity.Backend.StorageOps.NestedFreshComposition.child_of_missing' depends on axioms: [propext] -/
#guard_msgs in #print axioms child_of_missing
/-- info: 'Solidity.Backend.StorageOps.NestedFreshComposition.fresh_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_child
end Solidity.Backend.StorageOps.NestedFreshComposition
