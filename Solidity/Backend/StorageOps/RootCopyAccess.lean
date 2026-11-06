import Solidity.Backend.StorageOps.NestedRootComposition
import Solidity.Backend.StorageOps.CopyAccess

/-! Exact source-read demand propagation into actual full ROOT copy output.
Old broad root interfaces remain unchanged; every real access stays covered. -/
namespace Solidity.Backend.StorageOps.RootCopyAccess
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- The retained-live destination query may be older than the source's live
prefix. Only the captured header and selected LIVE source words need snapshot
representation/separation. No unread corresponding source coverage is assumed. -/
theorem retained_child {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (old source : Value G (.array (.array (.prim p)))) (i : Index) (indices : List Index)
    (oldInside : i.val < old.extent.val) (live : i.val < source.length.val)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (tail : List Evm.Word)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (beforeDst : Represented old ((PrimitivePop.queries indices).map (Query.prefix (NestedCopyObservations.childPath i))) dst store)
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
    (visitedCovered : ∀ j < max (NestedCopyObservations.child old i).length.val (NestedCopyObservations.child source i).length.val,
      Solidity.Storage.Loc.data (.data dst i.val) j ∈ locations)

    (sourceHeaderOwner : Represented source [.length .nil] src store)
    (dstHeader : dst ∈ locations) (srcHeader : src ∈ locations)
    (clearHeaders : ∀ k < max source.length.val (store dst).val.toNat, source.length.val ≤ k → Solidity.Storage.Loc.data dst k ∈ locations)
    (clearWrites : ∀ k < max source.length.val (store dst).val.toNat, source.length.val ≤ k →
      ∀ j < ((TargetNestedArrayTransport.clearStores
        (TargetNestedArrayTransport.copyStores store dst src source.length.val) dst source.length.val k) (.data dst k)).val.toNat,
        Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    (dstApart : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices,
      TargetOperations.toSlot (q.location (.data dst i.val)) (TargetOperations.query_keysFit q (.data dst i.val) dstFits) ∉
      TargetNestedArrayCopyLoop.touched target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) i.val)
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
  have oldChild : Represented (NestedCopyObservations.child old i) (PrimitivePop.queries indices) (.data dst i.val) store := by
    simpa only [NestedRetainedCopy.child_location] using
      PathRepresentation.focus old _ _ (NestedCopyObservations.find_child old i oldInside) _ dst store beforeDst
  have sourceChild : Represented (NestedCopyObservations.child source i)
      (CopyAccess.readQueries (NestedCopyObservations.child source i) indices) (.data src i.val) store := by
    simpa only [NestedRetainedCopy.child_location] using
      PathRepresentation.focus source _ _ (NestedCopyObservations.find_child source i sourceInside) _ src store beforeSrc
  have partialHeaders := fun k (inside : k < i.val) => headers k (by omega)
  have partialReads := fun k (inside : k < i.val) => reads k (by omega)
  have partialWrites := fun k (inside : k < i.val) => writes k (by omega)
  have previous := TargetNestedArrayTransport.copy_prefix run dst src dstFits srcFits store numeric target i.val initial fitting targetInitial partialHeaders partialReads partialWrites
  have dstQueries : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, q.location (.data dst i.val) ∈ locations := by
    intro q member
    simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
    rcases member with rfl | ⟨j,inside,rfl⟩
    · exact (headers i.val live).1
    · rw [PrimitivePop.element_location]; exact dstCovered j inside
  have srcQueries : ∀ q ∈ CopyAccess.readQueries (NestedCopyObservations.child source i) indices,
      q.location (.data src i.val) ∈ locations := by
    intro q member
    simp only [CopyAccess.readQueries,List.mem_cons,List.mem_map] at member
    rcases member with rfl | ⟨j,filtered,rfl⟩
    · exact (headers i.val live).2
    · rw [PrimitivePop.element_location]
      exact sourceCovered j.val (by simpa only [decide_eq_true_eq] using (List.mem_filter.mp filtered).2)
  have oldCurrent := NestedSnapshotFrames.represented_copy_frame run dst src dstFits srcFits store numeric target i.val initial fitting targetInitial
    partialHeaders partialReads partialWrites _ _ _ oldChild dstQueries dstApart
  have sourceCurrent := NestedSnapshotFrames.represented_copy_frame run dst src dstFits srcFits store numeric target i.val initial fitting targetInitial
    partialHeaders partialReads partialWrites _ _ _ sourceChild srcQueries srcApart
  have copied := CopyAccess.represented run (NestedCopyObservations.child old i) (NestedCopyObservations.child source i) indices
    (.data dst i.val) (.data src i.val) (TargetNestedArrayTransport.copyStores store dst src i.val)
    (TargetNestedArrayTransport.copyNumerics N hash numeric dst src i.val) oldCurrent sourceCurrent previous.1
    (headers i.val live).1 (headers i.val live).2 dstCovered sourceCovered visitedCovered
  have childOwner : Represented ((NestedCopyObservations.child old i).overlay (NestedCopyObservations.child source i))
      (PrimitivePop.queries indices) (.data dst i.val) (TargetNestedArrayTransport.copyStores store dst src (i.val+1)) := copied.2
  have completed := NestedPhaseComposition.finish_child run dst src dstFits srcFits store numeric target tail initial fitting targetInitial
    dstHeader srcHeader (by simpa only [countKnown] using headers) (by simpa only [countKnown] using reads)
    (by simpa only [countKnown] using writes) (by simpa only [countKnown] using clearHeaders)
    (by simpa only [countKnown] using clearWrites)
    ((NestedCopyObservations.child old i).overlay (NestedCopyObservations.child source i)) indices (i.val+1) i.val
    (by omega) (by omega) childOwner (by
      intro q member
      simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
      rcases member with rfl | ⟨j,inside,rfl⟩
      · exact (headers i.val live).1
      · rw [PrimitivePop.element_location]; exact dstCovered j inside)
  have supported : PathSupported (NestedCopyObservations.childPath (G := G) (p := p) i) :=
    ((Query.supported_prefix _ (.length .nil)).mp
      (beforeDst _ (List.mem_map.mpr ⟨_,List.mem_cons_self,rfl⟩)).1).1
  have finalChild : Represented ((NestedCopyObservations.child old i).overlay (NestedCopyObservations.child source i))
      (PrimitivePop.queries indices) (pathLoc (NestedCopyObservations.childPath (G := G) (p := p) i) dst)
      (TargetNestedArrayTransport.afterStore store dst src) := by
    simpa only [NestedRetainedCopy.child_location] using completed.2.1
  exact ⟨completed.1,Represented.prefix _ (NestedCopyObservations.overlay_find_live old source i live) supported finalChild,completed.2.2⟩


/-- info: 'Solidity.Backend.StorageOps.RootCopyAccess.retained_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms retained_child

/-- Source demand family is header plus per-child LIVE read slices. Reuses
existing typed Query/Path values; no source/value/state representation layer. -/
def sourceQueries {n : Nat} {G : Schema n} {p : PrimTy}
    (source : Value G (.array (.array (.prim p)))) (children : List Index) (indices : Index → List Index) :
    List (Query G (.array (.array (.prim p)))) :=
  .length .nil :: children.flatMap (fun i =>
    (CopyAccess.readQueries (NestedCopyObservations.child source i) (indices i)).map (Query.prefix (NestedCopyObservations.childPath i)))

/-- Full actual program and selected retained-live ROOT output with precise
source read demands. ALL target observations and actual accesses stay covered. -/
theorem live_root {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (old source : Value G (.array (.array (.prim p)))) (children : List Index) (indices : Index → List Index)
    (selected : ∀ i ∈ children, i.val < old.extent.val ∧ i.val < source.length.val)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (tail : List Evm.Word)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (beforeDst : Represented old (NestedRootComposition.rootQueries children indices) dst store)
    (beforeSrc : Represented source (sourceQueries source children indices) src store)
    (dstHeader : dst ∈ locations) (srcHeader : src ∈ locations)
    (headers : ∀ k < source.length.val, Solidity.Storage.Loc.data dst k ∈ locations ∧ Solidity.Storage.Loc.data src k ∈ locations)
    (reads : ∀ k < source.length.val, ∀ j < ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data src k) j ∈ locations)
    (writes : ∀ k < source.length.val, ∀ j < max ((TargetNestedArrayTransport.copyStores store dst src k) (.data dst k)).val.toNat
        ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    (clearHeaders : ∀ k < max source.length.val (store dst).val.toNat, source.length.val ≤ k → Solidity.Storage.Loc.data dst k ∈ locations)
    (clearWrites : ∀ k < max source.length.val (store dst).val.toNat, source.length.val ≤ k →
      ∀ j < ((TargetNestedArrayTransport.clearStores
        (TargetNestedArrayTransport.copyStores store dst src source.length.val) dst source.length.val k) (.data dst k)).val.toNat,
        Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    (dstCovered : ∀ i ∈ children, ∀ j ∈ indices i, Solidity.Storage.Loc.data (.data dst i.val) j.val ∈ locations)
    (sourceCovered : ∀ i ∈ children, ∀ j < (NestedCopyObservations.child source i).length.val,
      Solidity.Storage.Loc.data (.data src i.val) j ∈ locations)
    (visitedCovered : ∀ i ∈ children, ∀ j < max (NestedCopyObservations.child old i).length.val (NestedCopyObservations.child source i).length.val,
      Solidity.Storage.Loc.data (.data dst i.val) j ∈ locations)
    (dstApart : ∀ i ∈ children, ∀ q ∈ PrimitivePop.queries (G := G) (p := p) (indices i),
      TargetOperations.toSlot (q.location (.data dst i.val)) (TargetOperations.query_keysFit q (.data dst i.val) dstFits) ∉
      TargetNestedArrayCopyLoop.touched target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) i.val)
    (srcApart : ∀ i ∈ children, ∀ q ∈ CopyAccess.readQueries (NestedCopyObservations.child source i) (indices i),
      TargetOperations.toSlot (q.location (.data src i.val)) (TargetOperations.query_keysFit q (.data src i.val) srcFits) ∉
      TargetNestedArrayCopyLoop.touched target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) i.val) :
    Evm.run TargetNestedArrayCopy.code { target with stack := .slot (TargetOperations.toSlot src srcFits) :: .slot (TargetOperations.toSlot dst dstFits) :: tail } =
      .ok (TargetNestedArrayRuntime.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)) 0 ∧
    Represented (old.overlay source) (NestedRootComposition.rootQueries children indices) dst (TargetNestedArrayTransport.afterStore store dst src) ∧
    Transport N hash locations (TargetNestedArrayTransport.afterStore store dst src) (TargetNestedArrayTransport.execute N hash numeric dst src) ∧
    (∀ l (member : l ∈ locations),
      (TargetNestedArrayRuntime.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store.cells
        (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore store dst src l)) := by
  have oldHeader : Represented old [.length .nil] dst store := by
    intro q member; have same := List.mem_singleton.mp member; subst q
    exact beforeDst _ List.mem_cons_self
  have sourceHeader : Represented source [.length .nil] src store := by
    intro q member; have same := List.mem_singleton.mp member; subst q
    exact beforeSrc _ List.mem_cons_self
  have captured : store src = lengthWord source.length.val source.length.isLt :=
    (sourceHeader (.length .nil) List.mem_cons_self).2.2 _ (by cases source; rfl)
  have countKnown : (store src).val.toNat = source.length.val := by rw [captured]; rfl
  have finished : ∀ i ∈ children,
      Represented (old.overlay source) ((PrimitivePop.queries (indices i)).map (Query.prefix (NestedCopyObservations.childPath i))) dst
        (TargetNestedArrayTransport.afterStore store dst src) := by
    intro i member
    have oldChild : Represented old ((PrimitivePop.queries (indices i)).map (Query.prefix (NestedCopyObservations.childPath i))) dst store := by
      intro q inside
      exact beforeDst q (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨i,member,inside⟩))
    have sourceChild : Represented source ((CopyAccess.readQueries (NestedCopyObservations.child source i) (indices i)).map (Query.prefix (NestedCopyObservations.childPath i))) src store := by
      intro q inside
      exact beforeSrc q (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨i,member,inside⟩))
    have result := retained_child run old source i (indices i) (selected i member).1 (selected i member).2
      dst src dstFits srcFits store numeric target tail initial fitting targetInitial oldChild sourceChild headers reads writes
      (dstCovered i member) (sourceCovered i member) (visitedCovered i member)
      sourceHeader dstHeader srcHeader clearHeaders clearWrites (dstApart i member) (srcApart i member)
    exact result.2.1
  have owner : Represented (old.overlay source) (NestedRootComposition.rootQueries children indices) dst (TargetNestedArrayTransport.afterStore store dst src) := by
    intro q member
    simp only [NestedRootComposition.rootQueries,List.mem_cons,List.mem_flatMap] at member
    rcases member with rfl | ⟨i,inside,observation⟩
    · exact NestedRootComposition.root_header old source dst src store oldHeader sourceHeader _ List.mem_cons_self
    · exact finished i inside q observation
  have actual := TargetNestedArrayTransport.complete run dst src dstFits srcFits store numeric target tail initial fitting targetInitial
    dstHeader srcHeader (by simpa only [countKnown] using headers) (by simpa only [countKnown] using reads)
    (by simpa only [countKnown] using writes) (by simpa only [countKnown] using clearHeaders)
    (by simpa only [countKnown] using clearWrites)
  exact ⟨actual.1,owner,actual.2⟩

/-- info: 'Solidity.Backend.StorageOps.RootCopyAccess.sourceQueries' does not depend on any axioms -/
#guard_msgs in #print axioms sourceQueries
/-- info: 'Solidity.Backend.StorageOps.RootCopyAccess.live_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms live_root
end Solidity.Backend.StorageOps.RootCopyAccess
