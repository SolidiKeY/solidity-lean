import Solidity.Backend.StorageOps.NestedPhaseComposition

/-! Selected retained live-child ROOT output for the full actual nested program.
Every middle child/phase owner is derived from OLD independent root evidence. -/
namespace Solidity.Backend.StorageOps.NestedRootComposition
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

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
    (beforeSrc : Represented source ((PrimitivePop.queries indices).map (Query.prefix (NestedCopyObservations.childPath i))) src store)
    (headers : ∀ k < source.length.val, Solidity.Storage.Loc.data dst k ∈ locations ∧ Solidity.Storage.Loc.data src k ∈ locations)
    (reads : ∀ k < source.length.val, ∀ j < ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data src k) j ∈ locations)
    (writes : ∀ k < source.length.val, ∀ j < max ((TargetNestedArrayTransport.copyStores store dst src k) (.data dst k)).val.toNat
        ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    (dstCovered : ∀ j ∈ indices, Solidity.Storage.Loc.data (.data dst i.val) j.val ∈ locations)
    (srcCovered : ∀ j ∈ indices, Solidity.Storage.Loc.data (.data src i.val) j.val ∈ locations)
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
    (srcApart : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices,
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
  have copied := NestedRetainedCopy.copied_child run old source i indices oldInside live dst src dstFits srcFits store numeric target
    initial fitting targetInitial beforeDst beforeSrc
    (fun k inside => headers k (by omega)) (fun k inside => reads k (by omega)) (fun k inside => writes k (by omega))
    dstCovered srcCovered sourceCovered visitedCovered dstApart srcApart
  have childOwner : Represented ((NestedCopyObservations.child old i).overlay (NestedCopyObservations.child source i))
      (PrimitivePop.queries indices) (.data dst i.val) (TargetNestedArrayTransport.copyStores store dst src (i.val+1)) := by
    simpa only [NestedRetainedCopy.child_location] using
      PathRepresentation.focus (old.overlay source) _ _ (NestedCopyObservations.overlay_find_live old source i live) _ dst _ copied.1
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

/-- info: 'Solidity.Backend.StorageOps.NestedRootComposition.retained_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms retained_child

/-- The final header is captured from OLD source storage. PUBLIC root metadata
supplies both length and retained-extent bounds of the independent overlay. -/
theorem root_header {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old source : Value G (.array E)) (dst src : Solidity.Storage.Loc) (store : Store)
    (beforeDst : Represented old [.length .nil] dst store)
    (beforeSrc : Represented source [.length .nil] src store) :
    Represented (old.overlay source) [.length .nil] dst (TargetNestedArrayTransport.afterStore store dst src) := by
  have oldBounds : old.length.val ≤ lmax ∧ old.extent.val ≤ lmax := by
    have known := (beforeDst (.length .nil) List.mem_cons_self).2.1
    cases old
    exact known
  have sourceBounds : source.length.val ≤ lmax ∧ source.extent.val ≤ lmax := by
    have known := (beforeSrc (.length .nil) List.mem_cons_self).2.1
    cases source
    exact known
  have captured : store src = lengthWord source.length.val source.length.isLt :=
    (beforeSrc (.length .nil) List.mem_cons_self).2.2 _ (by cases source; rfl)
  intro q member
  have same := List.mem_singleton.mp member
  subst q
  refine ⟨True.intro,?_,?_⟩
  · cases old with
    | array oe ol oh os =>
      cases source with
      | array ne nl nh ns =>
        change nl.val ≤ lmax ∧ max oe.val nl.val ≤ lmax
        exact ⟨sourceBounds.1,Nat.max_le.mpr ⟨oldBounds.2,sourceBounds.1⟩⟩
  · intro word observed
    have header : (Query.length (G := G) (E := E) .nil).read (old.overlay source) =
        some (lengthWord source.length.val source.length.isLt) := by cases old; cases source; rfl
    have equal := Option.some.inj (header.symm.trans observed)
    change Representation.write _ dst (store src) dst = word
    rw [Representation.write_same,captured]
    exact equal

/-- Existing typed observation demands only, not a value/path/state layer. -/
def rootQueries {n : Nat} {G : Schema n} {p : PrimTy} (children : List Index)
    (indices : Index → List Index) : List (Query G (.array (.array (.prim p)))) :=
  .length .nil :: children.flatMap (fun i =>
    (PrimitivePop.queries (indices i)).map (Query.prefix (NestedCopyObservations.childPath i)))

/-- Finite selected live retained-child ROOT output for the actual full program.
Every per-child phase invariant/postowner is DERIVED from OLD root observations;
no desired per-child preservation theorem is assumed. This does not claim
fresh/stale/older queries or ordinary Source/world compiler closure. -/
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
    (beforeDst : Represented old (rootQueries children indices) dst store)
    (beforeSrc : Represented source (rootQueries children indices) src store)
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
    (srcCovered : ∀ i ∈ children, ∀ j ∈ indices i, Solidity.Storage.Loc.data (.data src i.val) j.val ∈ locations)
    (sourceCovered : ∀ i ∈ children, ∀ j < (NestedCopyObservations.child source i).length.val,
      Solidity.Storage.Loc.data (.data src i.val) j ∈ locations)
    (visitedCovered : ∀ i ∈ children, ∀ j < max (NestedCopyObservations.child old i).length.val (NestedCopyObservations.child source i).length.val,
      Solidity.Storage.Loc.data (.data dst i.val) j ∈ locations)
    (dstApart : ∀ i ∈ children, ∀ q ∈ PrimitivePop.queries (G := G) (p := p) (indices i),
      TargetOperations.toSlot (q.location (.data dst i.val)) (TargetOperations.query_keysFit q (.data dst i.val) dstFits) ∉
      TargetNestedArrayCopyLoop.touched target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) i.val)
    (srcApart : ∀ i ∈ children, ∀ q ∈ PrimitivePop.queries (G := G) (p := p) (indices i),
      TargetOperations.toSlot (q.location (.data src i.val)) (TargetOperations.query_keysFit q (.data src i.val) srcFits) ∉
      TargetNestedArrayCopyLoop.touched target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) i.val) :
    Evm.run TargetNestedArrayCopy.code { target with stack := .slot (TargetOperations.toSlot src srcFits) :: .slot (TargetOperations.toSlot dst dstFits) :: tail } =
      .ok (TargetNestedArrayRuntime.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)) 0 ∧
    Represented (old.overlay source) (rootQueries children indices) dst (TargetNestedArrayTransport.afterStore store dst src) ∧
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
    have sourceChild : Represented source ((PrimitivePop.queries (indices i)).map (Query.prefix (NestedCopyObservations.childPath i))) src store := by
      intro q inside
      exact beforeSrc q (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨i,member,inside⟩))
    have result := retained_child run old source i (indices i) (selected i member).1 (selected i member).2
      dst src dstFits srcFits store numeric target tail initial fitting targetInitial oldChild sourceChild headers reads writes
      (dstCovered i member) (srcCovered i member) (sourceCovered i member) (visitedCovered i member)
      sourceHeader dstHeader srcHeader clearHeaders clearWrites (dstApart i member) (srcApart i member)
    exact result.2.1
  have owner : Represented (old.overlay source) (rootQueries children indices) dst (TargetNestedArrayTransport.afterStore store dst src) := by
    intro q member
    simp only [rootQueries,List.mem_cons,List.mem_flatMap] at member
    rcases member with rfl | ⟨i,inside,observation⟩
    · exact root_header old source dst src store oldHeader sourceHeader _ List.mem_cons_self
    · exact finished i inside q observation
  have actual := TargetNestedArrayTransport.complete run dst src dstFits srcFits store numeric target tail initial fitting targetInitial
    dstHeader srcHeader (by simpa only [countKnown] using headers) (by simpa only [countKnown] using reads)
    (by simpa only [countKnown] using writes) (by simpa only [countKnown] using clearHeaders)
    (by simpa only [countKnown] using clearWrites)
  exact ⟨actual.1,owner,actual.2⟩

/-- info: 'Solidity.Backend.StorageOps.NestedRootComposition.root_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms root_header
/-- info: 'Solidity.Backend.StorageOps.NestedRootComposition.rootQueries' does not depend on any axioms -/
#guard_msgs in #print axioms rootQueries
/-- info: 'Solidity.Backend.StorageOps.NestedRootComposition.live_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms live_root

end Solidity.Backend.StorageOps.NestedRootComposition
