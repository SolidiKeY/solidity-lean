import Solidity.Backend.StorageOps.NestedFreshComposition

/-! Mixed retained/fresh live ROOT families. The branch is determined by the
OLD logical extent; no initial fresh destination owner or zero-header premise.
Every per-child output is derived from concrete checked operation certificates.
This does not claim stale/older query families or whole Source/world closure. -/
namespace Solidity.Backend.StorageOps.MixedLiveComposition
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

theorem live_root {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (old source : Value G (.array (.array (.prim p)))) (children : List Index) (indices : Index → List Index)
    (selected : ∀ i ∈ children, i.val < source.length.val)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (tail : List Evm.Word)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (oldHeader : Represented old [.length .nil] dst store)
    (beforeDst : ∀ i ∈ children, i.val < old.extent.val →
      Represented old ((PrimitivePop.queries (indices i)).map (Query.prefix (NestedCopyObservations.childPath i))) dst store)
    (beforeSrc : Represented source (RootCopyAccess.sourceQueries source children indices) src store)
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
    (visitedCovered : ∀ i ∈ children, i.val < old.extent.val → ∀ j < max (NestedCopyObservations.child old i).length.val (NestedCopyObservations.child source i).length.val,
      Solidity.Storage.Loc.data (.data dst i.val) j ∈ locations)
    (freshCovered : ∀ i ∈ children, old.extent.val ≤ i.val →
      ∀ j < max ((TargetNestedArrayTransport.copyStores store dst src i.val) (.data dst i.val)).val.toNat
          (NestedCopyObservations.child source i).length.val,
        Solidity.Storage.Loc.data (.data dst i.val) j ∈ locations)
    (freshSupported : ∀ i ∈ children, old.extent.val ≤ i.val →
      ∀ q ∈ PrimitivePop.queries (G := G) (p := p) (indices i), q.supported)
    (dstApart : ∀ i ∈ children, i.val < old.extent.val → ∀ q ∈ PrimitivePop.queries (G := G) (p := p) (indices i),
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
    have sourceChild : Represented source ((CopyAccess.readQueries (NestedCopyObservations.child source i) (indices i)).map (Query.prefix (NestedCopyObservations.childPath i))) src store := by
      intro q inside
      exact beforeSrc q (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨i,member,inside⟩))
    by_cases retained : i.val < old.extent.val
    · have result := RootCopyAccess.retained_child run old source i (indices i) retained (selected i member)
        dst src dstFits srcFits store numeric target tail initial fitting targetInitial (beforeDst i member retained) sourceChild headers reads writes
        (dstCovered i member) (sourceCovered i member) (visitedCovered i member retained)
        sourceHeader dstHeader srcHeader clearHeaders clearWrites (dstApart i member retained) (srcApart i member)
      exact result.2.1
    · have missing : old.extent.val ≤ i.val := Nat.le_of_not_gt retained
      have result := NestedFreshComposition.fresh_child run old source i (indices i) missing (selected i member)
        dst src dstFits srcFits store numeric target tail initial fitting targetInitial sourceChild headers reads writes
        (dstCovered i member) (sourceCovered i member) (freshCovered i member missing) (freshSupported i member missing)
        sourceHeader dstHeader srcHeader clearHeaders clearWrites (srcApart i member)
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

/-- info: 'Solidity.Backend.StorageOps.MixedLiveComposition.live_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms live_root
end Solidity.Backend.StorageOps.MixedLiveComposition
