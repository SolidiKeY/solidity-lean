import Solidity.Backend.StorageOps.AbsentRootQueries

/-! Actual output composition adds exact failed observations to nontrivial
successful ROOT families. Both are derived from OLD graph evidence and the
concrete runtime certificate; no desired postowner is an input. None imposes
no physical-cell contract; numeric/ALLtarget transport remains unchanged. -/
namespace Solidity.Backend.StorageOps.OutputRootComplete
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

theorem complete {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (old source : Value G (.array (.array (.prim p)))) (children : List Index) (indices : Index → List Index)
    (selected : ∀ i ∈ children, i.val < max old.extent.val source.length.val)
    (missing : Index) (outside : max old.extent.val source.length.val ≤ missing.val)
    (extra : List (Query G (.array (.prim p))))
    (extraSupported : ∀ q ∈ extra, (q.prefix (NestedCopyObservations.childPath missing)).supported)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (tail : List Evm.Word)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (oldHeader : Represented old [.length .nil] dst store)
    (beforeDst : ∀ i ∈ children, i.val < old.extent.val → i.val < source.length.val →
      Represented old ((PrimitivePop.queries (indices i)).map (Query.prefix (NestedCopyObservations.childPath i))) dst store)
    (sourceHeader : Represented source [.length .nil] src store)
    (beforeSrc : ∀ i ∈ children, i.val < source.length.val →
      Represented source ((CopyAccess.readQueries (NestedCopyObservations.child source i) (indices i)).map
        (Query.prefix (NestedCopyObservations.childPath i))) src store)
    (beforeStale : ∀ i ∈ children, source.length.val ≤ i.val → i.val < old.length.val →
      Represented old ((TargetClearRepresentation.oldQueries (NestedCopyObservations.child old i) (indices i)).map
        (Query.prefix (NestedCopyObservations.childPath i))) dst store)
    (beforeOlder : ∀ i ∈ children, source.length.val ≤ i.val → old.length.val ≤ i.val →
      Represented old ((PrimitivePop.queries (indices i)).map (Query.prefix (NestedCopyObservations.childPath i))) dst store)
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
    (sourceCovered : ∀ i ∈ children, i.val < source.length.val → ∀ j < (NestedCopyObservations.child source i).length.val,
      Solidity.Storage.Loc.data (.data src i.val) j ∈ locations)
    (visitedCovered : ∀ i ∈ children, i.val < old.extent.val → i.val < source.length.val → ∀ j < max (NestedCopyObservations.child old i).length.val (NestedCopyObservations.child source i).length.val,
      Solidity.Storage.Loc.data (.data dst i.val) j ∈ locations)
    (childHeader : ∀ i ∈ children, Solidity.Storage.Loc.data dst i.val ∈ locations)
    (freshCovered : ∀ i ∈ children, old.extent.val ≤ i.val →
      ∀ j < max ((TargetNestedArrayTransport.copyStores store dst src i.val) (.data dst i.val)).val.toNat
          (NestedCopyObservations.child source i).length.val,
        Solidity.Storage.Loc.data (.data dst i.val) j ∈ locations)
    (freshSupported : ∀ i ∈ children, old.extent.val ≤ i.val →
      ∀ q ∈ PrimitivePop.queries (G := G) (p := p) (indices i), q.supported)
    (dstApart : ∀ i ∈ children, i.val < old.extent.val → i.val < source.length.val → ∀ q ∈ PrimitivePop.queries (G := G) (p := p) (indices i),
      TargetOperations.toSlot (q.location (.data dst i.val)) (TargetOperations.query_keysFit q (.data dst i.val) dstFits) ∉
      TargetNestedArrayCopyLoop.touched target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) i.val)
    (srcApart : ∀ i ∈ children, i.val < source.length.val → ∀ q ∈ CopyAccess.readQueries (NestedCopyObservations.child source i) (indices i),
      TargetOperations.toSlot (q.location (.data src i.val)) (TargetOperations.query_keysFit q (.data src i.val) srcFits) ∉
      TargetNestedArrayCopyLoop.touched target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) i.val) :
    Evm.run TargetNestedArrayCopy.code { target with stack := .slot (TargetOperations.toSlot src srcFits) :: .slot (TargetOperations.toSlot dst dstFits) :: tail } =
      .ok (TargetNestedArrayRuntime.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)) 0 ∧
    Represented (old.overlay source)
      (NestedRootComposition.rootQueries children indices ++ extra.map (Query.prefix (NestedCopyObservations.childPath missing)))
      dst (TargetNestedArrayTransport.afterStore store dst src) ∧
    Transport N hash locations (TargetNestedArrayTransport.afterStore store dst src) (TargetNestedArrayTransport.execute N hash numeric dst src) ∧
    (∀ l (member : l ∈ locations),
      (TargetNestedArrayRuntime.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store.cells
        (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore store dst src l)) := by
  have actual := OutputRootComposition.root run old source children indices selected dst src dstFits srcFits store numeric target tail
    initial fitting targetInitial oldHeader beforeDst sourceHeader beforeSrc beforeStale beforeOlder dstHeader srcHeader
    headers reads writes clearHeaders clearWrites dstCovered sourceCovered visitedCovered childHeader freshCovered freshSupported dstApart srcApart
  have failed : Represented (old.overlay source) (extra.map (Query.prefix (NestedCopyObservations.childPath missing)))
      dst (TargetNestedArrayTransport.afterStore store dst src) :=
    AbsentRootQueries.represented_missing old source missing extra outside extraSupported dst _
  refine ⟨actual.1,?_,actual.2.2⟩
  intro q member
  rcases List.mem_append.mp member with live | absent
  · exact actual.2.1 q live
  · exact failed q absent

/-- info: 'Solidity.Backend.StorageOps.OutputRootComplete.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Backend.StorageOps.OutputRootComplete
