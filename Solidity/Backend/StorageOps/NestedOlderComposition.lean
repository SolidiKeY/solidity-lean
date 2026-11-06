import Solidity.Backend.StorageOps.NestedStaleComposition

/-! Older OUTER retained children survive actual runtime copy/clear/header
phases. Exact OLD independent observations derive the selected ROOT output. -/
namespace Solidity.Backend.StorageOps.NestedOlderComposition
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- A retained child beyond BOTH live lengths remains represented after the
full actual program. No source-child/default/current/postowner is a premise;
ALL actual accesses and selected observations use the original finite region. -/
theorem older_child {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (old source : Value G (.array (.array (.prim p)))) (i : Index) (indices : List Index)
    (oldInside : i.val < old.extent.val)
    (pastNew : source.length.val ≤ i.val) (pastOld : old.length.val ≤ i.val)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (tail : List Evm.Word)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (beforeDst : Represented old
      ((PrimitivePop.queries indices).map (Query.prefix (NestedCopyObservations.childPath i))) dst store)
    (oldHeaderOwner : Represented old [.length .nil] dst store)
    (sourceHeaderOwner : Represented source [.length .nil] src store)
    (dstHeader : dst ∈ locations) (srcHeader : src ∈ locations)
    (copyHeaders : ∀ k < (store src).val.toNat, Solidity.Storage.Loc.data dst k ∈ locations ∧ Solidity.Storage.Loc.data src k ∈ locations)
    (copyReads : ∀ k < (store src).val.toNat, ∀ j < ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data src k) j ∈ locations)
    (copyWrites : ∀ k < (store src).val.toNat, ∀ j < max ((TargetNestedArrayTransport.copyStores store dst src k) (.data dst k)).val.toNat
        ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    (clearHeaders : ∀ k < max (store src).val.toNat (store dst).val.toNat, (store src).val.toNat ≤ k → Solidity.Storage.Loc.data dst k ∈ locations)
    (clearWrites : ∀ k < max (store src).val.toNat (store dst).val.toNat, (store src).val.toNat ≤ k →
      ∀ j < ((TargetNestedArrayTransport.clearStores (TargetNestedArrayTransport.copyStores store dst src (store src).val.toNat)
        dst (store src).val.toNat k) (.data dst k)).val.toNat,
        Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    (covered : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, q.location (.data dst i.val) ∈ locations) :
    Evm.run TargetNestedArrayCopy.code { target with stack := .slot (TargetOperations.toSlot src srcFits) :: .slot (TargetOperations.toSlot dst dstFits) :: tail } =
      .ok (TargetNestedArrayRuntime.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)) 0 ∧
    Represented (old.overlay source) ((PrimitivePop.queries indices).map (Query.prefix (NestedCopyObservations.childPath i))) dst
      (TargetNestedArrayTransport.afterStore store dst src) ∧
    Transport N hash locations (TargetNestedArrayTransport.afterStore store dst src) (TargetNestedArrayTransport.execute N hash numeric dst src) ∧
    (∀ l (member : l ∈ locations),
      (TargetNestedArrayRuntime.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store.cells
        (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore store dst src l)) := by
  have oldCount : (store dst).val.toNat = old.length.val := by
    have known : store dst = lengthWord old.length.val old.length.isLt :=
      (oldHeaderOwner (.length .nil) List.mem_cons_self).2.2 _ (by cases old; rfl)
    rw [known]; rfl
  have newCount : (store src).val.toNat = source.length.val := by
    have known : store src = lengthWord source.length.val source.length.isLt :=
      (sourceHeaderOwner (.length .nil) List.mem_cons_self).2.2 _ (by cases source; rfl)
    rw [known]; rfl
  have future : (store src).val.toNat ≤ i.val := by rw [newCount]; exact pastNew
  have outside : max (store src).val.toNat (store dst).val.toNat ≤ i.val := by rw [oldCount,newCount]; omega
  have oldChild : Represented (NestedCopyObservations.child old i) (PrimitivePop.queries indices) (.data dst i.val) store := by
    simpa only [NestedRetainedCopy.child_location] using
      PathRepresentation.focus old _ _ (NestedCopyObservations.find_child old i oldInside) _ dst store beforeDst
  have afterCopies := NestedStaleComposition.unvisited_owner run dst src dstFits srcFits store numeric target (store src).val.toNat i.val
    initial fitting targetInitial copyHeaders copyReads copyWrites (NestedCopyObservations.child old i) indices future oldChild covered
  have copied := TargetNestedArrayTransport.copy_prefix run dst src dstFits srcFits store numeric target (store src).val.toNat
    initial fitting targetInitial copyHeaders copyReads copyWrites
  have afterClears := NestedClearFrames.clear_child_owner run dst dstFits
    (TargetNestedArrayTransport.copyStores store dst src (store src).val.toNat)
    (TargetNestedArrayTransport.copyNumerics N hash numeric dst src (store src).val.toNat)
    (TargetNestedArrayCopyLoop.prefixMachine target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) (store src).val.toNat)
    (store src).val.toNat (max (store src).val.toNat (store dst).val.toNat) copied.1 fitting copied.2
    clearHeaders clearWrites (NestedCopyObservations.child old i) indices i.val (Or.inr outside) afterCopies covered
  have finalChild : Represented (NestedCopyObservations.child old i) (PrimitivePop.queries indices) (.data dst i.val)
      (TargetNestedArrayTransport.afterStore store dst src) :=
    NestedClearFrames.header_child_owner (NestedCopyObservations.child old i) indices dst i.val _ (store src) afterClears
  have supported : PathSupported (NestedCopyObservations.childPath (G := G) (p := p) i) :=
    ((Query.supported_prefix _ (.length .nil)).mp
      (beforeDst _ (List.mem_map.mpr ⟨_,List.mem_cons_self,rfl⟩)).1).1
  have unchanged : (old.overlay source).find (NestedCopyObservations.childPath i) = old.find (NestedCopyObservations.childPath i) := by
    simpa only [NestedCopyObservations.childPath] using NestedStaleComposition.find_older old source i pastNew pastOld
  have found : (old.overlay source).find (NestedCopyObservations.childPath i) = some (NestedCopyObservations.child old i) :=
    unchanged.trans (NestedCopyObservations.find_child old i oldInside)
  have leaf : Represented (NestedCopyObservations.child old i) (PrimitivePop.queries indices)
      (pathLoc (NestedCopyObservations.childPath (G := G) (p := p) i) dst) (TargetNestedArrayTransport.afterStore store dst src) := by
    simpa only [NestedRetainedCopy.child_location] using finalChild
  have actual := TargetNestedArrayTransport.complete run dst src dstFits srcFits store numeric target tail initial fitting targetInitial
    dstHeader srcHeader copyHeaders copyReads copyWrites clearHeaders clearWrites
  exact ⟨actual.1,Represented.prefix _ found supported leaf,actual.2⟩

/-- info: 'Solidity.Backend.StorageOps.NestedOlderComposition.older_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms older_child
end Solidity.Backend.StorageOps.NestedOlderComposition
