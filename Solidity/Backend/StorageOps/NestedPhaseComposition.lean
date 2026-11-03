import Solidity.Backend.StorageOps.NestedLaterFrames

/-! Composition over the actual captured runtime copy/clear/header phases.
The selected child invariant at its own prefix can be derived by C69; the
final owner, numeric relation and actual program execution are not premises. -/
namespace Solidity.Backend.StorageOps.NestedPhaseComposition
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Carry an established copied-child output through ALL remaining runtime
iterations, the captured stale suffix, and final header emission. Original
finite-run/access evidence derives every middle transport/target agreement. -/
theorem finish_child {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (tail : List Evm.Word)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (dstHeader : dst ∈ locations) (srcHeader : src ∈ locations)
    (copyHeaders : ∀ k < (store src).val.toNat, Solidity.Storage.Loc.data dst k ∈ locations ∧ Solidity.Storage.Loc.data src k ∈ locations)
    (copyReads : ∀ k < (store src).val.toNat, ∀ j < ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data src k) j ∈ locations)
    (copyWrites : ∀ k < (store src).val.toNat, ∀ j < max ((TargetNestedArrayTransport.copyStores store dst src k) (.data dst k)).val.toNat
        ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat, Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    (clearHeaders : ∀ k < max (store src).val.toNat (store dst).val.toNat, (store src).val.toNat ≤ k → Solidity.Storage.Loc.data dst k ∈ locations)
    (clearWrites : ∀ k < max (store src).val.toNat (store dst).val.toNat, (store src).val.toNat ≤ k →
      ∀ j < ((TargetNestedArrayTransport.clearStores (TargetNestedArrayTransport.copyStores store dst src (store src).val.toNat) dst (store src).val.toNat k) (.data dst k)).val.toNat,
        Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    {n : Nat} {G : Schema n} {p : PrimTy} (child : Value G (.array (.prim p))) (indices : List Index)
    (first outer : Nat) (earlier : outer < first) (within : first ≤ (store src).val.toNat)
    (before : Represented child (PrimitivePop.queries indices) (.data dst outer)
      (TargetNestedArrayTransport.copyStores store dst src first))
    (covered : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, q.location (.data dst outer) ∈ locations) :
    Evm.run TargetNestedArrayCopy.code { target with stack := .slot (TargetOperations.toSlot src srcFits) :: .slot (TargetOperations.toSlot dst dstFits) :: tail } =
      .ok (TargetNestedArrayRuntime.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)) 0 ∧
    Represented child (PrimitivePop.queries indices) (.data dst outer) (TargetNestedArrayTransport.afterStore store dst src) ∧
    Transport N hash locations (TargetNestedArrayTransport.afterStore store dst src) (TargetNestedArrayTransport.execute N hash numeric dst src) ∧
    (∀ l (member : l ∈ locations),
      (TargetNestedArrayRuntime.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store.cells
        (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore store dst src l)) := by
  have total : first+((store src).val.toNat-first) = (store src).val.toNat := by omega
  have later := NestedLaterFrames.owner_interval run dst src dstFits srcFits store numeric target first ((store src).val.toNat-first) outer initial fitting targetInitial
    (by simpa only [total] using copyHeaders)
    (by simpa only [total] using copyReads)
    (by simpa only [total] using copyWrites) child indices earlier before covered
  have afterCopies : Represented child (PrimitivePop.queries indices) (.data dst outer)
      (TargetNestedArrayTransport.copyStores store dst src (store src).val.toNat) := by
    simpa only [total] using later
  have copied := TargetNestedArrayTransport.copy_prefix run dst src dstFits srcFits store numeric target (store src).val.toNat initial fitting targetInitial copyHeaders copyReads copyWrites
  have afterClears := NestedClearFrames.clear_child_owner run dst dstFits
    (TargetNestedArrayTransport.copyStores store dst src (store src).val.toNat)
    (TargetNestedArrayTransport.copyNumerics N hash numeric dst src (store src).val.toNat)
    (TargetNestedArrayCopyLoop.prefixMachine target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) (store src).val.toNat)
    (store src).val.toNat (max (store src).val.toNat (store dst).val.toNat) copied.1 fitting copied.2
    clearHeaders clearWrites child indices outer (Or.inl (by omega)) afterCopies covered
  have owner : Represented child (PrimitivePop.queries indices) (.data dst outer) (TargetNestedArrayTransport.afterStore store dst src) := by
    exact NestedClearFrames.header_child_owner child indices dst outer _ (store src) afterClears
  have actual := TargetNestedArrayTransport.complete run dst src dstFits srcFits store numeric target tail initial fitting targetInitial
    dstHeader srcHeader copyHeaders copyReads copyWrites clearHeaders clearWrites
  exact ⟨actual.1,owner,actual.2⟩

/-- info: 'Solidity.Backend.StorageOps.NestedPhaseComposition.finish_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms finish_child
end Solidity.Backend.StorageOps.NestedPhaseComposition
