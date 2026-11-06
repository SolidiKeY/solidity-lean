import Solidity.Backend.StorageOps.TargetNestedArrayTransport

/-! Frames derived from actual nested runtime writes and OLD finite-run evidence.
Failed graph reads are never interpreted as physical zero or as a frame. -/
namespace Solidity.Backend.StorageOps.NestedSnapshotFrames
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

theorem copy_word_frame {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (count : Nat)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (headers : ∀ k < count, Solidity.Storage.Loc.data dst k ∈ locations ∧ Solidity.Storage.Loc.data src k ∈ locations)
    (reads : ∀ k < count, ∀ j < ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data src k) j ∈ locations)
    (writes : ∀ k < count, ∀ j < max ((TargetNestedArrayTransport.copyStores store dst src k) (.data dst k)).val.toNat
        ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    (observer : Solidity.Storage.Loc) (covered : observer ∈ locations)
    (outside : TargetOperations.toSlot observer (fitting observer covered) ∉
      TargetNestedArrayCopyLoop.touched target (TargetOperations.toSlot src srcFits)
        (TargetOperations.toSlot dst dstFits) count) :
    TargetNestedArrayTransport.copyStores store dst src count observer = store observer := by
  have agreement := (TargetNestedArrayTransport.copy_prefix run dst src dstFits srcFits store numeric target count initial fitting targetInitial headers reads writes).2 observer covered
  have framed := TargetNestedArrayCopyLoop.prefix_outside target
    (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)
    (TargetOperations.toSlot observer (fitting observer covered)) count outside
  have equal : TargetOperations.encodeWord (TargetNestedArrayTransport.copyStores store dst src count observer) =
      TargetOperations.encodeWord (store observer) := by
    apply Fin.ext
    exact (congrArg Fin.val agreement).symm.trans (framed.trans (congrArg Fin.val (targetInitial observer covered)))
  exact keyWord_inj (p := .uint) (congrArg Fin.val equal)

/-- Reuses the PUBLIC owner relation. Even a failed selected query needs
explicit covered-address separation to obtain a physical frame. -/
theorem represented_copy_frame {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (count : Nat)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (headers : ∀ k < count, Solidity.Storage.Loc.data dst k ∈ locations ∧ Solidity.Storage.Loc.data src k ∈ locations)
    (reads : ∀ k < count, ∀ j < ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data src k) j ∈ locations)
    (writes : ∀ k < count, ∀ j < max ((TargetNestedArrayTransport.copyStores store dst src k) (.data dst k)).val.toNat
        ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data dst k) j ∈ locations)

    {n : Nat} {G : Schema n} {A : TypeGraph.Ty n}
    (value : Value G A) (queries : List (Query G A)) (base : Solidity.Storage.Loc)
    (before : Represented value queries base store)
    (covered : ∀ q ∈ queries, q.location base ∈ locations)
    (outside : ∀ q (member : q ∈ queries),
      TargetOperations.toSlot (q.location base) (fitting _ (covered q member)) ∉
        TargetNestedArrayCopyLoop.touched target (TargetOperations.toSlot src srcFits)
          (TargetOperations.toSlot dst dstFits) count) :
    Represented value queries base (TargetNestedArrayTransport.copyStores store dst src count) := by
  intro q member
  obtain ⟨supported,compatible,observed⟩ := before q member
  refine ⟨supported,compatible,?_⟩
  intro word found
  rw [copy_word_frame run dst src dstFits srcFits store numeric target count initial fitting targetInitial
    headers reads writes (q.location base) (covered q member) (outside q member)]
  exact observed word found

/-- info: 'Solidity.Backend.StorageOps.NestedSnapshotFrames.represented_copy_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_copy_frame

/-- info: 'Solidity.Backend.StorageOps.NestedSnapshotFrames.copy_word_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copy_word_frame

end Solidity.Backend.StorageOps.NestedSnapshotFrames
