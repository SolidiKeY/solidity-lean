import Solidity.Backend.StorageOps.NestedRetainedCopy
import Solidity.Backend.StorageOps.NestedClearFrames

/-! Actual later-copy frames for already processed children. They compare two
prefixes, not initial storage with the final prefix: the child was changed. -/
namespace Solidity.Backend.StorageOps.NestedLaterFrames
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Every later iteration writes a distinct outer child. All retained payload
observations are preserved, irrespective of current inner lengths or aliases
of SOURCE inputs; this theorem frames only the destination observations. -/
theorem target_interval (initial : Evm.Machine) (src dst : Evm.Slot)
    (first rest outer : Nat) (earlier : outer < first) (observer : Evm.Slot)
    (kind : observer = .data dst outer ∨ ∃ inner, observer = .data (.data dst outer) inner) :
    (TargetNestedArrayCopyLoop.prefixMachine initial src dst (first+rest)).store observer =
      (TargetNestedArrayCopyLoop.prefixMachine initial src dst first).store observer := by
  induction rest with
  | zero => rfl
  | succ rest ih =>
    have header : observer ≠ .data dst (first+rest) := by
      intro same
      rcases kind with rfl | ⟨inner,rfl⟩
      · have equal := (Evm.Slot.data.inj same).2
        omega
      · have depths := congrArg (fun slot => (Solidity.Storage.ofSlot slot).depth) same
        change (Solidity.Storage.ofSlot dst).depth+1+1 = (Solidity.Storage.ofSlot dst).depth+1 at depths
        omega
    have payload : ∀ j, j < max
        ((TargetNestedArrayCopyLoop.prefixMachine initial src dst (first+rest)).store (.data src (first+rest)))
        ((TargetNestedArrayCopyLoop.prefixMachine initial src dst (first+rest)).store (.data dst (first+rest))) →
        observer ≠ .data (.data dst (first+rest)) j := by
      intro j inside same
      rcases kind with rfl | ⟨inner,rfl⟩
      · have depths := congrArg (fun slot => (Solidity.Storage.ofSlot slot).depth) same
        change (Solidity.Storage.ofSlot dst).depth+1 = (Solidity.Storage.ofSlot dst).depth+1+1 at depths
        omega
      · have equal := (Evm.Slot.data.inj (Evm.Slot.data.inj same).1).2
        omega
    change (TargetArrayCopyTail.afterCopy _ _ _ _).store observer = _
    exact (TargetArrayCopyTail.after_outside
      (TargetNestedArrayCopyLoop.prefixMachine initial src dst (first+rest)) initial.stack
      (.data src (first+rest)) (.data dst (first+rest)) observer header payload).trans ih

/-- Original finite-run evidence derives both prefix agreements. No additional
symbolic/physical intermediate relation or final preservation premise. -/
theorem word_interval {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (first rest outer : Nat)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (headers : ∀ k < (first+rest), Solidity.Storage.Loc.data dst k ∈ locations ∧ Solidity.Storage.Loc.data src k ∈ locations)
    (reads : ∀ k < (first+rest), ∀ j < ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data src k) j ∈ locations)
    (writes : ∀ k < (first+rest), ∀ j < max ((TargetNestedArrayTransport.copyStores store dst src k) (.data dst k)).val.toNat
        ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    (earlier : outer < first) (observer : Solidity.Storage.Loc) (covered : observer ∈ locations)
    (kind : observer = .data dst outer ∨ ∃ inner, observer = .data (.data dst outer) inner) :
    TargetNestedArrayTransport.copyStores store dst src (first+rest) observer =
      TargetNestedArrayTransport.copyStores store dst src first observer := by
  have before := (TargetNestedArrayTransport.copy_prefix run dst src dstFits srcFits store numeric target first initial fitting targetInitial
    (fun k inside => headers k (by omega)) (fun k inside => reads k (by omega)) (fun k inside => writes k (by omega))).2 observer covered
  have afterPrefix := (TargetNestedArrayTransport.copy_prefix run dst src dstFits srcFits store numeric target (first+rest) initial fitting targetInitial headers reads writes).2 observer covered
  have targetKind : TargetOperations.toSlot observer (fitting observer covered) = .data (TargetOperations.toSlot dst dstFits) outer ∨
      ∃ inner, TargetOperations.toSlot observer (fitting observer covered) = .data (.data (TargetOperations.toSlot dst dstFits) outer) inner := by
    rcases kind with rfl | ⟨inner,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨inner,rfl⟩
  have framed := target_interval target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)
    first rest outer earlier (TargetOperations.toSlot observer (fitting observer covered)) targetKind
  have equal : TargetOperations.encodeWord (TargetNestedArrayTransport.copyStores store dst src (first+rest) observer) =
      TargetOperations.encodeWord (TargetNestedArrayTransport.copyStores store dst src first observer) := by
    apply Fin.ext
    exact (congrArg Fin.val afterPrefix).symm.trans (framed.trans (congrArg Fin.val before))
  exact keyWord_inj (p := .uint) (congrArg Fin.val equal)

/-- Already established child OUTPUT evidence survives the remaining actual
copies. A C69 derived copied-child owner can supply the first-prefix premise. -/
theorem owner_interval {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (first rest outer : Nat)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (headers : ∀ k < (first+rest), Solidity.Storage.Loc.data dst k ∈ locations ∧ Solidity.Storage.Loc.data src k ∈ locations)
    (reads : ∀ k < (first+rest), ∀ j < ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data src k) j ∈ locations)
    (writes : ∀ k < (first+rest), ∀ j < max ((TargetNestedArrayTransport.copyStores store dst src k) (.data dst k)).val.toNat
        ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    {n : Nat} {G : Schema n} {p : PrimTy} (child : Value G (.array (.prim p))) (indices : List Index)
    (earlier : outer < first)
    (before : Represented child (PrimitivePop.queries indices) (.data dst outer)
      (TargetNestedArrayTransport.copyStores store dst src first))
    (covered : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, q.location (.data dst outer) ∈ locations) :
    Represented child (PrimitivePop.queries indices) (.data dst outer)
      (TargetNestedArrayTransport.copyStores store dst src (first+rest)) := by
  intro q member
  obtain ⟨supported,compatible,observed⟩ := before q member
  refine ⟨supported,compatible,?_⟩
  intro word found
  have kind : q.location (.data dst outer) = .data dst outer ∨ ∃ inner, q.location (.data dst outer) = .data (.data dst outer) inner := by
    simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
    rcases member with rfl | ⟨i,inside,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨i.val,PrimitivePop.element_location _ i⟩
  rw [word_interval run dst src dstFits srcFits store numeric target first rest outer initial fitting targetInitial headers reads writes
    earlier (q.location (.data dst outer)) (covered q member) kind]
  exact observed word found

/-- info: 'Solidity.Backend.StorageOps.NestedLaterFrames.target_interval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms target_interval
/-- info: 'Solidity.Backend.StorageOps.NestedLaterFrames.word_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms word_interval
/-- info: 'Solidity.Backend.StorageOps.NestedLaterFrames.owner_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms owner_interval
end Solidity.Backend.StorageOps.NestedLaterFrames
