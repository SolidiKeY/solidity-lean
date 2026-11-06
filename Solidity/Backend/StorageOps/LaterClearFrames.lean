import Solidity.Backend.StorageOps.NestedClearFrames

/-! Frames from an already CHANGED clear prefix, not from the original store.
Every actual generated access stays inside the original per-run region. -/
namespace Solidity.Backend.StorageOps.LaterClearFrames
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Later stale iterations cannot overwrite an earlier processed child's
header or any retained payload, irrespective of current runtime lengths. -/
theorem target_interval (initial : Evm.Machine) (dst : Evm.Slot)
    (start first rest outer : Nat) (earlier : outer < first) (observer : Evm.Slot)
    (kind : observer = .data dst outer ∨ ∃ inner, observer = .data (.data dst outer) inner) :
    (TargetNestedArrayClearLoop.prefixMachine initial dst start (first+rest)).store observer =
      (TargetNestedArrayClearLoop.prefixMachine initial dst start first).store observer := by
  induction rest with
  | zero => rfl
  | succ rest ih =>
    by_cases active : start ≤ first+rest
    · have header : observer ≠ .data dst (first+rest) := by
        intro same
        rcases kind with rfl | ⟨inner,rfl⟩
        · have equal := (Evm.Slot.data.inj same).2
          omega
        · have depths := congrArg (fun slot => (Solidity.Storage.ofSlot slot).depth) same
          change (Solidity.Storage.ofSlot dst).depth+1+1 = (Solidity.Storage.ofSlot dst).depth+1 at depths
          omega
      have payload : ∀ j, j < (TargetNestedArrayClearLoop.prefixMachine initial dst start (first+rest)).store (.data dst (first+rest)) →
          observer ≠ .data (.data dst (first+rest)) j := by
        intro j inside same
        rcases kind with rfl | ⟨inner,rfl⟩
        · have depths := congrArg (fun slot => (Solidity.Storage.ofSlot slot).depth) same
          change (Solidity.Storage.ofSlot dst).depth+1 = (Solidity.Storage.ofSlot dst).depth+1+1 at depths
          omega
        · have equal := (Evm.Slot.data.inj (Evm.Slot.data.inj same).1).2
          omega
      rw [show first+(rest+1) = (first+rest)+1 by omega,TargetNestedArrayClearLoop.prefixMachine,if_pos active]
      exact (TargetArrayClear.after_outside
        (TargetNestedArrayClearLoop.prefixMachine initial dst start (first+rest)) initial.stack
        (.data dst (first+rest)) observer header payload).trans ih
    · rw [show first+(rest+1) = (first+rest)+1 by omega,TargetNestedArrayClearLoop.prefixMachine,if_neg active]
      exact ih

/-- Both CURRENT prefix agreements follow from the ORIGINAL finite region;
no raw-store frame or desired representation theorem is assumed. -/
theorem word_interval {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (dst : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (start first rest outer : Nat)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (headers : ∀ k < first+rest, start ≤ k → Solidity.Storage.Loc.data dst k ∈ locations)
    (writes : ∀ k < first+rest, start ≤ k → ∀ j < ((TargetNestedArrayTransport.clearStores store dst start k) (.data dst k)).val.toNat,
      Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    (earlier : outer < first) (observer : Solidity.Storage.Loc) (covered : observer ∈ locations)
    (kind : observer = .data dst outer ∨ ∃ inner, observer = .data (.data dst outer) inner) :
    TargetNestedArrayTransport.clearStores store dst start (first+rest) observer =
      TargetNestedArrayTransport.clearStores store dst start first observer := by
  have before := (TargetNestedArrayTransport.clear_prefix run dst dstFits store numeric target start first initial fitting targetInitial
    (fun k inside => headers k (by omega)) (fun k inside => writes k (by omega))).2 observer covered
  have afterPrefix := (TargetNestedArrayTransport.clear_prefix run dst dstFits store numeric target start (first+rest) initial fitting targetInitial headers writes).2 observer covered
  have targetKind : TargetOperations.toSlot observer (fitting observer covered) = .data (TargetOperations.toSlot dst dstFits) outer ∨
      ∃ inner, TargetOperations.toSlot observer (fitting observer covered) = .data (.data (TargetOperations.toSlot dst dstFits) outer) inner := by
    rcases kind with rfl | ⟨inner,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨inner,rfl⟩
  have framed := target_interval target (TargetOperations.toSlot dst dstFits) start first rest outer earlier
    (TargetOperations.toSlot observer (fitting observer covered)) targetKind
  have equal : TargetOperations.encodeWord (TargetNestedArrayTransport.clearStores store dst start (first+rest) observer) =
      TargetOperations.encodeWord (TargetNestedArrayTransport.clearStores store dst start first observer) := by
    apply Fin.ext
    exact (congrArg Fin.val afterPrefix).symm.trans (framed.trans (congrArg Fin.val before))
  exact keyWord_inj (p := .uint) (congrArg Fin.val equal)

/-- An already CLEARED selected child owner survives later stale siblings.
The input is the changed first prefix, never the old initial owner. -/
theorem owner_interval {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (dst : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (start first rest outer : Nat)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (headers : ∀ k < first+rest, start ≤ k → Solidity.Storage.Loc.data dst k ∈ locations)
    (writes : ∀ k < first+rest, start ≤ k → ∀ j < ((TargetNestedArrayTransport.clearStores store dst start k) (.data dst k)).val.toNat,
      Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    {n : Nat} {G : Schema n} {p : PrimTy} (child : Value G (.array (.prim p))) (indices : List Index)
    (earlier : outer < first)
    (before : Represented child (PrimitivePop.queries indices) (.data dst outer)
      (TargetNestedArrayTransport.clearStores store dst start first))
    (covered : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, q.location (.data dst outer) ∈ locations) :
    Represented child (PrimitivePop.queries indices) (.data dst outer)
      (TargetNestedArrayTransport.clearStores store dst start (first+rest)) := by
  intro q member
  obtain ⟨supported,compatible,observed⟩ := before q member
  refine ⟨supported,compatible,?_⟩
  intro word found
  have kind : q.location (.data dst outer) = .data dst outer ∨ ∃ inner, q.location (.data dst outer) = .data (.data dst outer) inner := by
    simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
    rcases member with rfl | ⟨i,inside,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨i.val,PrimitivePop.element_location _ i⟩
  rw [word_interval run dst dstFits store numeric target start first rest outer initial fitting targetInitial headers writes
    earlier (q.location (.data dst outer)) (covered q member) kind]
  exact observed word found

/-- info: 'Solidity.Backend.StorageOps.LaterClearFrames.target_interval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms target_interval

/-- info: 'Solidity.Backend.StorageOps.LaterClearFrames.word_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms word_interval

/-- info: 'Solidity.Backend.StorageOps.LaterClearFrames.owner_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms owner_interval
end Solidity.Backend.StorageOps.LaterClearFrames
