import Solidity.Backend.StorageOps.NestedCopyObservations

/-! OLD selected copied-child observations survive actual stale-child clearing
and the final outer header write. Original finite-run coverage stays explicit. -/
namespace Solidity.Backend.StorageOps.NestedClearFrames
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

theorem clear_child_word {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (dst : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (start count : Nat)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (headers : ∀ k < count, start ≤ k → Solidity.Storage.Loc.data dst k ∈ locations)
    (writes : ∀ k < count, start ≤ k → ∀ j < ((TargetNestedArrayTransport.clearStores store dst start k) (.data dst k)).val.toNat,
      Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    (outer : Nat) (outside : outer < start ∨ count ≤ outer)
    (observer : Solidity.Storage.Loc) (covered : observer ∈ locations)
    (kind : observer = .data dst outer ∨ ∃ inner, observer = .data (.data dst outer) inner) :
    TargetNestedArrayTransport.clearStores store dst start count observer = store observer := by
  have agreement := (TargetNestedArrayTransport.clear_prefix run dst dstFits store numeric target start count initial fitting targetInitial headers writes).2 observer covered
  have framed : (TargetNestedArrayClearLoop.prefixMachine target (TargetOperations.toSlot dst dstFits) start count).store
      (TargetOperations.toSlot observer (fitting observer covered)) = target.store (TargetOperations.toSlot observer (fitting observer covered)) := by
    have actual := TargetNestedArrayClearLoop.outside_child target (TargetOperations.toSlot dst dstFits) start count outer outside
    rcases kind with rfl | ⟨inner,rfl⟩
    · exact actual.1
    · exact actual.2 inner
  have equal : TargetOperations.encodeWord (TargetNestedArrayTransport.clearStores store dst start count observer) =
      TargetOperations.encodeWord (store observer) := by
    apply Fin.ext
    exact (congrArg Fin.val agreement).symm.trans (framed.trans (congrArg Fin.val (targetInitial observer covered)))
  exact keyWord_inj (p := .uint) (congrArg Fin.val equal)

theorem clear_child_owner {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (dst : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (start count : Nat)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (headers : ∀ k < count, start ≤ k → Solidity.Storage.Loc.data dst k ∈ locations)
    (writes : ∀ k < count, start ≤ k → ∀ j < ((TargetNestedArrayTransport.clearStores store dst start k) (.data dst k)).val.toNat,
      Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    {n : Nat} {G : Schema n} {p : PrimTy} (child : Value G (.array (.prim p)))
    (indices : List Index) (outer : Nat) (outside : outer < start ∨ count ≤ outer)
    (before : Represented child (PrimitivePop.queries indices) (.data dst outer) store)
    (covered : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, q.location (.data dst outer) ∈ locations) :
    Represented child (PrimitivePop.queries indices) (.data dst outer)
      (TargetNestedArrayTransport.clearStores store dst start count) := by
  intro q member
  obtain ⟨supported,compatible,observed⟩ := before q member
  refine ⟨supported,compatible,?_⟩
  intro word found
  have kind : q.location (.data dst outer) = .data dst outer ∨
      ∃ inner, q.location (.data dst outer) = .data (.data dst outer) inner := by
    simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
    rcases member with rfl | ⟨i,inside,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨i.val,PrimitivePop.element_location _ i⟩
  rw [clear_child_word run dst dstFits store numeric target start count initial fitting targetInitial headers writes
    outer outside (q.location (.data dst outer)) (covered q member) kind]
  exact observed word found

/-- The root header is never one of its own typed child header/payload slots.
This is symbolic finite-tree separation; no new cryptographic premise. -/
theorem header_child_owner {n : Nat} {G : Schema n} {p : PrimTy}
    (child : Value G (.array (.prim p))) (indices : List Index) (base : Solidity.Storage.Loc)
    (outer : Nat) (store : Store) (header : Semantics.Word)
    (before : Represented child (PrimitivePop.queries indices) (.data base outer) store) :
    Represented child (PrimitivePop.queries indices) (.data base outer) (Representation.write store base header) := by
  intro q member
  obtain ⟨supported,compatible,observed⟩ := before q member
  refine ⟨supported,compatible,?_⟩
  intro word found
  have apart : q.location (.data base outer) ≠ base := by
    simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
    rcases member with rfl | ⟨i,inside,rfl⟩
    · intro equal
      have depths := congrArg Solidity.Storage.Loc.depth equal
      change base.depth+1 = base.depth at depths
      omega
    · rw [PrimitivePop.element_location]
      intro equal
      have depths := congrArg Solidity.Storage.Loc.depth equal
      change base.depth+1+1 = base.depth at depths
      omega
  rw [Representation.write_other store base _ header apart]
  exact observed word found

/-- info: 'Solidity.Backend.StorageOps.NestedClearFrames.clear_child_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clear_child_word
/-- info: 'Solidity.Backend.StorageOps.NestedClearFrames.clear_child_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clear_child_owner
/-- info: 'Solidity.Backend.StorageOps.NestedClearFrames.header_child_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms header_child_owner
end Solidity.Backend.StorageOps.NestedClearFrames
