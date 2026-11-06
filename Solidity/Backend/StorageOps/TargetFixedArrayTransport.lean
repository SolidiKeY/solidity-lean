import Solidity.Backend.StorageOps.TargetFixedArrayCopy

/-! Finite-run transport for the evolving CURRENT-source child sequence.
No independent whole-fixed snapshot correspondence is asserted here. -/
namespace Solidity.Backend.StorageOps.TargetFixedArrayTransport
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def stores (initial : Store) (dst src : Solidity.Storage.Loc) (start : Nat) : Nat → Store
  | 0 => initial
  | count+1 => CopyTransport.symbolicCopy (dst.add (start+count)) (src.add (start+count))
      (stores initial dst src start count)

def numerics (N : Nat) (hash : Solidity.Storage.Pre → Nat) (initial : WordStore)
    (dst src : Solidity.Storage.Loc) (start : Nat) : Nat → WordStore
  | 0 => initial
  | count+1 => NumericTraversal.copy N hash (dst.add (start+count)) (src.add (start+count))
      (numerics N hash initial dst src start count)

theorem toSlot_add (base : Solidity.Storage.Loc) (fits : TargetOperations.KeysFit base) (offset : Nat) :
    TargetOperations.toSlot (base.add offset) (TargetOperations.add_keysFit base fits offset) =
      (TargetOperations.toSlot base fits).add offset := by
  cases base <;> rfl

/-- All intermediate certificates are DERIVED from OLD transport and generated
CURRENT read/write coverage. Coverage is finite-run evidence, not a desired
preservation result or a new source restriction. Logical overlap is permitted. -/
theorem prefix_transport {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (start count : Nat)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (headers : ∀ k < count, dst.add (start+k) ∈ locations ∧ src.add (start+k) ∈ locations)
    (reads : ∀ k < count, ∀ j < ((stores store dst src start k) (src.add (start+k))).val.toNat,
      Solidity.Storage.Loc.data (src.add (start+k)) j ∈ locations)
    (writes : ∀ k < count, ∀ j < max ((stores store dst src start k) (dst.add (start+k))).val.toNat
        ((stores store dst src start k) (src.add (start+k))).val.toNat,
      Solidity.Storage.Loc.data (dst.add (start+k)) j ∈ locations) :
    Transport N hash locations (stores store dst src start count) (numerics N hash numeric dst src start count) ∧
    (∀ l (member : l ∈ locations),
      (TargetFixedArrayCopy.prefixMachine target (TargetOperations.toSlot dst dstFits)
        (TargetOperations.toSlot src srcFits) start count).store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (stores store dst src start count l)) := by
  induction count with
  | zero => exact ⟨initial,targetInitial⟩
  | succ count ih =>
    have previous := ih (fun k inside => headers k (Nat.lt_trans inside (Nat.lt_succ_self count)))
      (fun k inside => reads k (Nat.lt_trans inside (Nat.lt_succ_self count)))
      (fun k inside => writes k (Nat.lt_trans inside (Nat.lt_succ_self count)))
    have covered := headers count (Nat.lt_succ_self count)
    have sourceLength : LifecycleNumeric.headerLength N hash (src.add (start+count))
        (numerics N hash numeric dst src start count) =
        ((stores store dst src start count) (src.add (start+count))).val.toNat := by
      unfold LifecycleNumeric.headerLength
      rw [previous.1 _ covered.2]
    have oldLength : LifecycleNumeric.headerLength N hash (dst.add (start+count))
        (numerics N hash numeric dst src start count) =
        ((stores store dst src start count) (dst.add (start+count))).val.toNat := by
      unfold LifecycleNumeric.headerLength
      rw [previous.1 _ covered.1]
    have transported := CopyTransport.transported run (dst.add (start+count)) (src.add (start+count))
      (stores store dst src start count) (numerics N hash numeric dst src start count) previous.1 covered.1 covered.2
      (reads count (Nat.lt_succ_self count)) (writes count (Nat.lt_succ_self count))
    have agreement := TargetCopyRepresentation.numeric_agreement run (dst.add (start+count)) (src.add (start+count))
      (TargetOperations.add_keysFit dst dstFits _) (TargetOperations.add_keysFit src srcFits _)
      (stores store dst src start count) (numerics N hash numeric dst src start count)
      (TargetFixedArrayCopy.prefixMachine target (TargetOperations.toSlot dst dstFits) (TargetOperations.toSlot src srcFits) start count)
      (TargetFixedArrayCopy.prefixMachine target (TargetOperations.toSlot dst dstFits) (TargetOperations.toSlot src srcFits) start count).stack
      previous.1 covered.1 covered.2
      (by simpa only [sourceLength] using reads count (Nat.lt_succ_self count))
      (by simpa only [sourceLength,oldLength] using writes count (Nat.lt_succ_self count)) fitting previous.2
    refine ⟨transported,?_⟩
    intro l member
    have actual := agreement l member
    rw [transported l member] at actual
    rw [toSlot_add src srcFits (start+count),toSlot_add dst dstFits (start+count)] at actual
    exact actual

/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayTransport.stores' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms stores
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayTransport.numerics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numerics
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayTransport.toSlot_add' does not depend on any axioms -/
#guard_msgs in #print axioms toSlot_add
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayTransport.prefix_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms prefix_transport

end Solidity.Backend.StorageOps.TargetFixedArrayTransport
