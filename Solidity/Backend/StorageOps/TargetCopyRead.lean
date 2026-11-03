import Solidity.Backend.StorageOps.TargetCopyRepresentation

/-! Actual copy followed by a current runtime indexed read. Intermediate
representation and target agreement are derived from the executed copy. -/
namespace Solidity.Backend.StorageOps.TargetCopyRead
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def operands (dst : Evm.Slot) : List Evm.Instr := [.push (.slot dst),.swap 1]
def code (dst : Evm.Slot) : List Evm.Instr := TargetArrayCopy.code ++ (operands dst ++ TargetArrayRead.code)

/-- The live bound is the ACTUAL copied header, and failed reading follows the
executed copy prefix. This is not a world rollback assertion. -/
theorem run_failed (target : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (i : Index) (outside : target.store src ≤ i.val) :
    Evm.run (code dst) { target with stack := .slot src :: .slot dst :: .val ⟨i.val,i.isLt⟩ :: tail } = .revert := by
  unfold code
  rw [Evm.run_append_ok (TargetArrayCopyTail.run_current target (.val ⟨i.val,i.isLt⟩ :: tail) src dst)]
  rw [Evm.run_append_ok (m' := { TargetArrayCopyTail.afterCopy target (.val ⟨i.val,i.isLt⟩ :: tail) src dst with stack := .val ⟨i.val,i.isLt⟩ :: .slot dst :: tail }) (by rfl)]
  rw [TargetArrayRead.run_current,TargetArrayCopyTail.after_header,if_neg (by omega)]

/-- BOTH target outcomes are driven by the current copied header and cell.
The loop preserves the original runtime index; success replaces it by SLOAD. -/
theorem run_current (target : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot) (i : Index) :
    let copied := TargetArrayCopyTail.afterCopy target (.val ⟨i.val,i.isLt⟩ :: tail) src dst
    Evm.run (code dst) { target with stack := .slot src :: .slot dst :: .val ⟨i.val,i.isLt⟩ :: tail } =
      if i.val < target.store src then
        .ok { copied with stack := .val (copied.store.cells (.data dst i.val)) :: tail } 0 else .revert := by
  unfold code
  rw [Evm.run_append_ok (TargetArrayCopyTail.run_current target (.val ⟨i.val,i.isLt⟩ :: tail) src dst)]
  rw [Evm.run_append_ok (m' := { TargetArrayCopyTail.afterCopy target (.val ⟨i.val,i.isLt⟩ :: tail) src dst with stack := .val ⟨i.val,i.isLt⟩ :: .slot dst :: tail }) (by rfl)]
  rw [TargetArrayRead.run_current,TargetArrayCopyTail.after_header]

/-- Plain current SOURCE-header agreement suffices for the exact intrinsic
LIVE failure outcome, even for retained or out-of-extent raw aliases. -/
theorem failure_matches {n : Nat} {G : Schema n} {p : PrimTy}
    (old source : Value G (.array (.prim p))) (i : Index)
    (target : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (header : target.store src = source.length.val) :
    Evm.run (code dst) { target with stack := .slot src :: .slot dst :: .val ⟨i.val,i.isLt⟩ :: tail } = .revert ↔
      (TargetArrayRead.path i).readLive Value.dflt (old.overlay source) = none := by
  have length : (old.overlay source).length.val = source.length.val := by cases old; cases source; rfl
  rw [run_current,header,TargetArrayRead.live_none_iff,length]
  by_cases live : i.val < source.length.val
  · rw [if_pos live]
    constructor
    · intro impossible; cases impossible
    · intro impossible; omega
  · rw [if_neg live]
    exact ⟨fun _ => by omega,fun _ => rfl⟩

/-- BOTH original selected owner relations and generated finite-run coverage
supply the intermediate certificate. The index arrives on the runtime stack;
the code contains no evaluated source result word or graph-value oracle. -/
theorem complete {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (old source : Value G (.array (.prim p))) (i : Index) (value : Value G (.prim p))
    (found : (TargetArrayRead.path i).readLive Value.dflt (old.overlay source) = some value)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (tail : List Evm.Word)
    (beforeDst : Represented old (PrimitivePop.queries [i]) dst store)
    (beforeSrc : Represented source (PrimitivePop.queries [i]) src store)
    (initial : Transport N hash locations store numeric)
    (dstHeader : dst ∈ locations) (srcHeader : src ∈ locations)
    (dstCovered : Solidity.Storage.Loc.data dst i.val ∈ locations)
    (srcCovered : Solidity.Storage.Loc.data src i.val ∈ locations)
    (sourceCovered : ∀ j < source.length.val, Solidity.Storage.Loc.data src j ∈ locations)
    (visitedCovered : ∀ j < max old.length.val source.length.val, Solidity.Storage.Loc.data dst j ∈ locations)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l)) :
    let copied := TargetArrayCopyTail.afterCopy target (.val ⟨i.val,i.isLt⟩ :: tail) (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)
    Evm.run (code (TargetOperations.toSlot dst dstFits)) { target with stack := .slot (TargetOperations.toSlot src srcFits) :: .slot (TargetOperations.toSlot dst dstFits) :: .val ⟨i.val,i.isLt⟩ :: tail } =
      .ok { copied with stack := .val (TargetOperations.encodeWord (PrimTy.toWord value.head)) :: tail } 0 ∧
    NumericTraversal.copy N hash dst src numeric ((Solidity.Storage.Loc.data dst i.val).word N hash) = PrimTy.toWord value.head := by
  have certified := TargetCopyRepresentation.complete run old source [i] dst src dstFits srcFits store numeric target (.val ⟨i.val,i.isLt⟩ :: tail)
    beforeDst beforeSrc initial dstHeader srcHeader (fun j member => by have same := List.mem_singleton.mp member; subst j; exact dstCovered)
    (fun j member => by have same := List.mem_singleton.mp member; subst j; exact srcCovered) sourceCovered visitedCovered fitting targetInitial
  have middleAgreement : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) [i],
      (TargetArrayCopyTail.afterCopy target (.val ⟨i.val,i.isLt⟩ :: tail) (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store.cells
        (TargetOperations.toSlot (q.location dst) (TargetOperations.query_keysFit q dst dstFits)) = TargetOperations.encodeWord (CopyTransport.symbolicCopy dst src store (q.location dst)) := by
    intro q member
    have covered : q.location dst ∈ locations := by
      simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
      rcases member with rfl | ⟨j,inside,rfl⟩
      · exact dstHeader
      · have same : j = i := by simpa only [List.not_mem_nil,or_false] using inside
        subst j
        rw [PrimitivePop.element_location]; exact dstCovered
    exact (certified.2.2.2.1 _ covered).trans (congrArg TargetOperations.encodeWord (certified.2.2.1 _ covered))
  have read := TargetArrayRead.complete_read (old.overlay source) i value found dst dstFits
    (CopyTransport.symbolicCopy dst src store)
    (TargetArrayCopyTail.afterCopy target (.val ⟨i.val,i.isLt⟩ :: tail) (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits))
    tail (NumericTraversal.copy N hash dst src numeric) hash locations certified.2.1 certified.2.2.1 dstCovered middleAgreement
  refine ⟨?_,read.2⟩
  unfold code
  rw [Evm.run_append_ok certified.1]
  rw [Evm.run_append_ok (m' := { TargetArrayCopyTail.afterCopy target (.val ⟨i.val,i.isLt⟩ :: tail) (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) with stack := .val ⟨i.val,i.isLt⟩ :: .slot (TargetOperations.toSlot dst dstFits) :: tail }) (by rfl)]
  exact read.1

/-- info: 'Solidity.Backend.StorageOps.TargetCopyRead.run_failed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_failed
/-- info: 'Solidity.Backend.StorageOps.TargetCopyRead.run_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_current
/-- info: 'Solidity.Backend.StorageOps.TargetCopyRead.failure_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms failure_matches
/-- info: 'Solidity.Backend.StorageOps.TargetCopyRead.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete

end Solidity.Backend.StorageOps.TargetCopyRead
