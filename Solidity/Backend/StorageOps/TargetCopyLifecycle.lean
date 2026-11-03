import Solidity.Backend.StorageOps.TargetCopyRepresentation
import Solidity.Backend.StorageOps.TargetPrimitivePopPush

/-! Evolving actual target storage copy, pop and regrowth. The executed copy
DERIVES the middle owner/transport consumed by the lifecycle certificate. -/
namespace Solidity.Backend.StorageOps.TargetCopyLifecycle
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def code (dst : Evm.Slot) : List Evm.Instr := TargetArrayCopy.code ++ TargetPrimitivePopPush.code dst
noncomputable def execute (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (dst src : Solidity.Storage.Loc) (numeric : WordStore) : Option WordStore :=
  TargetPrimitivePopPush.execute N hash dst (NumericTraversal.copy N hash dst src numeric)

/-- Empty copied length fails at the actual pop, AFTER copy has executed. This
Out result is not a theorem that the surrounding world rolls back prefix writes. -/
theorem run_empty (target : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (empty : target.store src = 0) :
    Evm.run (code dst) { target with stack := .slot src :: .slot dst :: tail } = .revert := by
  unfold code
  rw [Evm.run_append_ok (TargetArrayCopyTail.run_current target tail src dst)]
  apply TargetPrimitivePopPush.run_empty
  rw [TargetArrayCopyTail.after_header,empty]

/-- The OLD copy premises discharge all intermediate preservation. Pop's last
write coverage is derived from the original generated copy writes and its
successful source operation, not assumed for an arbitrary middle store. -/
theorem complete {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (old source middle result : Value G (.array (.prim p)))
    (popped : recursivePop (old.overlay source) = some middle) (pushed : operationPush middle = some result)
    (indices : List Index) (dst src : Solidity.Storage.Loc)
    (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (tail : List Evm.Word)
    (beforeDst : Represented old (PrimitivePop.queries indices) dst store)
    (beforeSrc : Represented source (PrimitivePop.queries indices) src store)
    (initial : Transport N hash locations store numeric)
    (dstHeader : dst ∈ locations) (srcHeader : src ∈ locations)
    (dstCovered : ∀ i ∈ indices, Solidity.Storage.Loc.data dst i.val ∈ locations)
    (srcCovered : ∀ i ∈ indices, Solidity.Storage.Loc.data src i.val ∈ locations)
    (sourceCovered : ∀ i < source.length.val, Solidity.Storage.Loc.data src i ∈ locations)
    (visitedCovered : ∀ i < max old.length.val source.length.val, Solidity.Storage.Loc.data dst i ∈ locations)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l)) :
    ∃ finalStore finalTarget finalNumeric,
      execute N hash dst src numeric = some finalNumeric ∧
      Evm.run (code (TargetOperations.toSlot dst dstFits)) { target with stack := .slot (TargetOperations.toSlot src srcFits) :: .slot (TargetOperations.toSlot dst dstFits) :: tail } = .ok finalTarget 0 ∧
      Represented result (PrimitivePop.queries indices) dst finalStore ∧
      Transport N hash locations finalStore finalNumeric ∧
      (∀ l (member : l ∈ locations), finalTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (finalNumeric (l.word N hash))) := by
  have copied := TargetCopyRepresentation.complete run old source indices dst src dstFits srcFits store numeric target tail
    beforeDst beforeSrc initial dstHeader srcHeader dstCovered srcCovered sourceCovered visitedCovered fitting targetInitial
  have middleAgreement : ∀ l (member : l ∈ locations),
      (TargetArrayCopyTail.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store.cells (TargetOperations.toSlot l (fitting l member)) =
        TargetOperations.encodeWord (CopyTransport.symbolicCopy dst src store l) := by
    intro l member
    exact (copied.2.2.2.1 l member).trans (congrArg TargetOperations.encodeWord (copied.2.2.1 l member))
  have copiedLength : (old.overlay source).length.val = source.length.val := by
    cases old; cases source; rfl
  have lengths := (recursivePop_header (old.overlay source) middle popped).1
  have lastCovered : Solidity.Storage.Loc.data dst ((old.overlay source).length.val - 1) ∈ locations := by
    apply visitedCovered
    rw [copiedLength] at lengths ⊢
    omega
  have selectedCovered : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, q.location dst ∈ locations := by
    intro q member
    simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
    rcases member with rfl | ⟨i,inside,rfl⟩
    · exact dstHeader
    · rw [PrimitivePop.element_location]; exact dstCovered i inside
  obtain ⟨finalNumeric,numericRun,targetRun,owner,transported,agreement⟩ :=
    TargetPrimitivePopPush.complete_numeric run (old.overlay source) middle result popped pushed indices dst dstFits
      (CopyTransport.symbolicCopy dst src store)
      (TargetArrayCopyTail.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits))
      (NumericTraversal.copy N hash dst src numeric) fitting copied.2.1 copied.2.2.1 middleAgreement selectedCovered lastCovered
  refine ⟨_,_,finalNumeric,numericRun,?_,owner,transported,agreement⟩
  unfold code
  rw [Evm.run_append_ok copied.1]
  exact targetRun

/-- info: 'Solidity.Backend.StorageOps.TargetCopyLifecycle.run_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_empty
/-- info: 'Solidity.Backend.StorageOps.TargetCopyLifecycle.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete

end Solidity.Backend.StorageOps.TargetCopyLifecycle
