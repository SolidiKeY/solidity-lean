import Solidity.Backend.StorageOps.PrimitiveSnapshotCommutation
import Solidity.Backend.StorageOps.TargetSnapshotRepeat

/-! Repeated CURRENT-input snapshot operations under the ORIGINAL finite-run
relation. Region interpretation is local to covered reads/writes, never global
hash injectivity or a definition of independent Source evaluation. -/
namespace Solidity.Backend.StorageOps.PrimitiveSnapshotRepeat
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph PrimitiveSnapshotNumeric

/-- All numeric words, not only the covered observer list, stabilize. Runtime
count is arbitrary; covered source/write locations and original region facts
derive source stability and distinct visited destination addresses. -/
theorem numeric_repeat {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (initial : WordStore)
 (dst src : Solidity.Storage.Loc) (count : Nat)
 (sourceCovered : ∀ i<count,src.add i ∈ locations) (dstCovered : ∀ i<count,dst.add i ∈ locations)
 (safe : src=dst ∨ ∀ i<count,∀ j<count,src.add i≠dst.add j) :
 numeric N hash (numeric N hash initial dst src count) dst src count=numeric N hash initial dst src count := by
 rcases safe with same | separate
 · subst dst
   simp only [PrimitiveSnapshotSelf.numeric_self]
 · let first := numeric N hash initial dst src count
   have stable : ∀ i<count,first ((src.add i).word N hash)=initial ((src.add i).word N hash) := by
    intro i inside
    apply numeric_outside run initial dst src count (src.add i) (sourceCovered i inside) dstCovered
    rintro ⟨j,visited,equal⟩
    exact separate i inside j visited equal
   have samePrefix : ∀ k,k≤count →
    NumericTraversal.writePrefix (fun i => (dst.add i).word N hash)
     (fun i => first ((src.add i).word N hash)) k first=
    NumericTraversal.writePrefix (fun i => (dst.add i).word N hash)
     (fun i => initial ((src.add i).word N hash)) k first := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro bound
      simp only [NumericTraversal.writePrefix]
      rw [ih (by omega),stable k (by omega)]
   have restarted := NumericTraversal.prefix_restart
    (fun i => (dst.add i).word N hash) (fun i => initial ((src.add i).word N hash)) count count initial (by
     simp only [Nat.max_self]
     intro i hi j hj different equal
     exact different (Solidity.Storage.Loc.add_inj (run.word_inj (dstCovered i hi) (dstCovered j hj) equal)))
   change NumericTraversal.writePrefix (fun i => (dst.add i).word N hash)
    (fun i => first ((src.add i).word N hash)) count first=first
   rw [samePrefix count (Nat.le_refl _)]
   simpa only [numeric,Nat.max_self] using restarted

/-- Whole symbolic-store repetition derives from OLD transport and the exact
numeric result on covered writes; all other observers use the actual frame. -/
theorem symbolic_repeat {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (captured : Store) (initial : WordStore)
 (before : Transport N hash locations captured initial) (dst src : Solidity.Storage.Loc) (count : Nat)
 (sourceCovered : ∀ i<count,src.add i ∈ locations) (dstCovered : ∀ i<count,dst.add i ∈ locations)
 (safe : src=dst ∨ ∀ i<count,∀ j<count,src.add i≠dst.add j) :
 symbolic (symbolic captured dst src count) dst src count=symbolic captured dst src count := by
 have first := transported run captured initial before dst src count sourceCovered dstCovered count (Nat.le_refl _)
 have twice := PrimitiveSnapshotCommutation.sequence_transport run captured initial before
  dst src count dst src count dstCovered sourceCovered dstCovered sourceCovered
 have numericEq := numeric_repeat run initial dst src count sourceCovered dstCovered safe
 funext observer
 by_cases copied : ∃ i,i<count ∧ observer=dst.add i
 · obtain ⟨i,inside,rfl⟩:=copied
   exact (twice _ (dstCovered i inside)).symm.trans
    ((congrFun numericEq _).trans (first _ (dstCovered i inside)))
 · apply PrimitiveSnapshotFrames.symbolic_outside
   intro i inside equal
   exact copied ⟨i,inside,equal⟩

/-- OLD relation and actual finite trace derive BOTH transports, whole-store
repetition and ACTUAL compiler execution/agreement. No middle owner, source
stability or desired result is supplied as a premise. -/
theorem complete {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (p : PrimTy) (size : FixedSize)
 (captured : Store) (initial : WordStore) (machine : Evm.Machine)
 (before : Transport N hash locations captured initial) (dst src : Solidity.Storage.Loc)
 (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
 (sourceCovered : ∀ i<size.val,src.add i ∈ locations) (dstCovered : ∀ i<size.val,dst.add i ∈ locations)
 (safe : src=dst ∨ ∀ i<size.val,∀ j<size.val,src.add i≠dst.add j)
 (fitting : ∀ l ∈ locations,TargetOperations.KeysFit l)
 (initialAgreement : ∀ l (member : l ∈ locations),machine.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (initial (l.word N hash))) :
 let sym1 := symbolic captured dst src size.val
 let num1 := numeric N hash initial dst src size.val
 let sym2 := symbolic sym1 dst src size.val
 let num2 := numeric N hash num1 dst src size.val
 let after := TargetFixedSnapshot.afterCopy p size machine (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)
 Transport N hash locations sym1 num1 ∧ Transport N hash locations sym2 num2 ∧
 sym2=sym1 ∧ num2=num1 ∧
 Evm.run (TargetFixedSnapshot.code p size (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) ++
  TargetFixedSnapshot.code p size (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)) machine=.ok after 0 ∧
 (∀ l (member : l ∈ locations),after.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (num2 (l.word N hash))) := by
 dsimp only
 have first := transported run captured initial before dst src size.val sourceCovered dstCovered size.val (Nat.le_refl _)
 have both := PrimitiveSnapshotCommutation.target_sequence run p p size size captured initial machine before
  dst src dst src dstFits srcFits dstFits srcFits dstCovered sourceCovered dstCovered sourceCovered fitting initialAgreement
 have numericEq := numeric_repeat run initial dst src size.val sourceCovered dstCovered safe
 have symbolicEq := symbolic_repeat run captured initial before dst src size.val sourceCovered dstCovered safe
 have targetSafe : TargetOperations.toSlot src srcFits=TargetOperations.toSlot dst dstFits ∨
  ∀ i<size.val,∀ j<size.val,(TargetOperations.toSlot src srcFits).add i≠(TargetOperations.toSlot dst dstFits).add j := by
  rcases safe with same | separate
  · subst dst
    exact Or.inl rfl
  · right
    intro i hi j hj equal
    have addresses : TargetOperations.toSlot (src.add i) (TargetOperations.add_keysFit src srcFits i)=
     TargetOperations.toSlot (dst.add j) (TargetOperations.add_keysFit dst dstFits j) := by
      rw [TargetFixedArrayTransport.toSlot_add,TargetFixedArrayTransport.toSlot_add]
      exact equal
    exact separate i hi j hj (TargetOperations.toSlot_injective _ _ _ _ addresses)
 have actual := TargetSnapshotRepeat.complete p size machine (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) targetSafe
 have finalAgreement := both.2.2
 rw [actual.2] at finalAgreement
 exact ⟨first,both.1,symbolicEq,numericEq,actual.1,finalAgreement⟩

/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotRepeat.numeric_repeat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_repeat
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotRepeat.symbolic_repeat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms symbolic_repeat
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotRepeat.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Backend.StorageOps.PrimitiveSnapshotRepeat
