import Solidity.Backend.StorageOps.CopyAccess
import Solidity.Backend.StorageOps.NestedCopyObservations

/-! Precise fresh/default copied OUTPUT under a potentially nonzero old raw
header. No initial default-child representation or physical zero premise.
PUBLIC requested-query support stays explicit; no new Source admission cap. -/
namespace Solidity.Backend.StorageOps.FreshCopyAccess
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Only header+selected LIVE source words are input observations. Every actual
source read, extra old-raw destination clear and selected target point remains
covered by the original finite run. None never gives a raw/default/frame law. -/
theorem represented {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (source : Value G (.array (.prim p))) (indices : List Index)
    (dst src : Solidity.Storage.Loc) (store : Store) (numeric : WordStore)
    (beforeSource : Represented source (CopyAccess.readQueries source indices) src store)
    (outputSupported : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, q.supported)
    (initial : Transport N hash locations store numeric)
    (dstHeader : dst ∈ locations) (srcHeader : src ∈ locations)
    (dstCovered : ∀ i ∈ indices, Solidity.Storage.Loc.data dst i.val ∈ locations)
    (sourceCovered : ∀ j < source.length.val, Solidity.Storage.Loc.data src j ∈ locations)
    (visitedCovered : ∀ j < max (store dst).val.toNat source.length.val, Solidity.Storage.Loc.data dst j ∈ locations) :
    Represented source.strip (PrimitivePop.queries indices) dst (CopyTransport.symbolicCopy dst src store) ∧
    Transport N hash locations (CopyTransport.symbolicCopy dst src store) (NumericTraversal.copy N hash dst src numeric) := by
  have sourceWord : store src = lengthWord source.length.val source.length.isLt :=
    (beforeSource (.length .nil) List.mem_cons_self).2.2 _ (by cases source; rfl)
  have sourceNumeric : numeric (src.word N hash) = lengthWord source.length.val source.length.isLt :=
    (initial src srcHeader).trans sourceWord
  have sourceLength : LifecycleNumeric.headerLength N hash src numeric = source.length.val :=
    LifecycleNumeric.headerLength_known hash src numeric source.length sourceNumeric
  have sourceStoredLength : (store src).val.toNat = source.length.val := by rw [sourceWord]; rfl
  have oldLength : LifecycleNumeric.headerLength N hash dst numeric = (store dst).val.toNat := by
    unfold LifecycleNumeric.headerLength
    rw [initial dst dstHeader]
  have transported := CopyTransport.transported run dst src store numeric initial dstHeader srcHeader
    (by simpa only [sourceStoredLength] using sourceCovered)
    (by simpa only [sourceStoredLength] using visitedCovered)
  refine ⟨?_,transported⟩
  intro q member
  simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
  rcases member with rfl | ⟨i,inside,rfl⟩
  · have sourceBounds := (beforeSource (.length .nil) List.mem_cons_self).2.1
    refine ⟨True.intro,?_,?_⟩
    · cases source with
      | array extent length bound slots =>
        change length.val ≤ lmax ∧ extent.val ≤ lmax at sourceBounds
        change length.val ≤ lmax ∧ max 0 length.val ≤ lmax
        simpa only [Nat.zero_max] using And.intro sourceBounds.1 sourceBounds.1
    · intro word observed
      have head : (Query.length (G := G) (E := .prim p) .nil).read source.strip =
          some (lengthWord source.length.val source.length.isLt) := by cases source; rfl
      have same := Option.some.inj (head.symm.trans observed)
      exact (transported dst dstHeader).symm.trans ((NumericTraversal.copy_header N hash dst src numeric).trans (sourceNumeric.trans same))
  · have queryMember : PrimitivePop.elementQuery (G := G) (p := p) i ∈ PrimitivePop.queries indices :=
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,inside,rfl⟩)
    refine ⟨outputSupported _ queryMember,True.intro,?_⟩
    intro word observed
    by_cases live : i.val < source.length.val
    · have sourceRead := observed
      rw [NestedCopyObservations.strip_element,if_pos live] at sourceRead
      have actual := NumericTraversal.copy_element run dst src numeric i.val dstHeader (dstCovered i inside)
        (by simpa only [sourceLength,oldLength] using visitedCovered)
      dsimp only at actual
      rw [sourceLength,oldLength,if_pos (show i.val < max (store dst).val.toNat source.length.val from Nat.lt_of_lt_of_le live (Nat.le_max_right _ _)),if_pos live] at actual
      have sourceMember : PrimitivePop.elementQuery (G := G) (p := p) i ∈ CopyAccess.readQueries source indices :=
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,List.mem_filter.mpr ⟨inside,by simpa only [decide_eq_true_eq] using live⟩,rfl⟩)
      have sourceValue := (beforeSource _ sourceMember).2.2 word sourceRead
      rw [PrimitivePop.element_location] at sourceValue
      have value : numeric ((Solidity.Storage.Loc.data src i.val).word N hash) = word :=
        (initial _ (sourceCovered i.val live)).trans sourceValue
      rw [PrimitivePop.element_location]
      exact (transported _ (dstCovered i inside)).symm.trans (actual.trans value)
    · rw [NestedCopyObservations.strip_element,if_neg live] at observed
      cases observed

/-- Existing current-header target code realizes the independent strip result.
ALL current target/numeric agreements are derived from OLD inputs. -/
theorem complete {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (source : Value G (.array (.prim p))) (indices : List Index)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (tail : List Evm.Word)
    (beforeSource : Represented source (CopyAccess.readQueries source indices) src store)
    (outputSupported : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, q.supported)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (dstHeader : dst ∈ locations) (srcHeader : src ∈ locations)
    (dstCovered : ∀ i ∈ indices, Solidity.Storage.Loc.data dst i.val ∈ locations)
    (sourceCovered : ∀ j < source.length.val, Solidity.Storage.Loc.data src j ∈ locations)
    (visitedCovered : ∀ j < max (store dst).val.toNat source.length.val, Solidity.Storage.Loc.data dst j ∈ locations) :
    Evm.run TargetArrayCopy.code { target with stack := .slot (TargetOperations.toSlot src srcFits) :: .slot (TargetOperations.toSlot dst dstFits) :: tail } =
      .ok (TargetArrayCopyTail.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)) 0 ∧
    Represented source.strip (PrimitivePop.queries indices) dst (CopyTransport.symbolicCopy dst src store) ∧
    Transport N hash locations (CopyTransport.symbolicCopy dst src store) (NumericTraversal.copy N hash dst src numeric) ∧
    (∀ l (member : l ∈ locations), (TargetArrayCopyTail.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store.cells
      (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (CopyTransport.symbolicCopy dst src store l)) := by
  have output := represented run source indices dst src store numeric beforeSource outputSupported initial dstHeader srcHeader
    dstCovered sourceCovered visitedCovered
  have sourceWord : numeric (src.word N hash) = lengthWord source.length.val source.length.isLt :=
    (initial src srcHeader).trans ((beforeSource (.length .nil) List.mem_cons_self).2.2 _ (by cases source; rfl))
  have sourceLength := LifecycleNumeric.headerLength_known hash src numeric source.length sourceWord
  have oldLength : LifecycleNumeric.headerLength N hash dst numeric = (store dst).val.toNat := by
    unfold LifecycleNumeric.headerLength
    rw [initial dst dstHeader]
  have actual := TargetCopyRepresentation.numeric_agreement run dst src dstFits srcFits store numeric target tail initial dstHeader srcHeader
    (by simpa only [sourceLength] using sourceCovered) (by simpa only [sourceLength,oldLength] using visitedCovered) fitting targetInitial
  refine ⟨TargetArrayCopyTail.run_current _ _ _ _,output.1,output.2,?_⟩
  intro l member
  have observed := actual l member
  rw [output.2 l member] at observed
  exact observed

/-- info: 'Solidity.Backend.StorageOps.FreshCopyAccess.represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms represented
/-- info: 'Solidity.Backend.StorageOps.FreshCopyAccess.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Backend.StorageOps.FreshCopyAccess
