import Solidity.Backend.StorageOps.TargetArrayCopyTail
import Solidity.Backend.StorageOps.CopyTransport

/-! Operation-side bridge from current numeric storage copy to the actual
structured target program. The original per-run region remains explicit. -/
namespace Solidity.Backend.StorageOps.TargetCopyRepresentation
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- OLD finite transport and independent target-cell agreement connect each
covered CURRENT input word, without asserting anything about failed queries. -/
theorem initial_word {N : Nat} (hash : Solidity.Storage.Pre → Nat)
    (locations : List Solidity.Storage.Loc) (store : Store) (numeric : WordStore)
    (target : Evm.Machine) (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (initial : Transport N hash locations store numeric)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (l : Solidity.Storage.Loc) (covered : l ∈ locations) :
    target.store (TargetOperations.toSlot l (fitting l covered)) =
      (TargetOperations.encodeWord (numeric (l.word N hash))).val := by
  have equal := targetInitial l covered
  rw [← initial l covered] at equal
  exact congrArg Fin.val equal

/-- All original covered locations agree after ACTUAL target execution and
current-numeric copy. No global hash injectivity or desired output premise. -/
theorem numeric_agreement {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (tail : List Evm.Word)
    (initial : Transport N hash locations store numeric)
    (dstHeader : dst ∈ locations) (srcHeader : src ∈ locations)
    (sourceCovered : ∀ i < LifecycleNumeric.headerLength N hash src numeric, Solidity.Storage.Loc.data src i ∈ locations)
    (visitedCovered : ∀ i < max (LifecycleNumeric.headerLength N hash dst numeric) (LifecycleNumeric.headerLength N hash src numeric), Solidity.Storage.Loc.data dst i ∈ locations)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l)) :
    ∀ l (member : l ∈ locations),
      (TargetArrayCopyTail.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store.cells
        (TargetOperations.toSlot l (fitting l member)) =
        TargetOperations.encodeWord (NumericTraversal.copy N hash dst src numeric (l.word N hash)) := by
  have sourceLength : target.store (TargetOperations.toSlot src srcFits) = LifecycleNumeric.headerLength N hash src numeric :=
    initial_word hash locations store numeric target fitting initial targetInitial src srcHeader
  have oldLength : target.store (TargetOperations.toSlot dst dstFits) = LifecycleNumeric.headerLength N hash dst numeric :=
    initial_word hash locations store numeric target fitting initial targetInitial dst dstHeader
  intro l member
  apply Fin.ext
  change (TargetArrayCopyTail.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store (TargetOperations.toSlot l (fitting l member)) = _
  by_cases header : l = dst
  · subst l
    rw [TargetArrayCopyTail.after_header,NumericTraversal.copy_header]
    exact initial_word hash locations store numeric target fitting initial targetInitial src srcHeader
  · by_cases touched : ∃ j, j < max (LifecycleNumeric.headerLength N hash dst numeric) (LifecycleNumeric.headerLength N hash src numeric) ∧ l = .data dst j
    · obtain ⟨j,inside,rfl⟩ := touched
      change (TargetArrayCopyTail.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store (.data (TargetOperations.toSlot dst dstFits) j) = _
      rw [TargetArrayCopyTail.after_data,sourceLength,oldLength,
        NumericTraversal.copy_element run dst src numeric j dstHeader member visitedCovered,if_pos inside]
      by_cases live : j < LifecycleNumeric.headerLength N hash src numeric
      · rw [if_pos live,if_pos live]
        exact initial_word hash locations store numeric target fitting initial targetInitial (.data src j) (sourceCovered j live)
      · have stale : j < LifecycleNumeric.headerLength N hash dst numeric := by omega
        rw [if_neg live,if_neg live,if_pos stale]
        rfl
    · have symbolicHeader : TargetOperations.toSlot l (fitting l member) ≠ TargetOperations.toSlot dst dstFits := by
        intro same; exact header (TargetOperations.toSlot_injective _ _ _ _ same)
      have symbolicPayload : ∀ j, j < max (target.store (TargetOperations.toSlot src srcFits)) (target.store (TargetOperations.toSlot dst dstFits)) →
          TargetOperations.toSlot l (fitting l member) ≠ .data (TargetOperations.toSlot dst dstFits) j := by
        intro j inside same
        have locEq : l = .data dst j := TargetOperations.toSlot_injective _ _ _ dstFits same
        exact touched ⟨j,by rw [sourceLength,oldLength] at inside; omega,locEq⟩
      have physicalHeader : l.word N hash ≠ dst.word N hash := by
        intro same; exact header (run.word_inj member dstHeader same)
      have physicalPayload : ∀ j < max (LifecycleNumeric.headerLength N hash dst numeric) (LifecycleNumeric.headerLength N hash src numeric),
          l.word N hash ≠ (Solidity.Storage.Loc.data dst j).word N hash := by
        intro j inside same
        exact touched ⟨j,inside,run.word_inj member (visitedCovered j inside) same⟩
      rw [TargetArrayCopyTail.after_outside _ _ _ _ _ symbolicHeader symbolicPayload,
        NumericTraversal.copy_outside N hash dst src numeric (l.word N hash) physicalHeader physicalPayload]
      exact initial_word hash locations store numeric target fitting initial targetInitial l member


/-- Composition with the independent graph overlay and PUBLIC owner's existing
selected representation. BOTH old relations, numeric transport and complete
generated read/write coverage discharge the component premises. -/
theorem complete {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (old source : Value G (.array (.prim p))) (indices : List Index)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
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
    Evm.run TargetArrayCopy.code { target with stack := .slot (TargetOperations.toSlot src srcFits) :: .slot (TargetOperations.toSlot dst dstFits) :: tail } =
      .ok (TargetArrayCopyTail.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)) 0 ∧
    Represented (old.overlay source) (PrimitivePop.queries indices) dst (CopyTransport.symbolicCopy dst src store) ∧
    Transport N hash locations (CopyTransport.symbolicCopy dst src store) (NumericTraversal.copy N hash dst src numeric) ∧
    (∀ l (member : l ∈ locations),
      (TargetArrayCopyTail.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store.cells
        (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (NumericTraversal.copy N hash dst src numeric (l.word N hash))) ∧
    (∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, ∀ word, q.read (old.overlay source) = some word →
      NumericTraversal.copy N hash dst src numeric ((q.location dst).word N hash) = word) := by
  have dstOwner : Represented old [.length .nil] dst store := by
    intro q member; have same := List.mem_singleton.mp member; subst q
    exact beforeDst _ List.mem_cons_self
  have srcOwner : Represented source [.length .nil] src store := by
    intro q member; have same := List.mem_singleton.mp member; subst q
    exact beforeSrc _ List.mem_cons_self
  have dstWord := LifecycleNumeric.array_header_numeric old dst store numeric hash locations dstOwner initial dstHeader
  have srcWord := LifecycleNumeric.array_header_numeric source src store numeric hash locations srcOwner initial srcHeader
  have dstLength := LifecycleNumeric.headerLength_known hash dst numeric old.length dstWord
  have srcLength := LifecycleNumeric.headerLength_known hash src numeric source.length srcWord
  have existing := CopyTransport.complete run old source indices dst src store numeric beforeDst beforeSrc initial
    dstHeader srcHeader dstCovered srcCovered sourceCovered visitedCovered
  have owner : Represented (old.overlay source) (PrimitivePop.queries indices) dst (CopyTransport.symbolicCopy dst src store) := by
    simpa only [recursiveCopy_eq_overlay] using existing.2
  have actual := numeric_agreement run dst src dstFits srcFits store numeric target tail initial dstHeader srcHeader
    (by simpa only [srcLength] using sourceCovered) (by simpa only [srcLength,dstLength] using visitedCovered) fitting targetInitial
  refine ⟨TargetArrayCopyTail.run_current _ _ _ _,owner,existing.1,actual,?_⟩
  intro q member word observed
  have covered : q.location dst ∈ locations := by
    simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
    rcases member with rfl | ⟨i,inside,rfl⟩
    · exact dstHeader
    · rw [PrimitivePop.element_location]; exact dstCovered i inside
  exact owner.numeric existing.1 q member covered word observed

/-- info: 'Solidity.Backend.StorageOps.TargetCopyRepresentation.initial_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms initial_word
/-- info: 'Solidity.Backend.StorageOps.TargetCopyRepresentation.numeric_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_agreement
/-- info: 'Solidity.Backend.StorageOps.TargetCopyRepresentation.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete

end Solidity.Backend.StorageOps.TargetCopyRepresentation
