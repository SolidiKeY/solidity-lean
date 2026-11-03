import Solidity.Backend.StorageOps.NestedSnapshotFrames

/-! Precise operation-generated source-read coverage. Existing broad adapters
remain unchanged; unread source queries are not extra execution premises. -/
namespace Solidity.Backend.StorageOps.CopyAccess
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Exactly the selected source payload reads used by the independent live
copy meaning, plus its captured header. Existing Query demands are reused. -/
def readQueries {n : Nat} {G : Schema n} {p : PrimTy}
    (source : Value G (.array (.prim p))) (indices : List Index) : List (Query G (.array (.prim p))) :=
  .length .nil :: (indices.filter (fun i => decide (i.val < source.length.val))).map PrimitivePop.elementQuery

theorem read_queries_from_full {n : Nat} {G : Schema n} {p : PrimTy}
    (source : Value G (.array (.prim p))) (indices : List Index) (base : Solidity.Storage.Loc) (store : Store)
    (before : Represented source (PrimitivePop.queries indices) base store) :
    Represented source (readQueries source indices) base store := by
  intro q member
  simp only [readQueries,List.mem_cons,List.mem_map] at member
  rcases member with rfl | ⟨i,filtered,rfl⟩
  · exact before _ List.mem_cons_self
  · exact before _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,(List.mem_filter.mp filtered).1,rfl⟩))

/-- All ACTUAL source live reads and destination writes/observations remain
covered. No source location outside its live prefix is required merely because
a retained destination observation uses the same index. -/
theorem represented {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (old source : Value G (.array (.prim p))) (indices : List Index)
    (dst src : Solidity.Storage.Loc) (store : Store) (numeric : WordStore)
    (beforeDst : Represented old (PrimitivePop.queries indices) dst store)
    (beforeSrc : Represented source (readQueries source indices) src store)
    (initial : Transport N hash locations store numeric)
    (dstHeader : dst ∈ locations) (srcHeader : src ∈ locations)
    (dstCovered : ∀ i ∈ indices, Solidity.Storage.Loc.data dst i.val ∈ locations)
    (sourceCovered : ∀ j < source.length.val, Solidity.Storage.Loc.data src j ∈ locations)
    (visitedCovered : ∀ j < max old.length.val source.length.val, Solidity.Storage.Loc.data dst j ∈ locations) :
    Transport N hash locations (CopyTransport.symbolicCopy dst src store) (NumericTraversal.copy N hash dst src numeric) ∧
    Represented (old.overlay source) (PrimitivePop.queries indices) dst (CopyTransport.symbolicCopy dst src store) := by
  have dstWord : store dst = lengthWord old.length.val old.length.isLt :=
    (beforeDst (.length .nil) List.mem_cons_self).2.2 _ (by cases old; rfl)
  have srcWord : store src = lengthWord source.length.val source.length.isLt :=
    (beforeSrc (.length .nil) List.mem_cons_self).2.2 _ (by cases source; rfl)
  have dstLen : LifecycleNumeric.headerLength N hash dst numeric = old.length.val :=
    LifecycleNumeric.headerLength_known hash dst numeric old.length ((initial dst dstHeader).trans dstWord)
  have srcLen : LifecycleNumeric.headerLength N hash src numeric = source.length.val :=
    LifecycleNumeric.headerLength_known hash src numeric source.length ((initial src srcHeader).trans srcWord)
  have dstStored : (store dst).val.toNat = old.length.val := by rw [dstWord]; rfl
  have srcStored : (store src).val.toNat = source.length.val := by rw [srcWord]; rfl
  have transported := CopyTransport.transported run dst src store numeric initial dstHeader srcHeader
    (by simpa only [srcStored] using sourceCovered) (by simpa only [dstStored,srcStored] using visitedCovered)
  refine ⟨transported,?_⟩
  intro q member
  simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
  rcases member with rfl | ⟨i,inside,rfl⟩
  · have oldBounds := (beforeDst (.length .nil) List.mem_cons_self).2.1
    have srcBounds := (beforeSrc (.length .nil) List.mem_cons_self).2.1
    refine ⟨True.intro,?_,?_⟩
    · cases old with
      | array oe ol oh os =>
        cases source with
        | array ne nl nh ns =>
          change ol.val ≤ lmax ∧ oe.val ≤ lmax at oldBounds
          change nl.val ≤ lmax ∧ ne.val ≤ lmax at srcBounds
          change nl.val ≤ lmax ∧ max oe.val nl.val ≤ lmax
          constructor <;> omega
    · intro word observed
      have header : (Query.length (G := G) (E := .prim p) .nil).read (old.overlay source) =
          some (lengthWord source.length.val source.length.isLt) := by cases old; cases source; rfl
      have equal := Option.some.inj (header.symm.trans observed)
      exact (transported dst dstHeader).symm.trans ((NumericTraversal.copy_header N hash dst src numeric).trans
        ((initial src srcHeader).trans (srcWord.trans equal)))
  · have queryMember : PrimitivePop.elementQuery (G := G) (p := p) i ∈ PrimitivePop.queries indices :=
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,inside,rfl⟩)
    refine ⟨(beforeDst _ queryMember).1,True.intro,?_⟩
    intro word observed
    have actual := NumericTraversal.copy_element run dst src numeric i.val dstHeader (dstCovered i inside)
      (by simpa only [dstLen,srcLen] using visitedCovered)
    dsimp only at actual
    rw [dstLen,srcLen] at actual
    rw [← recursiveCopy_eq_overlay,NumericTraversal.graph_read] at observed
    rw [PrimitivePop.element_location]
    apply (transported _ (dstCovered i inside)).symm.trans
    by_cases live : i.val < source.length.val
    · rw [if_pos live] at observed
      rw [if_pos (show i.val < max old.length.val source.length.val by omega),if_pos live] at actual
      have sourceMember : PrimitivePop.elementQuery (G := G) (p := p) i ∈ readQueries source indices :=
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,List.mem_filter.mpr ⟨inside,by simpa only [decide_eq_true_eq] using live⟩,rfl⟩)
      have read := (beforeSrc _ sourceMember).2.2 word observed
      rw [PrimitivePop.element_location] at read
      exact actual.trans ((initial _ (sourceCovered i.val live)).trans read)
    · rw [if_neg live] at observed
      by_cases stale : i.val < old.length.val
      · rw [if_pos stale] at observed
        cases observed
        rw [if_pos (show i.val < max old.length.val source.length.val by omega),if_neg live] at actual
        exact actual
      · rw [if_neg stale] at observed
        rw [if_neg (show ¬ i.val < max old.length.val source.length.val by omega)] at actual
        have read := (beforeDst _ queryMember).2.2 word observed
        rw [PrimitivePop.element_location] at read
        exact actual.trans ((initial _ (dstCovered i inside)).trans read)

/-- Compose precise actual reads with the existing executable target program.
No unused source-query coverage or desired postowner is a premise. -/
theorem complete {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (old source : Value G (.array (.prim p))) (indices : List Index)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (tail : List Evm.Word)
    (beforeDst : Represented old (PrimitivePop.queries indices) dst store)
    (beforeSrc : Represented source (readQueries source indices) src store)
    (initial : Transport N hash locations store numeric)
    (dstHeader : dst ∈ locations) (srcHeader : src ∈ locations)
    (dstCovered : ∀ i ∈ indices, Solidity.Storage.Loc.data dst i.val ∈ locations)
    (sourceCovered : ∀ j < source.length.val, Solidity.Storage.Loc.data src j ∈ locations)
    (visitedCovered : ∀ j < max old.length.val source.length.val, Solidity.Storage.Loc.data dst j ∈ locations)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l)) :
    Evm.run TargetArrayCopy.code { target with stack := .slot (TargetOperations.toSlot src srcFits) :: .slot (TargetOperations.toSlot dst dstFits) :: tail } =
      .ok (TargetArrayCopyTail.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)) 0 ∧
    Represented (old.overlay source) (PrimitivePop.queries indices) dst (CopyTransport.symbolicCopy dst src store) ∧
    Transport N hash locations (CopyTransport.symbolicCopy dst src store) (NumericTraversal.copy N hash dst src numeric) ∧
    (∀ l (member : l ∈ locations), (TargetArrayCopyTail.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store.cells
      (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (CopyTransport.symbolicCopy dst src store l)) := by
  have owner := represented run old source indices dst src store numeric beforeDst beforeSrc initial dstHeader srcHeader dstCovered sourceCovered visitedCovered
  have dstWord : numeric (dst.word N hash) = lengthWord old.length.val old.length.isLt :=
    (initial dst dstHeader).trans ((beforeDst (.length .nil) List.mem_cons_self).2.2 _ (by cases old; rfl))
  have srcWord : numeric (src.word N hash) = lengthWord source.length.val source.length.isLt :=
    (initial src srcHeader).trans ((beforeSrc (.length .nil) List.mem_cons_self).2.2 _ (by cases source; rfl))
  have dstLen := LifecycleNumeric.headerLength_known hash dst numeric old.length dstWord
  have srcLen := LifecycleNumeric.headerLength_known hash src numeric source.length srcWord
  have agreement := TargetCopyRepresentation.numeric_agreement run dst src dstFits srcFits store numeric target tail initial dstHeader srcHeader
    (by simpa only [srcLen] using sourceCovered) (by simpa only [dstLen,srcLen] using visitedCovered) fitting targetInitial
  refine ⟨TargetArrayCopyTail.run_current _ _ _ _,owner.2,owner.1,?_⟩
  intro l member
  have actual := agreement l member
  rw [owner.1 l member] at actual
  exact actual

/-- info: 'Solidity.Backend.StorageOps.CopyAccess.readQueries' does not depend on any axioms -/
#guard_msgs in #print axioms readQueries
/-- info: 'Solidity.Backend.StorageOps.CopyAccess.read_queries_from_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms read_queries_from_full
/-- info: 'Solidity.Backend.StorageOps.CopyAccess.represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms represented
/-- info: 'Solidity.Backend.StorageOps.CopyAccess.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete

/-- PUBLIC selected snapshot representation needs physical framing only for
successful logical observations. None yields no stored-word/default/frame law.
All actual operation reads/writes remain covered in the ORIGINAL finite run. -/
theorem observed_frame {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
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
    (covered : ∀ q ∈ queries, ∀ word, q.read value = some word → q.location base ∈ locations)
    (outside : ∀ q (member : q ∈ queries) word (observed : q.read value = some word),
      TargetOperations.toSlot (q.location base) (fitting _ (covered q member word observed)) ∉
        TargetNestedArrayCopyLoop.touched target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) count) :
    Represented value queries base (TargetNestedArrayTransport.copyStores store dst src count) := by
  intro q member
  obtain ⟨supported,compatible,observed⟩ := before q member
  refine ⟨supported,compatible,?_⟩
  intro word found
  rw [NestedSnapshotFrames.copy_word_frame run dst src dstFits srcFits store numeric target count initial fitting targetInitial
    headers reads writes (q.location base) (covered q member word found) (outside q member word found)]
  exact observed word found

/-- info: 'Solidity.Backend.StorageOps.CopyAccess.observed_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms observed_frame

end Solidity.Backend.StorageOps.CopyAccess
