import Solidity.Backend.StorageOps.TargetNestedArrayTransport
import Solidity.Backend.StorageOps.MappingPaths

/-! Operation-side observations of the independent published copy meaning.
No new source/value/state/representation and no missing-read=>zero rule. -/
namespace Solidity.Backend.StorageOps.NestedCopyObservations
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- A fresh/default primitive-array result has only the source LIVE extent.
Every older source shadow and every out-of-extent result read remains excluded
by the independent specification, not by a target-imposed length cap. -/
theorem strip_element {n : Nat} {G : Schema n} {p : PrimTy}
    (source : Value G (.array (.prim p))) (i : Index) :
    (PrimitivePop.elementQuery i).read source.strip =
      if i.val < source.length.val then (PrimitivePop.elementQuery i).read source else none := by
  cases source with
  | array extent length bound slots =>
    by_cases live : i.val < length.val
    · have inside : i.val < extent.val := Nat.lt_of_lt_of_le live bound
      simp only [Value.strip,Value.dflt,Value.defaultBelow,Value.overlay,
        PrimitivePop.elementQuery,Query.read,Value.observe,Value.find,TypeGraph.Path.read,Step.get,
        Nat.zero_max,Value.length,if_pos live,dif_pos live,dif_pos inside,dif_neg (Nat.not_lt_zero i.val),
        Option.bind_some,Option.map_some]
      cases current : slots ⟨i.val,inside⟩ with
      | absent => rfl
      | present value => cases value; rfl
    · simp only [Value.strip,Value.dflt,Value.defaultBelow,Value.overlay,
        PrimitivePop.elementQuery,Query.read,Value.observe,Value.find,TypeGraph.Path.read,Step.get,
        Nat.zero_max,Value.length,if_neg live,dif_neg live,Option.bind_none,Option.map_none]

/-- Copying into a logically fresh/default child can establish selected
OUTPUT representation even when its unobserved old raw header is nonzero.
No initial default-child relation or zero header is inferred/assumed. ALL
actual extra physical writes remain covered and transported explicitly. This
is selected output evidence, not a full physical fresh-default frame theorem. -/
theorem strip_postowner {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (source : Value G (.array (.prim p))) (indices : List Index)
    (dst src : Solidity.Storage.Loc) (store : Store) (numeric : WordStore)
    (beforeSource : Represented source (PrimitivePop.queries indices) src store)
    (initial : Transport N hash locations store numeric)
    (dstHeader : dst ∈ locations) (srcHeader : src ∈ locations)
    (dstCovered : ∀ i ∈ indices, Solidity.Storage.Loc.data dst i.val ∈ locations)
    (srcCovered : ∀ i ∈ indices, Solidity.Storage.Loc.data src i.val ∈ locations)
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
  · have sourceMember : PrimitivePop.elementQuery (G := G) (p := p) i ∈ PrimitivePop.queries indices :=
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,inside,rfl⟩)
    have old := beforeSource (PrimitivePop.elementQuery i) sourceMember
    refine ⟨old.1,True.intro,?_⟩
    intro word observed
    by_cases live : i.val < source.length.val
    · have sourceRead := observed
      rw [strip_element,if_pos live] at sourceRead
      have actual := NumericTraversal.copy_element run dst src numeric i.val dstHeader (dstCovered i inside)
        (by simpa only [sourceLength,oldLength] using visitedCovered)
      dsimp only at actual
      rw [sourceLength,oldLength,if_pos (show i.val < max (store dst).val.toNat source.length.val from Nat.lt_of_lt_of_le live (Nat.le_max_right _ _)),if_pos live] at actual
      have sourceValue := old.2.2 word sourceRead
      rw [PrimitivePop.element_location] at sourceValue
      have value : numeric ((Solidity.Storage.Loc.data src i.val).word N hash) = word :=
        (initial _ (srcCovered i inside)).trans sourceValue
      rw [PrimitivePop.element_location]
      exact (transported _ (dstCovered i inside)).symm.trans (actual.trans value)
    · rw [strip_element,if_neg live] at observed
      cases observed

/-- The selected fresh/default copied-OUTPUT relation composes with ACTUAL
current-header instructions and numeric transport without an initial default
header premise. Extra raw physical clearing remains explicit, not framed away. -/
theorem strip_complete {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (source : Value G (.array (.prim p))) (indices : List Index)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (tail : List Evm.Word)
    (beforeSource : Represented source (PrimitivePop.queries indices) src store)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (dstHeader : dst ∈ locations) (srcHeader : src ∈ locations)
    (dstCovered : ∀ i ∈ indices, Solidity.Storage.Loc.data dst i.val ∈ locations)
    (srcCovered : ∀ i ∈ indices, Solidity.Storage.Loc.data src i.val ∈ locations)
    (sourceCovered : ∀ j < source.length.val, Solidity.Storage.Loc.data src j ∈ locations)
    (visitedCovered : ∀ j < max (store dst).val.toNat source.length.val, Solidity.Storage.Loc.data dst j ∈ locations) :
    Evm.run TargetArrayCopy.code { target with stack := .slot (TargetOperations.toSlot src srcFits) :: .slot (TargetOperations.toSlot dst dstFits) :: tail } =
      .ok (TargetArrayCopyTail.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)) 0 ∧
    Represented source.strip (PrimitivePop.queries indices) dst (CopyTransport.symbolicCopy dst src store) ∧
    Transport N hash locations (CopyTransport.symbolicCopy dst src store) (NumericTraversal.copy N hash dst src numeric) ∧
    (∀ l (member : l ∈ locations), (TargetArrayCopyTail.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store.cells
      (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (CopyTransport.symbolicCopy dst src store l)) := by
  have output := strip_postowner run source indices dst src store numeric beforeSource initial dstHeader srcHeader
    dstCovered srcCovered sourceCovered visitedCovered
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

def childPath {n : Nat} {G : Schema n} {p : PrimTy} (i : Index) :
    TypeGraph.Path G (.array (.array (.prim p))) (.array (.prim p)) := .cons (.index i) .nil

def child {n : Nat} {G : Schema n} {p : PrimTy}
    (root : Value G (.array (.array (.prim p)))) (i : Index) : Value G (.array (.prim p)) :=
  (root.find (childPath i)).getD (Value.dflt _)

/-- Retained extent, not live length, governs this logical typed child read. -/
theorem find_child {n : Nat} {G : Schema n} {p : PrimTy}
    (root : Value G (.array (.array (.prim p)))) (i : Index) (inside : i.val < root.extent.val) :
    root.find (childPath i) = some (child root i) := by
  cases root with
  | array extent length bound slots =>
    change i.val < extent.val at inside
    simp only [child,childPath,Value.find,TypeGraph.Path.read,Step.get,dif_pos inside,Option.bind_some,Option.getD_some]

/-- The independent aggregate meaning factors at a live copied child,
including missing destination paths and absent/defaulted source slots. -/
theorem child_overlay_live {n : Nat} {G : Schema n} {p : PrimTy}
    (old source : Value G (.array (.array (.prim p)))) (i : Index) (live : i.val < source.length.val) :
    child (old.overlay source) i = (child old i).overlay (child source i) := by
  cases old with
  | array oe ol oh os =>
    cases source with
    | array ne nl nh ns =>
      change i.val < nl.val at live
      have sourceInside : i.val < ne.val := Nat.lt_of_lt_of_le live nh
      have resultInside : i.val < max oe.val nl.val := Nat.lt_of_lt_of_le live (Nat.le_max_right _ _)
      simp only [child,childPath,Value.overlay,Value.find,TypeGraph.Path.read,Step.get,
        dif_pos resultInside,dif_pos sourceInside,dif_pos live,Option.bind_some,Option.getD_some]
      by_cases oldInside : i.val < oe.val
      · simp only [dif_pos oldInside,Option.bind_some,Option.getD_some]
        exact overlay_slot_default _ _
      · simp only [dif_neg oldInside,Option.bind_none,Option.getD_none]
        exact overlay_slot_default .absent _

/-- Exact successful copied-child readback over the independent graph value. -/
theorem overlay_find_live {n : Nat} {G : Schema n} {p : PrimTy}
    (old source : Value G (.array (.array (.prim p)))) (i : Index) (live : i.val < source.length.val) :
    (old.overlay source).find (childPath i) = some ((child old i).overlay (child source i)) := by
  have inside : i.val < (old.overlay source).extent.val := by
    cases old with
    | array oe ol oh os =>
      cases source with
      | array ne nl nh ns =>
        change i.val < max oe.val nl.val
        change i.val < nl.val at live
        exact Nat.lt_of_lt_of_le live (Nat.le_max_right _ _)
  rw [find_child _ _ inside,child_overlay_live old source i live]

/-- A parent default/fresh overlay yields a STRIPPED child at every new live
position. This is a graph fact; it does not turn the old missing raw header zero. -/
theorem strip_child {n : Nat} {G : Schema n} {p : PrimTy}
    (source : Value G (.array (.array (.prim p)))) (i : Index) (live : i.val < source.length.val) :
    source.strip.find (childPath i) = some ((child source i).strip) := by
  have observed := overlay_find_live (Value.dflt _) source i live
  simpa only [Value.strip,child,childPath,Value.dflt,Value.defaultBelow,Value.find,TypeGraph.Path.read,Step.get,
    dif_neg (Nat.not_lt_zero i.val),Option.bind_none,Option.getD_none] using observed

/-- info: 'Solidity.Backend.StorageOps.NestedCopyObservations.strip_element' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms strip_element
/-- info: 'Solidity.Backend.StorageOps.NestedCopyObservations.strip_postowner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms strip_postowner
/-- info: 'Solidity.Backend.StorageOps.NestedCopyObservations.strip_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms strip_complete
/-- info: 'Solidity.Backend.StorageOps.NestedCopyObservations.childPath' does not depend on any axioms -/
#guard_msgs in #print axioms childPath
/-- info: 'Solidity.Backend.StorageOps.NestedCopyObservations.child' does not depend on any axioms -/
#guard_msgs in #print axioms child
/-- info: 'Solidity.Backend.StorageOps.NestedCopyObservations.find_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms find_child
/-- info: 'Solidity.Backend.StorageOps.NestedCopyObservations.child_overlay_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms child_overlay_live
/-- info: 'Solidity.Backend.StorageOps.NestedCopyObservations.overlay_find_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms overlay_find_live
/-- info: 'Solidity.Backend.StorageOps.NestedCopyObservations.strip_child' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms strip_child

end Solidity.Backend.StorageOps.NestedCopyObservations
