import Solidity.Backend.StorageOps.AbsentRootQueries

/-! Uniform existing typed finite ROOT query families, including failed outer
paths. Only PUBLIC support is required for outside-result logical observations;
no physical coverage/default/frame is inferred there. Every actual generated
access and successful-family transport retains its checked operation premises.
No selected-result bound, Source admission cap, new AST/state or postowner input. -/
namespace Solidity.Backend.StorageOps.FiniteRootComposition
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

theorem root {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (old source : Value G (.array (.array (.prim p)))) (children : List Index) (indices : Index → List Index)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (tail : List Evm.Word)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (oldHeader : Represented old [.length .nil] dst store)
    (beforeDst : ∀ i ∈ children, i.val < old.extent.val → i.val < source.length.val →
      Represented old ((PrimitivePop.queries (indices i)).map (Query.prefix (NestedCopyObservations.childPath i))) dst store)
    (sourceHeader : Represented source [.length .nil] src store)
    (beforeSrc : ∀ i ∈ children, i.val < source.length.val →
      Represented source ((CopyAccess.readQueries (NestedCopyObservations.child source i) (indices i)).map
        (Query.prefix (NestedCopyObservations.childPath i))) src store)
    (beforeStale : ∀ i ∈ children, source.length.val ≤ i.val → i.val < old.length.val →
      Represented old ((TargetClearRepresentation.oldQueries (NestedCopyObservations.child old i) (indices i)).map
        (Query.prefix (NestedCopyObservations.childPath i))) dst store)
    (beforeOlder : ∀ i ∈ children, i.val < old.extent.val → source.length.val ≤ i.val → old.length.val ≤ i.val →
      Represented old ((PrimitivePop.queries (indices i)).map (Query.prefix (NestedCopyObservations.childPath i))) dst store)
    (dstHeader : dst ∈ locations) (srcHeader : src ∈ locations)
    (headers : ∀ k < source.length.val, Solidity.Storage.Loc.data dst k ∈ locations ∧ Solidity.Storage.Loc.data src k ∈ locations)
    (reads : ∀ k < source.length.val, ∀ j < ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data src k) j ∈ locations)
    (writes : ∀ k < source.length.val, ∀ j < max ((TargetNestedArrayTransport.copyStores store dst src k) (.data dst k)).val.toNat
        ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    (clearHeaders : ∀ k < max source.length.val (store dst).val.toNat, source.length.val ≤ k → Solidity.Storage.Loc.data dst k ∈ locations)
    (clearWrites : ∀ k < max source.length.val (store dst).val.toNat, source.length.val ≤ k →
      ∀ j < ((TargetNestedArrayTransport.clearStores
        (TargetNestedArrayTransport.copyStores store dst src source.length.val) dst source.length.val k) (.data dst k)).val.toNat,
        Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    (dstCovered : ∀ i ∈ children, i.val < max old.extent.val source.length.val → ∀ j ∈ indices i, Solidity.Storage.Loc.data (.data dst i.val) j.val ∈ locations)
    (sourceCovered : ∀ i ∈ children, i.val < source.length.val → ∀ j < (NestedCopyObservations.child source i).length.val,
      Solidity.Storage.Loc.data (.data src i.val) j ∈ locations)
    (visitedCovered : ∀ i ∈ children, i.val < old.extent.val → i.val < source.length.val → ∀ j < max (NestedCopyObservations.child old i).length.val (NestedCopyObservations.child source i).length.val,
      Solidity.Storage.Loc.data (.data dst i.val) j ∈ locations)
    (childHeader : ∀ i ∈ children, i.val < max old.extent.val source.length.val → Solidity.Storage.Loc.data dst i.val ∈ locations)
    (freshCovered : ∀ i ∈ children, i.val < max old.extent.val source.length.val → old.extent.val ≤ i.val →
      ∀ j < max ((TargetNestedArrayTransport.copyStores store dst src i.val) (.data dst i.val)).val.toNat
          (NestedCopyObservations.child source i).length.val,
        Solidity.Storage.Loc.data (.data dst i.val) j ∈ locations)
    (freshSupported : ∀ i ∈ children, i.val < max old.extent.val source.length.val → old.extent.val ≤ i.val →
      ∀ q ∈ PrimitivePop.queries (G := G) (p := p) (indices i), q.supported)
    (outsideSupported : ∀ i ∈ children, max old.extent.val source.length.val ≤ i.val →
      ∀ q ∈ PrimitivePop.queries (G := G) (p := p) (indices i),
        (q.prefix (NestedCopyObservations.childPath i)).supported)
    (dstApart : ∀ i ∈ children, i.val < old.extent.val → i.val < source.length.val → ∀ q ∈ PrimitivePop.queries (G := G) (p := p) (indices i),
      TargetOperations.toSlot (q.location (.data dst i.val)) (TargetOperations.query_keysFit q (.data dst i.val) dstFits) ∉
      TargetNestedArrayCopyLoop.touched target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) i.val)
    (srcApart : ∀ i ∈ children, i.val < source.length.val → ∀ q ∈ CopyAccess.readQueries (NestedCopyObservations.child source i) (indices i),
      TargetOperations.toSlot (q.location (.data src i.val)) (TargetOperations.query_keysFit q (.data src i.val) srcFits) ∉
      TargetNestedArrayCopyLoop.touched target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) i.val) :
    Evm.run TargetNestedArrayCopy.code { target with stack := .slot (TargetOperations.toSlot src srcFits) :: .slot (TargetOperations.toSlot dst dstFits) :: tail } =
      .ok (TargetNestedArrayRuntime.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)) 0 ∧
    Represented (old.overlay source) (NestedRootComposition.rootQueries children indices) dst (TargetNestedArrayTransport.afterStore store dst src) ∧
    Transport N hash locations (TargetNestedArrayTransport.afterStore store dst src) (TargetNestedArrayTransport.execute N hash numeric dst src) ∧
    (∀ l (member : l ∈ locations),
      (TargetNestedArrayRuntime.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store.cells
        (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore store dst src l)) := by
  have captured : store src = lengthWord source.length.val source.length.isLt :=
    (sourceHeader (.length .nil) List.mem_cons_self).2.2 _ (by cases source; rfl)
  have countKnown : (store src).val.toNat = source.length.val := by rw [captured]; rfl
  have finished : ∀ i ∈ children,
      Represented (old.overlay source) ((PrimitivePop.queries (indices i)).map (Query.prefix (NestedCopyObservations.childPath i))) dst
        (TargetNestedArrayTransport.afterStore store dst src) := by
    intro i member
    by_cases inside : i.val < max old.extent.val source.length.val
    · have actual := OutputRootComposition.root run old source [i] indices
        (by intro j single; have same := List.mem_singleton.mp single; subst j; exact inside)
        dst src dstFits srcFits store numeric target tail initial fitting targetInitial oldHeader
        (by intro j single; have same := List.mem_singleton.mp single; subst j; exact beforeDst i member)
        sourceHeader
        (by intro j single; have same := List.mem_singleton.mp single; subst j; exact beforeSrc i member)
        (by intro j single; have same := List.mem_singleton.mp single; subst j; exact beforeStale i member)
        (by
          intro j single pastNew pastOld
          have same := List.mem_singleton.mp single
          subst j
          have oldInside : i.val < old.extent.val := by omega
          exact beforeOlder i member oldInside pastNew pastOld)
        dstHeader srcHeader headers reads writes clearHeaders clearWrites
        (by intro j single; have same := List.mem_singleton.mp single; subst j; exact dstCovered i member inside)
        (by intro j single; have same := List.mem_singleton.mp single; subst j; exact sourceCovered i member)
        (by intro j single; have same := List.mem_singleton.mp single; subst j; exact visitedCovered i member)
        (by intro j single; have same := List.mem_singleton.mp single; subst j; exact childHeader i member inside)
        (by intro j single; have same := List.mem_singleton.mp single; subst j; exact freshCovered i member inside)
        (by intro j single; have same := List.mem_singleton.mp single; subst j; exact freshSupported i member inside)
        (by intro j single; have same := List.mem_singleton.mp single; subst j; exact dstApart i member)
        (by intro j single; have same := List.mem_singleton.mp single; subst j; exact srcApart i member)
      intro q observation
      exact actual.2.1 q (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨i,List.mem_cons_self,observation⟩))
    · have outside : max old.extent.val source.length.val ≤ i.val := Nat.le_of_not_gt inside
      exact AbsentRootQueries.represented_missing old source i (PrimitivePop.queries (indices i)) outside
        (outsideSupported i member outside) dst _
  have owner : Represented (old.overlay source) (NestedRootComposition.rootQueries children indices) dst (TargetNestedArrayTransport.afterStore store dst src) := by
    intro q member
    simp only [NestedRootComposition.rootQueries,List.mem_cons,List.mem_flatMap] at member
    rcases member with rfl | ⟨i,inside,observation⟩
    · exact NestedRootComposition.root_header old source dst src store oldHeader sourceHeader _ List.mem_cons_self
    · exact finished i inside q observation
  have actual := TargetNestedArrayTransport.complete run dst src dstFits srcFits store numeric target tail initial fitting targetInitial
    dstHeader srcHeader (by simpa only [countKnown] using headers) (by simpa only [countKnown] using reads)
    (by simpa only [countKnown] using writes) (by simpa only [countKnown] using clearHeaders)
    (by simpa only [countKnown] using clearWrites)
  exact ⟨actual.1,owner,actual.2⟩

/-- info: 'Solidity.Backend.StorageOps.FiniteRootComposition.root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms root
end Solidity.Backend.StorageOps.FiniteRootComposition
