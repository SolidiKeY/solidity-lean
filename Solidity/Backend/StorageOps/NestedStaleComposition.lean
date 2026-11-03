import Solidity.Backend.StorageOps.LaterClearFrames
import Solidity.Backend.StorageOps.NestedRootComposition

/-! Stale and older child observations of the independent overlay, plus
operation-side transport of the CURRENT owner through actual runtime phases. -/
namespace Solidity.Backend.StorageOps.NestedStaleComposition
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- A shortened former-live child is cleared, including absent/defaulted
slots and arbitrary intrinsic endpoint types. Retained extents are preserved. -/
theorem find_stale {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old source : Value G (.array E)) (i : Index)
    (stale : source.length.val ≤ i.val) (oldLive : i.val < old.length.val) :
    (old.overlay source).find (.cons (.index i) .nil) =
      some (((old.find (.cons (.index i) .nil)).getD (Value.dflt E)).clear) := by
  cases old with
  | array oe ol oh os =>
    cases source with
    | array ne nl nh ns =>
      change nl.val ≤ i.val at stale
      change i.val < ol.val at oldLive
      have inside : i.val < oe.val := Nat.lt_of_lt_of_le oldLive oh
      have resultInside : i.val < max oe.val nl.val := Nat.lt_of_lt_of_le inside (Nat.le_max_left _ _)
      simp only [Value.overlay,Value.find,TypeGraph.Path.read,Step.get,dif_pos resultInside,
        dif_pos inside,dif_neg (Nat.not_lt_of_ge stale),if_pos oldLive,Option.bind_some,Option.getD_some]
      exact congrArg some (clear_slot_default (os ⟨i.val,inside⟩))

/-- Older retained children are unchanged; outside retained extent the exact
failed Option read stays failed. No raw/default/frame fact follows from None. -/
theorem find_older {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old source : Value G (.array E)) (i : Index)
    (pastNew : source.length.val ≤ i.val) (pastOld : old.length.val ≤ i.val) :
    (old.overlay source).find (.cons (.index i) .nil) = old.find (.cons (.index i) .nil) := by
  cases old with
  | array oe ol oh os =>
    cases source with
    | array ne nl nh ns =>
      change nl.val ≤ i.val at pastNew
      change ol.val ≤ i.val at pastOld
      by_cases inside : i.val < oe.val
      · have resultInside : i.val < max oe.val nl.val := Nat.lt_of_lt_of_le inside (Nat.le_max_left _ _)
        simp only [Value.overlay,Value.find,TypeGraph.Path.read,Step.get,dif_pos resultInside,dif_pos inside,
          dif_neg (Nat.not_lt_of_ge pastNew),if_neg (Nat.not_lt_of_ge pastOld),Option.bind_some]
      · have resultOutside : ¬ i.val < max oe.val nl.val := by omega
        simp only [Value.overlay,Value.find,TypeGraph.Path.read,Step.get,dif_neg resultOutside,dif_neg inside,Option.bind_none]

/-- Actual copy turns only write earlier destination children. The symbolic
frame follows from original finite-run transport and current target agreement. -/
theorem unvisited_word {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (count outer : Nat)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (headers : ∀ k < count, Solidity.Storage.Loc.data dst k ∈ locations ∧ Solidity.Storage.Loc.data src k ∈ locations)
    (reads : ∀ k < count, ∀ j < ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data src k) j ∈ locations)
    (writes : ∀ k < count, ∀ j < max ((TargetNestedArrayTransport.copyStores store dst src k) (.data dst k)).val.toNat
        ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    (future : count ≤ outer) (observer : Solidity.Storage.Loc) (covered : observer ∈ locations)
    (kind : observer = .data dst outer ∨ ∃ inner, observer = .data (.data dst outer) inner) :
    TargetNestedArrayTransport.copyStores store dst src count observer = store observer := by
  have agreement := (TargetNestedArrayTransport.copy_prefix run dst src dstFits srcFits store numeric target count initial fitting targetInitial headers reads writes).2 observer covered
  have framed : (TargetNestedArrayCopyLoop.prefixMachine target (TargetOperations.toSlot src srcFits)
      (TargetOperations.toSlot dst dstFits) count).store (TargetOperations.toSlot observer (fitting observer covered)) =
      target.store (TargetOperations.toSlot observer (fitting observer covered)) := by
    have actual := TargetNestedArrayCopyLoop.unvisited_child target (TargetOperations.toSlot src srcFits)
      (TargetOperations.toSlot dst dstFits) count outer future
    rcases kind with rfl | ⟨inner,rfl⟩
    · exact actual.1
    · exact actual.2 inner
  have equal : TargetOperations.encodeWord (TargetNestedArrayTransport.copyStores store dst src count observer) =
      TargetOperations.encodeWord (store observer) := by
    apply Fin.ext
    exact (congrArg Fin.val agreement).symm.trans (framed.trans (congrArg Fin.val (targetInitial observer covered)))
  exact keyWord_inj (p := .uint) (congrArg Fin.val equal)

/-- OLD child observations at an unvisited destination survive ALL actual
copy turns; source aliases require no extra input preservation assumption here. -/
theorem unvisited_owner {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (count outer : Nat)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (headers : ∀ k < count, Solidity.Storage.Loc.data dst k ∈ locations ∧ Solidity.Storage.Loc.data src k ∈ locations)
    (reads : ∀ k < count, ∀ j < ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data src k) j ∈ locations)
    (writes : ∀ k < count, ∀ j < max ((TargetNestedArrayTransport.copyStores store dst src k) (.data dst k)).val.toNat
        ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    {n : Nat} {G : Schema n} {p : PrimTy} (child : Value G (.array (.prim p)))
    (indices : List Index) (future : count ≤ outer)
    (before : Represented child (PrimitivePop.queries indices) (.data dst outer) store)
    (covered : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, q.location (.data dst outer) ∈ locations) :
    Represented child (PrimitivePop.queries indices) (.data dst outer)
      (TargetNestedArrayTransport.copyStores store dst src count) := by
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
  rw [unvisited_word run dst src dstFits srcFits store numeric target count outer initial fitting targetInitial headers reads writes
    future (q.location (.data dst outer)) (covered q member) kind]
  exact observed word found

/-- A derived stale child owner survives all remaining clears and the final
root header. Current middle transport/target agreements are not premises. -/
theorem finish_cleared_child {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (tail : List Evm.Word)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (dstHeader : dst ∈ locations) (srcHeader : src ∈ locations)
    (copyHeaders : ∀ k < (store src).val.toNat, Solidity.Storage.Loc.data dst k ∈ locations ∧ Solidity.Storage.Loc.data src k ∈ locations)
    (copyReads : ∀ k < (store src).val.toNat, ∀ j < ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data src k) j ∈ locations)
    (copyWrites : ∀ k < (store src).val.toNat, ∀ j < max ((TargetNestedArrayTransport.copyStores store dst src k) (.data dst k)).val.toNat
        ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat, Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    (clearHeaders : ∀ k < max (store src).val.toNat (store dst).val.toNat, (store src).val.toNat ≤ k → Solidity.Storage.Loc.data dst k ∈ locations)
    (clearWrites : ∀ k < max (store src).val.toNat (store dst).val.toNat, (store src).val.toNat ≤ k →
      ∀ j < ((TargetNestedArrayTransport.clearStores (TargetNestedArrayTransport.copyStores store dst src (store src).val.toNat) dst (store src).val.toNat k) (.data dst k)).val.toNat,
        Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    {n : Nat} {G : Schema n} {p : PrimTy} (child : Value G (.array (.prim p))) (indices : List Index)
    (first outer : Nat) (earlier : outer < first) (within : first ≤ max (store src).val.toNat (store dst).val.toNat)
    (before : Represented child (PrimitivePop.queries indices) (.data dst outer)
      (TargetNestedArrayTransport.clearStores (TargetNestedArrayTransport.copyStores store dst src (store src).val.toNat) dst (store src).val.toNat first))
    (covered : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, q.location (.data dst outer) ∈ locations) :
    Evm.run TargetNestedArrayCopy.code { target with stack := .slot (TargetOperations.toSlot src srcFits) :: .slot (TargetOperations.toSlot dst dstFits) :: tail } =
      .ok (TargetNestedArrayRuntime.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)) 0 ∧
    Represented child (PrimitivePop.queries indices) (.data dst outer) (TargetNestedArrayTransport.afterStore store dst src) ∧
    Transport N hash locations (TargetNestedArrayTransport.afterStore store dst src) (TargetNestedArrayTransport.execute N hash numeric dst src) ∧
    (∀ l (member : l ∈ locations),
      (TargetNestedArrayRuntime.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store.cells
        (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore store dst src l)) := by
  have total : first+(max (store src).val.toNat (store dst).val.toNat-first) = max (store src).val.toNat (store dst).val.toNat := by omega
  have copied := TargetNestedArrayTransport.copy_prefix run dst src dstFits srcFits store numeric target (store src).val.toNat initial fitting targetInitial copyHeaders copyReads copyWrites
  have later := LaterClearFrames.owner_interval run dst dstFits
    (TargetNestedArrayTransport.copyStores store dst src (store src).val.toNat)
    (TargetNestedArrayTransport.copyNumerics N hash numeric dst src (store src).val.toNat)
    (TargetNestedArrayCopyLoop.prefixMachine target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) (store src).val.toNat)
    (store src).val.toNat first (max (store src).val.toNat (store dst).val.toNat-first) outer copied.1 fitting copied.2
    (by simpa only [total] using clearHeaders) (by simpa only [total] using clearWrites) child indices earlier before covered
  have cleared : Represented child (PrimitivePop.queries indices) (.data dst outer)
      (TargetNestedArrayTransport.clearStores (TargetNestedArrayTransport.copyStores store dst src (store src).val.toNat)
        dst (store src).val.toNat (max (store src).val.toNat (store dst).val.toNat)) := by
    simpa only [total] using later
  have owner : Represented child (PrimitivePop.queries indices) (.data dst outer) (TargetNestedArrayTransport.afterStore store dst src) :=
    NestedClearFrames.header_child_owner child indices dst outer _ (store src) cleared
  have actual := TargetNestedArrayTransport.complete run dst src dstFits srcFits store numeric target tail initial fitting targetInitial
    dstHeader srcHeader copyHeaders copyReads copyWrites clearHeaders clearWrites
  exact ⟨actual.1,owner,actual.2⟩

/-- Full actual runtime stale-child ROOT transport derived from OLD root
header/retained observations only. No current owner, zero header, source child
relation or desired final preservation theorem is an input. -/
theorem stale_child {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (old source : Value G (.array (.array (.prim p)))) (i : Index) (indices : List Index)
    (stale : source.length.val ≤ i.val) (oldLive : i.val < old.length.val)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (tail : List Evm.Word)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (beforeDst : Represented old
      ((TargetClearRepresentation.oldQueries (NestedCopyObservations.child old i) indices).map (Query.prefix (NestedCopyObservations.childPath i))) dst store)
    (oldHeaderOwner : Represented old [.length .nil] dst store)
    (sourceHeaderOwner : Represented source [.length .nil] src store)
    (dstHeader : dst ∈ locations) (srcHeader : src ∈ locations)
    (copyHeaders : ∀ k < (store src).val.toNat, Solidity.Storage.Loc.data dst k ∈ locations ∧ Solidity.Storage.Loc.data src k ∈ locations)
    (copyReads : ∀ k < (store src).val.toNat, ∀ j < ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data src k) j ∈ locations)
    (copyWrites : ∀ k < (store src).val.toNat, ∀ j < max ((TargetNestedArrayTransport.copyStores store dst src k) (.data dst k)).val.toNat
        ((TargetNestedArrayTransport.copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    (clearHeaders : ∀ k < max (store src).val.toNat (store dst).val.toNat, (store src).val.toNat ≤ k → Solidity.Storage.Loc.data dst k ∈ locations)
    (clearWrites : ∀ k < max (store src).val.toNat (store dst).val.toNat, (store src).val.toNat ≤ k →
      ∀ j < ((TargetNestedArrayTransport.clearStores (TargetNestedArrayTransport.copyStores store dst src (store src).val.toNat)
        dst (store src).val.toNat k) (.data dst k)).val.toNat,
        Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    (covered : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, q.location (.data dst i.val) ∈ locations) :
    Evm.run TargetNestedArrayCopy.code { target with stack := .slot (TargetOperations.toSlot src srcFits) :: .slot (TargetOperations.toSlot dst dstFits) :: tail } =
      .ok (TargetNestedArrayRuntime.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)) 0 ∧
    Represented (old.overlay source) ((PrimitivePop.queries indices).map (Query.prefix (NestedCopyObservations.childPath i))) dst
      (TargetNestedArrayTransport.afterStore store dst src) ∧
    Transport N hash locations (TargetNestedArrayTransport.afterStore store dst src) (TargetNestedArrayTransport.execute N hash numeric dst src) ∧
    (∀ l (member : l ∈ locations),
      (TargetNestedArrayRuntime.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store.cells
        (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (TargetNestedArrayTransport.afterStore store dst src l)) := by
  have oldInside : i.val < old.extent.val := Nat.lt_of_lt_of_le oldLive (by cases old; assumption)
  have oldCount : (store dst).val.toNat = old.length.val := by
    have known : store dst = lengthWord old.length.val old.length.isLt :=
      (oldHeaderOwner (.length .nil) List.mem_cons_self).2.2 _ (by cases old; rfl)
    rw [known]; rfl
  have newCount : (store src).val.toNat = source.length.val := by
    have known : store src = lengthWord source.length.val source.length.isLt :=
      (sourceHeaderOwner (.length .nil) List.mem_cons_self).2.2 _ (by cases source; rfl)
    rw [known]; rfl
  have active : (store src).val.toNat ≤ i.val := by rw [newCount]; exact stale
  have within : i.val+1 ≤ max (store src).val.toNat (store dst).val.toNat := by rw [oldCount,newCount]; omega
  have oldChild : Represented (NestedCopyObservations.child old i)
      (TargetClearRepresentation.oldQueries (NestedCopyObservations.child old i) indices) (.data dst i.val) store := by
    simpa only [NestedRetainedCopy.child_location] using
      PathRepresentation.focus old _ _ (NestedCopyObservations.find_child old i oldInside) _ dst store beforeDst
  have oldCovered : ∀ q ∈ TargetClearRepresentation.oldQueries (NestedCopyObservations.child old i) indices,
      q.location (.data dst i.val) ∈ locations := by
    intro q member
    apply covered q
    simp only [TargetClearRepresentation.oldQueries,PrimitivePop.queries,List.mem_cons,List.mem_map] at member
    rcases member with rfl | ⟨j,filtered,rfl⟩
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j,(List.mem_filter.mp filtered).1,rfl⟩)
  have copied := TargetNestedArrayTransport.copy_prefix run dst src dstFits srcFits store numeric target (store src).val.toNat
    initial fitting targetInitial copyHeaders copyReads copyWrites
  have afterCopies := unvisited_owner run dst src dstFits srcFits store numeric target (store src).val.toNat i.val
    initial fitting targetInitial copyHeaders copyReads copyWrites (NestedCopyObservations.child old i)
    (indices.filter (fun j => decide ((NestedCopyObservations.child old i).length.val ≤ j.val))) active oldChild oldCovered
  have beforeClear := NestedClearFrames.clear_child_owner run dst dstFits
    (TargetNestedArrayTransport.copyStores store dst src (store src).val.toNat)
    (TargetNestedArrayTransport.copyNumerics N hash numeric dst src (store src).val.toNat)
    (TargetNestedArrayCopyLoop.prefixMachine target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) (store src).val.toNat)
    (store src).val.toNat i.val copied.1 fitting copied.2
    (fun k inside => clearHeaders k (by omega)) (fun k inside => clearWrites k (by omega))
    (NestedCopyObservations.child old i) (indices.filter (fun j => decide ((NestedCopyObservations.child old i).length.val ≤ j.val)))
    i.val (Or.inr (Nat.le_refl _)) afterCopies oldCovered
  have currentLength : ((TargetNestedArrayTransport.clearStores
      (TargetNestedArrayTransport.copyStores store dst src (store src).val.toNat) dst (store src).val.toNat i.val) (.data dst i.val)).val.toNat =
      (NestedCopyObservations.child old i).length.val := by
    have known : (TargetNestedArrayTransport.clearStores
        (TargetNestedArrayTransport.copyStores store dst src (store src).val.toNat) dst (store src).val.toNat i.val) (.data dst i.val) =
        lengthWord (NestedCopyObservations.child old i).length.val (NestedCopyObservations.child old i).length.isLt :=
      (beforeClear (.length .nil) List.mem_cons_self).2.2 _ (by cases NestedCopyObservations.child old i; rfl)
    rw [known]; rfl
  have clearedOwner := TargetClearRepresentation.represented_spec (NestedCopyObservations.child old i) indices (.data dst i.val)
    (TargetNestedArrayTransport.clearStores (TargetNestedArrayTransport.copyStores store dst src (store src).val.toNat) dst (store src).val.toNat i.val)
    beforeClear
  have firstOwner : Represented (NestedCopyObservations.child old i).clear (PrimitivePop.queries indices) (.data dst i.val)
      (TargetNestedArrayTransport.clearStores (TargetNestedArrayTransport.copyStores store dst src (store src).val.toNat) dst (store src).val.toNat (i.val+1)) := by
    rw [TargetNestedArrayTransport.clearStores,if_pos active]
    simpa only [TargetNestedArrayTransport.clearStore,TargetClearRepresentation.afterStore,currentLength] using clearedOwner
  have finished := finish_cleared_child run dst src dstFits srcFits store numeric target tail initial fitting targetInitial
    dstHeader srcHeader copyHeaders copyReads copyWrites clearHeaders clearWrites
    (NestedCopyObservations.child old i).clear indices (i.val+1) i.val (by omega) within firstOwner covered
  have supported : PathSupported (NestedCopyObservations.childPath (G := G) (p := p) i) :=
    ((Query.supported_prefix _ (.length .nil)).mp
      (beforeDst _ (List.mem_map.mpr ⟨_,List.mem_cons_self,rfl⟩)).1).1
  have found : (old.overlay source).find (NestedCopyObservations.childPath i) = some (NestedCopyObservations.child old i).clear := by
    simpa only [NestedCopyObservations.child,NestedCopyObservations.childPath] using find_stale old source i stale oldLive
  have leaf : Represented (NestedCopyObservations.child old i).clear (PrimitivePop.queries indices)
      (pathLoc (NestedCopyObservations.childPath (G := G) (p := p) i) dst) (TargetNestedArrayTransport.afterStore store dst src) := by
    simpa only [NestedRetainedCopy.child_location] using finished.2.1
  exact ⟨finished.1,Represented.prefix _ found supported leaf,finished.2.2⟩

/-- info: 'Solidity.Backend.StorageOps.NestedStaleComposition.stale_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms stale_child

/-- info: 'Solidity.Backend.StorageOps.NestedStaleComposition.finish_cleared_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms finish_cleared_child

/-- info: 'Solidity.Backend.StorageOps.NestedStaleComposition.find_stale' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms find_stale

/-- info: 'Solidity.Backend.StorageOps.NestedStaleComposition.find_older' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms find_older

/-- info: 'Solidity.Backend.StorageOps.NestedStaleComposition.unvisited_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms unvisited_word

/-- info: 'Solidity.Backend.StorageOps.NestedStaleComposition.unvisited_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms unvisited_owner
end Solidity.Backend.StorageOps.NestedStaleComposition
