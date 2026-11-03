import Solidity.Backend.StorageOps.TargetCopyRead

/-! Actual copy followed by a guarded runtime indexed write. Index and value
are input stack operands preserved through the copy, never compiled results. -/
namespace Solidity.Backend.StorageOps.TargetCopyWrite
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def code (dst : Evm.Slot) : List Evm.Instr :=
  TargetArrayCopy.code ++ (TargetCopyRead.operands dst ++ TargetArrayWrite.code)

/-- Existing current-numeric copy and a CURRENT copied-header write guard. -/
def execute (N : Nat) (hash : Solidity.Storage.Pre → Nat) (dst src : Solidity.Storage.Loc)
    (numeric : WordStore) (i : Index) (word : Semantics.Word) : Option WordStore :=
  let copied := NumericTraversal.copy N hash dst src numeric
  if i.val < LifecycleNumeric.headerLength N hash dst copied then
    some (writeWord copied ((Solidity.Storage.Loc.data dst i.val).word N hash) word) else none

/-- BOTH actual outcomes use the copied current header. Success consumes the
runtime index/value, updates exactly one child and restores the original tail. -/
theorem run_current (target : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (i : Index) (value : Fin Evm.W) :
    let copied := TargetArrayCopyTail.afterCopy target (.val ⟨i.val,i.isLt⟩ :: .val value :: tail) src dst
    Evm.run (code dst) { target with stack := .slot src :: .slot dst :: .val ⟨i.val,i.isLt⟩ :: .val value :: tail } =
      if i.val < target.store src then
        .ok { copied with stack := tail, store := Evm.WordStore.write copied.store (.data dst i.val) value.val } 0 else .revert := by
  unfold code
  rw [Evm.run_append_ok (TargetArrayCopyTail.run_current target (.val ⟨i.val,i.isLt⟩ :: .val value :: tail) src dst)]
  rw [Evm.run_append_ok (m' := { TargetArrayCopyTail.afterCopy target (.val ⟨i.val,i.isLt⟩ :: .val value :: tail) src dst with stack := .val ⟨i.val,i.isLt⟩ :: .slot dst :: .val value :: tail }) (by rfl)]
  rw [TargetArrayWrite.run_current,TargetArrayCopyTail.after_header]

/-- Failure follows the executed copy prefix and precedes the scalar write;
this is Evm.Out.revert, not a world rollback assertion. -/
theorem run_failed (target : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (i : Index) (value : Fin Evm.W) (outside : target.store src ≤ i.val) :
    Evm.run (code dst) { target with stack := .slot src :: .slot dst :: .val ⟨i.val,i.isLt⟩ :: .val value :: tail } = .revert := by
  rw [run_current,if_neg (by omega)]

/-- Plain original source-header agreement gives exact intrinsic guarded
live/save failure, including retained raw locations that could still be saved. -/
theorem failure_matches {n : Nat} {G : Schema n} {p : PrimTy}
    (old source : Value G (.array (.prim p))) (i : Index) (value : p.Denote)
    (target : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (header : target.store src = source.length.val) :
    Evm.run (code dst) { target with stack := .slot src :: .slot dst :: .val ⟨i.val,i.isLt⟩ :: .val (TargetOperations.encodeWord (PrimTy.toWord value)) :: tail } = .revert ↔
      TargetArrayWrite.writeAt (old.overlay source) i value = none := by
  have length : (old.overlay source).length.val = source.length.val := by cases old; cases source; rfl
  rw [run_current,header,TargetArrayWrite.failure,length]
  by_cases live : i.val < source.length.val
  · rw [if_pos live]
    constructor
    · intro impossible; cases impossible
    · intro impossible; omega
  · rw [if_neg live]
    exact ⟨fun _ => by omega,fun _ => rfl⟩

/-- The actual numeric guard matches the SAME independent operation outcome;
no finite-region premise is needed merely for header/failure correspondence. -/
theorem numeric_failure_matches {n N : Nat} {G : Schema n} {p : PrimTy}
    (old source : Value G (.array (.prim p))) (i : Index) (value : p.Denote)
    (hash : Solidity.Storage.Pre → Nat) (dst src : Solidity.Storage.Loc) (numeric : WordStore)
    (header : LifecycleNumeric.headerLength N hash src numeric = source.length.val) :
    execute N hash dst src numeric i (PrimTy.toWord value) = none ↔ TargetArrayWrite.writeAt (old.overlay source) i value = none := by
  have current : LifecycleNumeric.headerLength N hash dst (NumericTraversal.copy N hash dst src numeric) = LifecycleNumeric.headerLength N hash src numeric := by
    unfold LifecycleNumeric.headerLength
    rw [NumericTraversal.copy_header]
  have length : (old.overlay source).length.val = source.length.val := by cases old; cases source; rfl
  rw [execute,current,header,TargetArrayWrite.failure,length]
  by_cases live : i.val < source.length.val
  · rw [if_pos live]
    constructor
    · intro impossible; cases impossible
    · intro impossible; omega
  · rw [if_neg live]
    exact ⟨fun _ => by omega,fun _ => rfl⟩


/-- Only an observation list over the EXISTING Query type. The written index
is handled by changed-word preservation, so it is not incorrectly framed. -/
def contextQueries {n : Nat} {G : Schema n} {p : PrimTy} (indices : List Index) (i : Index) :
    List (Query G (.array (.prim p))) :=
  (indices.filter (fun j => decide (j ≠ i))).map PrimitivePop.elementQuery

private theorem context_member {n : Nat} {G : Schema n} {p : PrimTy}
    (indices : List Index) (i : Index) (q : Query G (.array (.prim p)))
    (member : q ∈ contextQueries indices i) : q ∈ PrimitivePop.queries indices := by
  obtain ⟨j,inside,rfl⟩ := List.mem_map.mp member
  exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j,(List.mem_filter.mp inside).1,rfl⟩)

private theorem context_apart {n : Nat} {G : Schema n} {p : PrimTy}
    (indices : List Index) (i : Index) (q : Query G (.array (.prim p)))
    (member : q ∈ contextQueries indices i) : q.apart (TargetArrayRead.path i) := by
  obtain ⟨j,inside,rfl⟩ := List.mem_map.mp member
  have different : j ≠ i := by simpa only [decide_eq_true_eq] using (List.mem_filter.mp inside).2
  exact Apart.fork (.index i j (fun same => different same.symm)) .nil .nil

private theorem context_nonalias {n : Nat} {G : Schema n} {p : PrimTy}
    (indices : List Index) (i : Index) (q : Query G (.array (.prim p)))
    (base : Solidity.Storage.Loc) (member : q ∈ contextQueries indices i) :
    q.location base ≠ pathLoc (TargetArrayRead.path (G := G) (p := p) i) base := by
  obtain ⟨j,inside,rfl⟩ := List.mem_map.mp member
  have different : j ≠ i := by simpa only [decide_eq_true_eq] using (List.mem_filter.mp inside).2
  rw [PrimitivePop.element_location,TargetArrayWrite.location]
  intro same
  exact different (Fin.ext (Solidity.Storage.Loc.data.inj same).2)

/-- Exact original selected postowner after actual copy/write. BOTH original
selected input relations are retained; sibling frames, support and middle
transport/target agreement are derived, never assumed as preservation premises. -/
theorem complete {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (old source result : Value G (.array (.prim p))) (i : Index) (value : p.Denote)
    (performed : TargetArrayWrite.writeAt (old.overlay source) i value = some result)
    (indices : List Index) (written : i ∈ indices)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (tail : List Evm.Word)
    (beforeDst : Represented old (PrimitivePop.queries indices) dst store)
    (beforeSrc : Represented source (PrimitivePop.queries indices) src store)
    (initial : Transport N hash locations store numeric)
    (dstHeader : dst ∈ locations) (srcHeader : src ∈ locations)
    (dstCovered : ∀ j ∈ indices, Solidity.Storage.Loc.data dst j.val ∈ locations)
    (srcCovered : ∀ j ∈ indices, Solidity.Storage.Loc.data src j.val ∈ locations)
    (sourceCovered : ∀ j < source.length.val, Solidity.Storage.Loc.data src j ∈ locations)
    (visitedCovered : ∀ j < max old.length.val source.length.val, Solidity.Storage.Loc.data dst j ∈ locations)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l)) :
    let path := TargetArrayRead.path (G := G) (p := p) i
    let child := pathLoc path dst
    let word := PrimTy.toWord value
    let copiedStore := CopyTransport.symbolicCopy dst src store
    let copiedNumeric := NumericTraversal.copy N hash dst src numeric
    let copiedTarget := TargetArrayCopyTail.afterCopy target (.val ⟨i.val,i.isLt⟩ :: .val (TargetOperations.encodeWord word) :: tail) (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)
    let finalStore := Representation.write copiedStore child word
    let finalNumeric := writeWord copiedNumeric (child.word N hash) word
    let finalTarget := { copiedTarget with stack := tail, store := Evm.WordStore.write copiedTarget.store (TargetOperations.toSlot child (TargetOperations.path_keysFit path dst dstFits)) (TargetOperations.encodeWord word).val }
    execute N hash dst src numeric i word = some finalNumeric ∧
    Evm.run (code (TargetOperations.toSlot dst dstFits)) { target with stack := .slot (TargetOperations.toSlot src srcFits) :: .slot (TargetOperations.toSlot dst dstFits) :: .val ⟨i.val,i.isLt⟩ :: .val (TargetOperations.encodeWord word) :: tail } = .ok finalTarget 0 ∧
    Represented result (PrimitivePop.queries indices) dst finalStore ∧
    Transport N hash locations finalStore finalNumeric ∧
    (∀ l (member : l ∈ locations), finalTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (finalNumeric (l.word N hash))) ∧
    (∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, ∀ observed,
      q.read result = some observed → finalNumeric ((q.location dst).word N hash) = observed) := by
  have copied := TargetCopyRepresentation.complete run old source indices dst src dstFits srcFits store numeric target
    (.val ⟨i.val,i.isLt⟩ :: .val (TargetOperations.encodeWord (PrimTy.toWord value)) :: tail)
    beforeDst beforeSrc initial dstHeader srcHeader dstCovered srcCovered sourceCovered visitedCovered fitting targetInitial
  have middleHeader : Represented (old.overlay source) [.length .nil] dst (CopyTransport.symbolicCopy dst src store) := by
    intro q member
    have same := List.mem_singleton.mp member; subst q
    exact copied.2.1 _ List.mem_cons_self
  have middleContext : Represented (old.overlay source) (contextQueries indices i) dst (CopyTransport.symbolicCopy dst src store) := by
    intro q member; exact copied.2.1 q (context_member indices i q member)
  have supported : PathSupported (TargetArrayRead.path (G := G) (p := p) i) :=
    (copied.2.1 (PrimitivePop.elementQuery i) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,written,rfl⟩))).1
  have childCovered : pathLoc (TargetArrayRead.path (G := G) (p := p) i) dst ∈ locations := by
    rw [TargetArrayWrite.location]; exact dstCovered i written
  have middleAgreement : ∀ l (member : l ∈ locations),
      (TargetArrayCopyTail.afterCopy target (.val ⟨i.val,i.isLt⟩ :: .val (TargetOperations.encodeWord (PrimTy.toWord value)) :: tail) (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store.cells (TargetOperations.toSlot l (fitting l member)) =
        TargetOperations.encodeWord (CopyTransport.symbolicCopy dst src store l) := by
    intro l member
    exact (copied.2.2.2.1 l member).trans (congrArg TargetOperations.encodeWord (copied.2.2.1 l member))
  have component := TargetArrayWrite.complete_numeric run (old.overlay source) result i value performed
    (contextQueries indices i) dst dstFits (CopyTransport.symbolicCopy dst src store) (NumericTraversal.copy N hash dst src numeric)
    (TargetArrayCopyTail.afterCopy target (.val ⟨i.val,i.isLt⟩ :: .val (TargetOperations.encodeWord (PrimTy.toWord value)) :: tail) (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)) tail
    middleHeader middleContext supported (context_apart indices i) (fun q member => context_nonalias indices i q dst member)
    copied.2.2.1 dstHeader childCovered fitting middleAgreement
  have finalOwner : Represented result (PrimitivePop.queries indices) dst
      (Representation.write (CopyTransport.symbolicCopy dst src store) (pathLoc (TargetArrayRead.path (G := G) (p := p) i) dst) (PrimTy.toWord value)) := by
    intro q member
    simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
    rcases member with rfl | ⟨j,inside,rfl⟩
    · exact component.2.1 _ List.mem_cons_self
    · by_cases same : j = i
      · subst j; exact component.2.1 _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · apply component.2.1
        apply List.mem_cons_of_mem
        apply List.mem_cons_of_mem
        exact List.mem_map.mpr ⟨j,List.mem_filter.mpr ⟨inside,by simpa only [decide_eq_true_eq] using same⟩,rfl⟩
  have headerWord := LifecycleNumeric.array_header_numeric (old.overlay source) dst (CopyTransport.symbolicCopy dst src store)
    (NumericTraversal.copy N hash dst src numeric) hash locations middleHeader copied.2.2.1 dstHeader
  have currentLength := LifecycleNumeric.headerLength_known hash dst (NumericTraversal.copy N hash dst src numeric) (old.overlay source).length headerWord
  have live := (TargetArrayWrite.success (old.overlay source) result i value performed).1
  refine ⟨?_,?_,finalOwner,component.2.2.1,?_,?_⟩
  · dsimp only [execute]
    rw [currentLength,if_pos live,TargetArrayWrite.location]
  · unfold code
    rw [Evm.run_append_ok copied.1]
    rw [Evm.run_append_ok (m' := { TargetArrayCopyTail.afterCopy target (.val ⟨i.val,i.isLt⟩ :: .val (TargetOperations.encodeWord (PrimTy.toWord value)) :: tail) (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) with stack := .val ⟨i.val,i.isLt⟩ :: .slot (TargetOperations.toSlot dst dstFits) :: .val (TargetOperations.encodeWord (PrimTy.toWord value)) :: tail }) (by rfl)]
    exact component.1
  · intro l member
    exact (component.2.2.2 l member).trans (congrArg TargetOperations.encodeWord (component.2.2.1 l member).symm)
  · intro q member observed found
    have covered : q.location dst ∈ locations := by
      simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
      rcases member with rfl | ⟨j,inside,rfl⟩
      · exact dstHeader
      · rw [PrimitivePop.element_location]; exact dstCovered j inside
    exact finalOwner.numeric component.2.2.1 q member covered observed found

/-- info: 'Solidity.Backend.StorageOps.TargetCopyWrite.run_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_current
/-- info: 'Solidity.Backend.StorageOps.TargetCopyWrite.run_failed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_failed
/-- info: 'Solidity.Backend.StorageOps.TargetCopyWrite.failure_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms failure_matches
/-- info: 'Solidity.Backend.StorageOps.TargetCopyWrite.numeric_failure_matches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_failure_matches
/-- info: 'Solidity.Backend.StorageOps.TargetCopyWrite.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete

end Solidity.Backend.StorageOps.TargetCopyWrite
