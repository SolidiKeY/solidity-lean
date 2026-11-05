import Solidity.Backend.StorageOps.TargetNestedArrayRuntime
import Solidity.Backend.StorageOps.TargetCopyRepresentation
import Solidity.Backend.StorageOps.TargetClearRepresentation

/-! Finite-run transport for actual evolving runtime nested operations.
No independent graph/default/liveness or Source preservation is assumed. -/
namespace Solidity.Backend.StorageOps.TargetNestedArrayTransport
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def copyStores (initial : Store) (dst src : Solidity.Storage.Loc) : Nat → Store
  | 0 => initial
  | count+1 => CopyTransport.symbolicCopy (.data dst count) (.data src count) (copyStores initial dst src count)

def copyNumerics (N : Nat) (hash : Solidity.Storage.Pre → Nat) (initial : WordStore)
    (dst src : Solidity.Storage.Loc) : Nat → WordStore
  | 0 => initial
  | count+1 => NumericTraversal.copy N hash (.data dst count) (.data src count) (copyNumerics N hash initial dst src count)

/-- Both intermediate concrete store relations are DERIVED from OLD transport
and actual generated read/write coverage of current child headers. Failed graph
queries never supply zero or an implicit allocation/default premise. -/
theorem copy_prefix {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (count : Nat)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (headers : ∀ k < count, Solidity.Storage.Loc.data dst k ∈ locations ∧ Solidity.Storage.Loc.data src k ∈ locations)
    (reads : ∀ k < count, ∀ j < ((copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data src k) j ∈ locations)
    (writes : ∀ k < count, ∀ j < max ((copyStores store dst src k) (.data dst k)).val.toNat
        ((copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data dst k) j ∈ locations) :
    Transport N hash locations (copyStores store dst src count) (copyNumerics N hash numeric dst src count) ∧
    (∀ l (member : l ∈ locations),
      (TargetNestedArrayCopyLoop.prefixMachine target (TargetOperations.toSlot src srcFits)
        (TargetOperations.toSlot dst dstFits) count).store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (copyStores store dst src count l)) := by
  induction count with
  | zero => exact ⟨initial,targetInitial⟩
  | succ count ih =>
    have previous := ih (fun k inside => headers k (Nat.lt_trans inside (Nat.lt_succ_self count)))
      (fun k inside => reads k (Nat.lt_trans inside (Nat.lt_succ_self count)))
      (fun k inside => writes k (Nat.lt_trans inside (Nat.lt_succ_self count)))
    have covered := headers count (Nat.lt_succ_self count)
    have sourceLength : LifecycleNumeric.headerLength N hash (.data src count) (copyNumerics N hash numeric dst src count) =
        ((copyStores store dst src count) (.data src count)).val.toNat := by
      unfold LifecycleNumeric.headerLength
      rw [previous.1 _ covered.2]
    have oldLength : LifecycleNumeric.headerLength N hash (.data dst count) (copyNumerics N hash numeric dst src count) =
        ((copyStores store dst src count) (.data dst count)).val.toNat := by
      unfold LifecycleNumeric.headerLength
      rw [previous.1 _ covered.1]
    have transported := CopyTransport.transported run (.data dst count) (.data src count)
      (copyStores store dst src count) (copyNumerics N hash numeric dst src count) previous.1 covered.1 covered.2
      (reads count (Nat.lt_succ_self count)) (writes count (Nat.lt_succ_self count))
    have agreement := TargetCopyRepresentation.numeric_agreement run (.data dst count) (.data src count) dstFits srcFits
      (copyStores store dst src count) (copyNumerics N hash numeric dst src count)
      (TargetNestedArrayCopyLoop.prefixMachine target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) count)
      target.stack previous.1 covered.1 covered.2
      (by simpa only [sourceLength] using reads count (Nat.lt_succ_self count))
      (by simpa only [sourceLength,oldLength] using writes count (Nat.lt_succ_self count)) fitting previous.2
    refine ⟨transported,?_⟩
    intro l member
    have actual := agreement l member
    rw [transported l member] at actual
    exact actual

/-- Reuse the checked operation-generated symbolic live-prefix writes.
The CURRENT concrete header supplies the count, not a graph result oracle. -/
def clearStore (store : Store) (base : Solidity.Storage.Loc) : Store :=
  Representation.write (TargetClearRepresentation.symbolicPrefix store base (store base).val.toNat) base ClearDemands.zero

/-- Raw operation transport has no default/graph assumption. Every current
nested header and every generated clear write must be covered by the OLD run. -/
theorem clear_one {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations) (base : Solidity.Storage.Loc) (baseFits : TargetOperations.KeysFit base)
    (store : Store) (numeric : WordStore) (target : Evm.Machine)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (header : base ∈ locations)
    (writes : ∀ j < (store base).val.toNat, Solidity.Storage.Loc.data base j ∈ locations) :
    Transport N hash locations (clearStore store base) (TargetClearRepresentation.execute N hash base numeric) ∧
    (∀ l (member : l ∈ locations), (TargetArrayClear.afterClear target target.stack (TargetOperations.toSlot base baseFits)).store.cells
      (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (clearStore store base l)) := by
  have numericLength : LifecycleNumeric.headerLength N hash base numeric = (store base).val.toNat := by
    unfold LifecycleNumeric.headerLength
    rw [initial base header]
  have targetLength : target.store (TargetOperations.toSlot base baseFits) = (store base).val.toNat :=
    congrArg Fin.val (targetInitial base header)
  have prefixTransport := TargetClearRepresentation.prefix_numeric run store numeric base initial (store base).val.toNat writes
  have finalTransport := transport_write run prefixTransport base header ClearDemands.zero
  have prefixTarget := TargetClearRepresentation.prefix_target store target base baseFits locations fitting targetInitial (store base).val.toNat
  have finalTarget := TargetOperations.write_agreement locations fitting base baseFits ClearDemands.zero
    (TargetClearRepresentation.symbolicPrefix store base (store base).val.toNat)
    { target with store := TargetArrayClear.clearPrefix target.store (TargetOperations.toSlot base baseFits) (store base).val.toNat } prefixTarget
  refine ⟨?_,?_⟩
  · simpa only [clearStore,TargetClearRepresentation.execute,numericLength] using finalTransport
  · intro l member
    change (Evm.WordStore.write (TargetArrayClear.clearPrefix target.store (TargetOperations.toSlot base baseFits)
      (target.store (TargetOperations.toSlot base baseFits))) (TargetOperations.toSlot base baseFits) 0).cells
      (TargetOperations.toSlot l (fitting l member)) = _
    rw [targetLength]
    exact finalTarget l member

def clearStores (initial : Store) (dst : Solidity.Storage.Loc) (start : Nat) : Nat → Store
  | 0 => initial
  | count+1 => if start ≤ count then clearStore (clearStores initial dst start count) (.data dst count)
      else clearStores initial dst start count

def clearNumerics (N : Nat) (hash : Solidity.Storage.Pre → Nat) (initial : WordStore)
    (dst : Solidity.Storage.Loc) (start : Nat) : Nat → WordStore
  | 0 => initial
  | count+1 => if start ≤ count then TargetClearRepresentation.execute N hash (.data dst count) (clearNumerics N hash initial dst start count)
      else clearNumerics N hash initial dst start count

/-- Every stale-child intermediate transport/target agreement is DERIVED from
OLD evidence; skipped prefix and actual current nested counts are preserved. -/
theorem clear_prefix {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (dst : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (start count : Nat)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (headers : ∀ k < count, start ≤ k → Solidity.Storage.Loc.data dst k ∈ locations)
    (writes : ∀ k < count, start ≤ k → ∀ j < ((clearStores store dst start k) (.data dst k)).val.toNat,
      Solidity.Storage.Loc.data (.data dst k) j ∈ locations) :
    Transport N hash locations (clearStores store dst start count) (clearNumerics N hash numeric dst start count) ∧
    (∀ l (member : l ∈ locations),
      (TargetNestedArrayClearLoop.prefixMachine target (TargetOperations.toSlot dst dstFits) start count).store.cells
        (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (clearStores store dst start count l)) := by
  induction count with
  | zero => exact ⟨initial,targetInitial⟩
  | succ count ih =>
    have previous := ih (fun k inside => headers k (Nat.lt_trans inside (Nat.lt_succ_self count)))
      (fun k inside => writes k (Nat.lt_trans inside (Nat.lt_succ_self count)))
    by_cases active : start ≤ count
    · have current := clear_one run (.data dst count) dstFits (clearStores store dst start count)
        (clearNumerics N hash numeric dst start count)
        (TargetNestedArrayClearLoop.prefixMachine target (TargetOperations.toSlot dst dstFits) start count)
        previous.1 fitting previous.2 (headers count (Nat.lt_succ_self count) active)
        (writes count (Nat.lt_succ_self count) active)
      refine ⟨?_,?_⟩
      · simpa only [clearStores,clearNumerics,if_pos active] using current.1
      · intro l member
        have actual := current.2 l member
        simpa only [TargetNestedArrayClearLoop.prefixMachine,clearStores,if_pos active] using actual
    · simpa only [TargetNestedArrayClearLoop.prefixMachine,clearStores,clearNumerics,if_neg active] using previous

/-- Captured OUTER headers choose both runtime phases; inner operations still
read their CURRENT concrete headers. This is an existing Store update program. -/
def afterStore (store : Store) (dst src : Solidity.Storage.Loc) : Store :=
  let live := (store src).val.toNat
  let oldLive := (store dst).val.toNat
  Representation.write (clearStores (copyStores store dst src live) dst live (max live oldLive)) dst (store src)

/-- Independent numeric execution captures its OWN initial numeric headers,
then performs current inner copies/clears and writes the captured header last. -/
def execute (N : Nat) (hash : Solidity.Storage.Pre → Nat) (numeric : WordStore)
    (dst src : Solidity.Storage.Loc) : WordStore :=
  let live := LifecycleNumeric.headerLength N hash src numeric
  let oldLive := LifecycleNumeric.headerLength N hash dst numeric
  writeWord (clearNumerics N hash (copyNumerics N hash numeric dst src live) dst live (max live oldLive))
    (dst.word N hash) (numeric (src.word N hash))

/-- Full actual runtime traversal/physical numeric transport from OLD evidence.
Every intermediate relation is DERIVED. No graph postowner/default/source
preservation theorem is a premise or claimed by this raw execution bridge. -/
theorem complete {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (tail : List Evm.Word)
    (initial : Transport N hash locations store numeric)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (dstHeader : dst ∈ locations) (srcHeader : src ∈ locations)
    (copyHeaders : ∀ k < (store src).val.toNat, Solidity.Storage.Loc.data dst k ∈ locations ∧ Solidity.Storage.Loc.data src k ∈ locations)
    (copyReads : ∀ k < (store src).val.toNat, ∀ j < ((copyStores store dst src k) (.data src k)).val.toNat,
      Solidity.Storage.Loc.data (.data src k) j ∈ locations)
    (copyWrites : ∀ k < (store src).val.toNat, ∀ j < max ((copyStores store dst src k) (.data dst k)).val.toNat
        ((copyStores store dst src k) (.data src k)).val.toNat, Solidity.Storage.Loc.data (.data dst k) j ∈ locations)
    (clearHeaders : ∀ k < max (store src).val.toNat (store dst).val.toNat, (store src).val.toNat ≤ k → Solidity.Storage.Loc.data dst k ∈ locations)
    (clearWrites : ∀ k < max (store src).val.toNat (store dst).val.toNat, (store src).val.toNat ≤ k →
      ∀ j < ((clearStores (copyStores store dst src (store src).val.toNat) dst (store src).val.toNat k) (.data dst k)).val.toNat,
        Solidity.Storage.Loc.data (.data dst k) j ∈ locations) :
    Evm.run TargetNestedArrayCopy.code { target with stack := .slot (TargetOperations.toSlot src srcFits) :: .slot (TargetOperations.toSlot dst dstFits) :: tail } =
      .ok (TargetNestedArrayRuntime.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)) 0 ∧
    Transport N hash locations (afterStore store dst src) (execute N hash numeric dst src) ∧
    (∀ l (member : l ∈ locations),
      (TargetNestedArrayRuntime.afterCopy target tail (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store.cells
        (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (afterStore store dst src l)) := by
  have sourceLength : LifecycleNumeric.headerLength N hash src numeric = (store src).val.toNat := by
    unfold LifecycleNumeric.headerLength
    rw [initial src srcHeader]
  have oldLength : LifecycleNumeric.headerLength N hash dst numeric = (store dst).val.toNat := by
    unfold LifecycleNumeric.headerLength
    rw [initial dst dstHeader]
  have targetNew : target.store (TargetOperations.toSlot src srcFits) = (store src).val.toNat := congrArg Fin.val (targetInitial src srcHeader)
  have targetOld : target.store (TargetOperations.toSlot dst dstFits) = (store dst).val.toNat := congrArg Fin.val (targetInitial dst dstHeader)
  have copied := copy_prefix run dst src dstFits srcFits store numeric target (store src).val.toNat initial fitting targetInitial
    copyHeaders copyReads copyWrites
  have cleared := clear_prefix run dst dstFits (copyStores store dst src (store src).val.toNat)
    (copyNumerics N hash numeric dst src (store src).val.toNat)
    (TargetNestedArrayCopyLoop.prefixMachine target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) (store src).val.toNat)
    (store src).val.toNat (max (store src).val.toNat (store dst).val.toNat) copied.1 fitting copied.2 clearHeaders clearWrites
  have transported := transport_write run cleared.1 dst dstHeader (store src)
  have written := TargetOperations.write_agreement locations fitting dst dstFits (store src)
    (clearStores (copyStores store dst src (store src).val.toNat) dst (store src).val.toNat (max (store src).val.toNat (store dst).val.toNat))
    (TargetNestedArrayClearLoop.prefixMachine
      (TargetNestedArrayCopyLoop.prefixMachine target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) (store src).val.toNat)
      (TargetOperations.toSlot dst dstFits) (store src).val.toNat (max (store src).val.toNat (store dst).val.toNat)) cleared.2
  refine ⟨TargetNestedArrayRuntime.run_current _ _ _ _,?_,?_⟩
  · simpa only [afterStore,execute,sourceLength,oldLength,initial src srcHeader] using transported
  · intro l member
    change (Evm.WordStore.write
      (TargetNestedArrayClearLoop.prefixMachine
        (TargetNestedArrayCopyLoop.prefixMachine target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)
          (target.store (TargetOperations.toSlot src srcFits)))
        (TargetOperations.toSlot dst dstFits) (target.store (TargetOperations.toSlot src srcFits))
        (max (target.store (TargetOperations.toSlot src srcFits)) (target.store (TargetOperations.toSlot dst dstFits)))).store
      (TargetOperations.toSlot dst dstFits) (target.store (TargetOperations.toSlot src srcFits))).cells
      (TargetOperations.toSlot l (fitting l member)) = _
    rw [targetNew,targetOld]
    exact written l member

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransport.copyStores' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copyStores
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransport.copyNumerics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copyNumerics
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransport.copy_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copy_prefix
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransport.clearStore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clearStore
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransport.clear_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clear_one
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransport.clearStores' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clearStores
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransport.clearNumerics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clearNumerics
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransport.clear_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clear_prefix
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransport.afterStore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms afterStore
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransport.execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms execute
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransport.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete

end Solidity.Backend.StorageOps.TargetNestedArrayTransport
