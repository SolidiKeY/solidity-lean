import Solidity.Backend.Aggregates.G18StorageValues
import Solidity.Storage.Representation.Updates
import Solidity.Backend.StorageOps.TargetOperations

/-! Scalar-valued mapping consumers over the independent Source storage,
legacy intrinsic values and published symbolic representation/target operations.
No Source address lowering, physical hashing or raw-byte EVM is implemented. -/
namespace Solidity.Backend.Aggregates.ScalarMapping
open Lowering.V07
open Solidity.Storage.Representation (Store ValueRep keyWord)

abbrev MapTy (K : PrimTy) (t : Source.IntTy) : Ty :=
  .ref (.mapping K (.prim (integerPrim t)))

/-- Agreement at EVERY typed key path, not a selected finite sample. -/
def Cells {D : Source.Layout} {L : Source.SPath → Source.STy} {K : PrimTy}
    (t : Source.IntTy) (source : Source.Storage D L) (value : SVal (MapTy K t))
    (paths : K.Denote → Source.SPath) (typed : ∀ k, L (paths k) = .int t) : Prop :=
  ∀ k, IntCellAt t source value (paths k) (typed k) (.key k .nil)

def location {K : PrimTy} (base : Solidity.Storage.Loc) (key : K.Denote) : Solidity.Storage.Loc :=
  .hash (keyWord key) base 0

/-- Output property of the actual source and intrinsic writes; not a premise
of a claimed compiler simulation. The constructor is the existing SVal. -/
def WritePost {D : Source.Layout} {L : Source.SPath → Source.STy} {K : PrimTy}
    (t : Source.IntTy) (source : Source.Storage D L)
    (value after : SVal (MapTy K t))
    (paths : K.Denote → Source.SPath) (typed : ∀ k, L (paths k) = .int t)
    (key : K.Denote) (n : Int) (range : t.lo ≤ n ∧ n ≤ t.hi)
    (base : Solidity.Storage.Loc) (store : Store) : Prop :=
  value.save (.key key .nil) (.prim (integerValue t n range)) = some after ∧
  Cells t (source.write (paths key) ((typed key).symm ▸ Source.Val.int n range)) after paths typed ∧
  ValueRep after (.map .word) base
    (Solidity.Storage.Representation.write store (location base key)
      (PrimTy.toWord (integerValue t n range)))

/-- Actual source and intrinsic writes preserve ALL key-cell agreements and
consume the published whole-mapping representation update. -/
theorem write {D : Source.Layout} {L : Source.SPath → Source.STy} {K : PrimTy}
    (t : Source.IntTy) (source : Source.Storage D L)
    (entries : SMap K (.prim (integerPrim t))) (fallback : SVal (.prim (integerPrim t)))
    (paths : K.Denote → Source.SPath) (typed : ∀ k, L (paths k) = .int t)
    (injective : Function.Injective paths) (cells : Cells t source (.map entries fallback) paths typed)
    (base : Solidity.Storage.Loc) (store : Store)
    (represented : ValueRep (.map entries fallback) (.map .word) base store)
    (key : K.Denote) (n : Int) (range : t.lo ≤ n ∧ n ≤ t.hi) :
    ∃ after, WritePost t source (.map entries fallback) after paths typed key n range base store := by
  obtain ⟨after, hs, hr⟩ := int_cell_write (cells key) n range
  have expected := Solidity.Storage.Representation.mapping_source_save entries fallback
    (.prim (integerValue t n range)) key
  have same := Option.some.inj (hs.symm.trans expected)
  subst after
  refine ⟨_,hs,?_,?_⟩
  · intro q
    by_cases equal : q = key
    · subst q
      exact hr
    · exact int_cell_write_other (sp := paths key) (pt := typed key) (cells q)
        (fun e => equal (injective e)) (.key .nil .nil (Ne.symm equal)) n range hs
  · have fresh := ValueRep.scalar (integerValue t n range) (location base key)
      (fun _ => PrimTy.toWord (integerValue t n range)) rfl
    have changed := Solidity.Storage.Representation.mapping_save represented key fresh
    simpa only [location, Solidity.Storage.Representation.patch_word] using changed

/-- Captured typed key slots in the EXISTING symbolic target. No physical
keccak calculation or source expression evaluation is hidden here. -/
def slot {K : PrimTy} (base : Evm.Slot) (key : K.Denote) : Evm.Slot :=
  .hash ⟨keyWord key, Solidity.Storage.Representation.keyWord_lt key⟩ base 0

def writtenMachine {K : PrimTy} (target : Evm.Machine) (base : Evm.Slot)
    (key : K.Denote) (word : Semantics.Word) : Evm.Machine :=
  {target with store := Evm.WordStore.write target.store (slot base key) (StorageOps.TargetOperations.encodeWord word).val}

/-- The target code reads its current source slot. The expected output uses
that captured source value only in the RESULT, never as an emitted literal. -/
def CopyPost {D : Source.Layout} {L : Source.SPath → Source.STy} {K : PrimTy}
    (t : Source.IntTy) (source : Source.Storage D L) (value after : SVal (MapTy K t))
    (paths : K.Denote → Source.SPath) (typed : ∀ k, L (paths k) = .int t)
    (src dst : K.Denote) (n : Int) (range : t.lo ≤ n ∧ n ≤ t.hi)
    (base : Evm.Slot) (store : Store) (target : Evm.Machine) : Prop :=
  WritePost t source value after paths typed dst n range (Solidity.Storage.ofSlot base) store ∧
  Evm.run (StorageOps.TargetOperations.copyCode (slot base dst) (slot base src)) target =
    .ok (writtenMachine target base dst (PrimTy.toWord (integerValue t n range))) 0 ∧
  ∀ key : K.Denote, (writtenMachine target base dst (PrimTy.toWord (integerValue t n range))).store.cells (slot base key) =
    StorageOps.TargetOperations.encodeWord
      (Solidity.Storage.Representation.write store (location (Solidity.Storage.ofSlot base) dst)
        (PrimTy.toWord (integerValue t n range)) (location (Solidity.Storage.ofSlot base) key))

/-- Capture the ACTUAL Source read, derive the intrinsic/symbolic write,
and consume the published current-store copy driver. Its result retains the
entire target machine frame and agreement at EVERY mapping key. -/
theorem copy {D : Source.Layout} {L : Source.SPath → Source.STy} {K : PrimTy}
    (t : Source.IntTy) (source : Source.Storage D L)
    (entries : SMap K (.prim (integerPrim t))) (fallback : SVal (.prim (integerPrim t)))
    (paths : K.Denote → Source.SPath) (typed : ∀ k, L (paths k) = .int t)
    (injective : Function.Injective paths) (cells : Cells t source (.map entries fallback) paths typed)
    (base : Evm.Slot) (store : Store)
    (represented : ValueRep (.map entries fallback) (.map .word) (Solidity.Storage.ofSlot base) store)
    (target : Evm.Machine)
    (initial : ∀ key : K.Denote, target.store.cells (slot base key) =
      StorageOps.TargetOperations.encodeWord (store (location (Solidity.Storage.ofSlot base) key)))
    (src dst : K.Denote) :
    ∃ (n : Int) (range : t.lo ≤ n ∧ n ≤ t.hi) (after : SVal (MapTy K t)),
      source.read (paths src) = some ((typed src).symm ▸ Source.Val.int n range) ∧
      CopyPost t source (.map entries fallback) after paths typed src dst n range base store target := by
  obtain ⟨n,range,sourceRead,legacyRead⟩ := cells src
  obtain ⟨found,foundRead,leafRep⟩ := Solidity.Storage.Representation.mapping_read represented src
  have same := Option.some.inj (foundRead.symm.trans legacyRead)
  subst found
  have beforeWord : store (location (Solidity.Storage.ofSlot base) src) =
      PrimTy.toWord (integerValue t n range) := Solidity.Storage.Representation.scalar_read leafRep
  have targetSource := (initial src).trans
    (congrArg StorageOps.TargetOperations.encodeWord beforeWord)
  obtain ⟨after,afterWrite⟩ := write t source entries fallback paths typed injective cells
    (Solidity.Storage.ofSlot base) store represented dst n range
  refine ⟨n,range,after,sourceRead,afterWrite,?_,?_⟩
  · rw [StorageOps.TargetOperations.run_copy,targetSource]
    rfl
  · intro key
    have fit : ∀ l ∈ [Solidity.Storage.ofSlot (slot base key)], StorageOps.TargetOperations.KeysFit l := by
      intro l hl
      have equal := List.mem_singleton.mp hl
      subst l
      exact Solidity.Storage.keysBelow_ofSlot _
    have before : ∀ l (hl : l ∈ [Solidity.Storage.ofSlot (slot base key)]),
        target.store.cells (StorageOps.TargetOperations.toSlot l (fit l hl)) =
          StorageOps.TargetOperations.encodeWord (store l) := by
      intro l hl
      have equal := List.mem_singleton.mp hl
      subst l
      simpa only [StorageOps.TargetOperations.toSlot_ofSlot] using initial key
    have agreement := StorageOps.TargetOperations.write_agreement
      [Solidity.Storage.ofSlot (slot base key)] fit
      (Solidity.Storage.ofSlot (slot base dst)) (Solidity.Storage.keysBelow_ofSlot _)
      (PrimTy.toWord (integerValue t n range)) store target before
      (Solidity.Storage.ofSlot (slot base key)) (List.mem_singleton_self _)
    simp only [StorageOps.TargetOperations.toSlot_ofSlot] at agreement
    simpa only [writtenMachine,slot,location,Solidity.Storage.ofSlot] using agreement

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms write

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy
end Solidity.Backend.Aggregates.ScalarMapping
