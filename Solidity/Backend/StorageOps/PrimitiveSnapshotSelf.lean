import Solidity.Backend.StorageOps.PrimitiveSnapshotSequence
import Solidity.Backend.StorageOps.PrefixLaws

/-! Actual fixed self-copy identities. A child's identity is deliberately
separate from raw ROOT identity: saving through defaults may materialize slots. -/
namespace Solidity.Backend.StorageOps.PrimitiveSnapshotSelf
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph PrimitiveSnapshotSequence

theorem value_self {n : Nat} {G : Schema n} {p : PrimTy} {m : FixedSize}
 (value : Value G (.fixed (.prim p) m)) : recursiveCopy value value=value := by
 rw [recursiveCopy_eq_overlay]
 cases value with
 | fixed slots =>
  apply congrArg Value.fixed
  funext i
  cases slots i with
  | absent => simp only [Slot.overlay,Slot.clear]
  | present v => cases v; simp only [Slot.overlay,Slot.getD,Value.overlay]

theorem symbolic_self (captured : Store) (base : Solidity.Storage.Loc) (count : Nat) :
 PrimitiveSnapshotNumeric.symbolic captured base base count=captured := by
 induction count with
 | zero => rfl
 | succ count ih =>
  change Representation.write (PrimitiveSnapshotNumeric.symbolic captured base base count) (base.add count) (captured (base.add count))=captured
  rw [ih]
  funext observer
  simp only [Representation.write]
  split
  next equal => exact congrArg captured equal.symm
  next => rfl

theorem numeric_self (N : Nat) (hash : Solidity.Storage.Pre → Nat) (initial : WordStore)
 (base : Solidity.Storage.Loc) (count : Nat) : PrimitiveSnapshotNumeric.numeric N hash initial base base count=initial := by
 induction count with
 | zero => rfl
 | succ count ih =>
  change writeWord (PrimitiveSnapshotNumeric.numeric N hash initial base base count) ((base.add count).word N hash) (initial ((base.add count).word N hash))=initial
  rw [ih]
  funext observer
  simp only [writeWord]
  split
  next equal => exact congrArg initial equal.symm
  next => rfl

/-- Actual compiler snapshot code still executes its loads/stores. Identity
here is only the existing Machine outcome, not a gas/trace/world statement. -/
theorem machine_self (p : PrimTy) (m : FixedSize) (machine : Evm.Machine) (slot : Evm.Slot) :
 TargetFixedSnapshot.afterCopy p m machine slot slot=machine := by
 classical
 have words : ∀ observer,(TargetFixedSnapshot.afterCopy p m machine slot slot).store observer=machine.store observer := by
  intro observer
  by_cases hit : ∃ i,i<m.val ∧ observer=slot.add i
  · obtain ⟨i,inside,rfl⟩:=hit
    exact TargetFixedSnapshot.after_data p m machine slot slot i inside
  · apply TargetFixedSnapshot.after_outside
    intro i inside equal
    exact hit ⟨i,inside,equal⟩
 have stores : (TargetFixedSnapshot.afterCopy p m machine slot slot).store=machine.store := by
  cases left : (TargetFixedSnapshot.afterCopy p m machine slot slot).store with
  | mk leftCells =>
   cases right : machine.store with
   | mk rightCells =>
    apply congrArg Evm.WordStore.mk
    funext observer
    apply Fin.ext
    simpa only [left,right,Evm.WordStore.read] using words observer
 exact congrArg (fun store : Evm.WordStore => {machine with store:=store}) stores

theorem run_self (p : PrimTy) (m : FixedSize) (machine : Evm.Machine) (slot : Evm.Slot) :
 Evm.run (TargetFixedSnapshot.code p m slot slot) machine=.ok machine 0 := by
 rw [TargetFixedSnapshot.run_code,machine_self]

/-- Logical selected ownership survives actual ROOT self-copy even if a
previously absent/defaulted prefix becomes present. No raw ROOT equality. -/
theorem root_owner {n : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy} {m : FixedSize}
 (root result : Value G A) (path : TypeGraph.Path G A (.fixed (.prim p) m))
 (old : Value G (.fixed (.prim p) m)) (found : root.find path=some old)
 (copied : recursiveCopyAt root path path=some result) (supported : PathSupported path)
 (indices : List (Fin m.val)) (base : Solidity.Storage.Loc) (captured : Store)
 (before : Represented root (queries path indices) base captured) :
 Represented result (queries path indices) base captured := by
 have readback := recursiveCopyAt_readback root result path path old old found found copied
 rw [value_self] at readback
 exact Represented.prefix path readback supported (PathRepresentation.focus root old path found _ base captured before)

/-- A successful prior save supplies a real sufficient condition for RAW ROOT
self-copy identity. Defaults may materialize once; overwriting the already
written prefix with the same fixed child is idempotent. -/
theorem after_save {n : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy} {m : FixedSize}
 (root result : Value G A) (path : TypeGraph.Path G A (.fixed (.prim p) m))
 (value : Value G (.fixed (.prim p) m)) (saved : root.save path value=some result) :
 recursiveCopyAt result path path=some result := by
 have readback := Value.find_save root result path value saved
 have overwritten := prefix_save_overwrite path root result value value saved
 simp only [recursiveCopyAt,Option.bind_eq_bind,readback,Option.bind_some,value_self]
 exact overwritten.trans saved

/-- Joint operation-side certificate from OLD relations. The special self-copy
identity needs no new hash premise and does not discharge parent trace premises.
Graph root materialization, ordinary Source and world effects remain separate. -/
theorem complete {n N : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy} {m : FixedSize}
 (root result : Value G A) (path : TypeGraph.Path G A (.fixed (.prim p) m))
 (old : Value G (.fixed (.prim p) m)) (found : root.find path=some old)
 (copied : recursiveCopyAt root path path=some result) (supported : PathSupported path)
 (indices : List (Fin m.val)) (base : Solidity.Storage.Loc) (fits : TargetOperations.KeysFit base)
 (captured : Store) (initial : WordStore) (machine : Evm.Machine)
 (hash : Solidity.Storage.Pre → Nat) (locations : List Solidity.Storage.Loc)
 (before : Represented root (queries path indices) base captured)
 (transport : Transport N hash locations captured initial)
 (fitting : ∀ l ∈ locations,TargetOperations.KeysFit l)
 (agreement : ∀ l (member : l ∈ locations),machine.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (initial (l.word N hash))) :
 let loc := pathLoc path base
 let afterStore := PrimitiveSnapshotNumeric.symbolic captured loc loc m.val
 let afterNumeric := PrimitiveSnapshotNumeric.numeric N hash initial loc loc m.val
 Represented result (queries path indices) base afterStore ∧ Transport N hash locations afterStore afterNumeric ∧
 Evm.run (TargetFixedSnapshot.code p m
  (TargetOperations.toSlot loc (TargetOperations.path_keysFit path base fits))
  (TargetOperations.toSlot loc (TargetOperations.path_keysFit path base fits))) machine=.ok machine 0 ∧
 (∀ l (member : l ∈ locations),machine.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (afterNumeric (l.word N hash))) := by
 simp only [symbolic_self,numeric_self]
 exact ⟨root_owner root result path old found copied supported indices base captured before,transport,run_self _ _ _ _,agreement⟩

/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSelf.value_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms value_self
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSelf.symbolic_self' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms symbolic_self
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSelf.numeric_self' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms numeric_self
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSelf.machine_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms machine_self
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSelf.run_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_self
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSelf.root_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms root_owner
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSelf.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSelf.after_save' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms after_save
end Solidity.Backend.StorageOps.PrimitiveSnapshotSelf
