import Solidity.Evm.SimLemmas
import Solidity.Backend.StorageOps.TargetHeaderPush

/-! Primitive pop adapter reuses the PUBLIC header program/proof, then clears
the former last slot from the ACTUAL decremented header. Intrinsic retained-tail
observations and finite numeric transport stay separate from emitted/world claims. -/
namespace Solidity.Backend.StorageOps.TargetPrimitivePop
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def headerCode (slot : Evm.Slot) : List Evm.Instr := [.push (.slot slot)] ++ Evm.popCode

def clearCode (slot : Evm.Slot) : List Evm.Instr :=
  [.push (.val ⟨0,by decide⟩),.push (.slot slot),.sload,.push (.slot slot),.keccakArr,.add,.sstore]

def code (slot : Evm.Slot) : List Evm.Instr := headerCode slot ++ clearCode slot

/-- Reuse the existing popCode theorem on an arbitrary original stack. -/
theorem run_header (slot : Evm.Slot) (machine : Evm.Machine) :
    Evm.run (headerCode slot) machine = if machine.store slot = 0 then .revert else
      .ok { machine with store := Evm.WordStore.write machine.store slot (machine.store slot - 1) } 0 := by
  unfold headerCode
  rw [Evm.run_append_ok (m' := { machine with stack := .slot slot :: machine.stack }) (by rfl)]
  exact Evm.popCode_run machine machine.stack slot (Evm.WordStore.read_lt machine.store slot)

/-- CURRENT header chooses the slot; neither graph length nor a constant index
is passed to executable code. The original stack/context are restored. -/
theorem run_clear (slot : Evm.Slot) (machine : Evm.Machine) :
    Evm.run (clearCode slot) machine =
      .ok { machine with store := Evm.WordStore.write machine.store (.data slot (machine.store slot)) 0 } 0 := by
  simp only [clearCode,Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,Evm.Slot.add,Nat.zero_add,Evm.WordStore.cells_val]

theorem run_current (slot : Evm.Slot) (machine : Evm.Machine) :
    Evm.run (code slot) machine = if machine.store slot = 0 then .revert else
      .ok { machine with store := Evm.WordStore.write (Evm.WordStore.write machine.store slot (machine.store slot - 1)) (.data slot (machine.store slot - 1)) 0 } 0 := by
  unfold code
  by_cases empty : machine.store slot = 0
  · rw [if_pos empty]
    apply Evm.run_append_revert
    rw [run_header,if_pos empty]
  · rw [if_neg empty,Evm.run_append_ok (m' := { machine with store := Evm.WordStore.write machine.store slot (machine.store slot - 1) }) (by rw [run_header,if_neg empty]),run_clear]
    have bound : machine.store slot - 1 < Evm.W := by have h := Evm.WordStore.read_lt machine.store slot; omega
    rw [Evm.WordStore.write_same_of_lt _ _ _ bound]

private theorem child_ne_header (base : Solidity.Storage.Loc) (i : Nat) : Solidity.Storage.Loc.data base i ≠ base := by
  intro same
  have depth := congrArg Solidity.Storage.Loc.depth same
  change base.depth + 1 = base.depth at depth
  omega

/-- The two OPERATION-GENERATED symbolic updates commute. Numeric separation
is supplied later by the existing covered finite-run transport, not global hashing. -/
theorem write_order (store : Store) (base : Solidity.Storage.Loc) (i : Nat) (word : Semantics.Word) :
    Representation.write (Representation.write store base word) (.data base i) ClearDemands.zero =
      Representation.write (Representation.write store (.data base i) ClearDemands.zero) base word := by
  have different := child_ne_header base i
  funext l
  by_cases header : l = base
  · subst l
    simp only [Representation.write,if_neg different.symm]
  · by_cases child : l = Solidity.Storage.Loc.data base i
    · subst l
      simp only [Representation.write,if_neg different]
    · simp only [Representation.write,if_neg header,if_neg child]

theorem failure_matches {n : Nat} {G : Schema n} {p : PrimTy}
    (old : Value G (.array (.prim p))) (slot : Evm.Slot) (machine : Evm.Machine)
    (header : machine.store slot = old.length.val) :
    Evm.run (code slot) machine = .revert ↔ recursivePop old = none := by
  rw [run_current,header,recursivePop_failure]
  by_cases empty : old.length.val = 0
  · rw [if_pos empty]
    exact ⟨fun _ => empty,fun _ => rfl⟩
  · rw [if_neg empty]
    constructor
    · intro impossible; cases impossible
    · intro impossible; exact False.elim (empty impossible)

/-- Selected source postrelation and ALL target cell agreements derive from
OLD evidence; actual execution preserves arbitrary stack and complete context.
Published popCode writes header first; the operation-generated order law above
reconciles this with the independently checked intrinsic/numeric pop certificate. -/
theorem represented {n : Nat} {G : Schema n} {p : PrimTy}
    (old result : Value G (.array (.prim p))) (popped : recursivePop old = some result)
    (indices : List Index) (base : Solidity.Storage.Loc) (baseFits : TargetOperations.KeysFit base)
    (store : Store) (machine : Evm.Machine) (locations : List Solidity.Storage.Loc)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l) (headerCovered : base ∈ locations)
    (before : Represented old (PrimitivePop.queries indices) base store)
    (initial : ∀ l (member : l ∈ locations), machine.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l)) :
    let word := lengthWord result.length.val result.length.isLt
    let child := Solidity.Storage.Loc.data base (old.length.val - 1)
    let afterStore := Representation.write (Representation.write store child ClearDemands.zero) base word
    let afterTarget := { machine with store := Evm.WordStore.write (Evm.WordStore.write machine.store (TargetOperations.toSlot base baseFits) (TargetOperations.encodeWord word).val) (TargetOperations.toSlot child baseFits) (TargetOperations.encodeWord ClearDemands.zero).val }
    Evm.run (code (TargetOperations.toSlot base baseFits)) machine = .ok afterTarget 0 ∧
      Represented result (PrimitivePop.queries indices) base afterStore ∧
      (∀ l (member : l ∈ locations), afterTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (afterStore l)) := by
  have beforeHeader : Represented old [.length .nil] base store := by
    intro q member; have same := List.mem_singleton.mp member; subst q
    exact before _ List.mem_cons_self
  have header := TargetHeaderPush.source_header old base baseFits store machine beforeHeader (initial base headerCovered)
  have headers := recursivePop_header old result popped
  have live : old.length.val ≠ 0 := by omega
  have length : result.length.val = old.length.val - 1 := by omega
  have headerAgreement := TargetOperations.write_agreement locations fitting base baseFits (lengthWord result.length.val result.length.isLt) store machine initial
  have agreement := TargetOperations.write_agreement locations fitting (.data base (old.length.val - 1)) baseFits ClearDemands.zero
    (Representation.write store base (lengthWord result.length.val result.length.isLt))
    { machine with store := Evm.WordStore.write machine.store (TargetOperations.toSlot base baseFits) (TargetOperations.encodeWord (lengthWord result.length.val result.length.isLt)).val } headerAgreement
  refine ⟨?_,PrimitivePop.represented old result popped indices base store before,?_⟩
  · rw [run_current,header,if_neg live]
    simp only [length]
    rfl
  · intro l member
    have order := congrArg (fun w : Store => w l) (write_order store base (old.length.val - 1) (lengthWord result.length.val result.length.isLt))
    exact (agreement l member).trans (congrArg TargetOperations.encodeWord order)

/-- Actual target instructions and the independently checked numeric program
agree through PUBLIC per-run transport. Physical separation is retained exactly. -/
theorem complete_numeric {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations)
    (old result : Value G (.array (.prim p))) (popped : recursivePop old = some result)
    (indices : List Index) (base : Solidity.Storage.Loc) (baseFits : TargetOperations.KeysFit base)
    (store : Store) (machine : Evm.Machine) (numeric : WordStore)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (before : Represented old (PrimitivePop.queries indices) base store) (initial : Transport N hash locations store numeric)
    (targetInitial : ∀ l (member : l ∈ locations), machine.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (covered : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, q.location base ∈ locations)
    (lastCovered : Solidity.Storage.Loc.data base (old.length.val - 1) ∈ locations) :
    let word := lengthWord result.length.val result.length.isLt
    let child := Solidity.Storage.Loc.data base (old.length.val - 1)
    let afterStore := Representation.write (Representation.write store child ClearDemands.zero) base word
    let afterTarget := { machine with store := Evm.WordStore.write (Evm.WordStore.write machine.store (TargetOperations.toSlot base baseFits) (TargetOperations.encodeWord word).val) (TargetOperations.toSlot child baseFits) (TargetOperations.encodeWord ClearDemands.zero).val }
    ∃ final, PrimitivePop.execute N hash base numeric = some final ∧
      Evm.run (code (TargetOperations.toSlot base baseFits)) machine = .ok afterTarget 0 ∧
      Represented result (PrimitivePop.queries indices) base afterStore ∧ Transport N hash locations afterStore final ∧
      (∀ l (member : l ∈ locations), afterTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (final (l.word N hash))) := by
  obtain ⟨executed,owner,agreement⟩ := represented old result popped indices base baseFits store machine locations fitting
    (covered (.length .nil) List.mem_cons_self) before targetInitial
  obtain ⟨final,numericExecuted,_,transported,_,_⟩ := PrimitivePop.complete_numeric run old result popped indices base store numeric before initial covered lastCovered
  exact ⟨final,numericExecuted,executed,owner,transported,fun l member =>
    (agreement l member).trans (congrArg TargetOperations.encodeWord (transported l member).symm)⟩

/-- info: 'Solidity.Backend.StorageOps.TargetPrimitivePop.run_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_header
/-- info: 'Solidity.Backend.StorageOps.TargetPrimitivePop.run_clear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_clear
/-- info: 'Solidity.Backend.StorageOps.TargetPrimitivePop.run_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_current
/-- info: 'Solidity.Backend.StorageOps.TargetPrimitivePop.write_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms write_order
/-- info: 'Solidity.Backend.StorageOps.TargetPrimitivePop.failure_matches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failure_matches
/-- info: 'Solidity.Backend.StorageOps.TargetPrimitivePop.represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms represented
/-- info: 'Solidity.Backend.StorageOps.TargetPrimitivePop.complete_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_numeric

end Solidity.Backend.StorageOps.TargetPrimitivePop
