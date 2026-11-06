import Solidity.Backend.StorageOps.TargetPrimitivePop
import Solidity.Backend.StorageOps.PushTransport

/-! Primitive push/reset reuses the checked full-uint guarded header program.
The newly live cell is addressed from ACTUAL incremented header minus1. PUBLIC
metadata coverage remains an exact IFF, never a new intrinsic source cap. -/
namespace Solidity.Backend.StorageOps.TargetPrimitivePush
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def resetCode (slot : Evm.Slot) : List Evm.Instr :=
  [.push (.val ⟨0,by decide⟩),.push (.slot slot),.sload,.push (.val ⟨1,by decide⟩),.swap 1,.sub,
   .push (.slot slot),.keccakArr,.add,.sstore]

def code (slot : Evm.Slot) : List Evm.Instr := TargetHeaderPush.code slot ++ resetCode slot

/-- Exact reset component on any machine. Successful push supplies a positive
new header, so the wrapped subtraction reduces to the former length. -/
theorem run_reset (slot : Evm.Slot) (machine : Evm.Machine) :
    Evm.run (resetCode slot) machine =
      .ok { machine with store := Evm.WordStore.write machine.store (.data slot ((machine.store slot + (Evm.W - 1)) % Evm.W)) 0 } 0 := by
  simp only [resetCode,Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,List.getElem?_cons_zero,List.set_cons_zero,Evm.Slot.add,Nat.zero_add,Evm.WordStore.cells_val,Evm.wmod]

/-- CURRENT header drives guard/increment and reset address. Failure precedes
ALL writes; success preserves arbitrary original stack and full Machine context. -/
theorem run_current (slot : Evm.Slot) (machine : Evm.Machine) :
    Evm.run (code slot) machine = if machine.store slot + 1 < Evm.W then
      .ok { machine with store := Evm.WordStore.write (Evm.WordStore.write machine.store slot (machine.store slot + 1)) (.data slot (machine.store slot)) 0 } 0
    else .revert := by
  unfold code
  by_cases room : machine.store slot + 1 < Evm.W
  · rw [if_pos room,Evm.run_append_ok (m' := TargetHeaderPush.incremented slot machine) (by rw [TargetHeaderPush.run_current,if_pos room]),run_reset]
    unfold TargetHeaderPush.incremented
    rw [Evm.WordStore.write_same_of_lt _ _ _ room]
    have arithmetic : (machine.store slot + 1 + (Evm.W - 1)) % Evm.W = machine.store slot := by
      rw [show machine.store slot + 1 + (Evm.W - 1) = machine.store slot + Evm.W by have h := Evm.W_pos; omega,
        Nat.add_mod_right,Nat.mod_eq_of_lt (Evm.WordStore.read_lt machine.store slot)]
    rw [arithmetic]
  · rw [if_neg room]
    apply Evm.run_append_revert
    rw [TargetHeaderPush.run_current,if_neg room]

theorem failure_matches {n : Nat} {G : Schema n} {p : PrimTy}
    (old : Value G (.array (.prim p))) (slot : Evm.Slot) (machine : Evm.Machine)
    (header : machine.store slot = old.length.val) :
    Evm.run (code slot) machine = .revert ↔ operationPush old = none := by
  rw [run_current,header,operationPush_failure]
  by_cases room : old.length.val + 1 < Evm.W
  · rw [if_pos room]
    constructor
    · intro impossible; cases impossible
    · intro impossible; change 2 ^ 256 ≤ old.length.val + 1 at impossible; change old.length.val + 1 < 2 ^ 256 at room; omega
  · rw [if_neg room]
    exact ⟨fun _ => by change 2 ^ 256 ≤ old.length.val + 1; change ¬ old.length.val + 1 < 2 ^ 256 at room; omega,fun _ => rfl⟩

/-- Actual guarded reset execution and ALL fitting target-cell agreements.
PUBLIC postmetadata coverage is characterized exactly, not made a source cap. -/
theorem represented_iff {n : Nat} {G : Schema n} {p : PrimTy}
    (old result : Value G (.array (.prim p))) (pushed : operationPush old = some result)
    (indices : List Index) (base : Solidity.Storage.Loc) (baseFits : TargetOperations.KeysFit base)
    (store : Store) (machine : Evm.Machine) (locations : List Solidity.Storage.Loc)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l) (headerCovered : base ∈ locations)
    (before : Represented old (PrimitivePop.queries indices) base store)
    (initial : ∀ l (member : l ∈ locations), machine.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l)) :
    let word := lengthWord result.length.val result.length.isLt
    let child := Solidity.Storage.Loc.data base old.length.val
    let afterStore := Representation.write (Representation.write store child ClearDemands.zero) base word
    let afterTarget := { machine with store := Evm.WordStore.write (Evm.WordStore.write machine.store (TargetOperations.toSlot base baseFits) (TargetOperations.encodeWord word).val) (TargetOperations.toSlot child baseFits) (TargetOperations.encodeWord ClearDemands.zero).val }
    Evm.run (code (TargetOperations.toSlot base baseFits)) machine = .ok afterTarget 0 ∧
      (Represented result (PrimitivePop.queries indices) base afterStore ↔ old.length.val + 1 ≤ lmax) ∧
      (∀ l (member : l ∈ locations), afterTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (afterStore l)) := by
  have beforeHeader : Represented old [.length .nil] base store := by
    intro q member; have same := List.mem_singleton.mp member; subst q
    exact before _ List.mem_cons_self
  have header := TargetHeaderPush.source_header old base baseFits store machine beforeHeader (initial base headerCovered)
  have headers := operationPush_header old result pushed
  have room : machine.store (TargetOperations.toSlot base baseFits) + 1 < Evm.W := by
    rw [header]; have bound := result.length.isLt; change old.length.val + 1 < 2 ^ 256; omega
  have headerAgreement := TargetOperations.write_agreement locations fitting base baseFits (lengthWord result.length.val result.length.isLt) store machine initial
  have agreement := TargetOperations.write_agreement locations fitting (.data base old.length.val) baseFits ClearDemands.zero
    (Representation.write store base (lengthWord result.length.val result.length.isLt))
    { machine with store := Evm.WordStore.write machine.store (TargetOperations.toSlot base baseFits) (TargetOperations.encodeWord (lengthWord result.length.val result.length.isLt)).val } headerAgreement
  refine ⟨?_,PushTransport.represented_iff old result pushed indices base store before,?_⟩
  · rw [run_current,if_pos room]
    simp only [header,headers.1]
    rfl
  · intro l member
    have order := congrArg (fun w : Store => w l) (TargetPrimitivePop.write_order store base old.length.val (lengthWord result.length.val result.length.isLt))
    exact (agreement l member).trans (congrArg TargetOperations.encodeWord order)

/-- Actual numeric primitive push, exact owner coverage IFF and target/numeric
agreement compose under the existing covered finite hash/layout premises. -/
theorem complete_numeric {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations)
    (old result : Value G (.array (.prim p))) (pushed : operationPush old = some result)
    (indices : List Index) (base : Solidity.Storage.Loc) (baseFits : TargetOperations.KeysFit base)
    (store : Store) (machine : Evm.Machine) (numeric : WordStore)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (before : Represented old (PrimitivePop.queries indices) base store) (initial : Transport N hash locations store numeric)
    (targetInitial : ∀ l (member : l ∈ locations), machine.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (headerCovered : base ∈ locations) (elementCovered : Solidity.Storage.Loc.data base old.length.val ∈ locations) :
    let word := lengthWord result.length.val result.length.isLt
    let child := Solidity.Storage.Loc.data base old.length.val
    let afterStore := Representation.write (Representation.write store child ClearDemands.zero) base word
    let afterTarget := { machine with store := Evm.WordStore.write (Evm.WordStore.write machine.store (TargetOperations.toSlot base baseFits) (TargetOperations.encodeWord word).val) (TargetOperations.toSlot child baseFits) (TargetOperations.encodeWord ClearDemands.zero).val }
    ∃ final, LifecycleNumeric.pushPrimitive N hash base numeric = some final ∧
      Evm.run (code (TargetOperations.toSlot base baseFits)) machine = .ok afterTarget 0 ∧
      (Represented result (PrimitivePop.queries indices) base afterStore ↔ old.length.val + 1 ≤ lmax) ∧
      Transport N hash locations afterStore final ∧
      (∀ l (member : l ∈ locations), afterTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (final (l.word N hash))) := by
  obtain ⟨executed,ownerIff,agreement⟩ := represented_iff old result pushed indices base baseFits store machine locations fitting headerCovered before targetInitial
  obtain ⟨final,numericExecuted,transported,_,_⟩ := PushTransport.complete_numeric run old result pushed indices base store numeric before initial headerCovered elementCovered
  exact ⟨final,numericExecuted,executed,ownerIff,transported,fun l member =>
    (agreement l member).trans (congrArg TargetOperations.encodeWord (transported l member).symm)⟩


/-- info: 'Solidity.Backend.StorageOps.TargetPrimitivePush.run_reset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_reset
/-- info: 'Solidity.Backend.StorageOps.TargetPrimitivePush.run_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_current
/-- info: 'Solidity.Backend.StorageOps.TargetPrimitivePush.failure_matches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failure_matches
/-- info: 'Solidity.Backend.StorageOps.TargetPrimitivePush.represented_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_iff
/-- info: 'Solidity.Backend.StorageOps.TargetPrimitivePush.complete_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_numeric

end Solidity.Backend.StorageOps.TargetPrimitivePush
