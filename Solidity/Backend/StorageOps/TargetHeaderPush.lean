import Solidity.Backend.StorageOps.TargetOperations
import Solidity.Backend.StorageOps.RetainedPush

/-! Runtime capacity-guarded current-header increment in EXISTING Evm.Instr.
Captured symbolic slot addressing remains the published target boundary; this
is not emitted bytecode, full error payloads or world rollback semantics. -/
namespace Solidity.Backend.StorageOps.TargetHeaderPush
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def code (slot : Evm.Slot) : List Evm.Instr :=
  [.push (.slot slot),.sload,.dup 1,.push (.val Evm.wMax),.gt,.jumpi 1,.revert,
   .push (.val ⟨1,by decide⟩),.add,.push (.slot slot),.sstore]

def incremented (slot : Evm.Slot) (machine : Evm.Machine) : Evm.Machine :=
  { machine with store := Evm.WordStore.write machine.store slot (machine.store slot + 1) }

/-- Actual SLOAD drives BOTH capacity guard and increment. Success preserves
original stack/context; UINT256-max reverts before SSTORE. -/
theorem run_current (slot : Evm.Slot) (machine : Evm.Machine) :
    Evm.run (code slot) machine = if machine.store slot + 1 < Evm.W then
      .ok (incremented slot machine) 0 else .revert := by
  by_cases room : machine.store slot + 1 < Evm.W
  · have guard : machine.store slot < Evm.W - 1 := by omega
    simp only [code,Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
      if_true,if_neg (by decide : ¬ ((1 : Nat) = 0)),
      Nat.sub_self,List.getElem?_cons_zero,Evm.wMax,Evm.bword,Evm.WordStore.cells_val,decide_eq_true guard,if_pos room]
    simp only [Evm.wmod,Nat.add_comm 1,Nat.mod_eq_of_lt room,incremented]
  · have guard : ¬ machine.store slot < Evm.W - 1 := by omega
    simp only [code,Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
      if_true,if_false,Bool.false_eq_true,
      Nat.sub_self,List.getElem?_cons_zero,Evm.wMax,Evm.bword,Evm.WordStore.cells_val,decide_eq_false guard,if_neg room]

/-- BOTH capacity outcomes match intrinsic push on its FULL uint256 length
range given the plain current-header observation. No lmax source cap is added. -/
theorem failure_matches {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) (slot : Evm.Slot) (machine : Evm.Machine)
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

/-- OLD PUBLIC header representation and independent target-cell agreement
derive the runtime numeric header; it is not supplied as a compiler oracle. -/
theorem source_header {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) (base : Solidity.Storage.Loc) (fits : TargetOperations.KeysFit base)
    (store : Store) (machine : Evm.Machine)
    (before : Represented old [.length .nil] base store)
    (initial : machine.store.cells (TargetOperations.toSlot base fits) = TargetOperations.encodeWord (store base)) :
    machine.store (TargetOperations.toSlot base fits) = old.length.val := by
  have header : store base = lengthWord old.length.val old.length.isLt := by
    apply (before (.length .nil) List.mem_cons_self).2.2
    cases old; rfl
  have encoded := congrArg Fin.val (initial.trans (congrArg TargetOperations.encodeWord header))
  exact encoded

/-- Actual guarded Evm.Instr execution derives selected retained aggregate
postrepresentation and ALL covered symbolic target cells. Full Machine record
update states exact stack/memory/balance/context preservation on success. -/
theorem represented_retained {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (pushed : operationPush old = some result)
    (nonprimitive : E.isPrimitive = false) (retained : old.length.val < old.extent.val)
    (groups : List (Index × List (Query G E))) (base : Solidity.Storage.Loc) (baseFits : TargetOperations.KeysFit base)
    (store : Store) (machine : Evm.Machine) (locations : List Solidity.Storage.Loc)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l) (headerCovered : base ∈ locations)
    (before : Represented old (RetainedPush.requested groups) base store)
    (initial : ∀ l (member : l ∈ locations), machine.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l)) :
    let word := lengthWord result.length.val result.length.isLt
    let afterStore := write store base word
    let afterTarget := { machine with store := Evm.WordStore.write machine.store (TargetOperations.toSlot base baseFits) (TargetOperations.encodeWord word).val }
    Evm.run (code (TargetOperations.toSlot base baseFits)) machine = .ok afterTarget 0 ∧
      Represented result (RetainedPush.requested groups) base afterStore ∧
      (∀ l (member : l ∈ locations), afterTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (afterStore l)) := by
  have headerBefore : Represented old [.length .nil] base store := by
    intro q member; have same := List.mem_singleton.mp member; subst q
    exact before _ List.mem_cons_self
  have header := source_header old base baseFits store machine headerBefore (initial base headerCovered)
  have headers := operationPush_header old result pushed
  have room : machine.store (TargetOperations.toSlot base baseFits) + 1 < Evm.W := by
    rw [header]; have bound := result.length.isLt; change old.length.val + 1 < 2 ^ 256; omega
  refine ⟨?_,RetainedPush.represented old result pushed nonprimitive retained groups base store before,
    TargetOperations.write_agreement locations fitting base baseFits _ store machine initial⟩
  rw [run_current,if_pos room]
  unfold incremented
  have encoded : (TargetOperations.encodeWord (lengthWord result.length.val result.length.isLt)).val = result.length.val := rfl
  rw [encoded,header,headers.1]

/-- Per-run numeric transport composes with actual guarded target execution.
The existing finite region conditions are retained, not replaced by ideal slots. -/
theorem numeric_retained {n N L R : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (pushed : operationPush old = some result)
    (nonprimitive : E.isPrimitive = false) (retained : old.length.val < old.extent.val)
    (groups : List (Index × List (Query G E))) (base : Solidity.Storage.Loc) (baseFits : TargetOperations.KeysFit base)
    (store : Store) (machine : Evm.Machine) (numeric : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations) (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (before : Represented old (RetainedPush.requested groups) base store)
    (initial : Transport N hash locations store numeric)
    (targetInitial : ∀ l (member : l ∈ locations), machine.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (covered : ∀ q ∈ RetainedPush.requested groups, q.location base ∈ locations) :
    ∃ final, LifecycleNumeric.pushHeader N hash base numeric = some final ∧
      let word := lengthWord result.length.val result.length.isLt
      let afterStore := write store base word
      let afterTarget := { machine with store := Evm.WordStore.write machine.store (TargetOperations.toSlot base baseFits) (TargetOperations.encodeWord word).val }
      Evm.run (code (TargetOperations.toSlot base baseFits)) machine = .ok afterTarget 0 ∧
      Represented result (RetainedPush.requested groups) base afterStore ∧ Transport N hash locations afterStore final ∧
      (∀ l (member : l ∈ locations), afterTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (final (l.word N hash))) := by
  have headerCovered : base ∈ locations := covered (.length .nil) List.mem_cons_self
  obtain ⟨executed,owner,agreement⟩ := represented_retained old result pushed nonprimitive retained groups base baseFits store machine locations fitting headerCovered before targetInitial
  obtain ⟨final,numericExecuted,_,transported,_,_⟩ := RetainedPush.complete_numeric old result pushed nonprimitive retained groups base store numeric run before initial covered
  exact ⟨final,numericExecuted,executed,owner,transported,fun l member =>
    (agreement l member).trans (congrArg TargetOperations.encodeWord (transported l member).symm)⟩

/-- info: 'Solidity.Backend.StorageOps.TargetHeaderPush.run_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_current
/-- info: 'Solidity.Backend.StorageOps.TargetHeaderPush.failure_matches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failure_matches
/-- info: 'Solidity.Backend.StorageOps.TargetHeaderPush.source_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_header
/-- info: 'Solidity.Backend.StorageOps.TargetHeaderPush.represented_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_retained
/-- info: 'Solidity.Backend.StorageOps.TargetHeaderPush.numeric_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_retained

end Solidity.Backend.StorageOps.TargetHeaderPush
