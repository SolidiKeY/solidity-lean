import Solidity.Backend.StorageOps.TargetPrimitivePop
import Solidity.Backend.StorageOps.TargetArrayClear

/-! Actual two-level aggregate pop: public outer-header pop, CURRENT last-child
address calculation and the existing runtime primitive-child clear loop. This
component is not a general recursive compiler/Source/world lifecycle theorem. -/
namespace Solidity.Backend.StorageOps.TargetNestedPop
open TypeGraph

def selectCode (slot : Evm.Slot) : List Evm.Instr :=
 [.push (.slot slot),.sload,.push (.slot slot),.keccakArr,.add]

def code (slot : Evm.Slot) : List Evm.Instr :=
 TargetPrimitivePop.headerCode slot ++ (selectCode slot ++ TargetArrayClear.code)

def decremented (machine : Evm.Machine) (slot : Evm.Slot) : Evm.Machine :=
 {machine with store := Evm.WordStore.write machine.store slot (machine.store slot - 1)}

def selected (machine : Evm.Machine) (slot : Evm.Slot) : Evm.Slot :=
 .data slot (machine.store slot - 1)

def after (machine : Evm.Machine) (slot : Evm.Slot) : Evm.Machine :=
 TargetArrayClear.afterClear (decremented machine slot) machine.stack (selected machine slot)

/-- Actual instructions compute a child slot from CURRENT SLOAD, preserving
all cells and context; no logical graph length is an executable argument. -/
theorem run_select (slot : Evm.Slot) (machine : Evm.Machine) :
 Evm.run (selectCode slot) machine =
 .ok {machine with stack := .slot (.data slot (machine.store slot)) :: machine.stack} 0 := by
 simp only [selectCode,Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
   Evm.Slot.add,Nat.zero_add,Evm.WordStore.cells_val]

/-- Arbitrary finite runtime outer and inner headers; empty outer pop fails
before any child selection. Original stack and non-store fields are restored. -/
theorem run_current (slot : Evm.Slot) (machine : Evm.Machine) :
 Evm.run (code slot) machine = if machine.store slot = 0 then .revert else .ok (after machine slot) 0 := by
 unfold code
 by_cases empty : machine.store slot = 0
 · rw [if_pos empty]
   apply Evm.run_append_revert
   rw [TargetPrimitivePop.run_header,if_pos empty]
 · rw [if_neg empty,Evm.run_append_ok (m' := decremented machine slot)
     (by rw [TargetPrimitivePop.run_header,if_neg empty]; rfl),Evm.run_append_ok (run_select slot (decremented machine slot))]
   have bound : machine.store slot - 1 < Evm.W := by
     have h := Evm.WordStore.read_lt machine.store slot
     omega
   have header : (decremented machine slot).store slot = machine.store slot - 1 :=
     Evm.WordStore.write_same_of_lt _ _ _ bound
   rw [header]
   exact TargetArrayClear.run_current (decremented machine slot) machine.stack (selected machine slot)

private theorem child_ne_root (slot : Evm.Slot) (i : Nat) : Evm.Slot.data slot i ≠ slot :=
 Ne.symm (Evm.Slot.ne_data slot i)
private theorem grand_ne_root (slot : Evm.Slot) (i j : Nat) : Evm.Slot.data (.data slot i) j ≠ slot := by
 intro same
 have depths := congrArg (fun s => (Solidity.Storage.ofSlot s).depth) same
 change (Solidity.Storage.ofSlot slot).depth + 1 + 1 = (Solidity.Storage.ofSlot slot).depth at depths
 omega
private theorem child_ne_grand (slot : Evm.Slot) (i k j : Nat) : Evm.Slot.data slot i ≠ .data (.data slot k) j := by
 intro same
 have depths := congrArg (fun s => (Solidity.Storage.ofSlot s).depth) same
 change (Solidity.Storage.ofSlot slot).depth + 1 = (Solidity.Storage.ofSlot slot).depth + 1 + 1 at depths
 omega

/-- Existing intrinsic nested pop fails on exactly the same empty header.
No successful representation or compiler preservation is assumed here. -/
theorem failure_matches {n : Nat} {G : Schema n} {p : PrimTy}
 (old : Value G (.array (.array (.prim p)))) (slot : Evm.Slot) (machine : Evm.Machine)
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

theorem outer_header (slot : Evm.Slot) (machine : Evm.Machine) :
 (after machine slot).store slot = machine.store slot - 1 := by
 unfold after selected
 rw [TargetArrayClear.after_outside _ _ _ slot (Evm.Slot.ne_data slot _)
   (by intro j _; exact Ne.symm (grand_ne_root slot _ j))]
 have bound : machine.store slot - 1 < Evm.W := by have h := Evm.WordStore.read_lt machine.store slot; omega
 exact Evm.WordStore.write_same_of_lt _ _ _ bound

theorem child_header (slot : Evm.Slot) (machine : Evm.Machine) :
 (after machine slot).store (selected machine slot) = 0 :=
 TargetArrayClear.after_header _ _ _

/-- Only the selected child's OLD live prefix is cleared; every older inner
shadow remains exactly its original raw word. -/
theorem child_data (slot : Evm.Slot) (machine : Evm.Machine) (j : Nat) :
 (after machine slot).store (.data (selected machine slot) j) =
 if j < machine.store (selected machine slot) then 0 else machine.store (.data (selected machine slot) j) := by
 unfold after
 rw [TargetArrayClear.after_data]
 simp only [decremented,selected,Evm.WordStore.write_other _ _ (child_ne_root slot _),
   Evm.WordStore.write_other _ _ (grand_ne_root slot _ j)]

theorem other_child_header (slot : Evm.Slot) (machine : Evm.Machine) (i : Nat)
 (other : i ≠ machine.store slot - 1) :
 (after machine slot).store (.data slot i) = machine.store (.data slot i) := by
 unfold after
 rw [TargetArrayClear.after_outside _ _ _ (.data slot i)
   (by intro same; exact other (Evm.Slot.data.inj same).2)
   (by intro j _; exact child_ne_grand slot i _ j)]
 exact Evm.WordStore.write_other _ _ (child_ne_root slot i)

theorem other_child_data (slot : Evm.Slot) (machine : Evm.Machine) (i j : Nat)
 (other : i ≠ machine.store slot - 1) :
 (after machine slot).store (.data (.data slot i) j) = machine.store (.data (.data slot i) j) := by
 unfold after selected
 rw [TargetArrayClear.after_outside _ _ _ (.data (.data slot i) j)
   (Ne.symm (child_ne_grand slot _ i j))
   (by intro k _ same; exact other (Evm.Slot.data.inj (Evm.Slot.data.inj same).1).2)]
 exact Evm.WordStore.write_other _ _ (grand_ne_root slot i j)

/-- Arbitrary raw symbolic observer frame with explicit actual access exclusions. -/
theorem outside (slot : Evm.Slot) (machine : Evm.Machine) (observer : Evm.Slot)
 (outerApart : observer ≠ slot) (childApart : observer ≠ selected machine slot)
 (dataApart : ∀ j, j < machine.store (selected machine slot) → observer ≠ .data (selected machine slot) j) :
 (after machine slot).store observer = machine.store observer := by
 unfold after
 rw [TargetArrayClear.after_outside _ _ _ observer childApart
   (by intro j inside; apply dataApart j; simpa only [decremented,selected,Evm.WordStore.write_other _ _ (child_ne_root slot _)] using inside)]
 exact Evm.WordStore.write_other _ _ outerApart

theorem context (slot : Evm.Slot) (machine : Evm.Machine) :
 (after machine slot).stack = machine.stack ∧ (after machine slot).mem = machine.mem ∧
 (after machine slot).bal = machine.bal ∧ (after machine slot).bal₀ = machine.bal₀ ∧
 (after machine slot).self = machine.self ∧ (after machine slot).caller = machine.caller ∧
 (after machine slot).callvalue = machine.callvalue ∧ (after machine slot).timestamp = machine.timestamp ∧
 (after machine slot).accepts = machine.accepts := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Successful outer-header correspondence to the EXISTING intrinsic pop;
selected child/payload representation is a separate operation bridge. -/
theorem graph_outer_header {n : Nat} {G : Schema n} {p : PrimTy}
 (old result : Value G (.array (.array (.prim p)))) (popped : recursivePop old = some result)
 (slot : Evm.Slot) (machine : Evm.Machine) (header : machine.store slot = old.length.val) :
 (after machine slot).store slot = result.length.val ∧ result.extent = old.extent := by
 have oldResult := recursivePop_header old result popped
 rw [outer_header,header]
 exact ⟨by omega,oldResult.2⟩

/-- info: 'Solidity.Backend.StorageOps.TargetNestedPop.run_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_select
/-- info: 'Solidity.Backend.StorageOps.TargetNestedPop.run_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_current
/-- info: 'Solidity.Backend.StorageOps.TargetNestedPop.failure_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms failure_matches
/-- info: 'Solidity.Backend.StorageOps.TargetNestedPop.outer_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms outer_header
/-- info: 'Solidity.Backend.StorageOps.TargetNestedPop.child_header' depends on axioms: [propext] -/
#guard_msgs in #print axioms child_header
/-- info: 'Solidity.Backend.StorageOps.TargetNestedPop.child_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms child_data
/-- info: 'Solidity.Backend.StorageOps.TargetNestedPop.other_child_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms other_child_header
/-- info: 'Solidity.Backend.StorageOps.TargetNestedPop.other_child_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms other_child_data
/-- info: 'Solidity.Backend.StorageOps.TargetNestedPop.outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms outside
/-- info: 'Solidity.Backend.StorageOps.TargetNestedPop.context' does not depend on any axioms -/
#guard_msgs in #print axioms context
/-- info: 'Solidity.Backend.StorageOps.TargetNestedPop.graph_outer_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms graph_outer_header
end Solidity.Backend.StorageOps.TargetNestedPop
