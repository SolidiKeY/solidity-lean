import Solidity.Backend.StorageOps.NestedPopRegrow

/-! Actual current-header push/pop on an already-cleared retained child.
Whole Machine equality includes older shadows and non-store context; this is
structured intrinsic EVM execution, not Source/compiler/world closure. -/
namespace Solidity.Backend.StorageOps.TargetRetainedCycle

def code (slot : Evm.Slot) : List Evm.Instr :=
 TargetHeaderPush.code slot ++ TargetNestedPop.code slot

def popRegrowPop (slot : Evm.Slot) : List Evm.Instr :=
 TargetNestedPop.code slot ++ code slot

private theorem clear_empty (machine : Evm.Machine) (slot : Evm.Slot)
 (empty : machine.store slot = 0) :
 TargetArrayClear.afterClear machine machine.stack slot = machine := by
 have unchanged : Evm.WordStore.write machine.store slot 0 = machine.store := by
  apply Evm.WordStore.ext
  intro observer
  by_cases same : observer = slot
  · subst observer
    rw [Evm.WordStore.write_same]
    exact empty.symm
  · exact Evm.WordStore.write_other _ _ same
 unfold TargetArrayClear.afterClear
 rw [empty,TargetArrayClear.clearPrefix,unchanged]

private theorem decrement_increment (machine : Evm.Machine) (slot : Evm.Slot)
 (room : machine.store slot + 1 < Evm.W) :
 TargetNestedPop.decremented (TargetHeaderPush.incremented slot machine) slot = machine := by
 have header : (TargetHeaderPush.incremented slot machine).store slot = machine.store slot + 1 :=
  Evm.WordStore.write_same_of_lt _ _ _ room
 have unchanged : Evm.WordStore.write (Evm.WordStore.write machine.store slot (machine.store slot + 1)) slot (machine.store slot) = machine.store := by
  apply Evm.WordStore.ext
  intro observer
  by_cases same : observer = slot
  · subst observer
    exact Evm.WordStore.write_same_of_lt _ _ _ (Evm.WordStore.read_lt _ _)
  · rw [Evm.WordStore.write_other _ _ same,Evm.WordStore.write_other _ _ same]
 unfold TargetNestedPop.decremented
 rw [header,Nat.add_sub_cancel]
 change {machine with store := Evm.WordStore.write (Evm.WordStore.write machine.store slot (machine.store slot+1)) slot (machine.store slot)} = machine
 rw [unchanged]

/-- Header regrowth followed by actual nested pop returns the ENTIRE input
Machine when the reused child is already empty; its retained data may be nonzero. -/
theorem after_reuse (machine : Evm.Machine) (slot : Evm.Slot)
 (room : machine.store slot + 1 < Evm.W)
 (empty : machine.store (.data slot (machine.store slot)) = 0) :
 TargetNestedPop.after (TargetHeaderPush.incremented slot machine) slot = machine := by
 have header : (TargetHeaderPush.incremented slot machine).store slot = machine.store slot + 1 :=
  Evm.WordStore.write_same_of_lt _ _ _ room
 unfold TargetNestedPop.after TargetNestedPop.selected
 rw [header,Nat.add_sub_cancel,decrement_increment machine slot room]
 exact clear_empty machine _ empty

/-- Both actual instruction programs execute, with capacity checked from SLOAD.
The zero-child premise constrains only its header, never its retained tail. -/
theorem run_reuse (machine : Evm.Machine) (slot : Evm.Slot)
 (room : machine.store slot + 1 < Evm.W)
 (empty : machine.store (.data slot (machine.store slot)) = 0) :
 Evm.run (code slot) machine = .ok machine 0 := by
 have header : (TargetHeaderPush.incremented slot machine).store slot = machine.store slot + 1 :=
  Evm.WordStore.write_same_of_lt _ _ _ room
 unfold code
 rw [Evm.run_append_ok (m' := TargetHeaderPush.incremented slot machine)
   (by rw [TargetHeaderPush.run_current,if_pos room]),TargetNestedPop.run_current,
   if_neg (by rw [header]; omega),after_reuse machine slot room empty]

/-- A successful initial pop DERIVES capacity and cleared selected header for
reuse. No middle zero, final equality or preservation theorem is assumed. -/
theorem run_pop_regrow_pop (machine : Evm.Machine) (slot : Evm.Slot) :
 Evm.run (popRegrowPop slot) machine =
 if machine.store slot = 0 then .revert else .ok (TargetNestedPop.after machine slot) 0 := by
 by_cases empty : machine.store slot = 0
 · unfold popRegrowPop
   rw [if_pos empty]
   apply Evm.run_append_revert
   rw [TargetNestedPop.run_current,if_pos empty]
 · have room : (TargetNestedPop.after machine slot).store slot + 1 < Evm.W := by
    rw [TargetNestedPop.outer_header]
    have bound := Evm.WordStore.read_lt machine.store slot
    omega
   have cleared : (TargetNestedPop.after machine slot).store
       (.data slot ((TargetNestedPop.after machine slot).store slot)) = 0 := by
    rw [TargetNestedPop.outer_header]
    exact TargetNestedPop.child_header slot machine
   unfold popRegrowPop
   rw [if_neg empty,Evm.run_append_ok (m' := TargetNestedPop.after machine slot)
     (by rw [TargetNestedPop.run_current,if_neg empty]),run_reuse _ _ room cleared]

/-- info: 'Solidity.Backend.StorageOps.TargetRetainedCycle.after_reuse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms after_reuse
/-- info: 'Solidity.Backend.StorageOps.TargetRetainedCycle.run_reuse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_reuse
/-- info: 'Solidity.Backend.StorageOps.TargetRetainedCycle.run_pop_regrow_pop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_pop_regrow_pop
end Solidity.Backend.StorageOps.TargetRetainedCycle
