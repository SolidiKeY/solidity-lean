import Solidity.Backend.StorageOps.PrimitiveCycleProgram

/-! Whole symbolic target Machine laws use actual current headers, with no
legacy metadata or selected representation premises. Symbolic Slot separation
is not a global physical hash-injectivity or ordinary Source/world claim. -/
namespace Solidity.Backend.StorageOps.PrimitiveCycleMachine

def afterPop (machine : Evm.Machine) (slot : Evm.Slot) : Evm.Machine :=
 {machine with store := Evm.WordStore.write (Evm.WordStore.write machine.store slot (machine.store slot-1)) (.data slot (machine.store slot-1)) 0}

def afterPush (machine : Evm.Machine) (slot : Evm.Slot) : Evm.Machine :=
 {machine with store := Evm.WordStore.write (Evm.WordStore.write machine.store slot (machine.store slot+1)) (.data slot (machine.store slot)) 0}

/-- Derive actual first-pop header and cleared selected slot, including any
nonzero retained data elsewhere. These facts are not caller assumptions. -/
theorem pop_observations (machine : Evm.Machine) (slot : Evm.Slot) :
 (afterPop machine slot).store slot=machine.store slot-1 ∧
 (afterPop machine slot).store (.data slot (machine.store slot-1))=0 := by
 constructor
 · unfold afterPop
   rw [Evm.WordStore.write_other _ _ (Evm.Slot.ne_data _ _)]
   exact Evm.WordStore.write_same_of_lt _ _ _ (by have h:=Evm.WordStore.read_lt machine.store slot; omega)
 · exact Evm.WordStore.write_same_of_lt _ _ _ Evm.W_pos

/-- Actual push then pop restores the ENTIRE machine exactly when this selected
slot is already zero. Every older shadow and non-store context is retained. -/
theorem after_reuse (machine : Evm.Machine) (slot : Evm.Slot)
 (room : machine.store slot+1<Evm.W)
 (cleared : machine.store (.data slot (machine.store slot))=0) :
 afterPop (afterPush machine slot) slot=machine := by
 have header : (afterPush machine slot).store slot=machine.store slot+1 := by
  unfold afterPush
  rw [Evm.WordStore.write_other _ _ (Evm.Slot.ne_data _ _)]
  exact Evm.WordStore.write_same_of_lt _ _ _ room
 unfold afterPop
 rw [header,Nat.add_sub_cancel]
 have stores : Evm.WordStore.write (Evm.WordStore.write (afterPush machine slot).store slot (machine.store slot)) (.data slot (machine.store slot)) 0 = machine.store := by
  apply Evm.WordStore.ext
  intro observer
  by_cases root : observer=slot
  · subst observer
    rw [Evm.WordStore.write_other _ _ (Evm.Slot.ne_data _ _)]
    exact Evm.WordStore.write_same_of_lt _ _ _ (Evm.WordStore.read_lt _ _)
  · by_cases child : observer=Evm.Slot.data slot (machine.store slot)
    · subst observer
      rw [Evm.WordStore.write_same_of_lt _ _ _ Evm.W_pos]
      exact cleared.symm
    · unfold afterPush
      rw [Evm.WordStore.write_other _ _ child,Evm.WordStore.write_other _ _ root,
       Evm.WordStore.write_other _ _ child,Evm.WordStore.write_other _ _ root]
 rw [stores]
 rfl

/-- The existing CURRENT-header guarded push/reset and pop programs run;
capacity and zero selected payload are exact, non-vacuous reuse premises. -/
theorem run_reuse (machine : Evm.Machine) (slot : Evm.Slot)
 (room : machine.store slot+1<Evm.W)
 (cleared : machine.store (.data slot (machine.store slot))=0) :
 Evm.run (TargetPrimitivePush.code slot ++ TargetPrimitivePop.code slot) machine=.ok machine 0 := by
 have header : (afterPush machine slot).store slot=machine.store slot+1 := by
  unfold afterPush
  rw [Evm.WordStore.write_other _ _ (Evm.Slot.ne_data _ _)]
  exact Evm.WordStore.write_same_of_lt _ _ _ room
 rw [Evm.run_append_ok (m' := afterPush machine slot)
  (by rw [TargetPrimitivePush.run_current,if_pos room]; rfl),TargetPrimitivePop.run_current,
  if_neg (by rw [header]; omega)]
 exact congrArg (fun m => Evm.Out.ok m 0) (after_reuse machine slot room cleared)

/-- For EVERY runtime header, the actual primitive triple equals its initial
pop outcome as an entire Machine, including all storage and context. No desired
middle equality/zero/capacity, finite query, graph length or lmax is assumed. -/
theorem run_cycle (machine : Evm.Machine) (slot : Evm.Slot) :
 Evm.run (PrimitiveCycleProgram.code slot) machine =
 if machine.store slot=0 then .revert else .ok (afterPop machine slot) 0 := by
 by_cases empty : machine.store slot=0
 · rw [if_pos empty]
   exact PrimitiveCycleProgram.run_empty slot machine empty
 · have room : (afterPop machine slot).store slot+1<Evm.W := by
    rw [(pop_observations machine slot).1]
    have h:=Evm.WordStore.read_lt machine.store slot
    omega
   have cleared : (afterPop machine slot).store (.data slot ((afterPop machine slot).store slot))=0 := by
    rw [(pop_observations machine slot).1]
    exact (pop_observations machine slot).2
   unfold PrimitiveCycleProgram.code TargetPrimitivePopPush.code
   rw [List.append_assoc,if_neg empty,Evm.run_append_ok (m' := afterPop machine slot)
    (by rw [TargetPrimitivePop.run_current,if_neg empty]; rfl)]
   exact run_reuse _ _ room cleared

/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleMachine.pop_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_observations
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleMachine.after_reuse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms after_reuse
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleMachine.run_reuse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_reuse
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleMachine.run_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_cycle
end Solidity.Backend.StorageOps.PrimitiveCycleMachine
