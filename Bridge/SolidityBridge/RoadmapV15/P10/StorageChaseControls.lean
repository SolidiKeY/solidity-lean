import SolidityBridge.RoadmapV15.P10.StorageChaseFixtures

/-! Complete-State actual two-read clients with value!=key, sameKey and local/otherWarm
warmth controls. Scalar/compiler symbolic-path and world correspondence stay open. -/
namespace SolidityBridge.RoadmapV15.P10.StorageChaseControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open StorageChaseFixtures

private theorem execute (sameKey warm otherWarm perm : Bool) (rest : List UInt256) (room : rest.length+1 ≤ 1024) :
    Assembly.driverSteps 2 4 #[] (input 4200 sameKey warm otherWarm perm rest) =
      .ok (storageChaseOutput (seed 4200 sameKey warm otherWarm perm) before after (u 13) rest) ∧
    EVM.X 4 #[] (input 4200 sameKey warm otherWarm perm rest) =
      EVM.X 2 #[] (storageChaseOutput (seed 4200 sameKey warm otherWarm perm) before after (u 13) rest) := by
  exact storage_chase_uniform_budget (seed 4200 sameKey warm otherWarm perm) before after (u 13) rest fits room (by change (4200 : Nat) ≤ 4200;decide) 1

theorem nonalias_cold :
    Assembly.driverSteps 2 4 #[] (input 4200 false false false false tail) =
      .ok (expected 4200 false false false false tail 99 4200) ∧
    EVM.X 4 #[] (input 4200 false false false false tail) =
      EVM.X 2 #[] (expected 4200 false false false false tail 99 4200) := by
  exact execute false false false false tail (by decide)

theorem alias_warm_second :
    Assembly.driverSteps 2 4 #[] (input 4200 true false false true tail) =
      .ok (expected 4200 true false false true tail 13 2200) ∧
    EVM.X 4 #[] (input 4200 true false false true tail) =
      EVM.X 2 #[] (expected 4200 true false false true tail 13 2200) := by
  exact execute true false false true tail (by decide)

theorem local_and_foreign_warmth :
    Assembly.driverSteps 2 4 #[] (input 4200 false true false false tail) =
      .ok (expected 4200 false true false false tail 99 2200) ∧
    Assembly.driverSteps 2 4 #[] (input 4200 false false true false tail) =
      .ok (expected 4200 false false true false tail 99 4200) := by
  exact ⟨(execute false true false false tail (by decide)).1,(execute false false true false tail (by decide)).1⟩

theorem full_input_stack :
    Assembly.driverSteps 2 4 #[] (input 4200 false false false false (List.replicate 1023 (u 769))) =
      .ok (expected 4200 false false false false (List.replicate 1023 (u 769)) 99 4200) := by
  exact (execute false false false false _ (by simp only [List.length_replicate];decide)).1

theorem exact_budget_and_refusals :
    Assembly.driverSteps 2 4 #[] (input 2200 true false false false tail) =
      .ok (expected 2200 true false false false tail 13 2200) ∧
    Assembly.driverSteps 2 3 #[] (input 2200 false false false false tail) = .error .OutOfGass ∧
    Assembly.driverSteps 2 3 #[] (input 2099 false false false false tail) = .error .OutOfGass ∧
    Assembly.driverSteps 2 2 #[] (input 4200 false false false false tail) = .error .OutOfFuel ∧
    Assembly.driverSteps 2 3 #[] (storageChaseInput (seed 4200 false false false false) before after (u 13) []) =
      .ok (expected 4200 false false false false [] 99 4200) ∧
    Assembly.driverSteps 2 3 #[] {(input 4200 false false false false []) with stack := []} = .error .StackUnderflow := by
  constructor
  · exact (storage_chase_execution (seed 2200 true false false false) before after (u 13) tail fits (by decide) (by decide) 1).1
  · exact ⟨rfl,rfl,rfl,
      (storage_chase_uniform_budget (seed 4200 false false false false) before after (u 13) [] fits (by decide) (by decide) 0).1,rfl⟩

theorem storage_transient_frame (probe : UInt256) :
    Solidity.Evm.StorageSlots.storageRead (storageChaseOutput (seed 4200 false false false false) before after (u 13) tail).toState =
      Solidity.Evm.StorageSlots.storageRead (input 4200 false false false false tail).toState ∧
    (EvmYul.State.tload (storageChaseOutput (seed 4200 false false false false) before after (u 13) tail).toState probe).2 =
      (EvmYul.State.tload (input 4200 false false false false tail).toState probe).2 := by
  exact ⟨storage_chase_storage_frame _ _ _ _ _,storage_chase_transient_frame _ _ _ _ _ _⟩

theorem values_and_ordered_observations :
    storageChaseValue (seed 4200 false false false false) before after (u 13) tail = u 17 ∧
    storageChaseCharge (seed 4200 false false false false) before after (u 13) tail = 4200 ∧
    storageChaseCharge (seed 4200 true false false true) before after (u 13) tail = 2200 ∧
    storageChaseCharge (seed 4200 false true false false) before after (u 13) tail = 2200 ∧
    storageChaseCharge (seed 4200 false false true false) before after (u 13) tail = 4200 ∧
    (storageChaseOutput (seed 4200 false false false false) before after (u 13) tail).stack ≠ [u 17,u 258,u 513] ∧
    (input 4200 false false false false tail).executionEnv.code.data.toList = [0x60,0x54,0x50,0x54,0x54,0x00] ∧
    (storageChaseFirst (seed 4200 false false false false) before after (u 13) tail).stack = [u 17,u 258,u 513] ∧
    (storageChaseFirst (seed 4200 false false false false) before after (u 13) tail).gasAvailable.toNat = 2100 ∧
    (expected 4200 false false false false tail 99 4200).stack = [u 99,u 258,u 513] ∧
    (expected 4200 false false false false tail 99 4200).pc.toNat = 5 ∧
    (expected 4200 false false false false tail 99 4200).gasAvailable.toNat = 0 ∧
    (expected 4200 false false false false tail 99 4200).execLength = 43 ∧
    (expected 4200 false false false false tail 99 4200).substate.accessedStorageKeys.contains (.ofNat 7,u 13) = true ∧
    (expected 4200 false false false false tail 99 4200).substate.accessedStorageKeys.contains (.ofNat 7,u 17) = true ∧
    (EvmYul.State.tload (expected 4200 false false false false tail 99 4200).toState (u 13)).2 = u 77 ∧
    (EvmYul.State.tload (expected 4200 false false false false tail 99 4200).toState (u 17)).2 = u 88 ∧
    (expected 4200 false false false false tail 99 4200).memory.data.toList = ([0xaa,0xbb] : List UInt8) ++ List.replicate 30 0 ∧
    (expected 4200 false false false false tail 99 4200).returnData.data.toList = [0xcc,0xdd] ∧
    (expected 4200 false false false false tail 99 4200).H_return.data.toList = [0xee,0xff] ∧
    (expected 4200 false false false false tail 99 4200).executionEnv.calldata.data.toList = [0x11,0x22,0x33] := by
  decide


/-- Direct inhabited consumers of both arms of the general second-charge law. -/
theorem charge_producer_clients :
    EVM.C' (storageChaseFirst (seed 4200 false false false false) before after (u 13) tail) .SLOAD =
      EVM.C' {(input 4200 false false false false tail) with stack := u 17::tail} .SLOAD ∧
    EVM.C' (storageChaseFirst (seed 4200 true false false true) before after (u 13) tail) .SLOAD = 100 := by
  have distinct := storage_chase_second_charge (seed 4200 false false false false) before after (u 13) tail
  have value : storageChaseValue (seed 4200 false false false false) before after (u 13) tail = u 17 := rfl
  have apart : u 17 ≠ u 13 := by decide
  rw [value,if_neg apart] at distinct
  have same := storage_chase_second_charge (seed 4200 true false false true) before after (u 13) tail
  have fixed : storageChaseValue (seed 4200 true false false true) before after (u 13) tail = u 13 := rfl
  rw [fixed,if_pos rfl] at same
  exact ⟨distinct,same⟩

#print axioms charge_producer_clients
#print axioms nonalias_cold
#print axioms alias_warm_second
#print axioms local_and_foreign_warmth
#print axioms full_input_stack
#print axioms exact_budget_and_refusals
#print axioms storage_transient_frame
#print axioms values_and_ordered_observations
end SolidityBridge.RoadmapV15.P10.StorageChaseControls
