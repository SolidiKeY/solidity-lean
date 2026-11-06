import SolidityBridge.RoadmapV15.P10.StorageWarmTransport

/-! Populated controls for `StorageWarmTransport`: a two-read success (the stored
value equals its key), a cold-key gas refusal, wrong owner/key and transient
negatives. -/
namespace SolidityBridge.RoadmapV15.P10.StorageWarmControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
private def u (n : Nat) : UInt256 := .ofNat n
private def tail : List UInt256 := [u 258,u 513]
private def seed : EVM.State :=
  {(default : EVM.State) with
    execLength := 41,gasAvailable := u 2200,activeWords := u 3
    memory := ⟨#[0xaa,0xbb]⟩,returnData := ⟨#[0xcc,0xdd]⟩,H_return := ⟨#[0xee,0xff]⟩
    executionEnv := {(default : EVM.State).executionEnv with
      codeOwner := .ofNat 7
      source := .ofNat 11,sender := .ofNat 19,perm := false,calldata := ⟨#[0x11,0x22,0x33]⟩}
    accountMap := ((∅ : AccountMap .EVM).insert (.ofNat 7)
      {(default : Account .EVM) with
        nonce := u 3,balance := u 29
        storage := ((∅ : Storage).insert (u 13) (u 13)).insert (u 14) (u 513)
        tstorage := (∅ : Storage).insert (u 13) (u 77)}).insert (.ofNat 11)
      {(default : Account .EVM) with
        nonce := u 5,balance := u 41
        storage := (∅ : Storage).insert (u 13) (u 4097)}}
private def base : Site .SLOAD := ⟨seed,[.push ⟨1,by decide⟩ #v[0x54],.op .POP],[.op .SLOAD,.op .STOP],by decide⟩
private def input (key : UInt256) : EVM.State := (slotReadSite base key tail).state
private def next (key value : UInt256) : EVM.State :=
  {input key with
    pc := u 4,gasAvailable := u 100,execLength := 42,stack := value::tail
    substate := (input key).substate.addAccessedStorageKey ((input key).executionEnv.codeOwner,key)}
private def twice : EVM.State := {next (u 13) (u 13) with pc := u 5,gasAvailable := u 0,execLength := 43,substate := (next (u 13) (u 13)).substate.addAccessedStorageKey ((next (u 13) (u 13)).executionEnv.codeOwner,u 13)}

theorem producer_client :
    Assembly.driverSteps 1 2 #[] (input (u 13)) = .ok (next (u 13) (u 13)) ∧
    EVM.X 2 #[] (input (u 13)) = EVM.X 1 #[] (next (u 13) (u 13)) ∧
    EVM.C' {next (u 13) (u 13) with stack := u 13::tail} .SLOAD = 100 ∧
    Solidity.Evm.StorageSlots.storageRead (next (u 13) (u 13)).toState = Solidity.Evm.StorageSlots.storageRead (input (u 13)).toState ∧
    (EvmYul.State.tload (next (u 13) (u 13)).toState (u 13)).2 = (EvmYul.State.tload (input (u 13)).toState (u 13)).2 := by
  have h := sload_resource_frame base (u 13) (u 13) tail (by decide)
    (by change 2100 ≤ 2200;decide) 0
  dsimp only at h
  rw [sload_read_shape] at h
  simpa only [base,slotReadSite,Site.state,seed,input,next,u] using h

theorem same_key_two_fetched_reads :
    Assembly.driverSteps 2 3 #[] (input (u 13)) = .ok twice := by
  rfl

theorem value_is_different_next_key :
    Assembly.driverSteps 2 3 #[] (input (u 14)) = .error .OutOfGass := by
  rfl

theorem wrong_key_stays_cold :
    EVM.C' {next (u 13) (u 13) with stack := u 14::tail} .SLOAD = 2100 := by
  rfl

theorem wrong_owner_stays_cold :
    EVM.C' {next (u 13) (u 13) with executionEnv := {(next (u 13) (u 13)).executionEnv with
      codeOwner := .ofNat 11}} .SLOAD = 2100 := by
  rfl

theorem transient_does_not_warm :
    let transient := ({Assembly.chargedPrepare (input (u 13)) 100 with toState := (EvmYul.State.tload (input (u 13)).toState (u 13)).1}).replaceStackAndIncrPC (u 77::tail)
    EVM.C' {transient with stack := u 13::tail} .SLOAD = 2100 := by
  rfl

theorem values_distinct :
    (EvmYul.State.sload seed.toState (u 13)).2 = u 13 ∧
    (EvmYul.State.tload seed.toState (u 13)).2 = u 77 ∧ u 13 ≠ u 77 := by
  decide +kernel

theorem ordered_observations :
    (input (u 13)).executionEnv.code.data.toList = [0x60,0x54,0x50,0x54,0x54,0x00] ∧
    twice.stack = [u 13,u 258,u 513] ∧ twice.memory.data.toList = [0xaa,0xbb] ∧
    twice.returnData.data.toList = [0xcc,0xdd] ∧ twice.H_return.data.toList = [0xee,0xff] ∧
    twice.executionEnv.calldata.data.toList = [0x11,0x22,0x33] := by
  decide +kernel
#print axioms producer_client
#print axioms same_key_two_fetched_reads
#print axioms value_is_different_next_key
#print axioms wrong_key_stays_cold
#print axioms wrong_owner_stays_cold
#print axioms transient_does_not_warm
#print axioms values_distinct
#print axioms ordered_observations
end SolidityBridge.RoadmapV15.P10.StorageWarmControls
