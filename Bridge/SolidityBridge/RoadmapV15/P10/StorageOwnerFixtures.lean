import SolidityBridge.RoadmapV15.P10.StorageWarmTransport

/-! Populated owner-isolation cost-probe fixtures. No new transition relation. -/
namespace SolidityBridge.RoadmapV15.P10.StorageOwnerFixtures
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
def u (n : Nat) : UInt256 := .ofNat n
def spill : List UInt256 := [u 258,u 513]
def sample (warm : Bool) : EVM.State :=
  {(default : EVM.State) with
    pc := u 3,execLength := 41,gasAvailable := u 2300,activeWords := u 3
    stack := u 13::spill,memory := ⟨#[0xaa,0xbb]⟩
    returnData := ⟨#[0xcc,0xdd]⟩,H_return := ⟨#[0xee,0xff]⟩
    executionEnv := {(default : EVM.State).executionEnv with
      codeOwner := .ofNat 7,source := .ofNat 11,sender := .ofNat 19,perm := false
      code := ⟨#[0x60,0x54,0x50,0x54,0x00]⟩,calldata := ⟨#[0x11,0x22,0x33]⟩}
    substate := if warm then (default : Substate).addAccessedStorageKey (.ofNat 7,u 14) else default
    accountMap := ((∅ : AccountMap .EVM).insert (.ofNat 7)
      {(default : Account .EVM) with
        nonce := u 3,balance := u 29,storage := (∅ : Storage).insert (u 13) (u 513)
        tstorage := (∅ : Storage).insert (u 13) (u 77)}).insert (.ofNat 11)
      {(default : Account .EVM) with nonce := u 5,balance := u 41}}
def afterRead (warm : Bool) : EVM.State :=
  ({Assembly.chargedPrepare (sample warm) 2100 with
    toState := (EvmYul.State.sload (sample warm).toState (u 13)).1}).replaceStackAndIncrPC
      ((EvmYul.State.sload (sample warm).toState (u 13)).2::spill)

/-- Warmness at another owner is independent of the read owner's same key. -/
def ownerSample (warm : Bool) : EVM.State :=
  {sample false with substate := if warm then
    (sample false).substate.addAccessedStorageKey (.ofNat 11,u 13) else (sample false).substate}
def ownerNext (warm : Bool) : EVM.State :=
  ({Assembly.chargedPrepare (ownerSample warm) 2100 with
    toState := (EvmYul.State.sload (ownerSample warm).toState (u 13)).1}).replaceStackAndIncrPC
      ((EvmYul.State.sload (ownerSample warm).toState (u 13)).2::spill)
def ownerProbe (warm : Bool) : EVM.State :=
  {ownerNext warm with stack := u 13::spill,executionEnv := {(ownerNext warm).executionEnv with codeOwner := .ofNat 11}}
def beforeProbe (warm : Bool) : EVM.State :=
  {ownerSample warm with stack := u 13::spill,executionEnv := {(ownerSample warm).executionEnv with codeOwner := .ofNat 11}}
end SolidityBridge.RoadmapV15.P10.StorageOwnerFixtures
