import SolidityBridge.RoadmapV15.P10.StorageChaseCost

/-! Populated numeric-reference data, including a genuine13->17->99 chain.
Warmth is keyed by actual owner/key pairs; no compiler source profile is added. -/
namespace SolidityBridge.RoadmapV15.P10.StorageChaseFixtures
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def u (n : Nat) : UInt256 := .ofNat n
def tail : List UInt256 := [u 258,u 513]
def before : Backend.Program := [.push ⟨1,by decide⟩ #v[0x54],.op .POP]
def after : Backend.Program := [.op .STOP]
def accounts (sameKey : Bool) : AccountMap .EVM :=
  ((∅ : AccountMap .EVM).insert (.ofNat 7)
    {(default : Account .EVM) with
      nonce := u 3,balance := u 29
      storage := ((∅ : EvmYul.Storage).insert (u 13) (if sameKey then u 13 else u 17)).insert (u 17) (u 99)
      tstorage := ((∅ : EvmYul.Storage).insert (u 13) (u 77)).insert (u 17) (u 88)}).insert (.ofNat 11)
    {(default : Account .EVM) with
      nonce := u 5,balance := u 41
      storage := ((∅ : EvmYul.Storage).insert (u 13) (u 23)).insert (u 17) (u 55)}
def seed (gas : Nat) (sameKey warm otherWarm perm : Bool) : EVM.State :=
  {(default : EVM.State) with
    execLength := 41,gasAvailable := u gas,activeWords := u 1
    memory := ⟨(([0xaa,0xbb] : List UInt8) ++ List.replicate 30 0).toArray⟩
    returnData := ⟨#[0xcc,0xdd]⟩,H_return := ⟨#[0xee,0xff]⟩
    accountMap := accounts sameKey,σ₀ := accounts sameKey
    executionEnv := {(default : EVM.State).executionEnv with
      codeOwner := .ofNat 7,source := .ofNat 11,
      sender := .ofNat 19,perm := perm,calldata := ⟨#[0x11,0x22,0x33]⟩}
    substate := let base := if warm then (default : Substate).addAccessedStorageKey (.ofNat 7,u 17) else default
      if otherWarm then base.addAccessedStorageKey (.ofNat 11,u 17) else base}
def input (gas : Nat) (sameKey warm otherWarm perm : Bool) (rest : List UInt256) : EVM.State :=
  storageChaseInput (seed gas sameKey warm otherWarm perm) before after (u 13) rest
def expected (gas : Nat) (sameKey warm otherWarm perm : Bool) (rest : List UInt256) (value spent : Nat) : EVM.State :=
  {input gas sameKey warm otherWarm perm rest with
    pc := u 5,gasAvailable := u (gas-spent),execLength := 43
    stack := u value::rest
    substate := ((input gas sameKey warm otherWarm perm rest).substate.addAccessedStorageKey (.ofNat 7,u 13)).addAccessedStorageKey
      (.ofNat 7,if sameKey then u 13 else u 17)}
def fits : (Backend.encode (before ++ [.op .SLOAD])).length < UInt256.size := by decide
end SolidityBridge.RoadmapV15.P10.StorageChaseFixtures
