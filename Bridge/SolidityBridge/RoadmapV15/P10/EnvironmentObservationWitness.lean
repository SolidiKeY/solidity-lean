import SolidityBridge.RoadmapV15.P10.EnvironmentObservationProducer

/-! Minimal inhabited producer clients. Broader routine control coverage remains
open; these clients prove only the actual native clauses. -/
namespace SolidityBridge.RoadmapV15.P10.EnvironmentProducerWitness
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open EnvironmentTasksV1
private def u (n : Nat) : UInt256 := .ofNat n
private def seed (gas : Nat) : EVM.State :=
  {(default : EVM.State) with
    gasAvailable := u gas,execLength := 41,activeWords := u 3,stack := [u 258,u 513]
    memory := ⟨#[0xaa,0xbb]⟩,returnData := ⟨#[0xcc,0xdd]⟩,H_return := ⟨#[0xee,0xff]⟩
    executionEnv := {(default : EVM.State).executionEnv with
      codeOwner := .ofNat 7,source := .ofNat 11,sender := .ofNat 19,gasPrice := 37,perm := false
      calldata := ⟨#[0x11,0x22,0x33]⟩}
    accountMap := ((∅ : AccountMap .EVM).insert (.ofNat 7)
      {(default : Account .EVM) with nonce := u 3,balance := u 29}).insert (.ofNat 11)
      {(default : Account .EVM) with nonce := u 5,balance := u 41}}
private def site (op : Backend.Op) (gas : Nat := 9) : Site op :=
  ⟨seed gas,[.push ⟨1,by decide⟩ #v[0x32],.op .POP],[.op .STOP],by decide⟩
private def next (op : Backend.Op) (value : Nat) : EVM.State :=
  (Assembly.chargedPrepare (site op).state 2).replaceStackAndIncrPC [u value,u 258,u 513]
theorem origin_client : LocalFacts .ORIGIN (site .ORIGIN) ∧
    Assembly.driverSteps 1 2 #[] (site .ORIGIN).state = .ok (next .ORIGIN 19) ∧
    EVM.X 2 #[] (site .ORIGIN).state = EVM.X 1 #[] (next .ORIGIN 19) := by
  have facts : LocalFacts .ORIGIN (site .ORIGIN) := by
    simp only [LocalFacts]
    decide +kernel
  exact ⟨facts,origin_at (site .ORIGIN) facts 0 (by decide +kernel) (by decide +kernel)⟩

theorem gasprice_client : LocalFacts .GASPRICE (site .GASPRICE) ∧
    Assembly.driverSteps 1 2 #[] (site .GASPRICE).state = .ok (next .GASPRICE 37) ∧
    EVM.X 2 #[] (site .GASPRICE).state = EVM.X 1 #[] (next .GASPRICE 37) := by
  have facts : LocalFacts .GASPRICE (site .GASPRICE) := by
    simp only [LocalFacts]
    decide +kernel
  exact ⟨facts,gasprice_at (site .GASPRICE) facts 0 (by decide +kernel) (by decide +kernel)⟩

theorem chainid_client : LocalFacts .CHAINID (site .CHAINID) ∧
    Assembly.driverSteps 1 2 #[] (site .CHAINID).state = .ok (next .CHAINID EvmYul.chainId) ∧
    EVM.X 2 #[] (site .CHAINID).state = EVM.X 1 #[] (next .CHAINID EvmYul.chainId) := by
  have facts : LocalFacts .CHAINID (site .CHAINID) := by
    simp only [LocalFacts]
    decide +kernel
  exact ⟨facts,chainid_at (site .CHAINID) facts 0 (by decide +kernel) (by decide +kernel)⟩

theorem gas_refusal : Assembly.driverSteps 1 2 #[] (site .ORIGIN 1).state = .error .OutOfGass := by rfl

theorem fuel_precedes_gas : Assembly.driverSteps 1 1 #[] (site .ORIGIN 0).state = .error .OutOfFuel := by rfl

theorem origin_is_not_caller : (next .ORIGIN 19).stack.head? ≠ some (u 11) := by decide +kernel

#print axioms origin_client
#print axioms gasprice_client
#print axioms chainid_client
#print axioms gas_refusal
#print axioms fuel_precedes_gas
#print axioms origin_is_not_caller
end SolidityBridge.RoadmapV15.P10.EnvironmentProducerWitness
