import SolidityBridge.RoadmapV15.P10.StorageWarmTransport

/-! Populated controls of the actual distinct-key resource observation.
Cold/warm clients consume the producer; the same-pair counterexample shows
why actual numeric pair separation is required. These are cost probes,
not additional fetched-execution or next-read adequacy proofs. -/
namespace SolidityBridge.RoadmapV15.P10.StorageIsolationControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
private def u (n : Nat) : UInt256 := .ofNat n
private def spill : List UInt256 := [u 258,u 513]
private def sample (warm : Bool) : EVM.State :=
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
private def afterRead (warm : Bool) : EVM.State :=
  ({Assembly.chargedPrepare (sample warm) 2100 with
    toState := (EvmYul.State.sload (sample warm).toState (u 13)).1}).replaceStackAndIncrPC
      ((EvmYul.State.sload (sample warm).toState (u 13)).2::spill)

theorem cold_distinct_client :
    EVM.C' {afterRead false with stack := u 14::spill} .SLOAD = 2100 := by
  exact sload_distinct_cost (sample false) (u 13) (u 14) (.ofNat 7) spill 2100 (by decide)

theorem warm_distinct_client :
    EVM.C' {afterRead true with stack := u 14::spill} .SLOAD = 100 := by
  exact sload_distinct_cost (sample true) (u 13) (u 14) (.ofNat 7) spill 2100 (by decide)

theorem same_pair_counterexample :
    EVM.C' (sample false) .SLOAD ≠ EVM.C' {afterRead false with stack := u 13::spill} .SLOAD := by
  decide +kernel

theorem complete_ordered_observations :
    (afterRead false).stack = [u 513,u 258,u 513] ∧
    (afterRead false).executionEnv.code.data.toList = [0x60,0x54,0x50,0x54,0x00] ∧
    (afterRead false).memory.data.toList = [0xaa,0xbb] ∧
    (afterRead false).returnData.data.toList = [0xcc,0xdd] ∧
    (afterRead false).H_return.data.toList = [0xee,0xff] ∧
    (afterRead false).executionEnv.calldata.data.toList = [0x11,0x22,0x33] := by
  decide +kernel

#print axioms cold_distinct_client
#print axioms warm_distinct_client
#print axioms same_pair_counterexample
#print axioms complete_ordered_observations
end SolidityBridge.RoadmapV15.P10.StorageIsolationControls
