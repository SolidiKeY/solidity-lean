import SolidityBridge.RoadmapV15.P10.StorageOwnerFixtures

/-! Same numeric slot at a different owner: actual post-SLOAD cost probes.
These clients do not assert that a following opcode supplies the probe or gas. -/
namespace SolidityBridge.RoadmapV15.P10.StorageOwnerControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open StorageOwnerFixtures

/-- The published universal law instantiated with distinct owners and equal slots. -/
theorem different_owner_cost (warm : Bool) :
    EVM.C' (ownerProbe warm) .SLOAD = EVM.C' (beforeProbe warm) .SLOAD :=
  sload_distinct_cost (ownerSample warm) (u 13) (u 13) (.ofNat 11) spill 2100 (by decide +revert)

theorem populated_controls :
(let probe := SolidityBridge.RoadmapV15.P10.StorageOwnerFixtures.ownerProbe;
let next := SolidityBridge.RoadmapV15.P10.StorageOwnerFixtures.ownerNext;
let u := SolidityBridge.RoadmapV15.P10.StorageOwnerFixtures.u;
 EvmYul.EVM.C' (probe false) .SLOAD = 2100 ∧ EvmYul.EVM.C' (probe true) .SLOAD = 100 ∧
 EvmYul.EVM.C' {next false with stack := [u 13,u 258,u 513]} .SLOAD = 100 ∧
 (next false).executionEnv.codeOwner ≠ (probe false).executionEnv.codeOwner ∧
 (probe false).stack = [u 13,u 258,u 513] ∧
 (probe false).memory.data.toList = [0xaa,0xbb] ∧
 (probe false).executionEnv.code.data.toList = [0x60,0x54,0x50,0x54,0x00] ∧
 (probe false).returnData.data.toList = [0xcc,0xdd] ∧
 (probe false).H_return.data.toList = [0xee,0xff] ∧
 (probe false).executionEnv.calldata.data.toList = [0x11,0x22,0x33])
 := by
  decide

#print axioms different_owner_cost
#print axioms populated_controls
end SolidityBridge.RoadmapV15.P10.StorageOwnerControls
