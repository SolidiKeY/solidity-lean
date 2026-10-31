import SolidityBridge.ExternalEvm.TryMemoryDriver
import SolidityBridge.ExternalEvm.Assembly.Driver
import SolidityBridge.RoadmapV15.ReferenceImageTransport

/-! One concrete fetched MSTORE checkpoint for both published runtime inputs.
The input is explicitly positioned atPC4; original reachability/installation is
not asserted. Its12gas is exact for this single store (9expansion+3base), not a
whole-frame resource bound. Actual memory retains vendor serialization/padding.
This is neither Osaka agreement nor source/transaction/trace correspondence. -/
namespace SolidityBridge.RoadmapV15
open Solidity.Evm.TryByteImage EvmYul
open Solidity.Evm.External

def compiledStoreInput (p : Pipeline) (s : EVM.State) : EVM.State :=
  {s with
    pc := .ofNat 4, stack := [.ofNat 64, .ofNat 128]
    activeWords := .ofNat 0, memory := .empty, gasAvailable := .ofNat 12
    executionEnv := {s.executionEnv with
      perm := true
      code := match p with
        | .legacy => TryMemoryCode.legacyRuntime
        | .viaIR => TryMemoryCode.viaIRRuntime} }

def compiledStoreCharged (p : Pipeline) (s : EVM.State) : EVM.State :=
  {compiledStoreInput p s with gasAvailable := .ofNat 3}

/-- Expected record result using the actual vendor store, never another memory
operation or a claimed byte/padding specification. -/
def compiledStoreNext (p : Pipeline) (s : EVM.State) : EVM.State :=
  let q := {compiledStoreCharged p s with
    execLength := s.execLength + 1
    gasAvailable := .ofNat 0}
  ({q with toMachineState := q.toMachineState.mstore (.ofNat 64) (.ofNat 128)}).replaceStackAndIncrPC []

private theorem chargeExpansion : (UInt256.ofNat 12) - UInt256.ofNat 9 = UInt256.ofNat 3 := by decide +kernel
private theorem chargeBase : (UInt256.ofNat 3) - UInt256.ofNat 3 = UInt256.ofNat 0 := by decide +kernel

theorem compiled_store_decode (p : Pipeline) (s : EVM.State) :
    EVM.decode (compiledStoreInput p s).executionEnv.code (compiledStoreInput p s).pc =
      some (.MSTORE, none) := by
  cases p
  · exact TryMemoryDriver.legacy_decode4
  · exact TryMemoryDriver.viaIR_decode4

/-- Discharge the actual driver's complete gate here; no desired-success
hypothesis, padding contract or assumed gas adequacy is introduced. -/
theorem compiled_store_gate (p : Pipeline) (s : EVM.State) :
    Assembly.driverGate #[] (compiledStoreInput p s) .MSTORE =
      .ok (compiledStoreCharged p s, 3) := by
  have expansion : EVM.memoryExpansionCost (compiledStoreInput p s) .MSTORE = 9 :=
    TryMemory.prologue_expansion (compiledStoreInput p s)
  simp only [Assembly.driverGate]
  rw [expansion]
  dsimp only [compiledStoreInput, compiledStoreCharged]
  rw [chargeExpansion]
  rfl

theorem compiled_store_supplied (p : Pipeline) (s : EVM.State) (fuel : Nat) :
    EVM.step (fuel + 1) 3 (some (.MSTORE, none)) (compiledStoreCharged p s) =
      .ok (compiledStoreNext p s) := by
  change EvmYul.step (.MSTORE : Operation .EVM) none
    {compiledStoreCharged p s with
      execLength := s.execLength + 1
      gasAvailable := UInt256.ofNat 3 - UInt256.ofNat 3} = _
  rw [chargeBase]
  rfl

/-- Actual fetch/decode/step, retaining complete state and its real opaque
memory operation. This starts at the explicit checkpoint, not entryPC0. -/
theorem compiled_store_fetched (p : Pipeline) (s : EVM.State) (fuel : Nat) :
    EVM.step (fuel + 1) 3 none (compiledStoreCharged p s) =
      .ok (compiledStoreNext p s) := by
  rw [TryMemoryDriver.driver_step fuel 3 (compiledStoreCharged p s)
    (compiled_store_decode p s)]
  change EvmYul.step (.MSTORE : Operation .EVM) none
    {compiledStoreCharged p s with
      execLength := s.execLength + 1
      gasAvailable := UInt256.ofNat 3 - UInt256.ofNat 3} = _
  rw [chargeBase]
  rfl

/-- One real X-driver continuation, with its gate discharged above. This does
not assert a successful whole execution or relate any source observation. -/
theorem compiled_store_driver (p : Pipeline) (s : EVM.State) (fuel : Nat) :
    EVM.X (fuel + 2) #[] (compiledStoreInput p s) =
      EVM.X (fuel + 1) #[] (compiledStoreNext p s) := by
  exact Assembly.X_continue fuel #[] (compiledStoreInput p s) (compiledStoreCharged p s)
    (compiledStoreNext p s) (.MSTORE, none) 3 (compiled_store_decode p s)
    (compiled_store_gate p s) (compiled_store_supplied p s fuel) (by unfold Assembly.NonhaltingOpcode; decide)
end SolidityBridge.RoadmapV15
