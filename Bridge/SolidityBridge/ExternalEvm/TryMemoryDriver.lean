import SolidityBridge.ExternalEvm.TryMemoryCode
import EvmYul.EVM.Semantics

/-! Existing EVMYul decoder/step/fuel components. No X gas-success theorem,
source execution, installed-code association or padding law is asserted. -/
namespace Solidity.Evm.External.TryMemoryDriver
open EvmYul

/-- Input-byte evidence, not a desired execution outcome. -/
theorem decode_mstore (code : ByteArray) (pc : UInt256)
    (h : code.get? pc.toNat = some 0x52) :
    EVM.decode code pc = some (.MSTORE, none) := by
  simp only [EVM.decode, h]
  rfl

theorem legacy_decode4 :
    EVM.decode TryMemoryCode.legacyRuntime (UInt256.ofNat 4) = some (.MSTORE, none) := by
  apply decode_mstore
  have h4 : (UInt256.ofNat 4).toNat = 4 := by decide +kernel
  rw [h4]
  exact TryMemoryCode.legacy_head.2.2.2.2

theorem viaIR_decode4 :
    EVM.decode TryMemoryCode.viaIRRuntime (UInt256.ofNat 4) = some (.MSTORE, none) := by
  apply decode_mstore
  have h4 : (UInt256.ofNat 4).toNat = 4 := by decide +kernel
  rw [h4]
  exact TryMemoryCode.viaIR_head.2.2.2.2

/-- Actual fetch+step: positive fuel, passed fee and execLength update.
The X precheck for gas/stack admissibility is separate and remains required. -/
theorem driver_step (fuel cost : Nat) (s : EVM.State)
    (h : EVM.decode s.executionEnv.code s.pc = some (.MSTORE, none)) :
    EVM.step (fuel + 1) cost none s =
      EvmYul.step (.MSTORE : Operation .EVM) none
        {s with
          execLength := s.execLength + 1
          gasAvailable := s.gasAvailable - UInt256.ofNat cost} := by
  simp only [EVM.step, EVM.fetchInstr, h, Option.option, bind, Except.bind]

/-- Exact compiled input at PC4; this does not claim original reachability. -/
theorem legacy_at4 (fuel cost : Nat) (s : EVM.State) :
    let at4 : EVM.State := {s with
      pc := UInt256.ofNat 4
      executionEnv := {s.executionEnv with code := TryMemoryCode.legacyRuntime}}
    EVM.step (fuel + 1) cost none at4 =
      EvmYul.step (.MSTORE : Operation .EVM) none
        {at4 with execLength := at4.execLength + 1
                  gasAvailable := at4.gasAvailable - UInt256.ofNat cost} := by
  apply driver_step
  exact legacy_decode4

theorem viaIR_at4 (fuel cost : Nat) (s : EVM.State) :
    let at4 : EVM.State := {s with
      pc := UInt256.ofNat 4
      executionEnv := {s.executionEnv with code := TryMemoryCode.viaIRRuntime}}
    EVM.step (fuel + 1) cost none at4 =
      EvmYul.step (.MSTORE : Operation .EVM) none
        {at4 with execLength := at4.execLength + 1
                  gasAvailable := at4.gasAvailable - UInt256.ofNat cost} := by
  apply driver_step
  exact viaIR_decode4

/-- Resource stops are real EVM exceptions, never Solidity completed failure. -/
theorem step_zero_fuel (cost : Nat) (s : EVM.State) :
    EVM.step 0 cost none s = .error .OutOfFuel := rfl

theorem X_zero_fuel (jumps : Array UInt256) (s : EVM.State) :
    EVM.X 0 jumps s = .error .OutOfFuel := rfl

end Solidity.Evm.External.TryMemoryDriver
