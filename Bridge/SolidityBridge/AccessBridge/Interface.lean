import SolidityBridge.RoadmapV15.P10.CalldataExtent
import SolidityBridge.RoadmapV15.P10.FrozenInterface
import SolidityBridge.RoadmapV15.ReferenceReader
import Solidity.Source.Eval

/-!
# Calldata load access contract

Signatures only, over the existing pinned state, emitted instruction site,
charged driver and source byte reader. No certificate instance, new evaluator,
ABI decoder or Source/world adequacy is supplied here. The input identity is an
initial byte installation fact, not a desired execution result. All offsets
are covered, including unaligned and out-of-buffer zero-padded reads.

CALLDATASIZE already has the published P10.calldatasize_source_input theorem;
consumers reuse it directly. Remaining memory/copy and storage access contracts
are separate obligations. These signatures do not modify frozen P10.
-/
namespace SolidityBridge.AccessBridge
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

/-- Exact payload and charged fetched execution for CALLDATALOAD. No sufficient-
gas, successful-step or opcode-result premise discards exceptional outcomes.
Positive-fuel continuation and low driver budgets are distinguished explicitly;
no equality with X at budgets zero or one is inferred. The complete reached
state and every exceptional gate outcome are retained. -/
structure CalldataLoadCertificate : Prop where
  payload : ∀ (native : EvmYul.State .EVM) (frame : Source.Fr)
      (offset : UInt256),
    native.executionEnv.calldata.data.toList = frame.cd →
    (EvmYul.State.calldataload native offset).toNat = Source.cdWordAt frame offset.toNat
  budget_zero : ∀ (site : RoadmapV15.P10.Site .CALLDATALOAD) (valid : Array UInt256),
    Assembly.driverSteps 1 0 valid site.state = .error .OutOfFuel
  budget_one : ∀ (site : RoadmapV15.P10.Site .CALLDATALOAD) (valid : Array UInt256),
    Assembly.driverSteps 1 1 valid site.state = .error .OutOfFuel
  charged : ∀ (site : RoadmapV15.P10.Site .CALLDATALOAD)
      (valid : Array UInt256) (fuel : Nat),
    Assembly.driverSteps 1 (fuel + 2) valid site.state =
      match Assembly.driverGate valid site.state .CALLDATALOAD with
      | .error error => .error error
      | .ok (charged, cost) =>
        match charged.stack.pop with
        | none => .error .StackUnderflow
        | some (tail, offset) =>
          let prepared := Assembly.chargedPrepare charged cost
          .ok (prepared.replaceStackAndIncrPC
            (EvmYul.State.calldataload prepared.toSharedState.toState offset :: tail))
  continuation : ∀ (site : RoadmapV15.P10.Site .CALLDATALOAD)
      (valid : Array UInt256) (fuel : Nat),
    EVM.X (fuel + 2) valid site.state =
      match Assembly.driverSteps 1 (fuel + 2) valid site.state with
      | .error error => .error error
      | .ok next => EVM.X (fuel + 1) valid next

end SolidityBridge.AccessBridge
