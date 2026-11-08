import SolidityBridge.RoadmapV15.P10.Interface
import SolidityBridge.ExternalEvm.Assembly.Driver

/-! Charged storage access contracts over existing P10 instruction sites.
The read and write families retain every actual gate error, native state update
and protected stack tail. Driver budgets zero and one are separate from the
positive-fuel X continuation. No successful gate, desired execution, account
presence or new admission restriction is assumed. Symbolic-path transport,
Source/native origin, transaction reset, frame rollback and the full pass bridge
remain separate obligations; this signature module supplies no certificate.
-/
namespace SolidityBridge.AccessBridge
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

structure StorageAccessCertificate : Prop where
  budget_zero : ∀ (op : Backend.Op) (site : RoadmapV15.P10.Site op)
      (valid : Array UInt256),
    Assembly.driverSteps 1 0 valid site.state = .error .OutOfFuel
  budget_one : ∀ (op : Backend.Op) (site : RoadmapV15.P10.Site op)
      (valid : Array UInt256),
    Assembly.driverSteps 1 1 valid site.state = .error .OutOfFuel
  read_charged : ∀ (op : Backend.Op), op ∈ [.SLOAD,.TLOAD] →
    ∀ (site : RoadmapV15.P10.Site op) (valid : Array UInt256) (fuel : Nat),
    Assembly.driverSteps 1 (fuel+2) valid site.state =
      match Assembly.driverGate valid site.state
          (if op=.SLOAD then .SLOAD else .TLOAD) with
      | .error error => .error error
      | .ok (charged,cost) =>
        match charged.stack.pop with
        | none => .error .StackUnderflow
        | some (tail,key) =>
          let prepared := Assembly.chargedPrepare charged cost
          let read := if op=.SLOAD then EvmYul.State.sload prepared.toState key
            else EvmYul.State.tload prepared.toState key
          .ok (({prepared with toState := read.1} : EVM.State).replaceStackAndIncrPC
            (read.2 :: tail))
  write_charged : ∀ (op : Backend.Op), op ∈ [.SSTORE,.TSTORE] →
    ∀ (site : RoadmapV15.P10.Site op) (valid : Array UInt256) (fuel : Nat),
    Assembly.driverSteps 1 (fuel+2) valid site.state =
      match Assembly.driverGate valid site.state
          (if op=.SSTORE then .SSTORE else .TSTORE) with
      | .error error => .error error
      | .ok (charged,cost) =>
        match charged.stack.pop2 with
        | none => .error .StackUnderflow
        | some (tail,key,value) =>
          let prepared := Assembly.chargedPrepare charged cost
          let stored := if op=.SSTORE then EvmYul.State.sstore prepared.toState key value
            else EvmYul.State.tstore prepared.toState key value
          .ok (({prepared with toState := stored} : EVM.State).replaceStackAndIncrPC tail)
  continuation : ∀ (op : Backend.Op), op ∈ [.SLOAD,.SSTORE,.TLOAD,.TSTORE] →
    ∀ (site : RoadmapV15.P10.Site op) (valid : Array UInt256) (fuel : Nat),
    EVM.X (fuel+2) valid site.state =
      match Assembly.driverSteps 1 (fuel+2) valid site.state with
      | .error error => .error error
      | .ok next => EVM.X (fuel+1) valid next

end SolidityBridge.AccessBridge
