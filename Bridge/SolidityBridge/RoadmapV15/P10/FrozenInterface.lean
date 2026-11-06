import SolidityBridge.RoadmapV15.P10.Interface
import SolidityBridge.ExternalEvm.Assembly.Driver

/-! Frozen P10 interface, version 1: signatures only, no axioms or placeholders.
Each field is a proof obligation over existing definitions; `FrozenWitness`
discharges all of them from existing P10 theorems, so `API` adds no fact beyond
those. A signature change becomes a new version.

Scope: a Backend-emitted `Site` (a state built with the encoded code and PC), the
pinned decoder, the charged driver and the reference CALL. `Site` does not prove
compiler/source frame origin; `validJumps` is an input array, not a scanner
certificate. No physical `PaddingCorrect`, Osaka/G45.03 execution meaning,
source/ABI/world, resource abstraction, transaction or trace adequacy is
asserted by this API. -/
namespace SolidityBridge.RoadmapV15.P10.FrozenV1
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

structure Decode : Prop where
  decode_call (site : Site .CALL) :
      EVM.decode site.state.executionEnv.code site.state.pc = some (.CALL,none)
  decode_return_size (site : Site .RETURNDATASIZE) :
      EVM.decode site.state.executionEnv.code site.state.pc = some (.RETURNDATASIZE,none)
  decode_return_copy (site : Site .RETURNDATACOPY) :
      EVM.decode site.state.executionEnv.code site.state.pc = some (.RETURNDATACOPY,none)
  decode_jump (site : Site .JUMP) :
      EVM.decode site.state.executionEnv.code site.state.pc = some (.JUMP,none)
  decode_jump_if (site : Site .JUMPI) :
      EVM.decode site.state.executionEnv.code site.state.pc = some (.JUMPI,none)
  decode_jump_dest (site : Site .JUMPDEST) :
      EVM.decode site.state.executionEnv.code site.state.pc = some (.JUMPDEST,none)

structure ChargedStep : Prop where
  checked_call (site : Site .CALL) (valid : Array UInt256) (fuel : Nat) :
      Assembly.driverSteps 1 (fuel+2) valid site.state =
        match Assembly.driverGate valid site.state .CALL with
        | .error error => .error error
        | .ok (charged,cost) =>
          match charged.stack.pop7 with
                | none => .error .StackUnderflow
                | some (tail,gas,recipient,value,inOffset,inSize,outOffset,outSize) =>
                  (EVM.call fuel cost charged.executionEnv.blobVersionedHashes gas
                    (.ofNat charged.executionEnv.codeOwner) recipient recipient value value inOffset inSize outOffset outSize
                    charged.executionEnv.perm {charged with execLength := charged.execLength+1}).map
                    (fun result => result.2.replaceStackAndIncrPC (result.1 :: tail))
  checked_return_size (site : Site .RETURNDATASIZE) (valid : Array UInt256) (fuel : Nat) :
      Assembly.driverSteps 1 (fuel+2) valid site.state =
        match Assembly.driverGate valid site.state .RETURNDATASIZE with
        | .error error => .error error
        | .ok (charged,cost) =>
          Except.ok ((Assembly.chargedPrepare charged cost).replaceStackAndIncrPC
                (UInt256.ofNat charged.returnData.size :: charged.stack))
  checked_return_copy (site : Site .RETURNDATACOPY) (valid : Array UInt256) (fuel : Nat) :
      Assembly.driverSteps 1 (fuel+2) valid site.state =
        match Assembly.driverGate valid site.state .RETURNDATACOPY with
        | .error error => .error error
        | .ok (charged,cost) =>
          match charged.stack.pop3 with
                | none => .error .StackUnderflow
                | some (tail,destination,source,length) =>
                  .ok (({Assembly.chargedPrepare charged cost with
                    toMachineState := (Assembly.chargedPrepare charged cost).toMachineState.returndatacopy destination source length}).replaceStackAndIncrPC tail)
  checked_jump (site : Site .JUMP) (valid : Array UInt256) (fuel : Nat) :
      Assembly.driverSteps 1 (fuel+2) valid site.state =
        match Assembly.driverGate valid site.state .JUMP with
        | .error error => .error error
        | .ok (charged,cost) =>
          match charged.stack.pop with
                | none => .error .StackUnderflow
                | some (tail,destination) =>
                  .ok {Assembly.chargedPrepare charged cost with pc := destination,stack := tail}
  checked_jump_if (site : Site .JUMPI) (valid : Array UInt256) (fuel : Nat) :
      Assembly.driverSteps 1 (fuel+2) valid site.state =
        match Assembly.driverGate valid site.state .JUMPI with
        | .error error => .error error
        | .ok (charged,cost) =>
          match charged.stack.pop2 with
                | none => .error .StackUnderflow
                | some (tail,destination,condition) =>
                  .ok {Assembly.chargedPrepare charged cost with
                    pc := if condition != (⟨0⟩ : UInt256) then destination else charged.pc + ⟨1⟩
                    stack := tail}
  checked_jump_dest (site : Site .JUMPDEST) (valid : Array UInt256) (fuel : Nat) :
      Assembly.driverSteps 1 (fuel+2) valid site.state =
        match Assembly.driverGate valid site.state .JUMPDEST with
        | .error error => .error error
        | .ok (charged,cost) =>
          Except.ok ((Assembly.chargedPrepare charged cost).replaceStackAndIncrPC charged.stack)

structure Continuation : Prop where
  x_call (site : Site .CALL) (valid : Array UInt256) (fuel : Nat) :
      EVM.X (fuel+2) valid site.state =
        match Assembly.driverSteps 1 (fuel+2) valid site.state with
        | .error error => .error error
        | .ok next => EVM.X (fuel+1) valid next
  x_return_size (site : Site .RETURNDATASIZE) (valid : Array UInt256) (fuel : Nat) :
      EVM.X (fuel+2) valid site.state =
        match Assembly.driverSteps 1 (fuel+2) valid site.state with
        | .error error => .error error
        | .ok next => EVM.X (fuel+1) valid next
  x_return_copy (site : Site .RETURNDATACOPY) (valid : Array UInt256) (fuel : Nat) :
      EVM.X (fuel+2) valid site.state =
        match Assembly.driverSteps 1 (fuel+2) valid site.state with
        | .error error => .error error
        | .ok next => EVM.X (fuel+1) valid next
  x_jump (site : Site .JUMP) (valid : Array UInt256) (fuel : Nat) :
      EVM.X (fuel+2) valid site.state =
        match Assembly.driverSteps 1 (fuel+2) valid site.state with
        | .error error => .error error
        | .ok next => EVM.X (fuel+1) valid next
  x_jump_if (site : Site .JUMPI) (valid : Array UInt256) (fuel : Nat) :
      EVM.X (fuel+2) valid site.state =
        match Assembly.driverSteps 1 (fuel+2) valid site.state with
        | .error error => .error error
        | .ok next => EVM.X (fuel+1) valid next
  x_jump_dest (site : Site .JUMPDEST) (valid : Array UInt256) (fuel : Nat) :
      EVM.X (fuel+2) valid site.state =
        match Assembly.driverSteps 1 (fuel+2) valid site.state with
        | .error error => .error error
        | .ok next => EVM.X (fuel+1) valid next

/-- All 18 obligations. No future execution theorem is assumed. -/
structure API : Prop where
  decoded : Decode
  charged : ChargedStep
  continuation : Continuation

end SolidityBridge.RoadmapV15.P10.FrozenV1
