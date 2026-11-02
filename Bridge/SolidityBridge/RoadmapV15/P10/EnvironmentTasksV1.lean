import SolidityBridge.RoadmapV15.P10.DecoderAgreement
import Solidity.Backend.Environment.Frames

/-! GENERATED frozen routine-task statements v1. No proof, instance or axiom is
provided. A value of PendingGlueBatch is an outstanding obligation, not evidence.
These native clauses cannot extend G31/source/Osaka admission. -/
namespace SolidityBridge.RoadmapV15.P10.EnvironmentTasksV1
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def OriginClaim : Prop :=
  ∀ (site : Site .ORIGIN) (fuel : Nat),
    2 ≤ site.state.gasAvailable.toNat → site.state.stack.length+1 ≤ 1024 →
    let next := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC
      (UInt256.ofNat site.state.executionEnv.sender.val :: site.state.stack)
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
      EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next

def GasPriceClaim : Prop :=
  ∀ (site : Site .GASPRICE) (fuel : Nat),
    2 ≤ site.state.gasAvailable.toNat → site.state.stack.length+1 ≤ 1024 →
    let next := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC
      (UInt256.ofNat site.state.executionEnv.gasPrice :: site.state.stack)
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
      EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next

def ChainIdClaim : Prop :=
  ∀ (site : Site .CHAINID) (fuel : Nat),
    2 ≤ site.state.gasAvailable.toNat → site.state.stack.length+1 ≤ 1024 →
    let next := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC
      (EvmYul.State.chainId site.state.toState :: site.state.stack)
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
      EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next

def SourceRefusalsClaim : Prop :=
  ∀ (frame : Backend.Environment.Frame) (tail : List Backend.Environment.Word),
    (Backend.Environment.admittedOp .ORIGIN = false ∧
      Backend.Environment.step frame (.op .ORIGIN) tail = none) ∧
    (Backend.Environment.admittedOp .GASPRICE = false ∧
      Backend.Environment.step frame (.op .GASPRICE) tail = none) ∧
    (Backend.Environment.admittedOp .CHAINID = false ∧
      Backend.Environment.step frame (.op .CHAINID) tail = none)

def LocalFacts (op : Backend.Op) (site : Site op) : Prop :=
  EVM.C' site.state (DecoderAgreement.referenceOp op) = 2 ∧
  EVM.δ (DecoderAgreement.referenceOp op) = some 0 ∧
  EVM.α (DecoderAgreement.referenceOp op) = some 1 ∧
  EVM.memoryExpansionCost site.state (DecoderAgreement.referenceOp op) = 0

def OriginFactsClaim : Prop :=
  ∀ site : Site .ORIGIN, LocalFacts .ORIGIN site

def GasPriceFactsClaim : Prop :=
  ∀ site : Site .GASPRICE, LocalFacts .GASPRICE site

def ChainIdFactsClaim : Prop :=
  ∀ site : Site .CHAINID, LocalFacts .CHAINID site

structure PendingGlueBatch : Prop where
  originFacts : OriginFactsClaim
  gasPriceFacts : GasPriceFactsClaim
  chainIdFacts : ChainIdFactsClaim
  sourceRefusals : SourceRefusalsClaim

end SolidityBridge.RoadmapV15.P10.EnvironmentTasksV1
