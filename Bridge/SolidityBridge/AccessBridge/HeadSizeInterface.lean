import SolidityBridge.RoadmapV15.P10.CalldataExtent
import Solidity.Backend.AbiEntry.HeadCheck

/-! Fetched native input extent to numeric short-head predicate. Word-size
representability remains explicit, not a new admission or a supplied run. -/
namespace SolidityBridge.AccessBridge
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
structure HeadSizeCertificate : Prop where
  checked : ∀ {D : Source.Layout} (site : RoadmapV15.P10.Site .CALLDATASIZE)
    (input : Source.Calldata D) (fuel : Nat),
    2≤site.seed.gasAvailable.toNat → site.seed.stack.length+1≤1024 →
    ∀ (parameters : List Solidity.AbiEntry.Param) (suffix : Scalar.Stack),
    let start := (RoadmapV15.P10.calldataSite site input).state
    let next := (Assembly.chargedPrepare start 2).replaceStackAndIncrPC
      (UInt256.ofNat input.input.length::start.stack)
    Assembly.driverSteps 1 (fuel+2) #[] start=.ok next ∧
    EVM.X (fuel+2) #[] start=EVM.X (fuel+1) #[] next ∧
    Scalar.run (Backend.AbiEntry.HeadCheck.code parameters)
      (BitVec.ofNat 256 (UInt256.ofNat input.input.length).toNat::suffix)=
      some (Scalar.flag (decide (input.input.length%2^256<Backend.AbiEntry.HeadCheck.need parameters))::suffix)
end SolidityBridge.AccessBridge
