import SolidityBridge.AccessBridge.MemoryInterface

/-! Actual zero-length CALLDATACOPY family. Source/destination words are
unrestricted. This is no claim about nonzero native writes or Source lowering. -/
namespace SolidityBridge.AccessBridge
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
structure EmptyCopyCertificate : Prop extends MemoryAccessCertificate where
  success : ∀ (site : RoadmapV15.P10.Site .CALLDATACOPY) (destination source : UInt256)
    (tail : List UInt256), site.state.stack=destination::source::UInt256.ofNat 0::tail →
    ∀ (valid : Array UInt256) (fuel : Nat), 3≤site.state.gasAvailable.toNat → tail.length+3≤1024 →
    let reached := (Assembly.chargedPrepare site.state 3).replaceStackAndIncrPC tail
    Assembly.driverSteps 1 (fuel+2) valid site.state=.ok reached ∧
    EVM.X (fuel+2) valid site.state=EVM.X (fuel+1) valid reached
end SolidityBridge.AccessBridge
