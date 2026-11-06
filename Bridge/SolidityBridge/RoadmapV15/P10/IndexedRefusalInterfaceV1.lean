import Solidity.Backend.Selection.StackSelection
import SolidityBridge.RoadmapV15.P10.DecoderAgreement

/-! Frozen indexed stack-refusal interface V1, generated signatures only.
`Producer` is an explicit proof contract, not an instance or execution oracle.
The numeric input relation and exact gas/shortage/fuel clauses remain visible.
No compiler/source frame origin, physical allocation, resource abstraction,
account/world rollback, transaction, trace or Osaka adequacy is asserted.
The existing P10 FrozenV1 signatures are unchanged. -/
namespace SolidityBridge.RoadmapV15.P10.IndexedRefusalInterfaceV1
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def DupClaim : Prop :=
  ∀ (valid : Array UInt256) (n : Fin 16) (site : Site (.DUP n))
    (words : Scalar.Stack) (m : Solidity.Evm.Machine) (fuel : Nat),
    m.stack=Selection.irStack words →
    words.length<n.val+1 →
    3≤site.seed.gasAvailable.toNat →
    (Solidity.Evm.Instr.step (.dup (n.val+1)) m=.fault ∧
      Scalar.run (Selection.dupCertificate n).code words=none ∧
      Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow) ∧
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow

def SwapClaim : Prop :=
  ∀ (valid : Array UInt256) (n : Fin 16) (site : Site (.SWAP n))
    (words : Scalar.Stack) (m : Solidity.Evm.Machine) (fuel : Nat),
    m.stack=Selection.irStack words →
    words.length<n.val+2 →
    3≤site.seed.gasAvailable.toNat →
    (Solidity.Evm.Instr.step (.swap (n.val+1)) m=.fault ∧
      Scalar.run (Selection.swapCertificate n).code words=none ∧
      Assembly.driverSteps 1 (fuel+2) valid (modularSite site words).state=.error .StackUnderflow) ∧
    EVM.X (fuel+1) valid (modularSite site words).state=.error .StackUnderflow

structure Producer : Prop where
  dup : DupClaim
  swap : SwapClaim

end SolidityBridge.RoadmapV15.P10.IndexedRefusalInterfaceV1
