import SolidityBridge.RoadmapV15.P10.SignedCleanupComposition
import SolidityBridge.RoadmapV15.P10.SignedCleanupFixtures

/-! Explicit initial and observed states for BOTH emitted instructions.
The positive complete-State fixture uses exactly8 gas; no terminal result is asserted. -/
namespace SolidityBridge.RoadmapV15.P10.SignedCompositionFixtures
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed before after spill u)
def input (gas : Nat) (w : Fin 32) (x : Scalar.Word) : EVM.State :=
  signedPushInput (seed gas false) before after w x spill
def next (w : Fin 32) (x : Scalar.Word) : EVM.State :=
  (Assembly.chargedPrepare (signedPushResult (seed 8 false) before after w x spill) 5).replaceStackAndIncrPC
    ((Scalar.signedClean w x::spill).map (fun y => UInt256.mk y.toFin))
def observed (w : Fin 32) (x result : Scalar.Word) : EVM.State :=
  {input 8 w x with
    pc := u 37,gasAvailable := u 0,execLength := 43
    stack := (result::spill).map (fun y => UInt256.mk y.toFin)}
end SolidityBridge.RoadmapV15.P10.SignedCompositionFixtures
