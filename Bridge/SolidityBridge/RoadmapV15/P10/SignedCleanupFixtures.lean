import SolidityBridge.RoadmapV15.P10.SignedCleanupTail
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Test data for explicit signed-cleanup tail entries; not a prefix-execution witness. -/
namespace SolidityBridge.RoadmapV15.P10.SignedCleanupFixtures
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (u before after spill seed)
def site (gas : Nat) (w : Fin 32) : Site .SIGNEXTEND :=
  signedCleanupSite (seed gas false) before after w (by decide +revert)
def input (gas : Nat) (w : Fin 32) (x : Scalar.Word) : EVM.State :=
  (modularSite (site gas w) (signedCleanupIndex w::x::spill)).state
def next (w : Fin 32) (x : Scalar.Word) : EVM.State :=
  (Assembly.chargedPrepare (input 10 w x) 5).replaceStackAndIncrPC
    ((Scalar.signedClean w x::spill).map (fun y => UInt256.mk y.toFin))
def observed (w : Fin 32) (x result : Scalar.Word) : EVM.State :=
  {input 10 w x with
    pc := u 37,gasAvailable := u 5,execLength := 42
    stack := (result::spill).map (fun y => UInt256.mk y.toFin)}
end SolidityBridge.RoadmapV15.P10.SignedCleanupFixtures
