import SolidityBridge.RoadmapV15.P10.BooleanNotConsumer
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Populated data for canonical Boolean clients and raw-word probes.
The nonempty array is a supplied-parameter probe, not a proved jump set. -/
namespace SolidityBridge.RoadmapV15.P10.BooleanNotFixtures
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed before after u)
def supplied : Array UInt256 := #[u 37,u 99]
def site (gas : Nat) (perm : Bool) : Site .ISZERO := ⟨seed gas perm,before,after,by decide⟩
def input (gas : Nat) (perm : Bool) (words : Scalar.Stack) : EVM.State :=
  (modularSite (site gas perm) words).state
def observed (gas : Nat) (perm : Bool) (a : Scalar.Word) (tail : Scalar.Stack) (result : Scalar.Word) : EVM.State :=
  {input gas perm (a::tail) with
    pc := u 4,gasAvailable := u (gas-3),execLength := 42
    stack := (result::tail).map (fun w => UInt256.mk w.toFin)}
end SolidityBridge.RoadmapV15.P10.BooleanNotFixtures
