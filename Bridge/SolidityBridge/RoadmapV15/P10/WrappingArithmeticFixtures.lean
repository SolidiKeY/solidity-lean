import SolidityBridge.RoadmapV15.P10.WrappingArithmeticConsumer
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Populated data only, using existing Op, Site, intrinsic Word and native State.
The observed record is a test observation, not a second arithmetic transition. -/
namespace SolidityBridge.RoadmapV15.P10.WrappingArithmeticFixtures
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed before after u)
def supplied : Array UInt256 := #[u 37,u 99]
def site (op : Backend.Op) (gas : Nat) (perm : Bool) : Site op := ⟨seed gas perm,before,after,by decide⟩
def input (op : Backend.Op) (gas : Nat) (perm : Bool) (words : Scalar.Stack) : EVM.State :=
  (modularSite (site op gas perm) words).state
def observed (op : Backend.Op) (gas : Nat) (perm : Bool) (cost : Nat)
    (a b : Scalar.Word) (tail : Scalar.Stack) (result : Scalar.Word) : EVM.State :=
  {input op gas perm (a::b::tail) with
    pc := u 4,gasAvailable := u (gas-cost),execLength := 42
    stack := (result::tail).map (fun w => UInt256.mk w.toFin)}
end SolidityBridge.RoadmapV15.P10.WrappingArithmeticFixtures
