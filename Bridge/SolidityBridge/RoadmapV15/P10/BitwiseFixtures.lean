import SolidityBridge.RoadmapV15.P10.BitwiseConsumer
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Typed populated bitwise fixtures; these are State observations, not a machine. -/
namespace SolidityBridge.RoadmapV15.P10.BitwiseFixtures
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed before after u)
def site (op : Backend.Op) (gas : Nat) (perm : Bool) : Site op :=
  ⟨seed gas perm,before,after,by decide⟩
def input (op : Backend.Op) (gas : Nat) (perm : Bool) (words : Scalar.Stack) : EVM.State :=
  (modularSite (site op gas perm) words).state
def observed (op : Backend.Op) (perm : Bool) (a b : Scalar.Word) (tail : Scalar.Stack)
    (result : Scalar.Word) : EVM.State :=
  {input op 3 perm (a::b::tail) with
    pc := u 4,gasAvailable := u 0,execLength := 42
    stack := (result::tail).map (fun w => UInt256.mk w.toFin)}
def observedAt (op : Backend.Op) (gas : Nat) (perm : Bool) (a b : Scalar.Word) (tail : Scalar.Stack)
    (result : Scalar.Word) : EVM.State :=
  {input op gas perm (a::b::tail) with
    pc := u 4,gasAvailable := u (gas-3),execLength := 42
    stack := (result::tail).map (fun w => UInt256.mk w.toFin)}
end SolidityBridge.RoadmapV15.P10.BitwiseFixtures
