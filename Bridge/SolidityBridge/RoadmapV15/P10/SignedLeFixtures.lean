import SolidityBridge.RoadmapV15.P10.SignedLeExecution
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Populated data for actual selected signed <= clients; no transition definition. -/
namespace SolidityBridge.RoadmapV15.P10.SignedLeFixtures
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed before after u)
def w (n : Int) : Scalar.Word := BitVec.ofInt 256 n
def fits : (Backend.encode (before ++ [.op .SGT])).length < UInt256.size := by decide
def input (gas : Nat) (perm : Bool) (a b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  signedLeInput (seed gas perm) before after (a::b::tail)
def observed (gas : Nat) (perm : Bool) (a b : Scalar.Word) (tail : Scalar.Stack) (result : Scalar.Word) : EVM.State :=
  {input gas perm a b tail with
    pc := u 5,gasAvailable := u (gas-6),execLength := 43
    stack := (result::tail).map (fun x => UInt256.mk x.toFin)}
end SolidityBridge.RoadmapV15.P10.SignedLeFixtures
