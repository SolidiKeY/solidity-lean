import SolidityBridge.RoadmapV15.P10.LogicalShiftExecution
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Populated data for actual emitted selected two-instruction shift clients. -/
namespace SolidityBridge.RoadmapV15.P10.LogicalShiftFixtures
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed before after u)
def fits : (Backend.encode (before ++ [.op (.SWAP 0)])).length < UInt256.size := by decide
def input (op : Backend.Op) (gas : Nat) (perm : Bool) (value count : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  logicalShiftInput (seed gas perm) before after op (value::count::tail)
def observed (op : Backend.Op) (gas : Nat) (perm : Bool) (value count : Scalar.Word)
    (tail : Scalar.Stack) (result : Scalar.Word) : EVM.State :=
  {input op gas perm value count tail with
    pc := u 5,gasAvailable := u (gas-6),execLength := 43
    stack := (result::tail).map (fun w => UInt256.mk w.toFin)}
end SolidityBridge.RoadmapV15.P10.LogicalShiftFixtures
