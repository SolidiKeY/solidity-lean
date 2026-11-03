import SolidityBridge.RoadmapV15.P10.LinkedJumpConsumer
import SolidityBridge.ExternalEvm.Assembly.LinkedChecks
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Existing published linked-loop certificate and an actual Backend encoding
of its byte image. The represented entry is JUMPI at 36; prior prefix execution
is not assumed proved. Only code is aligned, not source/account frame origin. -/
namespace SolidityBridge.RoadmapV15.P10.LinkedJumpFixtures
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed u)

def program := Assembly.LinkedChecks.loopProgram
def before : Backend.Program := [.op .JUMPDEST,.op .JUMPDEST,.op .ISZERO,
  Scalar.pushWord (BitVec.ofNat 256 72)]
def after : Backend.Program := [.op .JUMPDEST,Scalar.pushWord 0,.op .JUMP,.op .JUMPDEST,.op .STOP]
def tail : List UInt256 := [u 258,u 513]
def site (gas : Nat) (perm : Bool) : Site .JUMPI := ⟨seed gas perm,before,after,by decide⟩
def input (gas : Nat) (perm : Bool) (condition : UInt256) (rest : List UInt256) : EVM.State :=
  (jumpMemberSite (site gas perm) (u 72) condition rest).state
def observed (gas : Nat) (perm : Bool) (condition : UInt256) (rest : List UInt256) (pc : Nat) : EVM.State :=
  {input gas perm condition rest with
    pc := u pc,gasAvailable := u (gas-10),execLength := 42,stack := rest}
end SolidityBridge.RoadmapV15.P10.LinkedJumpFixtures
