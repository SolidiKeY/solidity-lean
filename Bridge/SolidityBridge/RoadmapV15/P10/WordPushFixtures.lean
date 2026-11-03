import SolidityBridge.RoadmapV15.P10.WordPushConsumer
import Solidity.Backend.Scalar.Typed

/-! Populated test data only, using the existing native State and backend code.
The expected record is a fixture observation, not another transition semantics. -/
namespace SolidityBridge.RoadmapV15.P10.WordPushFixtures
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
def u (n : Nat) : UInt256 := .ofNat n
def before : Backend.Program := [.push ⟨1,by decide⟩ #v[0x7f],.op .POP]
def after : Backend.Program := [.op .STOP]
def spill : Scalar.Stack := [258,513]
def accounts : AccountMap .EVM :=
  ((∅ : AccountMap .EVM).insert (.ofNat 7)
    {(default : Account .EVM) with nonce := u 3,balance := u 29}).insert (.ofNat 11)
    {(default : Account .EVM) with nonce := u 5,balance := u 41}
def seed (gas : Nat) (perm : Bool) : EVM.State :=
  {(default : EVM.State) with
    pc := u 99,execLength := 41,gasAvailable := u gas,activeWords := u 1
    memory := ⟨(([0xaa,0xbb] : List UInt8) ++ List.replicate 30 0).toArray⟩
    returnData := ⟨#[0xcc,0xdd]⟩,H_return := ⟨#[0xee,0xff]⟩
    accountMap := accounts,σ₀ := accounts
    executionEnv := {(default : EVM.State).executionEnv with
      codeOwner := .ofNat 7,source := .ofNat 11,sender := .ofNat 19,perm := perm
      calldata := ⟨#[0x11,0x22,0x33]⟩}}
def input (gas : Nat) (perm : Bool) (w : Scalar.Word) (words : Scalar.Stack) : EVM.State :=
  wordPushInput (seed gas perm) before after w words
def expected (perm : Bool) (w : Scalar.Word) (words : Scalar.Stack) : EVM.State :=
  {input 10 perm w words with
    pc := u 36,gasAvailable := u 7,execLength := 42
    stack := (w::words).map (fun x => UInt256.mk x.toFin)}
end SolidityBridge.RoadmapV15.P10.WordPushFixtures
