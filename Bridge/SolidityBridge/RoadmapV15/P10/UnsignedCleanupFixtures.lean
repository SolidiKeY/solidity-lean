import SolidityBridge.RoadmapV15.P10.UnsignedCleanupExecution
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Populated explicit initial/final State observations for unsignedCode. -/
namespace SolidityBridge.RoadmapV15.P10.UnsignedCleanupFixtures
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed before after spill u)
def fits (w : Fin 32) :
    (Backend.encode (before ++ [Scalar.pushWord (unsignedCleanupMask w)])).length < UInt256.size := by
  simp only [Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Scalar.encode_pushWord,
    List.length_append,List.length_cons,List.length_nil,Vector.length_toList]
  decide

def input (gas : Nat) (w : Fin 32) (words : Scalar.Stack) : EVM.State :=
  unsignedPushInput (seed gas false) before after w words
def next (w : Fin 32) (x : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (unsignedPushResult (seed 6 false) before after w (x::tail)) 3).replaceStackAndIncrPC
    ((Scalar.unsignedClean w x::tail).map (fun y => UInt256.mk y.toFin))
def observed (w : Fin 32) (x : Scalar.Word) (tail : Scalar.Stack) (result : Scalar.Word) : EVM.State :=
  {input 6 w (x::tail) with
    pc := u 37,gasAvailable := u 0,execLength := 43
    stack := (result::tail).map (fun y => UInt256.mk y.toFin)}
end SolidityBridge.RoadmapV15.P10.UnsignedCleanupFixtures
