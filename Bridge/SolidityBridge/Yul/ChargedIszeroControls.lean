import SolidityBridge.Yul.ChargedIszero
import SolidityBridge.Yul.ChargedQuotientPrefixControls
namespace SolidityBridge.Yul.ChargedIszero.Controls
open Solidity Solidity.Yul.Compilation Backend Scalar Solidity.Evm.External EvmYul
abbrev seed := ChargedQuotients.Controls.seed
abbrev dirty := ChargedQuotients.Controls.dirty
abbrev observeState := ChargedQuotientPrefix.Controls.observeState
-- Two instructions in the prelude occupy four bytes.
def prelude : Backend.Program := [.push 2 #v[0x01,0x01],.op .STOP]
def suffix : Backend.Program := [.op (.DUP 0),.op .ADD,.op .STOP]
def state (gas : Nat) (a : Scalar.Word) (caller : Scalar.Stack) : EVM.State :=
  entry prelude suffix (by decide) (seed gas) a caller
def observe (gas : Nat) (a : Scalar.Word) (caller : Scalar.Stack) :=
  (Assembly.driverSteps 2 3 #[] (state gas a caller)).map observeState
#guard (observe 6 0 [dirty,77]).toOption ==
  some (6,[1,0,dirty.toNat,77],0,9,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe 6 dirty [77]).toOption ==
  some (6,[0,dirty.toNat,77],0,9,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe 6 (BitVec.ofNat 256 (2^200)) []).toOption ==
  some (6,[0,2^200],0,9,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe 6 1 []).toOption ==
  some (6,[0,1],0,9,3,[0xaa],[0xbb],[0xcc],false)
#guard (Assembly.driverSteps 2 3 #[] {(state 6 0 []) with
    executionEnv := {(state 6 0 []).executionEnv with perm := true}}).toOption.map
    (fun s => (s.executionEnv.perm,s.stack.map UInt256.toNat)) == some (true,[1,0])
#guard (observe 6 0 (List.replicate 1022 77)).toOption.map (fun s => s.2.1.length) = some 1024
#guard match observe 6 0 (List.replicate 1023 77) with
  | .error .StackOverflow => true | _ => false
#guard match observe 5 0 [] with | .error .OutOfGass => true | _ => false
#guard match observe 2 0 [] with | .error .OutOfGass => true | _ => false
#guard match Assembly.driverSteps 2 2 #[] (state 6 0 []) with
  | .error .OutOfFuel => true | _ => false
#guard match Assembly.driverSteps 2 3 #[] {(state 6 0 []) with stack := []} with
  | .error .StackUnderflow => true | _ => false
-- Finite suffix regression, not a universal suffix theorem.
#guard (Assembly.driverSteps 4 5 #[] (state 12 0 [77])).toOption.map observeState ==
  some (8,[2,0,77],0,11,3,[0xaa],[0xbb],[0xcc],false)
#guard (state 6 0 []).executionEnv.code.data.toList = [0x61,0x01,0x01,0x00,0x80,0x15,0x80,0x01,0x00]
#print axioms execution
#print axioms zero_input
end SolidityBridge.Yul.ChargedIszero.Controls
