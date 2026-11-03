import SolidityBridge.Yul.QuotientSuffix
import SolidityBridge.Yul.ChargedQuotientPrefixControls
namespace SolidityBridge.Yul.QuotientSuffix.Controls
open Solidity Solidity.Yul.Compilation Backend Scalar Solidity.Evm.External EvmYul
abbrev seed := ChargedQuotients.Controls.seed
abbrev dirty := ChargedQuotients.Controls.dirty
abbrev observeState := ChargedQuotientPrefix.Controls.observeState

def continuation : Backend.Program := [.op (.DUP 0),.op .ADD,.op .STOP]
def observe (op : Backend.Op) (gas : Nat) (a b : Scalar.Word) (caller : Scalar.Stack) :=
  (Assembly.driverSteps 3 4 #[] (entry continuation (seed gas) op a b caller)).map observeState
#guard (observe .DIV 11 7 3 [dirty,77]).toOption ==
  some (3,[2,7,3,dirty.toNat,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe .MOD 11 7 3 [77]).toOption ==
  some (3,[1,7,3,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (entry continuation (seed 11) .DIV 7 3 []).executionEnv.code.data.toList =
  [0x81,0x81,0x04,0x80,0x01,0x00]
#guard ((Assembly.driverSteps 5 6 #[] (entry continuation (seed 17) .DIV 7 3 [dirty,77])).map observeState).toOption ==
  some (5,[4,7,3,dirty.toNat,77],0,12,3,[0xaa],[0xbb],[0xcc],false)
#guard ((Assembly.driverSteps 5 6 #[] (entry continuation (seed 17) .MOD 7 3 [77])).map observeState).toOption ==
  some (5,[2,7,3,77],0,12,3,[0xaa],[0xbb],[0xcc],false)
#guard match Assembly.driverSteps 5 6 #[] (entry continuation (seed 16) .DIV 7 3 []) with
  | .error .OutOfGass => true | _ => false
#guard match observe .DIV 10 7 3 [] with | .error .OutOfGass => true | _ => false
#guard match observe .DIV 11 7 3 (List.replicate 1021 77) with
  | .error .StackOverflow => true | _ => false
#guard (observe .DIV 11 7 0 [77]).toOption ==
  some (3,[0,7,0,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe .DIV 100 dirty 1 [77]).toOption ==
  some (3,[dirty.toNat,dirty.toNat,1,77],89,10,3,[0xaa],[0xbb],[0xcc],false)
-- An opcode-looking byte is actual PUSH data in the following code.
def payloadTail : Backend.Program := [.push 1 #v[0x04],.op .STOP]
#guard ((Assembly.driverSteps 4 5 #[] (entry payloadTail (seed 14) .DIV 7 3 [77])).map observeState).toOption ==
  some (5,[4,2,7,3,77],0,11,3,[0xaa],[0xbb],[0xcc],false)
#guard ((Assembly.driverSteps 3 4 #[] (entry [] (seed 11) .DIV 7 3 [])).toOption.map (fun s => s.pc.toNat)) = some 3
#guard match Assembly.driverSteps 4 5 #[] (entry [] (seed 14) .DIV 7 3 []) with
  | .error .InvalidInstruction => true | _ => false
#guard match Assembly.driverSteps 3 3 #[] (entry continuation (seed 11) .DIV 7 3 []) with
  | .error .OutOfFuel => true | _ => false
#print axioms reads
#print axioms div_continuation
#print axioms mod_continuation
end SolidityBridge.Yul.QuotientSuffix.Controls
