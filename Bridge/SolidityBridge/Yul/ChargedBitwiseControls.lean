import SolidityBridge.Yul.ChargedBitwise
import SolidityBridge.Yul.ChargedQuotientPrefixControls
/-! Native/reference arithmetic-site controls, not external solc/client tests
or proofs that the preceding DUP prefix is reached/executed. -/
namespace SolidityBridge.Yul.ChargedBitwise.Controls
open Solidity Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation Backend Scalar
open Solidity.Evm.External EvmYul
abbrev dirty := ChargedQuotients.Controls.dirty
abbrev observeState := ChargedQuotientPrefix.Controls.observeState

def seed (gas : Nat) (perm : Bool := false) : EVM.State :=
  {ChargedQuotients.Controls.seed gas with
    executionEnv := {(ChargedQuotients.Controls.seed gas).executionEnv with perm := perm}}
def prelude : Backend.Program := [.push 2 #v[0x1a,0x02],.op .STOP]
theorem fits : (Backend.encode prelude).length+3<UInt256.size := by decide
def suffix : Backend.Program := [.op (.DUP 0),.op .ADD,.op .STOP]
def observe (op : Backend.Op) (gas : Nat) (a b : Scalar.Word) (caller : Scalar.Stack)
    (perm : Bool := false) :=
  (Assembly.driverSteps 1 2 #[] (input prelude suffix fits (seed gas perm) op a b caller)).map observeState

#check and_correspondence prelude suffix fits (seed 3) dirty 255 [dirty,77] (by decide) (by decide) 0
#check or_correspondence prelude suffix fits (seed 3) dirty 255 [dirty,77] (by decide) (by decide) 0
#check xor_correspondence prelude suffix fits (seed 3) dirty 255 [dirty,77] (by decide) (by decide) 0
#guard (observe .AND 3 dirty 255 [dirty,77]).toOption ==
  some (7,[1,dirty.toNat,255,dirty.toNat,77],0,8,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe .OR 3 dirty 255 [77]).toOption ==
  some (7,[2^200+511,dirty.toNat,255,77],0,8,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe .XOR 3 dirty 255 [77] true).toOption ==
  some (7,[2^200+510,dirty.toNat,255,77],0,8,3,[0xaa],[0xbb],[0xcc],true)
#guard (input prelude suffix fits (seed 3) .AND dirty 255 []).executionEnv.code.data.toList =
  [0x61,0x1a,0x02,0x00,0x81,0x81,0x16,0x80,0x01,0x00]
#guard (input prelude suffix fits (seed 3) .AND dirty 255 []).pc.toNat = 6
#guard prelude.length = 2
#guard match observe .AND 2 dirty 255 [] with | .error .OutOfGass => true | _ => false
#guard match Assembly.driverSteps 1 1 #[] (input prelude suffix fits (seed 3) .AND dirty 255 []) with
  | .error .OutOfFuel => true | _ => false
#guard match Assembly.driverSteps 1 2 #[]
  {input prelude suffix fits (seed 3) .OR dirty 255 [] with stack := []} with
  | .error .StackUnderflow => true | _ => false
#guard match observe .XOR 3 dirty 255 (List.replicate 1022 77) with
  | .error .StackOverflow => true | _ => false
-- A shrinking opcode gate may accept an unreachable oversized incoming stack;
-- this does not validate the earlier DUP peak or our theorem's capacity premise.
#guard (Assembly.driverGate #[]
  (input prelude suffix fits (seed 3) .AND dirty 255 (List.replicate 1021 77)) .AND).toOption.isSome
#guard ((observe .AND 3 dirty 255 (List.replicate 1020 77)).toOption).map
  (fun out => out.2.1.length) = some 1023
-- A finite suffix-combination regression, not a universal suffix theorem.
#guard ((Assembly.driverSteps 3 4 #[] (input prelude suffix fits (seed 9) .AND dirty 255 [77])).map observeState).toOption ==
  some (9,[2,dirty.toNat,255,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (PureExpressions.compile 1 BitMachineExecution.andExpr).isNone
end SolidityBridge.Yul.ChargedBitwise.Controls
