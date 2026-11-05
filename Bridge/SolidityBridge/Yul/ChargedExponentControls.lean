import SolidityBridge.Yul.ChargedExponent
import SolidityBridge.Yul.ChargedQuotientPrefixControls
namespace SolidityBridge.Yul.ChargedExponent.Controls
open Solidity Solidity.Yul.Compilation Backend Scalar Solidity.Evm.External EvmYul
abbrev seed := ChargedQuotients.Controls.seed
abbrev dirty := ChargedQuotients.Controls.dirty
abbrev maximum := ChargedQuotients.Controls.maximum
abbrev observeState := ChargedQuotientPrefix.Controls.observeState
def prelude : Backend.Program := [.push 2 #v[0x01,0x01],.op .STOP]
def suffix : Backend.Program := [.op (.DUP 0),.op .ADD,.op .STOP]
def fits : (Backend.encode prelude).length+3<UInt256.size := by decide
def state (gas : Nat) (base exponent : Scalar.Word) (caller : Scalar.Stack) :=
  QuotientPlacement.entry prelude suffix fits (seed gas) .EXP base exponent caller
def observe (gas : Nat) (base exponent : Scalar.Word) (caller : Scalar.Stack) :=
  (Assembly.driverSteps 3 4 #[] (state gas base exponent caller)).map observeState
#check continuation prelude suffix fits (seed 66) 2 8 [dirty,77] (by decide)
  (by
    change 6+(10+50*(1+Nat.log 256 8))≤66
    rw [Nat.log_of_lt (by decide : 8<256)]) 0
#guard cost 0 = 10
#guard cost 1 = 60
#guard cost 255 = 60
#guard cost 256 = 110
#guard cost 65535 = 110
#guard cost 65536 = 160
-- Huge raw exponents are tested for byte gas; no gigantic host Nat power is evaluated.
#guard cost dirty = 1310
#guard cost maximum = 1610
#guard (observe 66 2 8 [dirty,77]).toOption ==
  some (7,[256,2,8,dirty.toNat,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe 66 8 2 []).toOption.map (fun s => s.2.1) == some [64,8,2]
#guard (observe 16 0 0 []).toOption.map (fun s => s.2.1) == some [1,0,0]
#guard (observe 66 0 7 []).toOption.map (fun s => s.2.1) == some [0,0,7]
#guard (observe 16 dirty 0 []).toOption.map (fun s => s.2.1) == some [1,dirty.toNat,0]
#guard (observe 66 dirty 1 []).toOption.map (fun s => s.2.1) == some [dirty.toNat,dirty.toNat,1]
#guard (observe 66 maximum 1 []).toOption.map (fun s => s.2.1) == some [maximum.toNat,maximum.toNat,1]
#guard (observe 66 2 255 []).toOption.map (fun s => s.2.1) == some [2^255,2,255]
#guard (observe 116 2 256 []).toOption.map (fun s => s.2.1) == some [0,2,256]
#guard (Assembly.driverSteps 3 4 #[] {(state 66 2 8 []) with
  executionEnv := {(state 66 2 8 []).executionEnv with perm := true}}).toOption.map
  (fun s => (s.executionEnv.perm,s.stack.map UInt256.toNat)) == some (true,[256,2,8])
#guard (state 66 2 8 []).executionEnv.code.data.toList =
  [0x61,0x01,0x01,0x00,0x81,0x81,0x0a,0x80,0x01,0x00]
#guard (observe 66 2 8 (List.replicate 1020 77)).toOption.map (fun s => s.2.1.length) = some 1023
#guard match observe 66 2 8 (List.replicate 1021 77) with
  | .error .StackOverflow => true | _ => false
#guard match observe 15 0 0 [] with | .error .OutOfGass => true | _ => false
#guard match observe 65 2 8 [] with | .error .OutOfGass => true | _ => false
#guard match observe 115 2 256 [] with | .error .OutOfGass => true | _ => false
#guard match observe 2 2 8 [] with | .error .OutOfGass => true | _ => false
#guard match Assembly.driverSteps 3 3 #[] (state 66 2 8 []) with
  | .error .OutOfFuel => true | _ => false
#guard match Assembly.driverSteps 3 4 #[] {(state 66 2 8 []) with stack := []} with
  | .error .StackUnderflow => true | _ => false
#guard (Assembly.driverSteps 5 6 #[] (state 72 2 8 [77])).toOption.map observeState ==
  some (9,[512,2,8,77],0,12,3,[0xaa],[0xbb],[0xcc],false)
#guard (PureExpressions.compile 1 ExponentMachine.expr).isNone
#print axioms continuation
end SolidityBridge.Yul.ChargedExponent.Controls
