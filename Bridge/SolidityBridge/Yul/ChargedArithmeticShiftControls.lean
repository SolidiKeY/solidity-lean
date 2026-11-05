import SolidityBridge.Yul.ChargedArithmeticShift
import SolidityBridge.Yul.ChargedQuotientPrefixControls
namespace SolidityBridge.Yul.ChargedArithmeticShift.Controls
open Solidity Solidity.Yul.Compilation Backend Scalar Solidity.Evm.External EvmYul
abbrev seed := ChargedQuotients.Controls.seed
abbrev dirty := ChargedQuotients.Controls.dirty
abbrev maximum := ChargedQuotients.Controls.maximum
abbrev observeState := ChargedQuotientPrefix.Controls.observeState
def prelude : Backend.Program := [.push 2 #v[0x01,0x01],.op .STOP]
def suffix : Backend.Program := [.op (.DUP 0),.op .ADD,.op .STOP]
def fits : (Backend.encode prelude).length+3<UInt256.size := by decide
def state (op : Backend.Op) (gas : Nat) (count value : Scalar.Word) (caller : Scalar.Stack) :=
  QuotientPlacement.entry prelude suffix fits (seed gas) op count value caller
def observe (op : Backend.Op) (gas : Nat) (count value : Scalar.Word) (caller : Scalar.Stack) :=
  (Assembly.driverSteps 3 4 #[] (state op gas count value caller)).map observeState
abbrev negativeThree : Scalar.Word := BitVec.ofInt 256 (-3)
abbrev minimum : Scalar.Word := BitVec.ofNat 256 (2^255)
#guard sarCompiled.lowered.code 0 = some sarProgram
#guard (PureExpressions.compile 1 sarExpr).isNone
#check sar_continuation prelude suffix fits (seed 11) 1 negativeThree [dirty,77] (by decide) (by decide) 0
#guard (observe .SAR 11 1 negativeThree [dirty,77]).toOption ==
  some (7,[2^256-2,1,negativeThree.toNat,dirty.toNat,77],2,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe .SAR 11 1 minimum []).toOption.map (fun s => s.2.1) ==
  some [2^256-2^254,1,2^255]
#guard (observe .SAR 11 255 minimum []).toOption.map (fun s => s.2.1) ==
  some [maximum.toNat,255,2^255]
#guard (observe .SAR 11 256 negativeThree []).toOption.map (fun s => s.2.1) ==
  some [maximum.toNat,256,negativeThree.toNat]
#guard (observe .SAR 11 dirty negativeThree []).toOption.map (fun s => s.2.1) ==
  some [maximum.toNat,dirty.toNat,negativeThree.toNat]
#guard (observe .SAR 11 257 dirty []).toOption.map (fun s => s.2.1) == some [0,257,dirty.toNat]
#guard (observe .SAR 11 8 dirty []).toOption.map (fun s => s.2.1) == some [2^192+1,8,dirty.toNat]
#guard (observe .SAR 11 0 negativeThree []).toOption.map (fun s => s.2.1) ==
  some [negativeThree.toNat,0,negativeThree.toNat]
#guard (observe .SAR 11 0 0 []).toOption.map (fun s => s.2.1) == some [0,0,0]
#guard (Assembly.driverSteps 3 4 #[] {(state .SAR 11 1 negativeThree []) with
  executionEnv := {(state .SAR 11 1 negativeThree []).executionEnv with perm := true}}).toOption.map
  (fun s => (s.executionEnv.perm,s.stack.map UInt256.toNat)) == some (true,[2^256-2,1,negativeThree.toNat])
#guard (state .SAR 11 1 negativeThree []).executionEnv.code.data.toList =
  [0x61,0x01,0x01,0x00,0x81,0x81,0x1d,0x80,0x01,0x00]
#guard (observe .SAR 11 1 7 (List.replicate 1020 77)).toOption.map (fun s => s.2.1.length) = some 1023
#guard match observe .SAR 11 1 7 (List.replicate 1021 77) with
  | .error .StackOverflow => true | _ => false
-- Finite sufficient-gas controls; the general theorem retains old gas11.
#guard (observe .SAR 9 1 negativeThree []).toOption.map (fun s => s.2.2.1) = some 0
#guard match observe .SAR 8 1 negativeThree [] with | .error .OutOfGass => true | _ => false
#guard match observe .SAR 2 1 negativeThree [] with | .error .OutOfGass => true | _ => false
#guard match Assembly.driverSteps 3 3 #[] (state .SAR 11 1 negativeThree []) with
  | .error .OutOfFuel => true | _ => false
#guard match Assembly.driverSteps 3 4 #[] {(state .SAR 11 1 negativeThree []) with stack := []} with
  | .error .StackUnderflow => true | _ => false
-- Finite suffix regression, not a universal suffix theorem.
#guard (Assembly.driverSteps 5 6 #[] (state .SAR 15 1 negativeThree [77])).toOption.map observeState ==
  some (9,[2^256-4,1,negativeThree.toNat,77],0,12,3,[0xaa],[0xbb],[0xcc],false)
#print axioms sar_continuation
end SolidityBridge.Yul.ChargedArithmeticShift.Controls
