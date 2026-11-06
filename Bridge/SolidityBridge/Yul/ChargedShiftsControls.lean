import SolidityBridge.Yul.ChargedShifts
import SolidityBridge.Yul.ChargedQuotientPrefixControls
namespace SolidityBridge.Yul.ChargedShifts.Controls
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
#check shl_continuation prelude suffix fits (seed 11) 8 dirty [77] (by decide) (by decide) 0
#check shr_continuation prelude suffix fits (seed 11) 8 dirty [77] (by decide) (by decide) 0
#guard (observe .SHL 11 8 dirty [77]).toOption ==
  some (7,[2^208+65792,8,dirty.toNat,77],2,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe .SHR 11 8 dirty [77]).toOption ==
  some (7,[2^192+1,8,dirty.toNat,77],2,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe .SHL 11 255 3 []).toOption ==
  some (7,[2^255,255,3],2,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe .SHR 11 255 maximum []).toOption ==
  some (7,[1,255,maximum.toNat],2,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe .SHL 11 256 dirty []).toOption.map (fun s => s.2.1) == some [0,256,dirty.toNat]
#guard (observe .SHR 11 257 dirty []).toOption.map (fun s => s.2.1) == some [0,257,dirty.toNat]
#guard (observe .SHL 11 dirty 1 []).toOption.map (fun s => s.2.1) == some [0,dirty.toNat,1]
#guard (observe .SHR 11 0 dirty []).toOption.map (fun s => s.2.1) == some [dirty.toNat,0,dirty.toNat]
#guard (Assembly.driverSteps 3 4 #[] {(state .SHL 11 1 7 []) with
  executionEnv := {(state .SHL 11 1 7 []).executionEnv with perm := true}}).toOption.map
  (fun s => (s.executionEnv.perm,s.stack.map UInt256.toNat)) == some (true,[14,1,7])
#guard (state .SHL 11 1 7 []).executionEnv.code.data.toList =
  [0x61,0x01,0x01,0x00,0x81,0x81,0x1b,0x80,0x01,0x00]
#guard (state .SHR 11 1 7 []).executionEnv.code.data.toList =
  [0x61,0x01,0x01,0x00,0x81,0x81,0x1c,0x80,0x01,0x00]
#guard (observe .SHL 11 1 7 (List.replicate 1020 77)).toOption.map (fun s => s.2.1.length) = some 1023
#guard match observe .SHL 11 1 7 (List.replicate 1021 77) with
  | .error .StackOverflow => true | _ => false
-- Finite checks show gas9 can suffice. The general theorem explicitly uses
-- the unchanged sufficient gas11 prefix contract; no minimum claim follows.
#guard (observe .SHR 9 1 7 []).toOption.map (fun s => s.2.2.1) = some 0
#guard match observe .SHR 8 1 7 [] with | .error .OutOfGass => true | _ => false
#guard match observe .SHL 2 1 7 [] with | .error .OutOfGass => true | _ => false
#guard match Assembly.driverSteps 3 3 #[] (state .SHL 11 1 7 []) with
  | .error .OutOfFuel => true | _ => false
#guard match Assembly.driverSteps 3 4 #[] {(state .SHR 11 1 7 []) with stack := []} with
  | .error .StackUnderflow => true | _ => false
-- Finite suffix regression, not universal future suffix execution.
#guard (Assembly.driverSteps 5 6 #[] (state .SHL 15 1 7 [77])).toOption.map observeState ==
  some (9,[28,1,7,77],0,12,3,[0xaa],[0xbb],[0xcc],false)
#guard (PureExpressions.compile 1 ShiftSubMachine.shlExpr).isNone
#guard (PureExpressions.compile 1 ShiftSubMachine.shrExpr).isNone
#print axioms shl_continuation
#print axioms shr_continuation
end SolidityBridge.Yul.ChargedShifts.Controls
