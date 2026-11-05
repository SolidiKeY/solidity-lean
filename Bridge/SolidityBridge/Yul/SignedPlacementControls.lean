import SolidityBridge.Yul.SignedPlacement
import SolidityBridge.Yul.ChargedQuotientPrefixControls
/-! Executable Lean/reference controls, separate from kernel-checked general
prefix theorems and from external solc/EVM-client evidence. -/
namespace SolidityBridge.Yul.SignedPlacement.Controls
open Solidity Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation Backend Scalar
open Solidity.Evm.External EvmYul QuotientPlacement
abbrev seed := ChargedQuotients.Controls.seed
abbrev dirty := ChargedQuotients.Controls.dirty
abbrev observeState := ChargedQuotientPrefix.Controls.observeState

def prelude : Backend.Program := [.push 2 #v[0x05,0x07],.op .STOP]
theorem fits : (Backend.encode prelude).length + 3 < UInt256.size := by decide
def continuation : Backend.Program := [.op (.DUP 0),.op .ADD,.op .STOP]
def negSeven : Scalar.Word := BitVec.ofInt 256 (-7)
def negThree : Scalar.Word := BitVec.ofInt 256 (-3)
def minusTwo : Scalar.Word := BitVec.ofInt 256 (-2)
def minusOne : Scalar.Word := BitVec.ofInt 256 (-1)
def minimum : Scalar.Word := BitVec.ofNat 256 (2^255)
def observe (op : Backend.Op) (gas : Nat) (a b : Scalar.Word) (caller : Scalar.Stack) :=
  (Assembly.driverSteps 3 4 #[] (entry prelude continuation fits (seed gas) op a b caller)).map observeState

#guard sdivCompiled.lowered.code 0 = some (ChargedQuotients.reads ++ [.op .SDIV])
#guard smodCompiled.lowered.code 0 = some (ChargedQuotients.reads ++ [.op .SMOD])
#guard (PureExpressions.compile 1 sdivExpr).isNone
#check fun (a b : Scalar.Word) => sdivCompiled.source #v[a,b]
#check fun (a b : Scalar.Word) => smodCompiled.source #v[a,b]
#guard (observe .SDIV 11 negSeven 3 [dirty,77]).toOption ==
  some (7,[minusTwo.toNat,negSeven.toNat,3,dirty.toNat,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe .SDIV 11 3 negSeven [77]).toOption ==
  some (7,[0,3,negSeven.toNat,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe .SMOD 11 negSeven 3 [77]).toOption ==
  some (7,[minusOne.toNat,negSeven.toNat,3,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe .SDIV 11 7 negThree []).toOption ==
  some (7,[minusTwo.toNat,7,negThree.toNat],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe .SMOD 11 7 negThree []).toOption ==
  some (7,[1,7,negThree.toNat],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe .SDIV 11 minimum minusOne [77]).toOption ==
  some (7,[minimum.toNat,minimum.toNat,minusOne.toNat,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe .SMOD 11 minimum minusOne [77]).toOption ==
  some (7,[0,minimum.toNat,minusOne.toNat,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe .SDIV 11 7 0 [77]).toOption ==
  some (7,[0,7,0,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe .SMOD 11 negSeven 0 [77]).toOption ==
  some (7,[0,negSeven.toNat,0,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe .SDIV 100 dirty 1 [77]).toOption ==
  some (7,[dirty.toNat,dirty.toNat,1,77],89,10,3,[0xaa],[0xbb],[0xcc],false)
#guard ((Assembly.driverSteps 5 6 #[] (entry prelude continuation fits (seed 17) .SDIV negSeven 3 [77])).map observeState).toOption ==
  some (9,[(BitVec.ofInt 256 (-4)).toNat,negSeven.toNat,3,77],0,12,3,[0xaa],[0xbb],[0xcc],false)
#guard (entry prelude continuation fits (seed 11) .SDIV 7 3 []).executionEnv.code.data.toList =
  [0x61,0x05,0x07,0x00,0x81,0x81,0x05,0x80,0x01,0x00]
#guard (entry prelude continuation fits (seed 11) .SDIV 7 3 []).pc.toNat = 4
#guard prelude.length = 2
#guard match observe .SDIV 10 7 3 [] with | .error .OutOfGass => true | _ => false
#guard match observe .SMOD 11 7 3 (List.replicate 1021 77) with
  | .error .StackOverflow => true | _ => false
-- Passing the shrinking arithmetic gate does not validate the earlier DUP peak.
#guard (Assembly.driverGate #[] (secondRead prelude continuation fits (seed 11) .SDIV 7 3
  (List.replicate 1021 77)) .SDIV).toOption.isSome
#guard match Assembly.driverSteps 3 3 #[] (entry prelude continuation fits (seed 11) .SDIV 7 3 []) with
  | .error .OutOfFuel => true | _ => false
#guard match Assembly.driverSteps 1 2 #[]
    {entry prelude continuation fits (seed 11) .SMOD 7 3 [] with stack := []} with
  | .error .StackUnderflow => true | _ => false
#guard match Assembly.driverSteps 4 5 #[] (entry prelude [] fits (seed 11) .SMOD 7 3 []) with
  | .error .InvalidInstruction => true | _ => false
#print axioms sdiv_continuation
#print axioms smod_continuation
end SolidityBridge.Yul.SignedPlacement.Controls
