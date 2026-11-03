import SolidityBridge.Yul.ChargedModular
import SolidityBridge.Yul.ChargedQuotientPrefixControls
namespace SolidityBridge.Yul.ChargedModular.Controls
open Solidity Solidity.Yul.Compilation Backend Scalar Solidity.Evm.External EvmYul
abbrev seed := ChargedQuotients.Controls.seed
abbrev dirty := ChargedQuotients.Controls.dirty
abbrev maximum := ChargedQuotients.Controls.maximum
abbrev observeState := ChargedQuotientPrefix.Controls.observeState
def prelude : Backend.Program := [.push 2 #v[0x01,0x01],.op .STOP]
def suffix : Backend.Program := [.op (.DUP 0),.op .ADD,.op .STOP]
def fits : (Backend.encode prelude).length+4<UInt256.size := by decide
def state (op : Backend.Op) (gas : Nat) (a b k : Scalar.Word) (caller : Scalar.Stack) :=
  entry prelude suffix fits (seed gas) op a b k caller
def observe (op : Backend.Op) (gas : Nat) (a b k : Scalar.Word) (caller : Scalar.Stack) :=
  (Assembly.driverSteps 4 5 #[] (state op gas a b k caller)).map observeState
#guard addCompiled.lowered.code 0 = some (reads ++ [.op .ADDMOD])
#guard mulCompiled.lowered.code 0 = some (reads ++ [.op .MULMOD])
#guard (addCompiled.lowered.code 13).isSome
#guard (addCompiled.lowered.code 14).isNone
#guard (PureExpressions.compile 1 addExpr).isNone
#guard (PureExpressions.compile 1 mulExpr).isNone
#check read_prefix prelude suffix fits (seed 17) .ADDMOD 35 64 17 [dirty,77] (by decide) (by decide) 0
#check add_continuation prelude suffix fits (seed 17) 35 64 17 [dirty,77] (by decide) (by decide) 0
#check mul_continuation prelude suffix fits (seed 17) 35 64 17 [dirty,77] (by decide) (by decide) 0
#guard (observe .ADDMOD 17 35 64 17 [dirty,77]).toOption ==
  some (8,[14,35,64,17,dirty.toNat,77],0,11,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe .MULMOD 17 35 64 17 [77]).toOption ==
  some (8,[13,35,64,17,77],0,11,3,[0xaa],[0xbb],[0xcc],false)
-- Unbounded intermediates: wrapping before taking the modulus would yield 0.
#guard (observe .ADDMOD 17 maximum 1 maximum []).toOption.map (fun s => s.2.1) ==
  some [1,maximum.toNat,1,maximum.toNat]
#guard (observe .MULMOD 17 (BitVec.ofNat 256 (2^255)) 2 3 []).toOption.map (fun s => s.2.1) ==
  some [1,2^255,2,3]
#guard (observe .ADDMOD 17 dirty 257 97 []).toOption.map (fun s => s.2.1) ==
  some [(2^200+514)%97,dirty.toNat,257,97]
#guard (observe .ADDMOD 17 35 64 dirty []).toOption.map (fun s => s.2.1) ==
  some [99,35,64,dirty.toNat]
#guard (observe .MULMOD 17 dirty maximum 0 []).toOption.map (fun s => s.2.1) ==
  some [0,dirty.toNat,maximum.toNat,0]
#guard (observe .ADDMOD 17 maximum dirty 0 []).toOption.map (fun s => s.2.1) ==
  some [0,maximum.toNat,dirty.toNat,0]
#guard observeState (firstRead prelude suffix fits (seed 17) .ADDMOD 35 64 17 [77]) ==
  (5,[17,35,64,17,77],14,8,3,[0xaa],[0xbb],[0xcc],false)
#guard observeState (secondRead prelude suffix fits (seed 17) .ADDMOD 35 64 17 [77]) ==
  (6,[64,17,35,64,17,77],11,9,3,[0xaa],[0xbb],[0xcc],false)
#guard observeState (thirdRead prelude suffix fits (seed 17) .ADDMOD 35 64 17 [77]) ==
  (7,[35,64,17,35,64,17,77],8,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (Assembly.driverSteps 4 5 #[] {(state .MULMOD 17 35 64 17 []) with
  executionEnv := {(state .MULMOD 17 35 64 17 []).executionEnv with perm := true}}).toOption.map
  (fun s => (s.executionEnv.perm,s.stack.map UInt256.toNat)) == some (true,[13,35,64,17])
#guard (state .ADDMOD 17 35 64 17 []).executionEnv.code.data.toList =
  [0x61,0x01,0x01,0x00,0x82,0x82,0x82,0x08,0x80,0x01,0x00]
#guard (state .MULMOD 17 35 64 17 []).executionEnv.code.data.toList =
  [0x61,0x01,0x01,0x00,0x82,0x82,0x82,0x09,0x80,0x01,0x00]
#guard (observe .ADDMOD 17 35 64 17 (List.replicate 1018 77)).toOption.map (fun s => s.2.1.length) = some 1022
#guard match observe .MULMOD 17 35 64 17 (List.replicate 1019 77) with
  | .error .StackOverflow => true | _ => false
#guard match observe .ADDMOD 16 35 64 17 [] with | .error .OutOfGass => true | _ => false
#guard match observe .MULMOD 8 35 64 17 [] with | .error .OutOfGass => true | _ => false
#guard match observe .ADDMOD 2 35 64 17 [] with | .error .OutOfGass => true | _ => false
#guard match Assembly.driverSteps 4 4 #[] (state .ADDMOD 17 35 64 17 []) with
  | .error .OutOfFuel => true | _ => false
#guard match Assembly.driverSteps 4 5 #[] {(state .MULMOD 17 35 64 17 []) with stack := []} with
  | .error .StackUnderflow => true | _ => false
-- Finite suffix regression, not a universal suffix theorem.
#guard (Assembly.driverSteps 6 7 #[] (state .MULMOD 23 35 64 17 [77])).toOption.map observeState ==
  some (10,[26,35,64,17,77],0,13,3,[0xaa],[0xbb],[0xcc],false)
#print axioms read_prefix
#print axioms add_continuation
#print axioms mul_continuation
end SolidityBridge.Yul.ChargedModular.Controls
