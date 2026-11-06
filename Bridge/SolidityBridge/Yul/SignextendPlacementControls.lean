import SolidityBridge.Yul.SignextendPlacement
import SolidityBridge.Yul.SignedPlacementControls
/-! Executable native/reference controls for concrete inhabited producer
instances. Kernel theorem and external compiler/client evidence stay separate. -/
namespace SolidityBridge.Yul.SignextendPlacement.Controls
open Solidity Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation Backend Scalar
open Solidity.Evm.External EvmYul QuotientPlacement
abbrev seed := SignedPlacement.Controls.seed
abbrev dirty := SignedPlacement.Controls.dirty
abbrev observeState := SignedPlacement.Controls.observeState

def prelude : Backend.Program := [.push 2 #v[0x0b,0x05],.op .STOP]
theorem fits : (Backend.encode prelude).length+3<UInt256.size := by decide
def suffix : Backend.Program := [.op (.DUP 0),.op .ADD,.op .STOP]
def maximum : Scalar.Word := BitVec.ofNat 256 (2^256-1)
def minimum : Scalar.Word := BitVec.ofNat 256 (2^255)
def minus128 : Scalar.Word := BitVec.ofInt 256 (-128)
def minus32768 : Scalar.Word := BitVec.ofInt 256 (-32768)
def observe (index value : Scalar.Word) (gas : Nat := 11) (caller : Scalar.Stack := [dirty,77]) :=
  (Assembly.driverSteps 3 4 #[] (entry prelude suffix fits (seed gas) .SIGNEXTEND index value caller)).map observeState

#check primitive.codeOrigin
#check signedPrimitive.codeOrigin
#check fun (a b : Scalar.Word) => compiled.source #v[a,b]
#check fun (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length≤1020) (gas : 11≤seed.gasAvailable.toNat) (fuel : Nat) =>
  continuation prelude suffix fits seed a b caller room gas fuel
#check fun (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length≤1020) (gas : 11≤seed.gasAvailable.toNat) (fuel : Nat) =>
  signedContinuation prelude suffix fits seed a b caller room gas fuel

#guard (observe 0 128).toOption ==
  some (7,[minus128.toNat,0,128,dirty.toNat,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe 0 255).toOption ==
  some (7,[maximum.toNat,0,255,dirty.toNat,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe 0 127).toOption ==
  some (7,[127,0,127,dirty.toNat,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe 0 0x17f).toOption ==
  some (7,[127,0,0x17f,dirty.toNat,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe 1 0x8000).toOption ==
  some (7,[minus32768.toNat,1,0x8000,dirty.toNat,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe 1 0x7f80).toOption ==
  some (7,[0x7f80,1,0x7f80,dirty.toNat,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe 0 dirty).toOption ==
  some (7,[1,0,dirty.toNat,dirty.toNat,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe 31 minimum).toOption ==
  some (7,[minimum.toNat,31,minimum.toNat,dirty.toNat,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe 32 dirty).toOption ==
  some (7,[dirty.toNat,32,dirty.toNat,dirty.toNat,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe maximum dirty).toOption ==
  some (7,[dirty.toNat,maximum.toNat,dirty.toNat,dirty.toNat,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe (BitVec.ofNat 256 (2^200+1)) dirty).toOption ==
  some (7,[dirty.toNat,2^200+1,dirty.toNat,dirty.toNat,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard ((Assembly.driverSteps 5 6 #[] (entry prelude suffix fits (seed 17) .SIGNEXTEND 0 128 [77])).map observeState).toOption ==
  some (9,[(BitVec.ofInt 256 (-256)).toNat,0,128,77],0,12,3,[0xaa],[0xbb],[0xcc],false)
#guard (entry prelude suffix fits (seed 11) .SIGNEXTEND 0 128 []).executionEnv.code.data.toList =
  [0x61,0x0b,0x05,0x00,0x81,0x81,0x0b,0x80,0x01,0x00]
#guard (entry prelude suffix fits (seed 11) .SIGNEXTEND 0 128 []).pc.toNat = 4
#guard (compiled.lowered.code 14).isSome
#guard (compiled.lowered.code 15).isNone
#guard (PureExpressions.compile 1 expr).isNone
#guard match observe 0 128 10 [] with | .error .OutOfGass => true | _ => false
#guard match observe 0 128 11 (List.replicate 1021 77) with
  | .error .StackOverflow => true | _ => false
#guard match Assembly.driverSteps 3 3 #[] (entry prelude suffix fits (seed 11) .SIGNEXTEND 0 128 []) with
  | .error .OutOfFuel => true | _ => false
#guard match Assembly.driverSteps 1 2 #[]
    {entry prelude suffix fits (seed 11) .SIGNEXTEND 0 128 [] with stack := []} with
  | .error .StackUnderflow => true | _ => false
#guard match Assembly.driverSteps 4 5 #[] (entry prelude [] fits (seed 11) .SIGNEXTEND 0 128 []) with
  | .error .InvalidInstruction => true | _ => false
-- Same generic consumer also has an actual SDIV compiler/native instance.
#guard ((Assembly.driverSteps 3 4 #[] (entry prelude suffix fits (seed 11) .SDIV
  SignedPlacement.Controls.negSeven 3 [77])).map observeState).toOption ==
  some (7,[SignedPlacement.Controls.minusTwo.toNat,SignedPlacement.Controls.negSeven.toNat,3,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#print axioms primitive
#print axioms continuation
#print axioms signedPrimitive
#print axioms signedContinuation
end SolidityBridge.Yul.SignextendPlacement.Controls
