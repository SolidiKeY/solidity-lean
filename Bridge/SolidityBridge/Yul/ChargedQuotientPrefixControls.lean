import SolidityBridge.Yul.ChargedQuotientPrefix
import SolidityBridge.Yul.ChargedQuotientsControls
namespace SolidityBridge.Yul.ChargedQuotientPrefix.Controls
open Solidity Solidity.Yul.Compilation Backend Scalar
open Solidity.Evm.External EvmYul
abbrev seed := ChargedQuotients.Controls.seed
abbrev dirty := ChargedQuotients.Controls.dirty
abbrev maximum := ChargedQuotients.Controls.maximum

def observeState (s : EVM.State) : Nat × List Nat × Nat × Nat × Nat × List UInt8 × List UInt8 × List UInt8 × Bool :=
  (s.pc.toNat,s.stack.map UInt256.toNat,s.gasAvailable.toNat,s.execLength,s.activeWords.toNat,
    s.memory.data.toList,s.returnData.data.toList,s.H_return.data.toList,s.executionEnv.perm)
def observe (remainder : Bool) (gas : Nat) (a b : Scalar.Word) (caller : Scalar.Stack) :=
  (Assembly.driverSteps 3 4 #[] (entry (seed gas) (if remainder then .MOD else .DIV) a b caller)).map observeState
#guard (observe false 11 7 3 [dirty,77]).toOption ==
  some (3,[2,7,3,dirty.toNat,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe true 11 7 3 [dirty,77]).toOption ==
  some (3,[1,7,3,dirty.toNat,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe false 11 7 0 [77]).toOption ==
  some (3,[0,7,0,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe true 11 7 0 [77]).toOption ==
  some (3,[0,7,0,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe false 100 dirty 1 [77]).toOption ==
  some (3,[dirty.toNat,dirty.toNat,1,77],89,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe false 11 maximum 2 [77]).toOption ==
  some (3,[2^255-1,maximum.toNat,2,77],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard (observe false 11 3 7 []).toOption ==
  some (3,[0,3,7],0,10,3,[0xaa],[0xbb],[0xcc],false)
#guard observeState (firstRead (seed 11) .DIV 7 3 [dirty,77]) ==
  (1,[3,7,3,dirty.toNat,77],8,8,3,[0xaa],[0xbb],[0xcc],false)
#guard observeState (secondRead (seed 11) .DIV 7 3 [dirty,77]) ==
  (2,[7,3,7,3,dirty.toNat,77],5,9,3,[0xaa],[0xbb],[0xcc],false)
#guard (entry (seed 11) .DIV 7 3 []).executionEnv.code.data.toList = [0x81,0x81,0x04]
#guard (entry (seed 11) .MOD 7 3 []).executionEnv.code.data.toList = [0x81,0x81,0x06]
#guard (observe false 11 7 3 (List.replicate 1020 77)).toOption.map (fun x => x.2.1.length) = some 1023
-- The arithmetic-only site previously allowed caller1021; its preceding DUP
-- really overflows, so that single-op gate never justified whole-prefix success.
#guard match observe false 11 7 3 (List.replicate 1021 77) with
  | .error .StackOverflow => true | _ => false
#guard match observe true 11 7 3 (List.replicate 1022 77) with
  | .error .StackOverflow => true | _ => false
#guard match observe false 10 7 3 [] with | .error .OutOfGass => true | _ => false
#guard match observe false 5 7 3 [] with | .error .OutOfGass => true | _ => false
#guard match observe false 2 7 3 [] with | .error .OutOfGass => true | _ => false
#guard match observe false 3 7 3 (List.replicate 1021 77) with
  | .error .OutOfGass => true | _ => false
#guard match observe false 6 7 3 (List.replicate 1021 77) with
  | .error .StackOverflow => true | _ => false
#guard match Assembly.driverSteps 3 3 #[] (entry (seed 11) .DIV 7 3 []) with
  | .error .OutOfFuel => true | _ => false
#guard match Assembly.driverSteps 3 4 #[] {(entry (seed 11) .DIV 7 3 []) with stack := []} with
  | .error .StackUnderflow => true | _ => false
#guard match Assembly.driverSteps 3 4 #[] {(entry (seed 2) .DIV 7 3 []) with stack := []} with
  | .error .OutOfGass => true | _ => false
#guard match Assembly.driverSteps 3 4 #[] {(entry (seed 11) .DIV 7 3 []) with pc := .ofNat 1} with
  | .error .InvalidInstruction => true | _ => false
#print axioms reads
#print axioms div_continuation
#print axioms mod_continuation
end SolidityBridge.Yul.ChargedQuotientPrefix.Controls
