import SolidityBridge.Yul.ChargedQuotients
namespace SolidityBridge.Yul.ChargedQuotients.Controls
open Solidity Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation
open Backend Scalar Solidity.Evm.External EvmYul

def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def maximum : Scalar.Word := BitVec.ofNat 256 (2^256-1)
def seed (gas : Nat) : EVM.State :=
  {(default : EVM.State) with
    gasAvailable := .ofNat gas,execLength := 7,activeWords := .ofNat 3
    memory := ⟨#[0xaa]⟩,returnData := ⟨#[0xbb]⟩,H_return := ⟨#[0xcc]⟩
    executionEnv := {(default : EVM.State).executionEnv with perm := false}}

def sourceDiv (a b : Scalar.Word) : Option Nat :=
  (evalExpr 2 .nil True.intro divExpr divCompiled.profile
    (ProducerExpressions.sourceLocals #v[a,b])).map (fun values => (values 0).val)
def sourceMod (a b : Scalar.Word) : Option Nat :=
  (evalExpr 2 .nil True.intro modExpr modCompiled.profile
    (ProducerExpressions.sourceLocals #v[a,b])).map (fun values => (values 0).val)
#guard divCompiled.lowered.code 0 = some divProgram
#guard modCompiled.lowered.code 0 = some modProgram
#guard Scalar.run reads [7,3,dirty,77] = some (packet 7 3 [dirty,77])
#guard Scalar.run reads [] = none
#guard Scalar.run reads [7] = none
#guard sourceDiv 7 3 == some 2
#guard sourceMod 7 3 == some 1
#guard sourceDiv 7 0 == some 0
#guard sourceMod 7 0 == some 0
#guard sourceDiv maximum 2 == some (2^255-1)
#guard sourceDiv dirty 1 == some dirty.toNat
#guard sourceMod dirty 256 == some 1
#guard sourceDiv 3 7 != sourceDiv 7 3
#guard ((PureExpressions.compile 1 divExpr).isNone)
#guard Scalar.stackBound divProgram 1022
#guard Scalar.stackBound modProgram 1022
#guard !(Scalar.stackBound divProgram 1023)
#guard !(Scalar.stackBound modProgram 1023)
#guard (divSite (seed 5)).state.executionEnv.code.data.toList = [0x81,0x81,0x04]
#guard (modSite (seed 5)).state.executionEnv.code.data.toList = [0x81,0x81,0x06]
#guard (divSite (seed 5)).state.pc.toNat = 2

def observeState (s : EVM.State) : Nat × List Nat × Nat × Nat × List UInt8 × List UInt8 × List UInt8 × Bool :=
  (s.pc.toNat,s.stack.map UInt256.toNat,s.gasAvailable.toNat,s.execLength,
    s.memory.data.toList,s.returnData.data.toList,s.H_return.data.toList,s.executionEnv.perm)
def observe (remainder : Bool) (gas : Nat) (a b : Scalar.Word) (caller : Scalar.Stack) :=
  (Assembly.driverSteps 1 2 #[]
    (if remainder then (modInput (seed gas) a b caller).state else (divInput (seed gas) a b caller).state)).map observeState
#guard (observe false 5 7 3 [dirty,77]).toOption ==
  some (3,[2,7,3,dirty.toNat,77],0,8,[0xaa],[0xbb],[0xcc],false)
#guard (observe true 5 7 3 [dirty,77]).toOption ==
  some (3,[1,7,3,dirty.toNat,77],0,8,[0xaa],[0xbb],[0xcc],false)
#guard (observe false 5 7 0 [77]).toOption ==
  some (3,[0,7,0,77],0,8,[0xaa],[0xbb],[0xcc],false)
#guard (observe true 5 7 0 [77]).toOption ==
  some (3,[0,7,0,77],0,8,[0xaa],[0xbb],[0xcc],false)
#guard (observe false 100 dirty 1 [77]).toOption ==
  some (3,[dirty.toNat,dirty.toNat,1,77],95,8,[0xaa],[0xbb],[0xcc],false)
#guard match observe false 4 7 3 [] with | .error .OutOfGass => true | _ => false
#guard ((observe false 5 7 3 (List.replicate 1020 77)).toOption.map (fun x => x.2.1.length)) = some 1023
-- Deliberately oversized entry: this single shrinking opcode can pass its gate.
-- The full source expression's stackBound above correctly refuses that prefix.
#guard (packet 7 3 (List.replicate 1021 77)).length = 1025
#guard ((observe false 5 7 3 (List.replicate 1021 77)).toOption.map (fun x => x.2.1.length)) = some 1024
#guard match observe false 5 7 3 (List.replicate 1022 77) with
  | .error .StackOverflow => true | _ => false
#guard match observe true 4 7 3 (List.replicate 1022 77) with
  | .error .OutOfGass => true | _ => false
#guard match Assembly.driverSteps 1 2 #[] (divSite (seed 5)).state with
  | .error .StackUnderflow => true | _ => false
#guard match Assembly.driverSteps 1 1 #[] (divInput (seed 0) 7 3 []).state with
  | .error .OutOfFuel => true | _ => false
-- Changing PC changes the fetched opcode; a site is not just a word equation.
#guard ((Assembly.driverSteps 1 2 #[] {(divInput (seed 5) 7 3 []).state with pc := .ofNat 0}).toOption.map
  (fun s => s.stack.map UInt256.toNat)) == some [3,7,3,7,3]
#print axioms gate
#print axioms divAgreement
#print axioms modAgreement
end SolidityBridge.Yul.ChargedQuotients.Controls
