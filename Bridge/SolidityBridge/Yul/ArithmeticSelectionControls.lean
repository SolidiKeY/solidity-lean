import SolidityBridge.Yul.ArithmeticSelection
namespace SolidityBridge.Yul.ArithmeticSelection.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation MachineAdapter

def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def maximum : Scalar.Word := BitVec.ofNat 256 (2^256-1)
def machine (input : Scalar.Stack) : Evm.Machine :=
  {(Evm.Machine.init (fun _ => 99) (Evm.wmod 7)) with
    stack := irStack input,mem := fun _ => coreWord dirty
    store := Evm.WordStore.ofFn (fun _ => 23),caller := Evm.wmod 11
    callvalue := Evm.wmod 19,timestamp := Evm.wmod 31,accepts := fun _ _ => false}
def number : Evm.Word → Option Nat
  | .val n => some n.val
  | .slot _ => none
def observe (out : Evm.Out) :=
  match out with
  | .ok m 0 => some (m.stack.map number,number (m.mem 7),m.store (.root 4),
      m.bal (Evm.wmod 5),m.bal₀ (Evm.wmod 5),m.self.val,m.caller.val,
      m.callvalue.val,m.timestamp.val,m.accepts (Evm.wmod 5) (Evm.wmod 1))
  | _ => none
#check add.success [dirty,255,77] [dirty+255,77] (machine [dirty,255,77]) rfl
#check mul.success [dirty,2,77] [dirty*2,77] (machine [dirty,2,77]) rfl
#check add.refusal [dirty] (machine [dirty]) rfl
#check mul.refusal [] (machine []) rfl
#check ArithmeticMachine.addCompiled.source #v[dirty,255]
#check ArithmeticMachine.mulCompiled.source #v[dirty,2]
#guard add.code = [.op .ADD]
#guard mul.code = [.op .MUL]
#guard ArithmeticMachine.addProgram = ArithmeticMachine.reads ++ add.code
#guard ArithmeticMachine.mulProgram = ArithmeticMachine.reads ++ mul.code
#guard observe (Evm.Instr.step .add (machine [dirty,255,77])) ==
  some ([some (2^200+512),some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.Instr.step .mul (machine [dirty,2,77])) ==
  some ([some (2^201+514),some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard (observe (Evm.Instr.step .add (machine [maximum,1]))).map (fun s => s.1) == some [some 0]
#guard (observe (Evm.Instr.step .mul (machine [BitVec.ofNat 256 (2^255),2]))).map (fun s => s.1) == some [some 0]
#guard match Evm.Instr.step .add (machine []) with | .fault => true | _ => false
#guard match Evm.Instr.step .add (machine [dirty]) with | .fault => true | _ => false
#guard match Evm.Instr.step .mul (machine []) with | .fault => true | _ => false
#guard match Evm.Instr.step .mul (machine [dirty]) with | .fault => true | _ => false
#guard Scalar.run add.code [] = none
#guard Scalar.run mul.code [dirty] = none
#guard observe (Evm.run [.add,.mul] (machine [dirty,255,2,77])) ==
  some ([some (2^201+1024),some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard Scalar.run (add.code ++ mul.code) [dirty,255,2,77] = some [(dirty+255)*2,77]
#guard (observe (Evm.run [.dup 2,.dup 2,.add] (machine [dirty,255,77]))).map (fun s => s.1) ==
  some [some (2^200+512),some dirty.toNat,some 255,some 77]
#guard Scalar.stackBound ArithmeticMachine.addProgram 1022
#guard !(Scalar.stackBound ArithmeticMachine.addProgram 1023)
-- Existing model success does not discharge physical 1024-word capacity.
#guard Scalar.run ArithmeticMachine.addProgram (dirty::255::List.replicate 1021 77) =
  some ((dirty+255)::dirty::255::List.replicate 1021 77)
#guard (observe (Evm.run [.dup 2,.dup 2,.add]
  (machine (dirty::255::List.replicate 1021 77)))).toList.length = 1
#guard !(Scalar.stackBound add.code 1025)
#print axioms add
#print axioms mul
end SolidityBridge.Yul.ArithmeticSelection.Controls
