import SolidityBridge.Yul.StackSelection
import SolidityBridge.Yul.ArithmeticSelectionControls
namespace SolidityBridge.Yul.StackSelection.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev maximum := ArithmeticSelection.Controls.maximum
def addProgram := SelectionSequence.emit [.dup 2,.dup 2,.add] addCertificates
def mulProgram := SelectionSequence.emit [.dup 2,.dup 2,.mul] mulCertificates
#guard addProgram = ArithmeticMachine.addProgram
#guard mulProgram = ArithmeticMachine.mulProgram
#guard ArithmeticMachine.addCompiled.lowered.code 0 = some addProgram
#guard ArithmeticMachine.mulCompiled.lowered.code 0 = some mulProgram
#check SelectionSequence.execute [.dup 2,.dup 2,.add] addCertificates
  [dirty,255,77] (machine [dirty,255,77]) rfl
#check SelectionSequence.execute [.dup 2,.dup 2,.mul] mulCertificates
  [dirty,2,77] (machine [dirty,2,77]) rfl
#check SelectionSequence.execute [.dup 2,.dup 2,.add] addCertificates
  [dirty] (machine [dirty]) rfl
#check (dup 0).success [dirty,77] [dirty,dirty,77] (machine [dirty,77]) rfl
#check (dup 15).refusal (List.replicate 15 dirty) (machine (List.replicate 15 dirty)) rfl
#guard (select (.dup 1)).map (fun c => c.code) = some [.op (.DUP 0)]
#guard (select (.dup 16)).map (fun c => c.code) = some [.op (.DUP 15)]
#guard (select (.dup 0)).isNone
#guard (select (.dup 17)).isNone
#guard (select .sub).isNone
#guard (observe (Evm.Instr.step (.dup 1) (machine [dirty,77]))).map (fun s => s.1) ==
  some [some dirty.toNat,some dirty.toNat,some 77]
def sixteen : Scalar.Stack := List.replicate 15 dirty ++ [maximum]
#guard Scalar.run (dup 15).code (sixteen ++ [77]) = some (maximum::(sixteen ++ [77]))
#guard (observe (Evm.Instr.step (.dup 16) (machine (sixteen ++ [77])))).map (fun s => s.1) ==
  some ((maximum::(sixteen ++ [77])).map (fun w => some w.toNat))
#guard Scalar.run (dup 15).code (List.replicate 15 dirty) = none
#guard match Evm.Instr.step (.dup 16) (machine (List.replicate 15 dirty)) with
  | .fault => true | _ => false
#guard Scalar.run (dup 0).code [] = none
#guard match Evm.Instr.step (.dup 1) (machine []) with | .fault => true | _ => false
-- The uncapped model can execute DUP17; the real Backend Fin16 encoding cannot.
#guard (observe (Evm.Instr.step (.dup 17) (machine (List.replicate 17 dirty)))).isSome
#guard Scalar.run addProgram [dirty,255,77] = some [dirty+255,dirty,255,77]
#guard Scalar.run mulProgram [dirty,2,77] = some [dirty*2,dirty,2,77]
#guard observe (Evm.run [.dup 2,.dup 2,.add] (machine [dirty,255,77])) ==
  some ([some (2^200+512),some dirty.toNat,some 255,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run [.dup 2,.dup 2,.mul] (machine [dirty,2,77])) ==
  some ([some (2^201+514),some dirty.toNat,some 2,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard Scalar.run addProgram [maximum,1,77] = some [0,maximum,1,77]
#guard Scalar.run addProgram [dirty] = none
#guard match Evm.run [.dup 2,.dup 2,.add] (machine [dirty]) with | .fault => true | _ => false
#guard Scalar.stackBound addProgram 1022
#guard !(Scalar.stackBound addProgram 1023)
#guard (Scalar.run addProgram (dirty::255::List.replicate 1021 77)).isSome
#guard (observe (Evm.run [.dup 2,.dup 2,.add] (machine (dirty::255::List.replicate 1021 77)))).isSome
#print axioms dup
#print axioms addCertificates
#print axioms mulCertificates
end SolidityBridge.Yul.StackSelection.Controls
