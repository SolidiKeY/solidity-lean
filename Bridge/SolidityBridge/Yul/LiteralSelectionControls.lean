import SolidityBridge.Yul.LiteralSelection
import SolidityBridge.Yul.ArithmeticSelectionControls
namespace SolidityBridge.Yul.LiteralSelection.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation MachineAdapter
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev maximum := ArithmeticSelection.Controls.maximum
def program (literal : Scalar.Word) := SelectionSequence.emit (letIR literal) (letCertificates literal)
def zeroProgram := SelectionSequence.emit zeroIR zeroCertificates
#guard (letCompiled dirty).lowered.code 0 = some (program dirty)
#guard zeroCompiled.lowered.code 0 = some zeroProgram
#guard ((letCompiled dirty).lowered.code 1).isNone
#guard (zeroCompiled.lowered.code 1).isNone
#guard (ScopedStatements.compile 4 (letStatement dirty)).isNone
#guard (ScopedStatements.compile 4 zeroStatement).isNone
#guard (letCompiled dirty).update #v[17,99] = #v[dirty,dirty+99]
#guard (letCompiled maximum).update #v[17,1] = #v[maximum,0]
#guard zeroCompiled.update #v[dirty,17] = #v[dirty,dirty]
#check let_model dirty #v[17,99] [77] (machine [17,99,77]) rfl
#check zero_model #v[dirty,17] [77] (machine [dirty,17,77]) rfl
#check (push dirty).success [77] [dirty,77] (machine [77]) rfl
#check (push dirty).refusal [] (machine []) rfl
#guard (select (.push (coreWord dirty))).map (fun c => c.code) = some [pushWord dirty]
#guard (select (.push (.slot (.root 7)))).isNone
#guard Scalar.run (push dirty).code [77] = some [dirty,77]
#guard Scalar.run (push maximum).code [] = some [maximum]
#guard (Backend.encode (push dirty).code).length = 33
#guard (Backend.encode (program dirty)).length = 42
#guard (Backend.encode zeroProgram).length = 76
#guard observe (Evm.run (letIR dirty) (machine [17,99,77])) ==
  some ([some dirty.toNat,some (2^200+356),some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard (observe (Evm.run (letIR maximum) (machine [17,1,77]))).map (fun s => s.1) ==
  some [some maximum.toNat,some 0,some 77]
#guard observe (Evm.run zeroIR (machine [dirty,17,77])) ==
  some ([some dirty.toNat,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard Scalar.run (program dirty) [17] = none
#guard match Evm.run (letIR dirty) (machine [17]) with | .fault => true | _ => false
#guard Scalar.run zeroProgram [dirty] = none
#guard match Evm.run zeroIR (machine [dirty]) with | .fault => true | _ => false
#guard Scalar.stackBound (program dirty) 1021
#guard !(Scalar.stackBound (program dirty) 1022)
#guard Scalar.stackBound zeroProgram 1020
#guard !(Scalar.stackBound zeroProgram 1021)
#guard (Scalar.run (program dirty) (17::99::List.replicate 1020 77)).isSome
#guard (observe (Evm.run (letIR dirty) (machine (17::99::List.replicate 1020 77)))).isSome
#print axioms push
#print axioms let_model
#print axioms zero_model
end SolidityBridge.Yul.LiteralSelection.Controls
