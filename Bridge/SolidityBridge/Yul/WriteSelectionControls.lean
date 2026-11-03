import SolidityBridge.Yul.WriteSelection
import SolidityBridge.Yul.ArithmeticSelectionControls
namespace SolidityBridge.Yul.WriteSelection.Controls
open Solidity Backend Scalar Selection
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev maximum := ArithmeticSelection.Controls.maximum
def program := SelectionSequence.emit assignmentIR assignmentCertificates
def seqProgram := SelectionSequence.emit sequenceIR sequenceCertificates
#guard compiled.lowered.code 0 = some program
#guard sequenceCompiled.lowered.code 0 = some seqProgram
#guard (Solidity.Yul.Compilation.PureStatements.compile 3 sequenceStatement).isNone
#guard compiled.update #v[17,dirty] = #v[dirty,dirty]
#guard sequenceCompiled.update #v[17,dirty] = #v[dirty,dirty+dirty]
#check assignment_model #v[17,dirty] [77] (machine [17,dirty,77]) rfl
#check sequence_model #v[17,dirty] [77] (machine [17,dirty,77]) rfl
#check (swap 0).success [17,dirty,77] [dirty,17,77] (machine [17,dirty,77]) rfl
#check (swap 15).refusal (17::List.replicate 15 dirty) (machine (17::List.replicate 15 dirty)) rfl
#check pop.success [dirty,77] [77] (machine [dirty,77]) rfl
#check pop.refusal [] (machine []) rfl
#guard (select (.swap 1)).map (fun c => c.code) = some [.op (.SWAP 0)]
#guard (select (.swap 16)).map (fun c => c.code) = some [.op (.SWAP 15)]
#guard (select .pop).map (fun c => c.code) = some [.op .POP]
#guard (select (.swap 0)).isNone
#guard (select (.swap 17)).isNone
#guard Scalar.run (swap 0).code [17,dirty,77] = some [dirty,17,77]
#guard (observe (Evm.Instr.step (.swap 1) (machine [17,dirty,77]))).map (fun s => s.1) ==
  some [some dirty.toNat,some 17,some 77]
def sixteen : Scalar.Stack := List.replicate 15 dirty ++ [maximum]
#guard Scalar.run (swap 15).code (17::(sixteen ++ [77])) =
  some (maximum::((sixteen.set 15 17) ++ [77]))
#guard (observe (Evm.Instr.step (.swap 16) (machine (17::(sixteen ++ [77]))))).map (fun s => s.1) ==
  some ((maximum::((sixteen.set 15 17) ++ [77])).map (fun w => some w.toNat))
#guard Scalar.run (swap 15).code (17::List.replicate 15 dirty) = none
#guard match Evm.Instr.step (.swap 16) (machine (17::List.replicate 15 dirty)) with
  | .fault => true | _ => false
#guard Scalar.run (swap 0).code [dirty] = none
#guard match Evm.Instr.step (.swap 1) (machine [dirty]) with | .fault => true | _ => false
#guard Scalar.run pop.code [] = none
#guard match Evm.Instr.step .pop (machine []) with | .fault => true | _ => false
-- An uncapped model SWAP17 does not grant a Fin16 backend encoding.
#guard (observe (Evm.Instr.step (.swap 17) (machine (List.replicate 18 dirty)))).isSome
#guard observe (Evm.run assignmentIR (machine [17,dirty,77])) ==
  some ([some dirty.toNat,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run sequenceIR (machine [17,dirty,77])) ==
  some ([some dirty.toNat,some (2^201+514),some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard Scalar.run seqProgram [17,maximum,77] = some [maximum,maximum+maximum,77]
#guard Scalar.run program [dirty] = none
#guard match Evm.run assignmentIR (machine [dirty]) with | .fault => true | _ => false
#guard Scalar.stackBound program 1023
#guard !(Scalar.stackBound program 1024)
#guard Scalar.stackBound seqProgram 1022
#guard !(Scalar.stackBound seqProgram 1023)
#guard (Scalar.run seqProgram (17::dirty::List.replicate 1021 77)).isSome
#guard (observe (Evm.run sequenceIR (machine (17::dirty::List.replicate 1021 77)))).isSome
#print axioms swap
#print axioms pop
#print axioms assignment_model
#print axioms sequence_model
end SolidityBridge.Yul.WriteSelection.Controls
