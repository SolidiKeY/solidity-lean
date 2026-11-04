import SolidityBridge.Yul.BranchModel
import SolidityBridge.Yul.ArithmeticSelectionControls
namespace SolidityBridge.Yul.BranchModel.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev maximum := ArithmeticSelection.Controls.maximum
def highOnly : Scalar.Word := BitVec.ofNat 256 (2^200)
def sourceResult (a b : Scalar.Word) :=
  (Solidity.Yul.Closed.evalStmt 4 .nil True.intro (.if_ test body)
    (branch condition arm).profile (ProducerExpressions.sourceLocals #v[a,b])).map
      (fun out => ((out.vars 0).val,(out.vars 1).val,out.flow.isNormal))
#check example_model #v[0,17] [77] (machine [0,17,77]) rfl
#check example_model #v[highOnly,17] [dirty,77] (machine [highOnly,17,dirty,77]) rfl
#check example_model #v[dirty,maximum] [77] (machine [dirty,maximum,77]) rfl
#check (rfl : compiled.emit 0 = some (.ite (SelectionSequence.emit conditionIR conditionCertificates)
  (.code (SelectionSequence.emit armIR armCertificates)) (.code [])))
#guard condition.lowered.code 0 = some (SelectionSequence.emit conditionIR conditionCertificates)
#guard arm.lowered.code 0 = some (SelectionSequence.emit armIR armCertificates)
#check (rfl : code = MachineControl.branchCode conditionIR armIR [])
#guard sourceResult 0 17 == some (0,17,true)
#guard sourceResult highOnly 17 == some (highOnly.toNat,18,true)
#guard sourceResult dirty maximum == some (dirty.toNat,0,true)
#guard observe (Evm.run code (machine [highOnly,17,dirty,77])) ==
  some ([some highOnly.toNat,some 18,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run code (machine [0,17,77])) ==
  some ([some 0,some 17,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard (observe (Evm.run code (machine [dirty,maximum,77]))).map (fun s => s.1) ==
  some [some dirty.toNat,some 0,some 77]
#guard match Evm.run code (machine []) with | .fault => true | _ => false
#guard match Evm.run code (machine [1]) with | .fault => true | _ => false
-- A false path can run on a short stack. It does not inhabit source Vector Word2.
#guard (observe (Evm.run code (machine [0]))).isSome
#guard (NormalControl.compile 3 (Solidity.Yul.Stmt.if_ test body)).isNone
#guard (condition.lowered.code 16).isNone
#guard (arm.lowered.code 16).isNone
#guard Scalar.stackBound (SelectionSequence.emit armIR armCertificates) 1022
#guard !(Scalar.stackBound (SelectionSequence.emit armIR armCertificates) 1023)
-- Uncapped model success supplies no expanded native-branch capacity certificate.
#guard (observe (Evm.run code (machine (highOnly::17::List.replicate 1021 77)))).isSome
#print axioms source_model
#print axioms example_model
end SolidityBridge.Yul.BranchModel.Controls
