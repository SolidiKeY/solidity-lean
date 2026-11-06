import SolidityBridge.Yul.OccurrenceSelection
import SolidityBridge.Yul.ArithmeticSelectionControls
namespace SolidityBridge.Yul.OccurrenceSelection.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev maximum := ArithmeticSelection.Controls.maximum
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe
def pattern : Scalar.Word := BitVec.ofNat 256 (0x12*2^248+0xAB)
#guard (ByteSelection.compileLeaf mixedCode).isNone
#guard (selectCode mixedCode).isSome
#guard mixedSelected.ir.length == 3
#guard (mixedSelected.certificates ⟨0,by decide⟩).code == [pushWord 31]
#guard (mixedSelected.certificates ⟨1,by decide⟩).code == [pushByte 31]
#guard (mixedSelected.certificates ⟨2,by decide⟩).code == [.op .ADD]
#guard (Scalar.run mixedCode [dirty,71]) == some [62,dirty,71]
#guard observe (Evm.run mixedSelected.ir (machine [dirty,71])) ==
  some ([some 62,some dirty.toNat,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard (selectCode [pushByte 31,pushWord 31,.op .ADD]).isSome
#guard (selectCode [pushWord dirty,pushByte 255,.op .XOR]).isSome
#guard (selectCode [.push 2 #v[0,31]]).isNone
#guard (selectCode [.push 0 #v[]]).isNone
#guard (selectCode [.op .BYTE]).isNone
#guard (selectCode [.op .SAR]).isNone
#guard (selectCode [.op .SLOAD]).isNone
#guard (checkStep (.op .SUB) .add ArithmeticSelection.add).isNone
#guard (selectStep (.op (.DUP 15))).isSome
#guard (selectStep (.op (.SWAP 15))).isSome
#guard (selectCode [.op .ADD]).isSome
#check fault_iff [.op .ADD] ((selectCode [.op .ADD]).get (by rfl)) [dirty] (machine [dirty]) rfl
#guard match Evm.run ((selectCode [.op .ADD]).get (by rfl)).ir (machine [dirty]) with | .fault => true | _ => false
#guard (ByteSelection.compileLeaf code).isNone
#guard (ByteSelection.compileLeaf prefixedCode).isNone
#guard (PureStatements.compile 2 statement).isNone
#guard (compiled.lowered.code 16).isNone
#check assignment_model #v[maximum,pattern,dirty] #v[] [71] (machine [maximum,pattern,dirty,71]) rfl
#check prefixed_model #v[maximum,pattern,dirty] #v[dirty,99] [71] (machine [dirty,99,maximum,pattern,dirty,71]) rfl
#check mixedLowering
#check assignmentLowering
#check prefixedLowering
#check selected.origin

def sourceResult (a value flag : Scalar.Word) :=
  (Solidity.Yul.Closed.evalStmt 3 .nil True.intro statement compiled.profile
    (ProducerExpressions.sourceLocals #v[a,value,flag])).map
      (fun out => ((out.vars 0).val,(out.vars 1).val,(out.vars 2).val,out.flow.isNormal))
#guard sourceResult maximum pattern dirty == some (0xAB,pattern.toNat,dirty.toNat,true)
#guard sourceResult 0 dirty maximum == some (1,dirty.toNat,maximum.toNat,true)
#guard sourceResult dirty 0 maximum == some (0,0,maximum.toNat,true)
#guard sourceResult 0 maximum dirty == some (255,maximum.toNat,dirty.toNat,true)
#guard observe (Evm.run selected.ir (machine [maximum,pattern,dirty,71])) ==
  some ([some 0xAB,some pattern.toNat,some dirty.toNat,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run prefixed.ir (machine [dirty,99,maximum,pattern,dirty,71])) ==
  some ([some dirty.toNat,some 99,some 0xAB,some pattern.toNat,some dirty.toNat,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard match Evm.run selected.ir (machine [dirty]) with | .fault => true | _ => false
#guard Scalar.stackBound mixedCode 1022
#guard !Scalar.stackBound mixedCode 1023
#guard (Scalar.run mixedCode (List.replicate 1023 dirty)).isSome
#guard (observe (Evm.run selected.ir (machine (maximum::pattern::dirty::List.replicate 1020 71)))).isSome

-- Enforce observed scoped transitive axiom reports.
/-- info: 'SolidityBridge.Yul.OccurrenceSelection.Certificates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceSelection.Certificates
/-- info: 'SolidityBridge.Yul.OccurrenceSelection.emit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceSelection.emit
/-- info: 'SolidityBridge.Yul.OccurrenceSelection.execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceSelection.execute
/-- info: 'SolidityBridge.Yul.OccurrenceSelection.Step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceSelection.Step
/-- info: 'SolidityBridge.Yul.OccurrenceSelection.checkStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceSelection.checkStep
/-- info: 'SolidityBridge.Yul.OccurrenceSelection.selectStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceSelection.selectStep
/-- info: 'SolidityBridge.Yul.OccurrenceSelection.Slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceSelection.Slice
/-- info: 'SolidityBridge.Yul.OccurrenceSelection.selectCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceSelection.selectCode
/-- info: 'SolidityBridge.Yul.OccurrenceSelection.lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceSelection.lowering
/-- info: 'SolidityBridge.Yul.OccurrenceSelection.fault_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceSelection.fault_iff
/-- info: 'SolidityBridge.Yul.OccurrenceSelection.source_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceSelection.source_model
/-- info: 'SolidityBridge.Yul.OccurrenceSelection.mixedSelected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceSelection.mixedSelected
/-- info: 'SolidityBridge.Yul.OccurrenceSelection.mixedLowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceSelection.mixedLowering
/-- info: 'SolidityBridge.Yul.OccurrenceSelection.compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceSelection.compiled
/-- info: 'SolidityBridge.Yul.OccurrenceSelection.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceSelection.selected
/-- info: 'SolidityBridge.Yul.OccurrenceSelection.assignmentLowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceSelection.assignmentLowering
/-- info: 'SolidityBridge.Yul.OccurrenceSelection.assignment_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceSelection.assignment_model
/-- info: 'SolidityBridge.Yul.OccurrenceSelection.prefixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceSelection.prefixed
/-- info: 'SolidityBridge.Yul.OccurrenceSelection.prefixedLowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceSelection.prefixedLowering
/-- info: 'SolidityBridge.Yul.OccurrenceSelection.prefixed_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceSelection.prefixed_model

end SolidityBridge.Yul.OccurrenceSelection.Controls
