import SolidityBridge.Yul.OccurrenceControl
import SolidityBridge.Yul.ArithmeticSelectionControls
namespace SolidityBridge.Yul.OccurrenceControl.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev maximum := ArithmeticSelection.Controls.maximum
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe
def highOnly : Scalar.Word := BitVec.ofNat 256 (2^200)
def pattern : Scalar.Word := BitVec.ofNat 256 (0x12*2^248+0xAB)
#guard (ByteSelection.compileBlock block).isNone
#guard (ByteSelection.compileBlock prefixedBlock).isNone
#guard (selectBlock block).isSome
#guard (selectBlock prefixedBlock).isSome
#guard (selectBlock (.loop [] (.code []))).isNone
#guard (selectBlock (.ite [pushWord 0] (.loop [] (.code [])) (.code []))).isNone
#guard (selectBlock (.code [.push 2 #v[0,31]])).isNone
#guard (selectBlock (.code [.op .BYTE])).isNone
#guard (selectBlock (.code [.op .SAR])).isNone
#guard (NormalControl.compile 4 statement).isNone
#guard (compiled.emit 16).isNone
#check source_model #v[maximum,pattern,dirty] #v[] [71] (machine [maximum,pattern,dirty,71]) rfl
#check prefixed_source_model #v[maximum,dirty,maximum] #v[dirty,99] [71] (machine [dirty,99,maximum,dirty,maximum,71]) rfl
#check lowering
#check prefixed_lowering
#check fault_iff block selected [] (machine []) rfl

def sourceResult (a value flag : Scalar.Word) :=
  (Solidity.Yul.Closed.evalStmt 5 .nil True.intro statement compiled.profile
    (ProducerExpressions.sourceLocals #v[a,value,flag])).map
      (fun out => ((out.vars 0).val,(out.vars 1).val,(out.vars 2).val,out.flow.isNormal))
#guard sourceResult maximum pattern dirty == some (0x12,pattern.toNat,0,true)
#guard sourceResult maximum dirty maximum == some (0,dirty.toNat,1,true)
#guard sourceResult maximum highOnly dirty == some (maximum.toNat,highOnly.toNat,dirty.toNat,true)
#guard sourceResult 42 0 dirty == some (42,0,dirty.toNat,true)
#guard sourceResult 0 maximum dirty == some (255,maximum.toNat,0,true)
#guard observe (Evm.run selected.realization.ir (machine [maximum,pattern,dirty,71])) ==
  some ([some 0x12,some pattern.toNat,some 0,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run prefixed.realization.ir (machine [dirty,99,maximum,dirty,maximum,71])) ==
  some ([some dirty.toNat,some 99,some 0,some dirty.toNat,some 1,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard match Evm.run selected.realization.ir (machine [dirty]) with | .fault => true | _ => false
#guard (observe (Evm.run selected.realization.ir (machine (maximum::pattern::dirty::List.replicate 1020 71)))).isSome

def trueBlock : Backend.Block := .ite [pushWord highOnly] (.code []) (.code [.op .ADD])
def trueSelected := (selectBlock trueBlock).get (by rfl)
def falseBlock : Backend.Block := .ite [pushWord 0] (.code [.op .ADD]) (.code [])
def falseSelected := (selectBlock falseBlock).get (by rfl)
#guard observe (Evm.run trueSelected.realization.ir (machine [])) ==
  some ([],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run falseSelected.realization.ir (machine [])) ==
  some ([],some dirty.toNat,23,99,99,7,11,19,31,false)
#check trueSelected.lowering
#check falseSelected.lowering

def emptyConditionBlock : Backend.Block := .ite [] (.code []) (.code [])
def emptyCondition := (selectBlock emptyConditionBlock).get (by rfl)
#guard match Evm.run emptyCondition.realization.ir (machine []) with | .fault => true | _ => false
#guard (observe (Evm.run emptyCondition.realization.ir (machine [dirty,71]))).map (fun out => out.1) == some [some 71]
#check fault_iff emptyConditionBlock emptyCondition [] (machine []) rfl

def thenFaultBlock : Backend.Block := .ite [pushWord highOnly] (.code [.op .ADD]) (.code [])
def thenFault := (selectBlock thenFaultBlock).get (by rfl)
def condFaultBlock : Backend.Block := .ite [.op .ADD] (.code []) (.code [])
def condFault := (selectBlock condFaultBlock).get (by rfl)
#guard match Evm.run thenFault.realization.ir (machine [dirty]) with | .fault => true | _ => false
#guard match Evm.run condFault.realization.ir (machine [dirty]) with | .fault => true | _ => false
#check fault_iff thenFaultBlock thenFault [dirty] (machine [dirty]) rfl

def firstFault := (selectBlock (.seq (.code [.op .ADD]) (.code []))).get (by rfl)
def laterFault := (selectBlock (.seq (.code []) (.code [.op .ADD]))).get (by rfl)
#guard match Evm.run firstFault.realization.ir (machine [dirty]) with | .fault => true | _ => false
#guard match Evm.run laterFault.realization.ir (machine [dirty]) with | .fault => true | _ => false

-- Enforce observed scoped transitive axiom reports.
/-- info: 'SolidityBridge.Yul.OccurrenceControl.Selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceControl.Selected
/-- info: 'SolidityBridge.Yul.OccurrenceControl.scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceControl.scalar
/-- info: 'SolidityBridge.Yul.OccurrenceControl.scalar_classified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceControl.scalar_classified
/-- info: 'SolidityBridge.Yul.OccurrenceControl.conditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceControl.conditional
/-- info: 'SolidityBridge.Yul.OccurrenceControl.conditional_classified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceControl.conditional_classified
/-- info: 'SolidityBridge.Yul.OccurrenceControl.leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceControl.leaf
/-- info: 'SolidityBridge.Yul.OccurrenceControl.combine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceControl.combine
/-- info: 'SolidityBridge.Yul.OccurrenceControl.branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceControl.branch
/-- info: 'SolidityBridge.Yul.OccurrenceControl.selectBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceControl.selectBlock
/-- info: 'SolidityBridge.Yul.OccurrenceControl.Selected.lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceControl.Selected.lowering
/-- info: 'SolidityBridge.Yul.OccurrenceControl.fault_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceControl.fault_iff
/-- info: 'SolidityBridge.Yul.OccurrenceControl.byteAt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceControl.byteAt
/-- info: 'SolidityBridge.Yul.OccurrenceControl.statement' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceControl.statement
/-- info: 'SolidityBridge.Yul.OccurrenceControl.compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceControl.compiled
/-- info: 'SolidityBridge.Yul.OccurrenceControl.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceControl.selected
/-- info: 'SolidityBridge.Yul.OccurrenceControl.lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceControl.lowering
/-- info: 'SolidityBridge.Yul.OccurrenceControl.source_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceControl.source_model
/-- info: 'SolidityBridge.Yul.OccurrenceControl.prefixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceControl.prefixed
/-- info: 'SolidityBridge.Yul.OccurrenceControl.prefixed_lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceControl.prefixed_lowering
/-- info: 'SolidityBridge.Yul.OccurrenceControl.prefixed_source_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.OccurrenceControl.prefixed_source_model

end SolidityBridge.Yul.OccurrenceControl.Controls
