import SolidityBridge.Yul.ByteSelection
import SolidityBridge.Yul.ArithmeticSelectionControls
namespace SolidityBridge.Yul.ByteSelection.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev maximum := ArithmeticSelection.Controls.maximum
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe
def highOnly : Scalar.Word := BitVec.ofNat 256 (2^200)
def pattern : Scalar.Word := BitVec.ofNat 256 (0x12*2^248+0xAB)
#check (push (Solidity.Yul.word 255) (by decide)).success [dirty,71] [255,dirty,71] (machine [dirty,71]) rfl
#check (push (Solidity.Yul.word 0) (by decide)).refusal [] (machine []) rfl
#guard (compileLeaf [Scalar.pushByte 0]).isSome
#guard (compileLeaf [Scalar.pushByte 255]).isSome
#guard (compileLeaf [Scalar.pushWord 0]).isSome
#guard (compileLeaf [Scalar.pushWord dirty]).isSome
#guard (ExpSelection.compileLeaf [Scalar.pushByte 0]).isNone
#guard (compileLeaf [Scalar.pushWord 1,Scalar.pushByte 1]).isNone
#guard (compileLeaf [.push 2 #v[0,1]]).isNone
#guard (compileLeaf [.push 0 #v[]]).isNone
#guard (ControlRealization.selectSliceUsing (fun _ => some [.push (.val (Solidity.Yul.word 1))]) select [Scalar.pushByte 2]).isNone
#guard (compileLeaf [.op .BYTE]).isNone
#guard (compileLeaf [.op .SAR]).isNone
#guard (compileLeaf [.op .SIGNEXTEND]).isNone
#guard (compileBlock (.loop [] (.code []))).isNone
#guard (NormalControl.compile 5 statement).isNone
#guard (compiled.emit 16).isNone
#guard (compileLeaf byteExpansion).isSome
#guard (ExpSelection.compileLeaf byteExpansion).isNone
#check source_model #v[0,pattern,dirty] #v[] [71] (machine [0,pattern,dirty,71]) rfl
#check prefixed_source_model #v[31,pattern,dirty] #v[dirty,99] [71] (machine [dirty,99,31,pattern,dirty,71]) rfl
#check lowering
#check prefixed_lowering
#check ControlCompleteness.fault_iff_with compileLeaf selected (by rfl) [] (machine []) rfl

def sourceResult (index value flag : Scalar.Word) :=
  (Solidity.Yul.Closed.evalStmt 6 .nil True.intro statement compiled.profile
    (ProducerExpressions.sourceLocals #v[index,value,flag])).map
      (fun out => ((out.vars 0).val,(out.vars 1).val,(out.vars 2).val,out.flow.isNormal))
#guard sourceResult 0 pattern dirty == some (0x12,0,1,true)
#guard sourceResult 31 pattern dirty == some (0xAB,0,1,true)
#guard sourceResult 1 pattern dirty == some (1,pattern.toNat,dirty.toNat,true)
#guard sourceResult 32 pattern dirty == some (32,pattern.toNat,dirty.toNat,true)
#guard sourceResult highOnly pattern dirty == some (highOnly.toNat,pattern.toNat,dirty.toNat,true)
#guard sourceResult 6 dirty maximum == some (1,0,1,true)
#guard sourceResult 31 dirty maximum == some (1,0,1,true)
#guard sourceResult 0 maximum dirty == some (255,0,1,true)
#guard observe (Evm.run selected.ir (machine [0,pattern,dirty,71])) ==
  some ([some 0x12,some 0,some 1,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run prefixed.ir (machine [dirty,99,31,pattern,dirty,71])) ==
  some ([some dirty.toNat,some 99,some 0xAB,some 0,some 1,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard match Evm.run selected.ir (machine [dirty]) with | .fault => true | _ => false
#guard (observe (Evm.run selected.ir (machine (0::pattern::dirty::List.replicate 1020 71)))).isSome
#guard Scalar.stackBound [Scalar.pushByte 255] 1023
#guard !Scalar.stackBound [Scalar.pushByte 255] 1024
#guard (Scalar.run [Scalar.pushByte 255] (List.replicate 1024 dirty)).isSome

-- Enforce observed scoped transitive axiom reports.
/-- info: 'SolidityBridge.Yul.ByteSelection.compact_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ByteSelection.compact_run
/-- info: 'SolidityBridge.Yul.ByteSelection.push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ByteSelection.push
/-- info: 'SolidityBridge.Yul.ByteSelection.select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ByteSelection.select
/-- info: 'SolidityBridge.Yul.ByteSelection.compileLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ByteSelection.compileLeaf
/-- info: 'SolidityBridge.Yul.ByteSelection.compileBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ByteSelection.compileBlock
/-- info: 'SolidityBridge.Yul.ByteSelection.compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ByteSelection.compiled
/-- info: 'SolidityBridge.Yul.ByteSelection.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ByteSelection.selected
/-- info: 'SolidityBridge.Yul.ByteSelection.lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ByteSelection.lowering
/-- info: 'SolidityBridge.Yul.ByteSelection.source_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ByteSelection.source_model
/-- info: 'SolidityBridge.Yul.ByteSelection.prefixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ByteSelection.prefixed
/-- info: 'SolidityBridge.Yul.ByteSelection.prefixed_lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ByteSelection.prefixed_lowering
/-- info: 'SolidityBridge.Yul.ByteSelection.prefixed_source_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ByteSelection.prefixed_source_model
/-- info: 'SolidityBridge.Yul.ByteSelection.compact_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ByteSelection.compact_capacity

end SolidityBridge.Yul.ByteSelection.Controls
