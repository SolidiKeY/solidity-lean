import SolidityBridge.Yul.BitwiseSelection
import SolidityBridge.Yul.ArithmeticSelectionControls
namespace SolidityBridge.Yul.BitwiseSelection.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev maximum := ArithmeticSelection.Controls.maximum
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe
def high : Scalar.Word := BitVec.ofNat 256 (2^200)
def mask : Scalar.Word := BitVec.ofNat 256 (2^200+3)
#check band.success [dirty,maximum,71] [dirty,71] (machine [dirty,maximum,71]) rfl
#check bor.success [3,8,71] [11,71] (machine [3,8,71]) rfl
#check bxor.success [dirty,257,71] [high,71] (machine [dirty,257,71]) rfl
#check shl.success [256,maximum,71] [0,71] (machine [256,maximum,71]) rfl
#check shr.success [dirty,maximum,71] [0,71] (machine [dirty,maximum,71]) rfl
#check band.refusal [dirty] (machine [dirty]) rfl
#check shl.refusal [] (machine []) rfl
#check shr.refusal [dirty] (machine [dirty]) rfl
#guard observe (Evm.Instr.step .and (machine [dirty,maximum,71])) ==
  some ([some dirty.toNat,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard (observe (Evm.Instr.step .or (machine [3,8,71]))).map (fun s => s.1) == some [some 11,some 71]
#guard (observe (Evm.Instr.step .xor (machine [dirty,257,71]))).map (fun s => s.1) == some [some high.toNat,some 71]
#guard (observe (Evm.Instr.step .shl (machine [1,3,71]))).map (fun s => s.1) == some [some 6,some 71]
#guard (observe (Evm.Instr.step .shr (machine [1,3,71]))).map (fun s => s.1) == some [some 1,some 71]
#guard (observe (Evm.Instr.step .shl (machine [255,3,71]))).map (fun s => s.1) == some [some (2^255),some 71]
#guard (observe (Evm.Instr.step .shr (machine [255,maximum,71]))).map (fun s => s.1) == some [some 1,some 71]
#guard (observe (Evm.Instr.step .shl (machine [256,maximum,71]))).map (fun s => s.1) == some [some 0,some 71]
#guard (observe (Evm.Instr.step .shr (machine [dirty,maximum,71]))).map (fun s => s.1) == some [some 0,some 71]
#guard match Evm.Instr.step .and (machine []) with | .fault => true | _ => false
#guard match Evm.Instr.step .shr (machine [1]) with | .fault => true | _ => false
#guard (QuotientSelection.select .and).isNone
#guard (QuotientSelection.select .shl).isNone
#guard (compileLeaf [.op .AND,.op .OR,.op .XOR,.op .SHL,.op .SHR]).isSome
#guard (compileLeaf [.op .SAR]).isNone
#guard (compileLeaf [.push 1 #v[1]]).isNone
#guard (compileBlock (.loop [] (.code []))).isNone
#guard (ControlRealization.selectBlock block).isNone
#guard (NormalControl.compile 6 statement).isNone
#guard (compiled.emit 16).isNone
#check source_model #v[8,high,mask] #v[] [dirty,71] (machine [8,high,mask,dirty,71]) rfl
#check prefixed_source_model #v[8,high,mask] #v[dirty,99] [71] (machine [dirty,99,8,high,mask,71]) rfl
#check lowering
#check prefixed_lowering
#check ControlCompleteness.fault_iff_with compileLeaf selected (by rfl) [] (machine []) rfl

def sourceResult (count value bits : Scalar.Word) :=
  (Solidity.Yul.Closed.evalStmt 7 .nil True.intro statement compiled.profile
    (ProducerExpressions.sourceLocals #v[count,value,bits])).map
      (fun out => ((out.vars 0).val,(out.vars 1).val,(out.vars 2).val,out.flow.isNormal))
#guard sourceResult 0 high mask == some (0,3,mask.toNat,true)
#guard sourceResult 8 high mask == some (8,3,mask.toNat,true)
#guard sourceResult 8 dirty mask == some (8,2,mask.toNat,true)
#guard sourceResult 255 high mask == some (255,1,mask.toNat,true)
#guard sourceResult 256 high mask == some (256,0,mask.toNat,true)
#guard sourceResult dirty high mask == some (dirty.toNat,0,mask.toNat,true)
#guard sourceResult 8 8 mask == some (8,8,mask.toNat,true)
#guard observe (Evm.run selected.ir (machine [8,high,mask,dirty,71])) ==
  some ([some 8,some 3,some mask.toNat,some dirty.toNat,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard (observe (Evm.run selected.ir (machine [255,high,mask,71]))).map (fun s => s.1) == some [some 255,some 1,some mask.toNat,some 71]
#guard (observe (Evm.run selected.ir (machine [dirty,high,mask,71]))).map (fun s => s.1) == some [some dirty.toNat,some 0,some mask.toNat,some 71]
#guard observe (Evm.run prefixed.ir (machine [dirty,99,8,high,mask,71])) ==
  some ([some dirty.toNat,some 99,some 8,some 3,some mask.toNat,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard match Evm.run selected.ir (machine []) with | .fault => true | _ => false
#guard match Evm.run selected.ir (machine [8,high]) with | .fault => true | _ => false
-- Successful gasless model execution does not provide physical capacity.
#guard (observe (Evm.run selected.ir (machine (8::high::mask::List.replicate 1020 71)))).isSome

-- Generated from the actual scoped kernel axiom report.
/-- info: 'SolidityBridge.Yul.BitwiseSelection.andFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.BitwiseSelection.andFacts
/-- info: 'SolidityBridge.Yul.BitwiseSelection.orFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.BitwiseSelection.orFacts
/-- info: 'SolidityBridge.Yul.BitwiseSelection.xorFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.BitwiseSelection.xorFacts
/-- info: 'SolidityBridge.Yul.BitwiseSelection.shlFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.BitwiseSelection.shlFacts
/-- info: 'SolidityBridge.Yul.BitwiseSelection.shrFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.BitwiseSelection.shrFacts
/-- info: 'SolidityBridge.Yul.BitwiseSelection.band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.BitwiseSelection.band
/-- info: 'SolidityBridge.Yul.BitwiseSelection.bor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.BitwiseSelection.bor
/-- info: 'SolidityBridge.Yul.BitwiseSelection.bxor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.BitwiseSelection.bxor
/-- info: 'SolidityBridge.Yul.BitwiseSelection.shl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.BitwiseSelection.shl
/-- info: 'SolidityBridge.Yul.BitwiseSelection.shr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.BitwiseSelection.shr
/-- info: 'SolidityBridge.Yul.BitwiseSelection.select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.BitwiseSelection.select
/-- info: 'SolidityBridge.Yul.BitwiseSelection.compileLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.BitwiseSelection.compileLeaf
/-- info: 'SolidityBridge.Yul.BitwiseSelection.compileBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.BitwiseSelection.compileBlock
/-- info: 'SolidityBridge.Yul.BitwiseSelection.compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.BitwiseSelection.compiled
/-- info: 'SolidityBridge.Yul.BitwiseSelection.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.BitwiseSelection.selected
/-- info: 'SolidityBridge.Yul.BitwiseSelection.lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.BitwiseSelection.lowering
/-- info: 'SolidityBridge.Yul.BitwiseSelection.source_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.BitwiseSelection.source_model
/-- info: 'SolidityBridge.Yul.BitwiseSelection.prefixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.BitwiseSelection.prefixed
/-- info: 'SolidityBridge.Yul.BitwiseSelection.prefixed_lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.BitwiseSelection.prefixed_lowering
/-- info: 'SolidityBridge.Yul.BitwiseSelection.prefixed_source_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.BitwiseSelection.prefixed_source_model
end SolidityBridge.Yul.BitwiseSelection.Controls
