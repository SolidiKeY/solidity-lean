import SolidityBridge.Yul.ExpSelection
import SolidityBridge.Yul.ArithmeticSelectionControls
namespace SolidityBridge.Yul.ExpSelection.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev maximum := ArithmeticSelection.Controls.maximum
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe
def halfway : Scalar.Word := BitVec.ofNat 256 (2^255)
#check exp.success [2,3,71] [8,71] (machine [2,3,71]) rfl
#check exp.refusal [] (machine []) rfl
#check exp.refusal [dirty] (machine [dirty]) rfl
#guard observe (Evm.Instr.step .exp (machine [2,3,71])) ==
  some ([some 8,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard (observe (Evm.Instr.step .exp (machine [3,2,71]))).map (fun s => s.1) == some [some 9,some 71]
#guard (observe (Evm.Instr.step .exp (machine [0,0,71]))).map (fun s => s.1) == some [some 1,some 71]
#guard (observe (Evm.Instr.step .exp (machine [0,1,71]))).map (fun s => s.1) == some [some 0,some 71]
#guard (observe (Evm.Instr.step .exp (machine [maximum,2,71]))).map (fun s => s.1) == some [some 1,some 71]
#guard (observe (Evm.Instr.step .exp (machine [2,255,71]))).map (fun s => s.1) == some [some halfway.toNat,some 71]
#guard (observe (Evm.Instr.step .exp (machine [2,256,71]))).map (fun s => s.1) == some [some 0,some 71]
#guard (observe (Evm.Instr.step .exp (machine [dirty,1,71]))).map (fun s => s.1) == some [some dirty.toNat,some 71]
#guard (Scalar.run [.op .EXP] [dirty,2,71]) == some [dirty*dirty,71]
#guard match Evm.Instr.step .exp (machine [1]) with | .fault => true | _ => false
#guard (UnarySelection.select .exp).isNone
#guard (UnarySelection.compileLeaf [.op .EXP]).isNone
#guard (compileLeaf [.op .EXP,.op .ISZERO]).isSome
#guard (ControlRealization.selectSliceUsing (fun _ => some [.exp]) select [.op .MUL]).isNone
#guard (compileLeaf [.op .SAR]).isNone
#guard (compileLeaf [.op .ADDMOD]).isNone
#guard (compileLeaf [.op .MULMOD]).isNone
#guard (compileLeaf [.push 1 #v[1]]).isNone
#guard (compileBlock (.loop [] (.code []))).isNone
#guard (NormalControl.compile 5 statement).isNone
#guard (compiled.emit 16).isNone
#check source_model #v[2,3,dirty] #v[] [71] (machine [2,3,dirty,71]) rfl
#check prefixed_source_model #v[maximum,2,dirty] #v[dirty,99] [71] (machine [dirty,99,maximum,2,dirty,71]) rfl
#check lowering
#check prefixed_lowering
#check ControlCompleteness.fault_iff_with compileLeaf selected (by rfl) [] (machine []) rfl

def sourceResult (a b flag : Scalar.Word) :=
  (Solidity.Yul.Closed.evalStmt 6 .nil True.intro statement compiled.profile
    (ProducerExpressions.sourceLocals #v[a,b,flag])).map
      (fun out => ((out.vars 0).val,(out.vars 1).val,(out.vars 2).val,out.flow.isNormal))
#guard sourceResult 2 3 dirty == some (8,512,0,true)
#guard sourceResult 0 0 dirty == some (1,1,0,true)
#guard sourceResult 0 1 dirty == some (0,1,dirty.toNat,true)
#guard sourceResult maximum 2 dirty == some (1,1,0,true)
#guard sourceResult 2 256 dirty == some (2,256,dirty.toNat,true)
#guard sourceResult dirty 1 maximum == some (dirty.toNat,dirty.toNat,0,true)
#guard observe (Evm.run selected.ir (machine [2,3,dirty,71])) ==
  some ([some 8,some 512,some 0,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run prefixed.ir (machine [dirty,99,maximum,2,dirty,71])) ==
  some ([some dirty.toNat,some 99,some 1,some 1,some 0,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard match Evm.run selected.ir (machine [dirty]) with | .fault => true | _ => false
#guard (observe (Evm.run selected.ir (machine (dirty::1::maximum::List.replicate 1020 71)))).isSome
#guard Scalar.stackBound [.op .EXP] 1024
#guard !Scalar.stackBound [.op .EXP] 1025
#guard Scalar.stackBound [.op .EXP] 1 && (Scalar.run [.op .EXP] [dirty]).isNone
#guard !Scalar.stackBound [.op .EXP] 0
#guard (Scalar.run [.op .EXP] (dirty::1::List.replicate 1023 71)).isSome

-- Enforce observed scoped transitive axiom reports.
/-- info: 'SolidityBridge.Yul.ExpSelection.expFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ExpSelection.expFacts
/-- info: 'SolidityBridge.Yul.ExpSelection.exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ExpSelection.exp
/-- info: 'SolidityBridge.Yul.ExpSelection.select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ExpSelection.select
/-- info: 'SolidityBridge.Yul.ExpSelection.compileLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ExpSelection.compileLeaf
/-- info: 'SolidityBridge.Yul.ExpSelection.compileBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ExpSelection.compileBlock
/-- info: 'SolidityBridge.Yul.ExpSelection.compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ExpSelection.compiled
/-- info: 'SolidityBridge.Yul.ExpSelection.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ExpSelection.selected
/-- info: 'SolidityBridge.Yul.ExpSelection.lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ExpSelection.lowering
/-- info: 'SolidityBridge.Yul.ExpSelection.source_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ExpSelection.source_model
/-- info: 'SolidityBridge.Yul.ExpSelection.prefixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ExpSelection.prefixed
/-- info: 'SolidityBridge.Yul.ExpSelection.prefixed_lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ExpSelection.prefixed_lowering
/-- info: 'SolidityBridge.Yul.ExpSelection.prefixed_source_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ExpSelection.prefixed_source_model
/-- info: 'SolidityBridge.Yul.ExpSelection.exp_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ExpSelection.exp_capacity

end SolidityBridge.Yul.ExpSelection.Controls
