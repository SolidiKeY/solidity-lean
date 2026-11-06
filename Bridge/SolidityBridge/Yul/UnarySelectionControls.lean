import SolidityBridge.Yul.UnarySelection
import SolidityBridge.Yul.ArithmeticSelectionControls
import Solidity.Backend.Scalar.Heights
namespace SolidityBridge.Yul.UnarySelection.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev maximum := ArithmeticSelection.Controls.maximum
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe
def highOnly : Scalar.Word := BitVec.ofNat 256 (2^200)
#check iszero.success [0,71] [1,71] (machine [0,71]) rfl
#check iszero.success [dirty,71] [0,71] (machine [dirty,71]) rfl
#check not.success [maximum,71] [0,71] (machine [maximum,71]) rfl
#check iszero.refusal [] (machine []) rfl
#check not.refusal [] (machine []) rfl
#guard observe (Evm.Instr.step .iszero (machine [highOnly,71])) ==
  some ([some 0,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard (observe (Evm.Instr.step .iszero (machine [0,71]))).map (fun s => s.1) == some [some 1,some 71]
#guard (observe (Evm.Instr.step .not (machine [dirty,71]))).map (fun s => s.1) == some [some (maximum.toNat-dirty.toNat),some 71]
#guard (observe (Evm.Instr.step .not (machine [0,71]))).map (fun s => s.1) == some [some maximum.toNat,some 71]
#guard (observe (Evm.Instr.step .not (machine [maximum,71]))).map (fun s => s.1) == some [some 0,some 71]
#guard match Evm.Instr.step .iszero (machine []) with | .fault => true | _ => false
#guard (ComparisonSelection.select .iszero).isNone
#guard (ComparisonSelection.compileLeaf [.op .NOT]).isNone
#guard (compileLeaf [.op .ISZERO,.op .NOT]).isSome
#guard (ControlRealization.selectSliceUsing (fun _ => some [.not]) select [.op .ISZERO]).isNone
#guard (compileLeaf [.op .EXP]).isNone
#guard (compileLeaf [.op .SAR]).isNone
#guard (compileLeaf [.push 1 #v[1]]).isNone
#guard (compileBlock (.loop [] (.code []))).isNone
#guard (NormalControl.compile 5 statement).isNone
#guard (compiled.emit 16).isNone
#check source_model #v[maximum,dirty,highOnly] #v[] [71] (machine [maximum,dirty,highOnly,71]) rfl
#check prefixed_source_model #v[maximum,dirty,highOnly] #v[dirty,99] [71] (machine [dirty,99,maximum,dirty,highOnly,71]) rfl
#check lowering
#check prefixed_lowering
#check ControlCompleteness.fault_iff_with compileLeaf selected (by rfl) [] (machine []) rfl

def sourceResult (a b flag : Scalar.Word) :=
  (Solidity.Yul.Closed.evalStmt 6 .nil True.intro statement compiled.profile
    (ProducerExpressions.sourceLocals #v[a,b,flag])).map
      (fun out => ((out.vars 0).val,(out.vars 1).val,(out.vars 2).val,out.flow.isNormal))
#guard sourceResult maximum dirty highOnly == some (0,1,maximum.toNat-1,true)
#guard sourceResult 0 dirty highOnly == some (0,dirty.toNat,highOnly.toNat,true)
#guard sourceResult highOnly dirty maximum == some (highOnly.toNat,dirty.toNat,maximum.toNat,true)
#guard sourceResult dirty 257 highOnly == some (dirty.toNat,257,highOnly.toNat,true)
#guard observe (Evm.run selected.ir (machine [maximum,dirty,highOnly,71])) ==
  some ([some 0,some 1,some (maximum.toNat-1),some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run prefixed.ir (machine [dirty,99,maximum,dirty,highOnly,71])) ==
  some ([some dirty.toNat,some 99,some 0,some 1,some (maximum.toNat-1),some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard match Evm.run selected.ir (machine [maximum]) with | .fault => true | _ => false
#guard (observe (Evm.run selected.ir (machine (maximum::dirty::highOnly::List.replicate 1020 71)))).isSome
#guard Scalar.stackBound [.op .NOT] 1024
#guard !Scalar.stackBound [.op .NOT] 1025
#guard Scalar.stackBound [.op .ISZERO] 0 && (Scalar.run [.op .ISZERO] []).isNone
#guard (Scalar.run [.op .NOT] (maximum::List.replicate 1024 71)).isSome

-- Enforce observed scoped transitive axiom reports.
/-- info: 'SolidityBridge.Yul.UnarySelection.scalar_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.UnarySelection.scalar_outcome
/-- info: 'SolidityBridge.Yul.UnarySelection.model_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.UnarySelection.model_outcome
/-- info: 'SolidityBridge.Yul.UnarySelection.bridge_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.UnarySelection.bridge_step
/-- info: 'SolidityBridge.Yul.UnarySelection.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.UnarySelection.certificate
/-- info: 'SolidityBridge.Yul.UnarySelection.iszeroFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.UnarySelection.iszeroFacts
/-- info: 'SolidityBridge.Yul.UnarySelection.notFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.UnarySelection.notFacts
/-- info: 'SolidityBridge.Yul.UnarySelection.iszero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.UnarySelection.iszero
/-- info: 'SolidityBridge.Yul.UnarySelection.not' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.UnarySelection.not
/-- info: 'SolidityBridge.Yul.UnarySelection.select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.UnarySelection.select
/-- info: 'SolidityBridge.Yul.UnarySelection.compileLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.UnarySelection.compileLeaf
/-- info: 'SolidityBridge.Yul.UnarySelection.compileBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.UnarySelection.compileBlock
/-- info: 'SolidityBridge.Yul.UnarySelection.compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.UnarySelection.compiled
/-- info: 'SolidityBridge.Yul.UnarySelection.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.UnarySelection.selected
/-- info: 'SolidityBridge.Yul.UnarySelection.lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.UnarySelection.lowering
/-- info: 'SolidityBridge.Yul.UnarySelection.source_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.UnarySelection.source_model
/-- info: 'SolidityBridge.Yul.UnarySelection.prefixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.UnarySelection.prefixed
/-- info: 'SolidityBridge.Yul.UnarySelection.prefixed_lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.UnarySelection.prefixed_lowering
/-- info: 'SolidityBridge.Yul.UnarySelection.prefixed_source_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.UnarySelection.prefixed_source_model
/-- info: 'SolidityBridge.Yul.UnarySelection.iszero_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.UnarySelection.iszero_capacity
/-- info: 'SolidityBridge.Yul.UnarySelection.not_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.UnarySelection.not_capacity

end SolidityBridge.Yul.UnarySelection.Controls
