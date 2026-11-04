import SolidityBridge.Yul.ComparisonSelection
import SolidityBridge.Yul.ArithmeticSelectionControls
namespace SolidityBridge.Yul.ComparisonSelection.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev maximum := ArithmeticSelection.Controls.maximum
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe
#check lt.success [maximum,0,71] [0,71] (machine [maximum,0,71]) rfl
#check gt.success [maximum,0,71] [1,71] (machine [maximum,0,71]) rfl
#check eq.success [dirty,dirty,71] [1,71] (machine [dirty,dirty,71]) rfl
#check lt.refusal [] (machine []) rfl
#check eq.refusal [dirty] (machine [dirty]) rfl
#guard observe (Evm.Instr.step .lt (machine [0,maximum,71])) ==
  some ([some 1,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard (observe (Evm.Instr.step .lt (machine [maximum,0,71]))).map (fun s => s.1) == some [some 0,some 71]
#guard (observe (Evm.Instr.step .gt (machine [maximum,0,71]))).map (fun s => s.1) == some [some 1,some 71]
#guard (observe (Evm.Instr.step .gt (machine [0,maximum,71]))).map (fun s => s.1) == some [some 0,some 71]
#guard (observe (Evm.Instr.step .eq (machine [dirty,257,71]))).map (fun s => s.1) == some [some 0,some 71]
#guard (observe (Evm.Instr.step .eq (machine [dirty,dirty,71]))).map (fun s => s.1) == some [some 1,some 71]
#guard match Evm.Instr.step .gt (machine [1]) with | .fault => true | _ => false
#guard (SignedSelection.select .lt).isNone
#guard (SignedSelection.compileLeaf [.op .EQ]).isNone
#guard (compileLeaf [.op .LT,.op .GT,.op .EQ]).isSome
#guard (ControlRealization.selectSliceUsing (fun _ => some [.lt]) select [.op .GT]).isNone
#guard (compileLeaf [.op .ISZERO]).isNone
#guard (compileLeaf [.op .NOT]).isNone
#guard (compileLeaf [.op .EXP]).isNone
#guard (compileLeaf [.op .SAR]).isNone
#guard (compileLeaf [.push 1 #v[1]]).isNone
#guard (compileBlock (.loop [] (.code []))).isNone
#guard (NormalControl.compile 5 statement).isNone
#guard (compiled.emit 16).isNone
#check source_model #v[dirty,dirty,maximum] #v[] [71] (machine [dirty,dirty,maximum,71]) rfl
#check prefixed_source_model #v[0,0,dirty] #v[dirty,99] [71] (machine [dirty,99,0,0,dirty,71]) rfl
#check lowering
#check prefixed_lowering
#check ControlCompleteness.fault_iff_with compileLeaf selected (by rfl) [] (machine []) rfl

def sourceResult (a b flag : Scalar.Word) :=
  (Solidity.Yul.Closed.evalStmt 6 .nil True.intro statement compiled.profile
    (ProducerExpressions.sourceLocals #v[a,b,flag])).map
      (fun out => ((out.vars 0).val,(out.vars 1).val,(out.vars 2).val,out.flow.isNormal))
#guard sourceResult dirty dirty maximum == some (0,1,0,true)
#guard sourceResult 0 0 dirty == some (0,0,1,true)
#guard sourceResult maximum maximum dirty == some (0,1,0,true)
#guard sourceResult 257 dirty maximum == some (257,dirty.toNat,maximum.toNat,true)
#guard sourceResult dirty 257 maximum == some (dirty.toNat,257,maximum.toNat,true)
#guard observe (Evm.run selected.ir (machine [dirty,dirty,maximum,71])) ==
  some ([some 0,some 1,some 0,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run prefixed.ir (machine [dirty,99,0,0,dirty,71])) ==
  some ([some dirty.toNat,some 99,some 0,some 0,some 1,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard match Evm.run selected.ir (machine [dirty]) with | .fault => true | _ => false
#guard (observe (Evm.run selected.ir (machine (dirty::dirty::maximum::List.replicate 1020 71)))).isSome

-- Enforce actual scoped transitive axiom reports.
/-- info: 'SolidityBridge.Yul.ComparisonSelection.ltFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ComparisonSelection.ltFacts
/-- info: 'SolidityBridge.Yul.ComparisonSelection.gtFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ComparisonSelection.gtFacts
/-- info: 'SolidityBridge.Yul.ComparisonSelection.eqFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ComparisonSelection.eqFacts
/-- info: 'SolidityBridge.Yul.ComparisonSelection.lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ComparisonSelection.lt
/-- info: 'SolidityBridge.Yul.ComparisonSelection.gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ComparisonSelection.gt
/-- info: 'SolidityBridge.Yul.ComparisonSelection.eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ComparisonSelection.eq
/-- info: 'SolidityBridge.Yul.ComparisonSelection.select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ComparisonSelection.select
/-- info: 'SolidityBridge.Yul.ComparisonSelection.compileLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ComparisonSelection.compileLeaf
/-- info: 'SolidityBridge.Yul.ComparisonSelection.compileBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ComparisonSelection.compileBlock
/-- info: 'SolidityBridge.Yul.ComparisonSelection.compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ComparisonSelection.compiled
/-- info: 'SolidityBridge.Yul.ComparisonSelection.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ComparisonSelection.selected
/-- info: 'SolidityBridge.Yul.ComparisonSelection.lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ComparisonSelection.lowering
/-- info: 'SolidityBridge.Yul.ComparisonSelection.source_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ComparisonSelection.source_model
/-- info: 'SolidityBridge.Yul.ComparisonSelection.prefixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ComparisonSelection.prefixed
/-- info: 'SolidityBridge.Yul.ComparisonSelection.prefixed_lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ComparisonSelection.prefixed_lowering
/-- info: 'SolidityBridge.Yul.ComparisonSelection.prefixed_source_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ComparisonSelection.prefixed_source_model

end SolidityBridge.Yul.ComparisonSelection.Controls
