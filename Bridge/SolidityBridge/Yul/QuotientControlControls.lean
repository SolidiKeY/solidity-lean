import SolidityBridge.Yul.QuotientControl
import SolidityBridge.Yul.ArithmeticSelectionControls
namespace SolidityBridge.Yul.QuotientControl.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev maximum := ArithmeticSelection.Controls.maximum
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe
#check source_model #v[29,5] #v[] [dirty,71] (machine [29,5,dirty,71]) rfl
#check source_model #v[10,0] #v[] [71] (machine [10,0,71]) rfl
#check prefixed_source_model #v[29,5] #v[dirty,99] [71] (machine [dirty,99,29,5,71]) rfl
#check lowering
#check prefixed_lowering
#check ControlCompleteness.fault_iff_with compileLeaf selected (by rfl) [] (machine []) rfl
#guard (compileBlock block).isSome
#guard (compileBlock prefixedBlock).isSome
-- Legacy source/table verdicts remain unchanged after generic factoring.
#guard (ControlRealization.selectBlock block).isNone
#guard (ControlRealization.selectSlice [.op .SUB]).isNone
#guard (ControlRealization.selectSlice [.op .DIV]).isNone
#guard (ControlRealization.selectSlice [.op .MOD]).isNone
#guard (compileLeaf [.op .SUB]).isSome
#guard (compileLeaf [.op .DIV]).isSome
#guard (compileLeaf [.op .MOD]).isSome
#guard (compileLeaf [.op .AND]).isNone
#guard (compileLeaf [.push 1 #v[1]]).isNone
#guard (compileBlock (.loop [] (.code []))).isNone
#guard (NormalControl.compile 5 statement).isNone
#guard (compiled.emit 16).isNone

def sourceResult (a b : Scalar.Word) :=
  (Solidity.Yul.Closed.evalStmt 6 .nil True.intro statement compiled.profile
    (ProducerExpressions.sourceLocals #v[a,b])).map
      (fun out => ((out.vars 0).val,(out.vars 1).val,out.flow.isNormal))
#guard sourceResult 29 5 == some (0,4,true)
#guard sourceResult 3 10 == some (3,10,true)
#guard sourceResult 10 0 == some (10,0,true)
#guard sourceResult maximum 1 == some (0,maximum.toNat-1,true)
#guard observe (Evm.run selected.ir (machine [29,5,dirty,71])) ==
  some ([some 0,some 4,some dirty.toNat,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard (observe (Evm.run selected.ir (machine [3,10,71]))).map (fun s => s.1) == some [some 3,some 10,some 71]
#guard (observe (Evm.run selected.ir (machine [10,0,71]))).map (fun s => s.1) == some [some 10,some 0,some 71]
#guard observe (Evm.run prefixed.ir (machine [dirty,99,29,5,71])) ==
  some ([some dirty.toNat,some 99,some 0,some 4,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard match Evm.run selected.ir (machine []) with | .fault => true | _ => false
#guard match Evm.run selected.ir (machine [1]) with | .fault => true | _ => false
-- The numeric model remains uncapped: this is not native join-jump capacity.
#guard (observe (Evm.run selected.ir (machine (29::5::List.replicate 1021 71)))).isSome
#guard !(stackBound (SelectionSequence.emit QuotientSelection.code QuotientSelection.certificates) 1023)
-- Default entry points remain exact specializations of the factored code.
example (p : Backend.Program) : ControlRealization.selectSlice p =
    ControlRealization.selectSliceWith LiteralSelection.select p := rfl
example (b : Backend.Block) : ControlRealization.selectBlock b =
    ControlRealization.selectBlockWith ControlRealization.selectSlice b := rfl

-- Generated from the actual scoped kernel axiom report.
/-- info: 'SolidityBridge.Yul.ControlRealization.selectSliceWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlRealization.selectSliceWith
/-- info: 'SolidityBridge.Yul.ControlRealization.selectSlice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlRealization.selectSlice
/-- info: 'SolidityBridge.Yul.ControlRealization.selectBlockWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlRealization.selectBlockWith
/-- info: 'SolidityBridge.Yul.ControlRealization.selectBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlRealization.selectBlock
/-- info: 'SolidityBridge.Yul.ControlCompleteness.selected_classified_with' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.selected_classified_with
/-- info: 'SolidityBridge.Yul.ControlCompleteness.selected_classified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.selected_classified
/-- info: 'SolidityBridge.Yul.ControlCompleteness.selected_lowering_with' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.selected_lowering_with
/-- info: 'SolidityBridge.Yul.ControlCompleteness.selected_lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.selected_lowering
/-- info: 'SolidityBridge.Yul.ControlCompleteness.fault_iff_with' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.fault_iff_with
/-- info: 'SolidityBridge.Yul.ControlCompleteness.fault_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlCompleteness.fault_iff
/-- info: 'SolidityBridge.Yul.QuotientControl.compileLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientControl.compileLeaf
/-- info: 'SolidityBridge.Yul.QuotientControl.compileBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientControl.compileBlock
/-- info: 'SolidityBridge.Yul.QuotientControl.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientControl.selected
/-- info: 'SolidityBridge.Yul.QuotientControl.lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientControl.lowering
/-- info: 'SolidityBridge.Yul.QuotientControl.source_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientControl.source_model
/-- info: 'SolidityBridge.Yul.QuotientControl.prefixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientControl.prefixed
/-- info: 'SolidityBridge.Yul.QuotientControl.prefixed_lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientControl.prefixed_lowering
/-- info: 'SolidityBridge.Yul.QuotientControl.prefixed_source_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientControl.prefixed_source_model
end SolidityBridge.Yul.QuotientControl.Controls
