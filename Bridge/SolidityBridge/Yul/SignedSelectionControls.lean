import SolidityBridge.Yul.SignedSelection
import SolidityBridge.Yul.ArithmeticSelectionControls
namespace SolidityBridge.Yul.SignedSelection.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev maximum := ArithmeticSelection.Controls.maximum
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe
def neg (n : Nat) : Scalar.Word := BitVec.ofInt 256 (-(n : Int))
def minimum : Scalar.Word := BitVec.ofNat 256 (2^255)
#check sdiv.success [neg 17,5,71] [neg 3,71] (machine [neg 17,5,71]) rfl
#check smod.success [neg 17,5,71] [neg 2,71] (machine [neg 17,5,71]) rfl
#check slt.success [minimum,0,71] [1,71] (machine [minimum,0,71]) rfl
#check sgt.success [maximum,0,71] [0,71] (machine [maximum,0,71]) rfl
#check sdiv.refusal [minimum] (machine [minimum]) rfl
#check smod.refusal [] (machine []) rfl
#guard observe (Evm.Instr.step .sdiv (machine [neg 17,5,71])) ==
  some ([some (neg 3).toNat,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard (observe (Evm.Instr.step .smod (machine [neg 17,5,71]))).map (fun s => s.1) == some [some (neg 2).toNat,some 71]
#guard (observe (Evm.Instr.step .sdiv (machine [17,neg 5,71]))).map (fun s => s.1) == some [some (neg 3).toNat,some 71]
#guard (observe (Evm.Instr.step .smod (machine [17,neg 5,71]))).map (fun s => s.1) == some [some 2,some 71]
#guard (observe (Evm.Instr.step .sdiv (machine [minimum,maximum,71]))).map (fun s => s.1) == some [some minimum.toNat,some 71]
#guard (observe (Evm.Instr.step .smod (machine [minimum,maximum,71]))).map (fun s => s.1) == some [some 0,some 71]
#guard (observe (Evm.Instr.step .sdiv (machine [neg 17,0,71]))).map (fun s => s.1) == some [some 0,some 71]
#guard (observe (Evm.Instr.step .smod (machine [minimum,0,71]))).map (fun s => s.1) == some [some 0,some 71]
#guard (observe (Evm.Instr.step .slt (machine [minimum,0,71]))).map (fun s => s.1) == some [some 1,some 71]
#guard (observe (Evm.Instr.step .sgt (machine [maximum,0,71]))).map (fun s => s.1) == some [some 0,some 71]
#guard match Evm.Instr.step .sdiv (machine []) with | .fault => true | _ => false
#guard match Evm.Instr.step .slt (machine [1]) with | .fault => true | _ => false
#guard (BitwiseSelection.select .sdiv).isNone
#guard (ControlRealization.selectSliceWith select [.op .SDIV]).isNone
#guard (compileLeaf [.op .SDIV,.op .SMOD,.op .SLT,.op .SGT]).isSome
-- Incorrect proposals cannot bypass exact re-emission checking.
#guard (ControlRealization.selectSliceUsing (fun _ => some [.sdiv]) select [.op .SUB]).isNone
#guard (ControlRealization.selectSliceUsing (fun _ => some []) select [.op .SDIV]).isNone
#guard (compileLeaf [.op .SAR]).isNone
#guard (compileLeaf [.op .EXP]).isNone
#guard (compileLeaf [.push 1 #v[1]]).isNone
#guard (compileBlock (.loop [] (.code []))).isNone
#guard (NormalControl.compile 5 statement).isNone
#guard (compiled.emit 16).isNone
#check source_model #v[neg 100,neg 3,dirty] #v[] [71] (machine [neg 100,neg 3,dirty,71]) rfl
#check prefixed_source_model #v[minimum,maximum,dirty] #v[dirty,99] [71] (machine [dirty,99,minimum,maximum,dirty,71]) rfl
#check lowering
#check prefixed_lowering
#check ControlCompleteness.fault_iff_with compileLeaf selected (by rfl) [] (machine []) rfl

def sourceResult (a b flag : Scalar.Word) :=
  (Solidity.Yul.Closed.evalStmt 6 .nil True.intro statement compiled.profile
    (ProducerExpressions.sourceLocals #v[a,b,flag])).map
      (fun out => ((out.vars 0).val,(out.vars 1).val,(out.vars 2).val,out.flow.isNormal))
#guard sourceResult (neg 17) 5 dirty == some ((neg 3).toNat,(neg 3).toNat,0,true)
#guard sourceResult (neg 100) (neg 3) dirty == some (33,0,1,true)
#guard sourceResult minimum maximum dirty == some (minimum.toNat,0,0,true)
#guard sourceResult (neg 17) 0 dirty == some (0,0,0,true)
#guard sourceResult 5 (neg 17) dirty == some (5,(neg 17).toNat,dirty.toNat,true)
#guard observe (Evm.run selected.ir (machine [neg 100,neg 3,dirty,71])) ==
  some ([some 33,some 0,some 1,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard (observe (Evm.run selected.ir (machine [5,neg 17,dirty,71]))).map (fun s => s.1) == some [some 5,some (neg 17).toNat,some dirty.toNat,some 71]
#guard observe (Evm.run prefixed.ir (machine [dirty,99,minimum,maximum,dirty,71])) ==
  some ([some dirty.toNat,some 99,some minimum.toNat,some 0,some 0,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard match Evm.run selected.ir (machine [minimum]) with | .fault => true | _ => false
#guard (observe (Evm.run selected.ir (machine (minimum::maximum::dirty::List.replicate 1020 71)))).isSome
example (p : Backend.Program) : ControlRealization.selectSliceWith BitwiseSelection.select p =
  ControlRealization.selectSliceUsing NumericMachine.selectCode BitwiseSelection.select p := rfl

-- Pin the actual scoped transitive axiom reports.
/-- info: 'SolidityBridge.Yul.ControlRealization.selectSliceUsing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.ControlRealization.selectSliceUsing
/-- info: 'SolidityBridge.Yul.SignedSelection.sdivFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.SignedSelection.sdivFacts
/-- info: 'SolidityBridge.Yul.SignedSelection.smodFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.SignedSelection.smodFacts
/-- info: 'SolidityBridge.Yul.SignedSelection.sltFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.SignedSelection.sltFacts
/-- info: 'SolidityBridge.Yul.SignedSelection.sgtFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.SignedSelection.sgtFacts
/-- info: 'SolidityBridge.Yul.SignedSelection.sdiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.SignedSelection.sdiv
/-- info: 'SolidityBridge.Yul.SignedSelection.smod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.SignedSelection.smod
/-- info: 'SolidityBridge.Yul.SignedSelection.slt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.SignedSelection.slt
/-- info: 'SolidityBridge.Yul.SignedSelection.sgt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.SignedSelection.sgt
/-- info: 'SolidityBridge.Yul.SignedSelection.select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.SignedSelection.select
/-- info: 'SolidityBridge.Yul.SignedSelection.compileLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.SignedSelection.compileLeaf
/-- info: 'SolidityBridge.Yul.SignedSelection.compileBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.SignedSelection.compileBlock
/-- info: 'SolidityBridge.Yul.SignedSelection.compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.SignedSelection.compiled
/-- info: 'SolidityBridge.Yul.SignedSelection.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.SignedSelection.selected
/-- info: 'SolidityBridge.Yul.SignedSelection.lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.SignedSelection.lowering
/-- info: 'SolidityBridge.Yul.SignedSelection.source_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.SignedSelection.source_model
/-- info: 'SolidityBridge.Yul.SignedSelection.prefixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.SignedSelection.prefixed
/-- info: 'SolidityBridge.Yul.SignedSelection.prefixed_lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.SignedSelection.prefixed_lowering
/-- info: 'SolidityBridge.Yul.SignedSelection.prefixed_source_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.SignedSelection.prefixed_source_model

end SolidityBridge.Yul.SignedSelection.Controls
