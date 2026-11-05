import SolidityBridge.Yul.QuotientSelection
import SolidityBridge.Yul.ControlRealization
import SolidityBridge.Yul.ArithmeticSelectionControls
namespace SolidityBridge.Yul.QuotientSelection.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev maximum := ArithmeticSelection.Controls.maximum
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe
#check sub.success [dirty,257,71] [dirty-257,71] (machine [dirty,257,71]) rfl
#check div.success [17,0,71] [0,71] (machine [17,0,71]) rfl
#check mod.success [17,0,71] [0,71] (machine [17,0,71]) rfl
#check sub.refusal [] (machine []) rfl
#check div.refusal [dirty] (machine [dirty]) rfl
#check mod.refusal [dirty] (machine [dirty]) rfl
#guard (select .sub).isSome
#guard (select .div).isSome
#guard (select .mod).isSome
-- Original refusal controls stay true. No existing selector/admission changed.
#guard (LiteralSelection.select .sub).isNone
#guard (LiteralSelection.select .div).isNone
#guard (LiteralSelection.select .mod).isNone
#guard (select .sdiv).isNone
#guard (select (.dup 17)).isNone
#guard (select (.swap 0)).isNone
#guard observe (Evm.Instr.step .sub (machine [dirty,257,71])) ==
  some ([some (2^200),some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard (observe (Evm.Instr.step .sub (machine [3,10,71]))).map (fun s => s.1) ==
  some [some (2^256-7),some 71]
#guard (observe (Evm.Instr.step .div (machine [17,5,71]))).map (fun s => s.1) == some [some 3,some 71]
#guard (observe (Evm.Instr.step .mod (machine [17,5,71]))).map (fun s => s.1) == some [some 2,some 71]
#guard (observe (Evm.Instr.step .div (machine [17,0,71]))).map (fun s => s.1) == some [some 0,some 71]
#guard (observe (Evm.Instr.step .mod (machine [17,0,71]))).map (fun s => s.1) == some [some 0,some 71]
#guard match Evm.Instr.step .sub (machine [17]) with | .fault => true | _ => false
#guard match Evm.Instr.step .div (machine []) with | .fault => true | _ => false
#guard match Evm.Instr.step .mod (machine [17]) with | .fault => true | _ => false
#guard compiled.lowered.code 0 = some (SelectionSequence.emit code certificates)
#check source_model #v[29,5] [dirty,71] (machine [29,5,dirty,71]) rfl
#check source_model #v[10,0] [71] (machine [10,0,71]) rfl
def sourceResult (a b : Scalar.Word) :=
  (Solidity.Yul.Closed.evalStmt 5 .nil True.intro statement compiled.profile
    (ProducerExpressions.sourceLocals #v[a,b])).map
      (fun out => ((out.vars 0).val,(out.vars 1).val,out.flow.isNormal))
#guard sourceResult 29 5 == some (0,4,true)
#guard sourceResult 10 0 == some (0,0,true)
#guard sourceResult 3 10 == some (9,(2^256-7)/10,true)
#guard observe (Evm.run code (machine [29,5,dirty,71])) ==
  some ([some 0,some 4,some dirty.toNat,some 71],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard (observe (Evm.run code (machine [10,0,71]))).map (fun s => s.1) == some [some 0,some 0,some 71]
#guard (observe (Evm.run code (machine [3,10,71]))).map (fun s => s.1) == some [some 9,some ((2^256-7)/10),some 71]
#guard match Evm.run code (machine [17]) with | .fault => true | _ => false
#guard (PureStatements.compile 4 statement).isNone
#guard (compiled.lowered.code 16).isNone
#guard stackBound (SelectionSequence.emit code certificates) 1022
#guard !(stackBound (SelectionSequence.emit code certificates) 1023)
-- Uncapped model success is not physical capacity or native execution.
#guard (observe (Evm.run code (machine (29::5::List.replicate 1021 71)))).isSome
-- A genuine published iff lowering artifact for the SAME actual emitted
-- source statement program, not an arbitrary selected function or run premise.
def lowering_witness := (show ControlRealization.Slice
    ((compiled.lowered.code 0).get (by rfl)) from ⟨code,certificates,by rfl⟩).lowering
#check lowering_witness

-- Generated from the actual scoped kernel axiom report.
/-- info: 'SolidityBridge.Yul.QuotientSelection.stack_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientSelection.stack_cons
/-- info: 'SolidityBridge.Yul.QuotientSelection.args_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientSelection.args_eq
/-- info: 'SolidityBridge.Yul.QuotientSelection.scalar_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientSelection.scalar_outcome
/-- info: 'SolidityBridge.Yul.QuotientSelection.model_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientSelection.model_outcome
/-- info: 'SolidityBridge.Yul.QuotientSelection.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientSelection.certificate
/-- info: 'SolidityBridge.Yul.QuotientSelection.bridge_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientSelection.bridge_step
/-- info: 'SolidityBridge.Yul.QuotientSelection.subFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientSelection.subFacts
/-- info: 'SolidityBridge.Yul.QuotientSelection.divFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientSelection.divFacts
/-- info: 'SolidityBridge.Yul.QuotientSelection.modFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientSelection.modFacts
/-- info: 'SolidityBridge.Yul.QuotientSelection.sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientSelection.sub
/-- info: 'SolidityBridge.Yul.QuotientSelection.div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientSelection.div
/-- info: 'SolidityBridge.Yul.QuotientSelection.mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientSelection.mod
/-- info: 'SolidityBridge.Yul.QuotientSelection.select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientSelection.select
/-- info: 'SolidityBridge.Yul.QuotientSelection.compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientSelection.compiled
/-- info: 'SolidityBridge.Yul.QuotientSelection.certificates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientSelection.certificates
/-- info: 'SolidityBridge.Yul.QuotientSelection.source_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientSelection.source_model
/-- info: 'SolidityBridge.Yul.QuotientSelection.Controls.lowering_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.QuotientSelection.Controls.lowering_witness
end SolidityBridge.Yul.QuotientSelection.Controls
