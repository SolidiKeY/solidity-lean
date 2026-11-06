import SolidityBridge.Yul.LoopSelection
import SolidityBridge.Yul.ArithmeticSelectionControls
/-! Finite target-loop tests and inhabited whole-iff certificates.
Never evaluate a divergent loopRun runtime implementation. -/
namespace SolidityBridge.Yul.LoopSelection.Controls
open Solidity Backend Scalar Selection
open SolidityBridge.Yul
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe

def counter := (selectBlock LoopRealization.counterBlock).get (by rfl)
#check counter.lowering
#check (counter.lowering.success [2,dirty,77] [0,dirty,77]
  (machine [2,dirty,77]) rfl).mpr (LoopRealization.counter_two [dirty,77])
#check OccurrenceControl.fault_iff LoopRealization.counterBlock counter [] (machine []) rfl
#check LoopClassification.iter_classified LoopRealization.counterCondition
  (.code LoopRealization.counterBodyCode) LoopRealization.counterTest LoopRealization.counterBody
  LoopRealization.counterBodySelected.classified 1 [2,dirty,77] (machine [2,dirty,77]) rfl
#guard (OccurrenceControl.selectBlock LoopRealization.counterBlock).isNone
#guard (selectBlock LoopRealization.counterBlock).isSome
#guard observe (Evm.run counter.realization.ir (machine [2,dirty,77])) ==
  some ([some 0,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run counter.realization.ir (machine [0,dirty,77])) ==
  some ([some 0,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard match Evm.run counter.realization.ir (machine []) with | .fault => true | _ => false

def nestedBlock : Backend.Block := .loop LoopRealization.counterCondition
  (.seq LoopRealization.counterBlock (.code []))
def nested := (selectBlock nestedBlock).get (by rfl)
#check nested.lowering
#check OccurrenceControl.fault_iff nestedBlock nested [] (machine []) rfl
#guard observe (Evm.run nested.realization.ir (machine [3,dirty,77])) ==
  some ([some 0,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)

def combinedBlock : Backend.Block := .seq
  (.ite [pushWord 1] (.code []) (.code [.op .ADD])) nestedBlock
def combined := (selectBlock combinedBlock).get (by rfl)
#check combined.lowering
#guard observe (Evm.run combined.realization.ir (machine [2,dirty,77])) ==
  some ([some 0,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)

def failingBlock : Backend.Block := .loop LoopRealization.counterCondition (.code [.op .ADD])
def failing := (selectBlock failingBlock).get (by rfl)
#check OccurrenceControl.fault_iff failingBlock failing [1] (machine [1]) rfl
#guard match Evm.run failing.realization.ir (machine [1]) with | .fault => true | _ => false
#guard observe (Evm.run failing.realization.ir (machine [0])) ==
  some ([some 0],some dirty.toNat,23,99,99,7,11,19,31,false)

def emptyTestBlock : Backend.Block := .loop [] (.code [])
def emptyTest := (selectBlock emptyTestBlock).get (by rfl)
#guard match Evm.run emptyTest.realization.ir (machine []) with | .fault => true | _ => false
-- An empty condition consumes an actual preexisting top word, not a fabricated guard.
#guard observe (Evm.run emptyTest.realization.ir (machine [0,dirty,77])) ==
  some ([some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)

def highGuardBlock : Backend.Block := .loop [pushWord (BitVec.ofNat 256 (2^200))] (.code [.op .ADD])
def highGuard := (selectBlock highGuardBlock).get (by rfl)
#guard match Evm.run highGuard.realization.ir (machine []) with | .fault => true | _ => false

def lastSlotBlock : Backend.Block := .loop [.op (.DUP 15)] (.code [.op .ADD])
def lastSlot := (selectBlock lastSlotBlock).get (by rfl)
#guard match Evm.run lastSlot.realization.ir (machine (List.replicate 15 0)) with | .fault => true | _ => false
#guard (observe (Evm.run lastSlot.realization.ir (machine (List.replicate 16 0)))).isSome
#guard (selectBlock (.loop [.op .SAR] (.code []))).isNone
#guard (selectBlock (.loop [.push 2 #v[0,31]] (.code []))).isNone
#guard (selectBlock (.ite [pushWord 0] (.loop [.op .SAR] (.code [])) (.code []))).isNone
#guard !(Scalar.stackBound LoopRealization.counterCondition 1025)
#guard (observe (Evm.run counter.realization.ir (machine (0::List.replicate 1024 dirty)))).isSome

-- Certificate construction is safe; never run the selected always-true loop.
def alwaysBlock : Backend.Block := .loop [pushByte 1] (.code [])
def always := (selectBlock alwaysBlock).get (by rfl)
#check always.lowering
/-- info: 'SolidityBridge.Yul.LoopClassification.turn_classified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.LoopClassification.turn_classified
/-- info: 'SolidityBridge.Yul.LoopClassification.iter_classified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.LoopClassification.iter_classified
/-- info: 'SolidityBridge.Yul.LoopClassification.classified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.LoopClassification.classified
/-- info: 'SolidityBridge.Yul.LoopSelection.selectBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.LoopSelection.selectBlock
end SolidityBridge.Yul.LoopSelection.Controls
