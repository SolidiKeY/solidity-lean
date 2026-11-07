import SolidityBridge.Yul.LoopRealization
import SolidityBridge.Yul.ArithmeticSelectionControls

/-! Finite target-loop controls only. Never execute the runtime implementation
of the always-true loop: its no-finite-outcome law is a kernel theorem. -/
namespace SolidityBridge.Yul.LoopRealization.Controls
open Solidity Backend Scalar Selection
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe

#check counter_two [dirty,77]
#check counterRealization.execute (2::[dirty,77]) (0::[dirty,77])
  (machine [2,dirty,77]) rfl (counter_two [dirty,77])
#check finite_prefix counterCondition (.code counterBodyCode) counterTest counterBody
  (counter_two [dirty,77]) (machine [2,dirty,77]) rfl
#check always_no_finite_outcome
#guard (OccurrenceControl.selectBlock counterBlock).isNone
#guard Scalar.run counterBodyCode [2,dirty,77] == some [1,dirty,77]
#guard Scalar.run counterBodyCode [1,dirty,77] == some [0,dirty,77]
#guard Scalar.run counterBodyCode [] == none
#guard Scalar.run counterCondition [] == none
#guard observe (Evm.run counterRealization.ir (machine [2,dirty,77])) ==
  some ([some 0,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run counterRealization.ir (machine [0,dirty,77])) ==
  some ([some 0,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run counterRealization.ir (machine [3,dirty,77])) ==
  some ([some 0,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard match Evm.run counterRealization.ir (machine []) with | .fault => true | _ => false
#guard match Evm.run counterBody.ir (machine []) with | .fault => true | _ => false

/-- Observe only finite prefixes, including the final zero-condition turn. -/
def prefixObservation (n : Nat) : Option (List (Option Nat)) :=
  match Evm.loopIterN (Evm.run counterTest.ir) (Evm.run counterBody.ir) n (machine [2,dirty,77]) with
  | .inl m => some (m.stack.map ArithmeticSelection.Controls.number)
  | .inr _ => none
#guard prefixObservation 0 == some [some 2,some dirty.toNat,some 77]
#guard prefixObservation 1 == some [some 1,some dirty.toNat,some 77]
#guard prefixObservation 2 == some [some 0,some dirty.toNat,some 77]
#guard prefixObservation 3 == none
#guard match Evm.loopIterN (Evm.run counterTest.ir) (Evm.run counterBody.ir) 3
    (machine [2,dirty,77]) with
  | .inr out => observe out ==
      some ([some 0,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
  | _ => false
#guard match Evm.loopIterN (Evm.run alwaysCondition) (Evm.run alwaysBody) 8
    (machine [dirty,77]) with
  | .inl m => m.stack.map ArithmeticSelection.Controls.number == [some dirty.toNat,some 77]
  | _ => false
#guard Scalar.stackBound counterCondition 1023
#guard !(Scalar.stackBound counterCondition 1024)
#guard Scalar.stackBound counterBodyCode 1023
#guard !(Scalar.stackBound counterBodyCode 1024)
-- Scalar and the numeric model are not 1024-capacity admission checks.
#guard (Scalar.run counterCondition (0::List.replicate 1024 dirty)).isSome
#guard !(Scalar.stackBound counterCondition 1025)
#guard (observe (Evm.run counterRealization.ir (machine (0::List.replicate 1024 dirty)))).isSome
/-- info: 'SolidityBridge.Yul.LoopRealization.turn_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.LoopRealization.turn_done
/-- info: 'SolidityBridge.Yul.LoopRealization.turn_more' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.LoopRealization.turn_more
/-- info: 'SolidityBridge.Yul.LoopRealization.finite_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.LoopRealization.finite_prefix
/-- info: 'SolidityBridge.Yul.LoopRealization.realization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.LoopRealization.realization
/-- info: 'SolidityBridge.Yul.LoopRealization.always_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.LoopRealization.always_prefix
/-- info: 'SolidityBridge.Yul.LoopRealization.counter_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.LoopRealization.counter_two
/-- info: 'SolidityBridge.Yul.LoopRealization.always_no_finite_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.LoopRealization.always_no_finite_outcome
end SolidityBridge.Yul.LoopRealization.Controls
