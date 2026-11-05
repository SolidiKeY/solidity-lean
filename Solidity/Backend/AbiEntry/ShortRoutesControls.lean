import Solidity.Backend.AbiEntry.ShortRoutes
import Solidity.Source.SemanticsExamples

/-! Actual selected routes, including the padded-selector counterexample now
guarded by length. Short and unmatched labels are not executed special bodies. -/
namespace Solidity.Backend.AbiEntry.ShortRoutesControls
open Solidity.Evm
open Interface (RouteCtx shortRouteOutcome rawSelectorWord)
private def C : Contract := {vars := []}
private def table : Interface.PayableRouteTable :=
  [(wmod 0xdeadbe00,wmod 11,false),(wmod 0xdeadbe00,wmod 22,true)]
private def fallback : Fin W := wmod 99
private def short : Fin W := wmod 88
private def compiled := ShortRoutes.compiled C 7 table fallback short
private def machine (selector size value : Fin W) : Machine :=
  {Machine.init with
    callvalue := value
    mem := fun address => if address=7 then .val selector else if address=8 then .val size else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private def written (selector size value label : Fin W) : Machine :=
  {machine selector size value with mem := upd (machine selector size value).mem 8 (.val label)}
private theorem actual (selector size value : Fin W) :
    run compiled.code (machine selector size value)=shortRouteOutcome 7 table fallback short selector size
      (machine selector size value) :=
  ShortRoutes.executed C 7 table fallback short compiled (ShortRoutes.selected C 7 table fallback short)
    (machine selector size value) selector size rfl rfl

theorem all_short (selector size value : Fin W) (small : size.val<4) :
    run compiled.code (machine selector size value)=.ok (written selector size value short) 0 := by
  simpa only [shortRouteOutcome,if_pos small] using actual selector size value

theorem zero_through_three (selector value : Fin W) :
    run compiled.code (machine selector (wmod 0) value)=.ok (written selector (wmod 0) value short) 0 ∧
    run compiled.code (machine selector (wmod 1) value)=.ok (written selector (wmod 1) value short) 0 ∧
    run compiled.code (machine selector (wmod 2) value)=.ok (written selector (wmod 2) value short) 0 ∧
    run compiled.code (machine selector (wmod 3) value)=.ok (written selector (wmod 3) value short) 0 :=
  ⟨all_short selector _ value (by decide),all_short selector _ value (by decide),
    all_short selector _ value (by decide),all_short selector _ value (by decide)⟩

theorem four_zero_value :
    run compiled.code (machine (wmod 0xdeadbe00) (wmod 4) (wmod 0))=
      .ok (written (wmod 0xdeadbe00) (wmod 4) (wmod 0) (wmod 11)) 0 := by
  have reached := actual (wmod 0xdeadbe00) (wmod 4) (wmod 0)
  have selected : shortRouteOutcome 7 table fallback short (wmod 0xdeadbe00) (wmod 4)
      (machine (wmod 0xdeadbe00) (wmod 4) (wmod 0))=
        .ok (written (wmod 0xdeadbe00) (wmod 4) (wmod 0) (wmod 11)) 0 := by rfl
  exact reached.trans selected

theorem four_nonzero (value : Fin W) (nonzero : value.val≠0) :
    run compiled.code (machine (wmod 0xdeadbe00) (wmod 4) value)=.revert := by
  have reached := actual (wmod 0xdeadbe00) (wmod 4) value
  have selected : Interface.payableRouteResult table fallback (wmod 0xdeadbe00)=(wmod 11,false) := by decide
  have full : ¬(wmod 4).val<4 := by decide
  have observed : (machine (wmod 0xdeadbe00) (wmod 4) value).callvalue.val≠0 := nonzero
  simpa only [shortRouteOutcome,if_neg full,Interface.payableRouteOutcome,selected,Bool.false_or,
    decide_eq_false observed,if_false] using reached

private def bytes : List UInt8 := [0xde,0xad,0xbe]
private def frame : Source.Fr := {Source.SemanticsExamples.F0 with cd := bytes}

theorem padded_collision_guarded (value : Fin W) :
    run compiled.code (machine (rawSelectorWord frame) (wmod bytes.length) value)=
      .ok (written (rawSelectorWord frame) (wmod bytes.length) value short) 0 :=
  all_short _ _ _ (by decide)

/-- Omitting the guard can select the padded collision, and for nonzero value
reject it instead of reaching the short continuation. -/
theorem padded_collision_unguarded :
    run (PayableRoutes.compiled C 7 table fallback).code
      (machine (rawSelectorWord frame) (wmod bytes.length) (wmod 0))=
        .ok (written (rawSelectorWord frame) (wmod bytes.length) (wmod 0) (wmod 11)) 0 := by
  have reached := PayableRoutes.executed C 7 table fallback (PayableRoutes.compiled C 7 table fallback)
    (PayableRoutes.selected C 7 table fallback) (machine (rawSelectorWord frame) (wmod bytes.length) (wmod 0))
      (rawSelectorWord frame) rfl
  have chosen : Interface.payableRouteResult table fallback (rawSelectorWord frame)=(wmod 11,false) := by decide
  simpa only [Interface.payableRouteOutcome,chosen,Bool.false_or,decide_true,if_true] using reached

theorem source_no_ordinary (pipeline : Roadmap.Pipeline) :
    (Source.SemanticsExamples.GAB pipeline).pickFn frame bytes=none :=
  ShortRoutes.source_short _ frame (by decide)

theorem malformed_length_fault :
    run compiled.code {machine (wmod 0xdeadbe00) (wmod 3) (wmod 0) with
      mem := fun address => if address=8 then .slot (.root 0) else .val (wmod 71)}=.fault := by rfl

theorem protected_and_saved (selector size value label : Fin W) :
    (written selector size value label).mem 7=.val selector ∧
    (written selector size value label).mem 9=.val (wmod 71) ∧
    (written selector size value label).stack=[.val (wmod 258),.val (wmod 513)] ∧
    (written selector size value label).callvalue=value := ⟨rfl,rfl,rfl,rfl⟩
/-- info: 'Solidity.Backend.AbiEntry.ShortRoutesControls.all_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms all_short
/-- info: 'Solidity.Backend.AbiEntry.ShortRoutesControls.zero_through_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_through_three
/-- info: 'Solidity.Backend.AbiEntry.ShortRoutesControls.four_zero_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms four_zero_value
/-- info: 'Solidity.Backend.AbiEntry.ShortRoutesControls.four_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms four_nonzero
/-- info: 'Solidity.Backend.AbiEntry.ShortRoutesControls.padded_collision_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms padded_collision_guarded
/-- info: 'Solidity.Backend.AbiEntry.ShortRoutesControls.padded_collision_unguarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms padded_collision_unguarded
/-- info: 'Solidity.Backend.AbiEntry.ShortRoutesControls.source_no_ordinary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_no_ordinary
/-- info: 'Solidity.Backend.AbiEntry.ShortRoutesControls.malformed_length_fault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms malformed_length_fault
/-- info: 'Solidity.Backend.AbiEntry.ShortRoutesControls.protected_and_saved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.ShortRoutesControls
