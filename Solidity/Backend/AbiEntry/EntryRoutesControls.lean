import Solidity.Backend.AbiEntry.EntryRoutes

/-! One actual compiled tree, not concatenated assumed runs. A padded selector
and a payable fallback cannot bypass first-match length/value precedence. -/
namespace Solidity.Backend.AbiEntry.EntryRoutesControls
open Solidity.Evm
open Interface (SpecialRow entryRouteOutcome ordinaryResult specialOutcome specialRowOutcome specialResult)
private def C : Contract := {vars := []}
private def table : Interface.PayableRouteTable :=
  [(wmod 0xdeadbe00,wmod 33,false),(wmod 0xdeadbe00,wmod 44,true)]
private def recv : Option SpecialRow := some (wmod 11,true)
private def fb : Option SpecialRow := some (wmod 22,true)
private def compiled := EntryRoutes.compiled C 7 table recv fb
private def machine (selector size value : Fin W) : Machine :=
  {Machine.init with
    callvalue := value
    mem := fun address => if address=7 then .val selector else if address=8 then .val size else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private def written (selector size value label : Fin W) : Machine :=
  {machine selector size value with mem := upd (machine selector size value).mem 8 (.val label)}
private theorem actual (selector size value : Fin W) :
    run compiled.code (machine selector size value)=entryRouteOutcome 7 table recv fb selector size (machine selector size value) :=
  EntryRoutes.executed C 7 table recv fb compiled (EntryRoutes.selected C 7 table recv fb)
    (machine selector size value) selector size rfl rfl

theorem empty_receive (selector value : Fin W) :
    run compiled.code (machine selector (wmod 0) value)=.ok (written selector (wmod 0) value (wmod 11)) 0 := by
  have reached := actual selector (wmod 0) value
  have small : (wmod 0).val<4 := by decide
  have empty : (wmod 0).val=0 := rfl
  simpa only [entryRouteOutcome,if_pos small,specialOutcome,specialResult,if_pos empty,recv,
    Option.orElse_some,specialRowOutcome,Bool.true_or,if_true] using reached

theorem short_fallback (selector value : Fin W) (size : Fin W) (nonempty : size.val≠0) (small : size.val<4) :
    run compiled.code (machine selector size value)=.ok (written selector size value (wmod 22)) 0 := by
  have reached := actual selector size value
  simpa only [entryRouteOutcome,if_pos small,specialOutcome,specialResult,if_neg nonempty,fb,
    specialRowOutcome,Bool.true_or,if_true] using reached

theorem ordinary_zero :
    run compiled.code (machine (wmod 0xdeadbe00) (wmod 4) (wmod 0))=
      .ok (written (wmod 0xdeadbe00) (wmod 4) (wmod 0) (wmod 33)) 0 := by
  have reached := actual (wmod 0xdeadbe00) (wmod 4) (wmod 0)
  have full : ¬(wmod 4).val<4 := by decide
  have chosen : ordinaryResult table (wmod 0xdeadbe00)=some (wmod 33,false) := by decide
  simpa only [entryRouteOutcome,if_neg full,chosen,specialRowOutcome,Bool.false_or,decide_true,if_true] using reached

theorem ordinary_reject_no_fallback (value : Fin W) (nonzero : value.val≠0) :
    run compiled.code (machine (wmod 0xdeadbe00) (wmod 4) value)=.revert := by
  have reached := actual (wmod 0xdeadbe00) (wmod 4) value
  have full : ¬(wmod 4).val<4 := by decide
  have chosen : ordinaryResult table (wmod 0xdeadbe00)=some (wmod 33,false) := by decide
  have observed : (machine (wmod 0xdeadbe00) (wmod 4) value).callvalue.val≠0 := nonzero
  simpa only [entryRouteOutcome,if_neg full,chosen,specialRowOutcome,Bool.false_or,
    decide_eq_false observed,if_false] using reached

theorem full_miss_fallback (value : Fin W) :
    run compiled.code (machine (wmod 0) (wmod 4) value)=.ok (written (wmod 0) (wmod 4) value (wmod 22)) 0 := by
  have reached := actual (wmod 0) (wmod 4) value
  have full : ¬(wmod 4).val<4 := by decide
  have nonempty : (wmod 4).val≠0 := by decide
  have missed : ordinaryResult table (wmod 0)=none := by decide
  simpa only [entryRouteOutcome,if_neg full,missed,specialOutcome,specialResult,if_neg nonempty,
    fb,specialRowOutcome,Bool.true_or,if_true] using reached

theorem absent_all (selector size value : Fin W) :
    run (EntryRoutes.compiled C 7 [] none none).code (machine selector size value)=.revert := by
  have reached := EntryRoutes.executed C 7 [] none none (EntryRoutes.compiled C 7 [] none none)
    (EntryRoutes.selected C 7 [] none none) (machine selector size value) selector size rfl rfl
  have missed : ordinaryResult [] selector=none := rfl
  have absent : specialResult none none size=none := by
    by_cases empty : size.val=0
    · simp only [specialResult,if_pos empty,Option.orElse_none]
    · simp only [specialResult,if_neg empty]
  by_cases small : size.val<4
  · simpa only [entryRouteOutcome,if_pos small,specialOutcome,absent,specialRowOutcome] using reached
  · simpa only [entryRouteOutcome,if_neg small,missed,specialOutcome,absent,specialRowOutcome] using reached

theorem padded_collision_fixed (value : Fin W) :
    run compiled.code (machine (wmod 0xdeadbe00) (wmod 3) value)=
      .ok (written (wmod 0xdeadbe00) (wmod 3) value (wmod 22)) 0 :=
  short_fallback _ _ _ (by decide) (by decide)

theorem equal_label_no_bypass (value : Fin W) (nonzero : value.val≠0) :
    run (EntryRoutes.compiled C 7 table recv (some (wmod 33,true))).code
      (machine (wmod 0xdeadbe00) (wmod 4) value)=.revert := by
  have reached := EntryRoutes.executed C 7 table recv (some (wmod 33,true))
    (EntryRoutes.compiled C 7 table recv (some (wmod 33,true)))
    (EntryRoutes.selected C 7 table recv (some (wmod 33,true)))
    (machine (wmod 0xdeadbe00) (wmod 4) value) (wmod 0xdeadbe00) (wmod 4) rfl rfl
  have full : ¬(wmod 4).val<4 := by decide
  have chosen : ordinaryResult table (wmod 0xdeadbe00)=some (wmod 33,false) := by decide
  have observed : (machine (wmod 0xdeadbe00) (wmod 4) value).callvalue.val≠0 := nonzero
  simpa only [entryRouteOutcome,if_neg full,chosen,specialRowOutcome,Bool.false_or,
    decide_eq_false observed,if_false] using reached

theorem malformed_length_fault :
    run compiled.code {machine (wmod 0) (wmod 0) (wmod 0) with mem := fun _ => .slot (.root 0)}=.fault := by rfl

theorem protected_and_saved (selector size value label : Fin W) :
    (written selector size value label).mem 7=.val selector ∧
    (written selector size value label).mem 9=.val (wmod 71) ∧
    (written selector size value label).stack=[.val (wmod 258),.val (wmod 513)] ∧
    (written selector size value label).callvalue=value := ⟨rfl,rfl,rfl,rfl⟩
/-- info: 'Solidity.Backend.AbiEntry.EntryRoutesControls.empty_receive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_receive
/-- info: 'Solidity.Backend.AbiEntry.EntryRoutesControls.short_fallback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_fallback
/-- info: 'Solidity.Backend.AbiEntry.EntryRoutesControls.ordinary_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ordinary_zero
/-- info: 'Solidity.Backend.AbiEntry.EntryRoutesControls.ordinary_reject_no_fallback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ordinary_reject_no_fallback
/-- info: 'Solidity.Backend.AbiEntry.EntryRoutesControls.full_miss_fallback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms full_miss_fallback
/-- info: 'Solidity.Backend.AbiEntry.EntryRoutesControls.absent_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms absent_all
/-- info: 'Solidity.Backend.AbiEntry.EntryRoutesControls.padded_collision_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms padded_collision_fixed
/-- info: 'Solidity.Backend.AbiEntry.EntryRoutesControls.equal_label_no_bypass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms equal_label_no_bypass
/-- info: 'Solidity.Backend.AbiEntry.EntryRoutesControls.malformed_length_fault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms malformed_length_fault
/-- info: 'Solidity.Backend.AbiEntry.EntryRoutesControls.protected_and_saved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.EntryRoutesControls
