import Solidity.Backend.AbiEntry.PayableRoutes

/-! A rejecting matched row never falls through to a payable collision; a
nonmatching row never performs its gate. The no-match label is not a fallback body. -/
namespace Solidity.Backend.AbiEntry.PayableRoutesControls
open Solidity.Evm
open Interface (RouteCtx PayableRouteTable payableRouteOutcome payableRouteResult)
private def C : Contract := {vars := []}
private def table : PayableRouteTable :=
  [(wmod 0xdeadbeef,wmod 11,false),(wmod 0xdeadbeef,wmod 22,true),(wmod 0x12345678,wmod 33,true)]
private def fallback : Fin W := wmod 99
private def selected := PayableRoutes.compiled C 7 table fallback
private def machine (selector value : Fin W) : Machine :=
  {Machine.init with
    callvalue := value
    stack := [.val (wmod 258),.val (wmod 513)]
    mem := fun address => if address=7 then .val selector else .val (wmod 71)}
private def written (selector value label : Fin W) : Machine :=
  {machine selector value with mem := upd (machine selector value).mem 8 (.val label)}
private theorem actual (selector value : Fin W) : run selected.code (machine selector value)=
    payableRouteOutcome 7 table fallback selector (machine selector value) :=
  PayableRoutes.executed C 7 table fallback selected (PayableRoutes.selected C 7 table fallback)
    (machine selector value) selector rfl

theorem checked_selection : Compiler.compile 7 (Frag.init RouteCtx)
    (PayableRoutes.route C table fallback)=some selected := PayableRoutes.selected C 7 table fallback

theorem zero_nonpayable : run selected.code (machine (wmod 0xdeadbeef) (wmod 0))=
    .ok (written (wmod 0xdeadbeef) (wmod 0) (wmod 11)) 0 := by
  have reached := actual (wmod 0xdeadbeef) (wmod 0)
  rw [payableRouteOutcome,show payableRouteResult table fallback (wmod 0xdeadbeef)=(wmod 11,false) from by decide] at reached
  exact reached

theorem nonzero_nonpayable (value : Fin W) (nonzero : value.val≠0) :
    run selected.code (machine (wmod 0xdeadbeef) value)=.revert := by
  have reached := actual (wmod 0xdeadbeef) value
  rw [payableRouteOutcome,show payableRouteResult table fallback (wmod 0xdeadbeef)=(wmod 11,false) from by decide] at reached
  have observed : (machine (wmod 0xdeadbeef) value).callvalue.val≠0 := nonzero
  simpa only [Bool.false_or,decide_eq_false observed,Bool.false_eq_true,if_false] using reached

theorem payable_later (value : Fin W) : run selected.code (machine (wmod 0x12345678) value)=
    .ok (written (wmod 0x12345678) value (wmod 33)) 0 := by
  have reached := actual (wmod 0x12345678) value
  rw [payableRouteOutcome,show payableRouteResult table fallback (wmod 0x12345678)=(wmod 33,true) from by decide] at reached
  exact reached

theorem no_match_label (value : Fin W) : run selected.code (machine (wmod 0x11223344) value)=
    .ok (written (wmod 0x11223344) value fallback) 0 := by
  have reached := actual (wmod 0x11223344) value
  rw [payableRouteOutcome,show payableRouteResult table fallback (wmod 0x11223344)=(fallback,true) from by decide] at reached
  exact reached

theorem no_collision_fallthrough (value : Fin W) (nonzero : value.val≠0) :
    run selected.code (machine (wmod 0xdeadbeef) value)≠.ok (written (wmod 0xdeadbeef) value (wmod 22)) 0 := by
  rw [nonzero_nonpayable value nonzero]
  intro impossible
  cases impossible

theorem protected_and_saved (selector value label : Fin W) :
    (written selector value label).mem 7=.val selector ∧
    (written selector value label).mem 9=.val (wmod 71) ∧
    (written selector value label).stack=[.val (wmod 258),.val (wmod 513)] ∧
    (written selector value label).callvalue=value := ⟨rfl,rfl,rfl,rfl⟩

private def malformed : Machine := {machine (wmod 0) (wmod 1) with mem := fun _ => .slot (.root 0)}
theorem malformed_fault : run selected.code malformed=.fault := by rfl

/-- info: 'Solidity.Backend.AbiEntry.PayableRoutesControls.checked_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checked_selection
/-- info: 'Solidity.Backend.AbiEntry.PayableRoutesControls.zero_nonpayable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_nonpayable
/-- info: 'Solidity.Backend.AbiEntry.PayableRoutesControls.nonzero_nonpayable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonzero_nonpayable
/-- info: 'Solidity.Backend.AbiEntry.PayableRoutesControls.payable_later' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms payable_later
/-- info: 'Solidity.Backend.AbiEntry.PayableRoutesControls.no_match_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_match_label
/-- info: 'Solidity.Backend.AbiEntry.PayableRoutesControls.no_collision_fallthrough' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_collision_fallthrough
/-- info: 'Solidity.Backend.AbiEntry.PayableRoutesControls.protected_and_saved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
/-- info: 'Solidity.Backend.AbiEntry.PayableRoutesControls.malformed_fault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms malformed_fault
end Solidity.Backend.AbiEntry.PayableRoutesControls
