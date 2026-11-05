import Solidity.Backend.AbiEntry.SelectorRoutes

/-! Actual public compiler selection and routing, with duplicate selector
priority, fallback, protected cells/stack and a raw malformed-cell fault. -/
namespace Solidity.Backend.AbiEntry.SelectorRoutesControls
open Solidity.Evm
open Interface (RouteCtx RouteTable routeResult)
private def C : Contract := {vars := []}
private def table : RouteTable :=
  [(wmod 0xdeadbeef,wmod 11),(wmod 0xdeadbeef,wmod 22),(wmod 0x12345678,wmod 33)]
private def fallback : Fin W := wmod 99
private def selected := SelectorRoutes.compiled C 7 table fallback
private def machine (selector : Fin W) : Machine :=
  {Machine.init with
    stack := [.val (wmod 258),.val (wmod 513)]
    mem := fun address => if address=7 then .val selector else .val (wmod 71)}
private def written (initial : Machine) (label : Fin W) : Machine :=
  {initial with mem := upd initial.mem 8 (.val label)}
private theorem actual (selector : Fin W) : run selected.code (machine selector)=
    .ok (written (machine selector) (routeResult table fallback selector)) 0 :=
  SelectorRoutes.executed C 7 table fallback selected (SelectorRoutes.selected C 7 table fallback)
    (machine selector) selector rfl

theorem checked_selection : Compiler.compile 7 (Frag.init RouteCtx)
    (SelectorRoutes.route C table fallback)=some selected := SelectorRoutes.selected C 7 table fallback

theorem duplicate_first : run selected.code (machine (wmod 0xdeadbeef))=
    .ok (written (machine (wmod 0xdeadbeef)) (wmod 11)) 0 := by
  have reached := actual (wmod 0xdeadbeef)
  rw [show routeResult table fallback (wmod 0xdeadbeef)=wmod 11 from by decide] at reached
  exact reached

theorem later_match : run selected.code (machine (wmod 0x12345678))=
    .ok (written (machine (wmod 0x12345678)) (wmod 33)) 0 := by
  have reached := actual (wmod 0x12345678)
  rw [show routeResult table fallback (wmod 0x12345678)=wmod 33 from by decide] at reached
  exact reached

theorem unmatched_fallback : run selected.code (machine (wmod 0x11223344))=
    .ok (written (machine (wmod 0x11223344)) (wmod 99)) 0 := by
  have reached := actual (wmod 0x11223344)
  rw [show routeResult table fallback (wmod 0x11223344)=wmod 99 from by decide] at reached
  exact reached

theorem protected_and_saved (selector label : Fin W) :
    (written (machine selector) label).mem 7=.val selector ∧
    (written (machine selector) label).mem 9=.val (wmod 71) ∧
    (written (machine selector) label).stack=[.val (wmod 258),.val (wmod 513)] := ⟨rfl,rfl,rfl⟩

private def malformed : Machine := {machine (wmod 0) with mem := fun _ => .slot (.root 0)}
theorem malformed_fault : run selected.code malformed=.fault := by rfl

theorem empty_table :
    run (SelectorRoutes.compiled C 7 [] fallback).code malformed=.ok (written malformed fallback) 0 := by rfl

theorem mutation_not_noop : written (machine (wmod 0xdeadbeef)) (wmod 11)≠machine (wmod 0xdeadbeef) := by
  intro same
  have impossible : Word.val (wmod 11)=Word.val (wmod 71) := congrArg (fun state => state.mem 8) same
  exact (by decide : Word.val (wmod 11)≠Word.val (wmod 71)) impossible

/-- info: 'Solidity.Backend.AbiEntry.SelectorRoutesControls.checked_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checked_selection
/-- info: 'Solidity.Backend.AbiEntry.SelectorRoutesControls.duplicate_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms duplicate_first
/-- info: 'Solidity.Backend.AbiEntry.SelectorRoutesControls.later_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms later_match
/-- info: 'Solidity.Backend.AbiEntry.SelectorRoutesControls.unmatched_fallback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unmatched_fallback
/-- info: 'Solidity.Backend.AbiEntry.SelectorRoutesControls.protected_and_saved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
/-- info: 'Solidity.Backend.AbiEntry.SelectorRoutesControls.malformed_fault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms malformed_fault
/-- info: 'Solidity.Backend.AbiEntry.SelectorRoutesControls.empty_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_table
/-- info: 'Solidity.Backend.AbiEntry.SelectorRoutesControls.mutation_not_noop' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms mutation_not_noop
end Solidity.Backend.AbiEntry.SelectorRoutesControls
