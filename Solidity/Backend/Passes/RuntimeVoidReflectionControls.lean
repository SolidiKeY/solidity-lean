import Solidity.Backend.Passes.RuntimeVoidReflection
import Solidity.Backend.Passes.RuntimeVoidCaptureControls

namespace Solidity.Backend.Passes.RuntimeVoidReflection.Controls
open Evm Evm.Memory
open Solidity.Backend.InternalFlow.RuntimeFrame
open V3FixedThunkProducer.Witness

def badArgument : Val P.C P.Γ .uint :=
  .readMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 9 rfl)))
def badArgs : Args P.C P.Γ [.val .uint,.mem A] :=
  .snoc (.snocMemory .nil A (.user "input") (.var (.there .here) rfl))
    .uint (.user "index") badArgument
def badCall : Stmt P.C P.Γ P.Γ := .call "argumentBounds" badArgs .none (thunk ())
def badStatement : Composition.Statement 0 F badCall :=
  (Mutation.compileCall 0 F "argumentBounds" badArgs .none (thunk ())).get
    (by first | rfl | decide | omega | decide +kernel)
def badSelected := Composition.cons badStatement (Composition.nil 0 badStatement.checked.frag)

theorem argument_failure : badArgs.evalT caller0 = .error .revert := by
  first | rfl | decide | omega | with_unfolding_all rfl

theorem bad_source : badCall.run caller0 = .error .revert := by
  first | rfl | decide | omega | with_unfolding_all rfl

theorem bad_need : 0 + badSelected.checked.need ≤ 8 := by
  first | rfl | decide | omega | decide +kernel

theorem bad_nonallocating : badSelected.checked.allocates = false := by
  first | rfl | decide | omega | decide +kernel

def bad_member : V3FixedThunkProducer.admitted 0 F badSelected.checked.need 8 8
    1 16 caller0 P.base machine0 10 :=
  ⟨represented0,by decide,bad_need,by decide,by decide,by decide,by decide,
    .inl (by decide),by decide,rfl⟩
def bad_entry := V3FixedThunkProducer.coverage thunk badSelected 8 8 bad_nonallocating
  1 16 caller0 P.base machine0 10 bad_member

def window : List Nat := List.range 22

theorem captured_window (before saved : Machine)
    (captured : Context.Captured before saved (Restore.contextCells 0 P.Γ) 8 8 10) :
    window.map saved.mem = [before.mem 0,before.mem 1,before.mem 2,before.mem 3,before.mem 4,before.mem 5,before.mem 6,before.mem 7,w[14],before.mem 9,before.mem 0,before.mem 1,before.mem 2,before.mem 3,before.mem 14,before.mem 15,before.mem 16,before.mem 17,before.mem 18,before.mem 19,before.mem 20,before.mem 21] := by
  have cell0 : saved.mem 0 = before.mem 0 := captured.locals 0 (by decide)
  have cell1 : saved.mem 1 = before.mem 1 := captured.locals 1 (by decide)
  have cell2 : saved.mem 2 = before.mem 2 := captured.locals 2 (by decide)
  have cell3 : saved.mem 3 = before.mem 3 := captured.locals 3 (by decide)
  have cell4 : saved.mem 4 = before.mem 4 := captured.locals 4 (by decide)
  have cell5 : saved.mem 5 = before.mem 5 := captured.locals 5 (by decide)
  have cell6 : saved.mem 6 = before.mem 6 := captured.locals 6 (by decide)
  have cell7 : saved.mem 7 = before.mem 7 := captured.locals 7 (by decide)
  have cell8 : saved.mem 8 = w[14] := captured.cursor
  have cell9 : saved.mem 9 = before.mem 9 := captured.exterior 9 (by decide) (.inl (by decide))
  have cell10 : saved.mem 10 = before.mem 0 := captured.payload 0 (by decide)
  have cell11 : saved.mem 11 = before.mem 1 := captured.payload 1 (by decide)
  have cell12 : saved.mem 12 = before.mem 2 := captured.payload 2 (by decide)
  have cell13 : saved.mem 13 = before.mem 3 := captured.payload 3 (by decide)
  have cell14 : saved.mem 14 = before.mem 14 := captured.exterior 14 (by decide) (.inr (by decide))
  have cell15 : saved.mem 15 = before.mem 15 := captured.exterior 15 (by decide) (.inr (by decide))
  have cell16 : saved.mem 16 = before.mem 16 := captured.exterior 16 (by decide) (.inr (by decide))
  have cell17 : saved.mem 17 = before.mem 17 := captured.exterior 17 (by decide) (.inr (by decide))
  have cell18 : saved.mem 18 = before.mem 18 := captured.exterior 18 (by decide) (.inr (by decide))
  have cell19 : saved.mem 19 = before.mem 19 := captured.exterior 19 (by decide) (.inr (by decide))
  have cell20 : saved.mem 20 = before.mem 20 := captured.exterior 20 (by decide) (.inr (by decide))
  have cell21 : saved.mem 21 = before.mem 21 := captured.exterior 21 (by decide) (.inr (by decide))
  change [saved.mem 0,saved.mem 1,saved.mem 2,saved.mem 3,saved.mem 4,saved.mem 5,saved.mem 6,saved.mem 7,saved.mem 8,saved.mem 9,saved.mem 10,saved.mem 11,saved.mem 12,saved.mem 13,saved.mem 14,saved.mem 15,saved.mem 16,saved.mem 17,saved.mem 18,saved.mem 19,saved.mem 20,saved.mem 21] = _
  rw [cell0,cell1,cell2,cell3,cell4,cell5,cell6,cell7,cell8,cell9,cell10,cell11,cell12,cell13,cell14,cell15,cell16,cell17,cell18,cell19,cell20,cell21]

def expected0 : List Word := [w[20],w[16],w[16],w[0],w[0],w[0],w[0],w[0],w[14],w[99],w[20],w[16],w[16],w[0],w[0],w[0],w[2],w[7],w[9],w[0],w[1],w[4]]
def expected9 : List Word := [w[20],w[16],w[16],w[9],w[0],w[0],w[0],w[0],w[14],w[99],w[20],w[16],w[16],w[9],w[0],w[0],w[2],w[7],w[9],w[0],w[1],w[4]]
def flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl := NoneProducer.init_flags selected.checked.frag (.refl : Ext P.Γ P.Γ)
def bodyEntry := V3FixedThunkProducer.coverage thunk selected 8 8 nonallocating
  1 16 caller9 P.base machine9 10 member9

/-- Actual successful capture, full checked singleton-call Input, then internal revert. -/
theorem body_prefix :
    ∃ saved, run (Restore.saveCells 8 (Restore.contextCells 0 P.Γ)) machine9 = .ok saved 0 ∧
      Context.Captured machine9 saved (Restore.contextCells 0 P.Γ) 8 8 10 ∧
      StateRepr 1 0 16 F caller9 P.base saved ∧
      0 + selected.checked.need ≤ 16 ∧
      AllocationInput 0 16 (selected.checked.cost caller9) caller9 P.base saved ∧
      run selected.checked.code saved = .revert ∧
      run (NoneProducer.plan selected 8 8).code machine9 = .revert ∧
      window.map saved.mem = expected9 ∧ saved.stack = [w[77]] := by
  obtain ⟨saved,captureRun,captured,represented,room,capacity,alternatives⟩ :=
    terminal_exact selected 8 8 (NoneProducer.init_flags selected.checked.frag .refl) bodyEntry
  rcases alternatives with ⟨out,source,returned⟩ | ⟨source,bodyRun,whole⟩
  · change call.run caller9 = .ok out at source
    rw [source9] at source
    cases source
  · exact ⟨saved,captureRun,captured,represented,room,capacity,bodyRun,whole,
      captured_window machine9 saved captured,captured.stack⟩

/-- Actual successful capture, full checked singleton-call Input, then internal revert. -/
theorem argument_prefix :
    ∃ saved, run (Restore.saveCells 8 (Restore.contextCells 0 P.Γ)) machine0 = .ok saved 0 ∧
      Context.Captured machine0 saved (Restore.contextCells 0 P.Γ) 8 8 10 ∧
      StateRepr 1 0 16 F caller0 P.base saved ∧
      0 + badSelected.checked.need ≤ 16 ∧
      AllocationInput 0 16 (badSelected.checked.cost caller0) caller0 P.base saved ∧
      run badSelected.checked.code saved = .revert ∧
      run (NoneProducer.plan badSelected 8 8).code machine0 = .revert ∧
      window.map saved.mem = expected0 ∧ saved.stack = [w[77]] := by
  obtain ⟨saved,captureRun,captured,represented,room,capacity,alternatives⟩ :=
    terminal_exact badSelected 8 8 (NoneProducer.init_flags badSelected.checked.frag .refl) bad_entry
  rcases alternatives with ⟨out,source,returned⟩ | ⟨source,bodyRun,whole⟩
  · change badCall.run caller0 = .ok out at source
    rw [bad_source] at source
    cases source
  · exact ⟨saved,captureRun,captured,represented,room,capacity,bodyRun,whole,
      captured_window machine0 saved captured,captured.stack⟩

theorem success_reflected :
    ∃ final addresses, run (NoneProducer.plan selected 8 8).code machine0 = .ok final 0 ∧
      StateRepr 1 0 16 selected.checked.frag reached addresses final ∧
      final.stack = [w[77]] ∧ BaseExtends caller0.H P.base addresses ∧
      GrowsAllocator 0 16 (selected.checked.cost caller0) caller0 P.base machine0 reached addresses final ∧
      final.mem 8 = w[10] ∧ Footprint.Words 8 10 machine0 final := by
  obtain ⟨wholeSource,mid,originalMap,word,final,repr,callRun,rest⟩ :=
    RuntimeVoidCapture.Controls.instantiated
  obtain ⟨out,addresses,source,represented,stack,extension,growth,cursor,older⟩ :=
    reflect_success selected 8 8 flags RuntimeVoidCapture.Controls.entry callRun
  have same : out = ⟨reached,List.prefix_refl _⟩ := Except.ok.inj (source.symm.trans source0)
  subst out
  exact ⟨mid,addresses,callRun,represented,stack,extension,growth,cursor,older⟩

theorem argument_tail (tail : List Word) :
    run (NoneProducer.plan badSelected 8 8).code (appendTail machine0 tail) = .revert :=
  (revert_iff_tail badSelected 8 8 (NoneProducer.init_flags badSelected.checked.frag .refl)
    bad_entry tail).mpr bad_source

theorem body_tail (tail : List Word) :
    run (NoneProducer.plan selected 8 8).code (appendTail machine9 tail) = .revert :=
  (revert_iff_tail selected 8 8 flags bodyEntry tail).mpr source9

theorem success_not_revert : run (NoneProducer.plan selected 8 8).code machine0 ≠ .revert := by
  intro bad
  have source := (revert_iff selected 8 8 flags RuntimeVoidCapture.Controls.entry).mp bad
  change call.run caller0 = .error .revert at source
  rw [source0] at source
  cases source

def panicBody : Prog P.C [.val .uint,.mem A] [.val .uint,.mem A] :=
  .cons (.assert (.simple (.bool false))) .nil

theorem panic_source : (Stmt.call "panic" args .none panicBody).run caller0 = .error .panic := by
  first | rfl | decide | omega | with_unfolding_all rfl

theorem panic_selector_refused :
    (Mutation.compileCall 0 F "panic" args .none panicBody).isSome = false := by
  first | rfl | decide | omega | decide +kernel

def loopBody : Prog P.C [.val .uint,.mem A] [.val .uint,.mem A] :=
  .cons (.loop .auto (.simple (.bool true)) .nil) .nil

theorem loop_selector_refused :
    (Mutation.compileCall 0 F "loop" args .none loopBody).isSome = false := by
  first | rfl | decide | omega | decide +kernel

theorem original_arguments_succeed : args.evalT caller9 =
    .ok (P.uint 9 (by decide),some P.r0,()) := by
  first | rfl | decide | omega | with_unfolding_all rfl

theorem original_body_fails :
    (thunk ()).runR (caller9.withEnv (P.uint 9 (by decide),some P.r0,())) = .error .revert := by
  first | rfl | decide | omega | with_unfolding_all rfl

theorem skipped_capture_window_refused : window.map machine0.mem ≠ expected0 := by decide

end Solidity.Backend.Passes.RuntimeVoidReflection.Controls
