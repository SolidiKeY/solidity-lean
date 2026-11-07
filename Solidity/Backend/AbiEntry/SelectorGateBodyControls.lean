import Solidity.Backend.AbiEntry.SelectorGateBody
import Solidity.Backend.AbiEntry.SourceRoutesInterface
import Solidity.Source.SemanticsExamples

/-! Distinct typed selector/argument/length cells feed the existing decoder and
actual body through Prog.wk, not copied validation. These are represented-local
controls, not a native loader or full Source dispatch certificate. -/
namespace Solidity.Backend.AbiEntry.SelectorGateBodyControls
open Solidity.Evm
open Interface
private def C : Contract := {vars := []}
private def label : Fin W := wmod 99
private def tag : Fin W := wmod 0xabcdef12
private abbrev InputCtx : Ctx := RouteCtx++[.val .uint]
private def selectorIndex : Idx InputCtx (.val .uint) := .there (.there .here)
private def injectSelector : Thin RouteCtx InputCtx := .keep (.keep (.drop .refl))
private def BodyCtx : Ctx := .val .bool :: UIntBoundCtx
private def payload : Prog C UIntBoundCtx BodyCtx :=
  .cons (.declLocal .bool (.user "matchesTwo") (some
    (.binop .eqB rfl rfl (.simple (.local .here)) (.simple (.lit 2 (by decide)))))) .nil
private theorem payloadCore : inFragP (Frag.init UIntBoundCtx) payload=some (Frag.init BodyCtx) := by rfl
private def oldProgram := WordCarrierEntryBody.program (.enumBelow 3) false label payload
private def lifted := oldProgram.wk injectSelector
private def entry : Prog C InputCtx lifted.1 := lifted.2.2
private theorem entryCore : inFragP (Frag.init InputCtx) entry=some (Frag.init lifted.1) := by rfl
private def back := SelectorGateBody.selectedBody 7 (Frag.init InputCtx) entry _ entryCore
private def whole := SelectorGateBody.selectedWhole 7 (Frag.init InputCtx) selectorIndex tag entry _ entryCore
private def oldCompiled := WordCarrierEntryBody.compiled 8 (.enumBelow 3) false label payload _ payloadCore
private def payloadCompiled := WordCarrierEntryBody.Binding.selectedBody 8 payload _ payloadCore

/-- Weakening adds an outer selector; the actual decoder code is unchanged at the shifted base. -/
theorem existing_entry_code : back.code=oldCompiled.code := by rfl

private def good : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 31 0++[2,0x77,0x88],free := 71}
private def miss : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x13]++List.replicate 31 0++[2],free := 71}
private def dirty : Solidity.AbiEntry.Input :=
  {data := [0xab,0xcd,0xef,0x12]++List.replicate 31 0++[3],free := 71}
private def frame (input : Solidity.AbiEntry.Input) : Source.Fr :=
  {this := ⟨0,by decide⟩,sender := ⟨0,by decide⟩,value := wmod 0,
    static := false,contract := "C",cd := input.data}
private def machine (input : Solidity.AbiEntry.Input) (value : Fin W) : Machine :=
  {Machine.init with
    callvalue := value
    mem := fun address => if address=7 then .val (rawSelectorWord (frame input))
      else if address=8 then .val (rawArgumentWord input)
      else if address=9 then .val (wmod input.size) else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private def bound (input : Solidity.AbiEntry.Input) (value : Fin W) : Machine :=
  uintBoundMachine 8 label (rawArgumentWord input) (machine input value)
private def finished (input : Solidity.AbiEntry.Input) (value : Fin W) : Machine :=
  {bound input value with mem := upd (bound input value).mem 11 (.val (bword true))}
private theorem guarded (input : Solidity.AbiEntry.Input) (value : Fin W) :
    run whole.code (machine input value)=if tag.val=(rawSelectorWord (frame input)).val then
      run oldCompiled.code (machine input value) else .revert := by
  rw [SelectorGateBody.executed 7 (Frag.init InputCtx) selectorIndex tag entry _ entryCore whole back
    (SelectorGateBody.whole_selected 7 (Frag.init InputCtx) selectorIndex tag entry _ entryCore)
    (SelectorGateBody.body_selected 7 (Frag.init InputCtx) entry _ entryCore)
    (machine input value) (rawSelectorWord (frame input)) rfl,existing_entry_code]
private theorem decoded (input : Solidity.AbiEntry.Input) (value : Fin W) :
    run oldCompiled.code (machine input value)=if false || decide (value.val=0) then
      if (wmod input.size).val<36 then .revert else
      if (Solidity.AbiEntry.Kind.enumBelow 3).valid (rawArgumentWord input).val then
        run payloadCompiled.code (bound input value) else .revert else .revert :=
  WordCarrierEntryBody.executed 8 (.enumBelow 3) false label payload _ payloadCore oldCompiled payloadCompiled
    (WordCarrierEntryBody.selected 8 (.enumBelow 3) false label payload _ payloadCore)
    (WordCarrierEntryBody.Binding.body_selected 8 payload _ payloadCore)
    (machine input value) _ _ rfl rfl

theorem selected_and_executes :
    Compiler.compile 7 (Frag.init InputCtx) (SelectorGateBody.program selectorIndex tag entry)=some whole ∧
    Compiler.compile 7 (Frag.init InputCtx) entry=some back ∧
    run whole.code (machine good (wmod 0))=.ok (finished good (wmod 0)) 0 := by
  refine ⟨SelectorGateBody.whole_selected 7 (Frag.init InputCtx) selectorIndex tag entry _ entryCore,
    SelectorGateBody.body_selected 7 (Frag.init InputCtx) entry _ entryCore,?_⟩
  have matched : tag.val=(rawSelectorWord (frame good)).val := by decide
  have full : ¬(wmod good.size).val<36 := by decide
  have valid : (Solidity.AbiEntry.Kind.enumBelow 3).valid (rawArgumentWord good).val=true := by decide
  rw [guarded,if_pos matched,decoded,if_neg full,if_pos valid]
  rfl

theorem wrong_selector_rejected : run whole.code (machine miss (wmod 0))=.revert := by
  have different : tag.val≠(rawSelectorWord (frame miss)).val := by decide
  rw [guarded,if_neg different]

theorem dirty_enum_after_match (fuel : Nat) :
    run whole.code (machine dirty (wmod 0))=.revert ∧
    Solidity.AbiEntry.entry dirty (fuel+2) (singleWordParams (.enumBelow 3))=.error .revert := by
  have matched : tag.val=(rawSelectorWord (frame dirty)).val := by decide
  have full : ¬(wmod dirty.size).val<36 := by decide
  have invalid : ¬(Solidity.AbiEntry.Kind.enumBelow 3).valid (rawArgumentWord dirty).val=true := by decide
  constructor
  · rw [guarded,if_pos matched,decoded,if_neg full,if_neg invalid]
    rfl
  · rw [SingleWordGate.entry_form]
    have size : ¬dirty.size<36 := by decide
    rw [if_neg size]
    exact dif_neg invalid

theorem matched_nonpayable (value : Fin W) (nonzero : value.val≠0) :
    run whole.code (machine good value)=.revert := by
  have matched : tag.val=(rawSelectorWord (frame good)).val := by decide
  have blocked : (false || decide (value.val=0))=false := by
    simp only [Bool.false_or,decide_eq_false nonzero]
  rw [guarded,if_pos matched,decoded]
  simp only [blocked,Bool.false_eq_true,if_false]

/-- A miss needs only the selector cell, even if every other local is malformed. -/
theorem miss_before_any_entry_local (initial : Machine)
    (selectorCell : initial.mem 7=.val (wmod 1)) : run whole.code initial=.revert :=
  SelectorGateBody.miss_before_body 7 (Frag.init InputCtx) selectorIndex tag entry _ entryCore
    initial (wmod 1) selectorCell (by decide)

theorem raw_value_and_body (fuel : Nat) :
    ∃ value : Solidity.AbiEntry.Word (.enumBelow 3),
      Solidity.AbiEntry.entry good (fuel+2) (singleWordParams (.enumBelow 3))=.ok (.cons (.val (.word value)) .nil) ∧
      (bound good (wmod 0)).mem 10=.val ⟨value.val,value.lt⟩ ∧
      run whole.code (machine good (wmod 0))=run payloadCompiled.code (bound good (wmod 0)) := by
  rcases WordCarrierEntryBody.decoded_body 8 (.enumBelow 3) false label payload _ payloadCore oldCompiled payloadCompiled
    (WordCarrierEntryBody.selected 8 (.enumBelow 3) false label payload _ payloadCore)
    (WordCarrierEntryBody.Binding.body_selected 8 payload _ payloadCore)
    good fuel (machine good (wmod 0)) (wmod good.size) rfl rfl (by decide) (by decide) (by decide) (by decide) with
    ⟨value,semantic,cell,bodyRun⟩
  refine ⟨value,semantic,cell,?_⟩
  have matched : tag.val=(rawSelectorWord (frame good)).val := by decide
  rw [guarded,if_pos matched,bodyRun]
  rfl

theorem protected_and_saved :
    (finished good (wmod 0)).mem 7=.val (rawSelectorWord (frame good)) ∧
    (finished good (wmod 0)).mem 8=.val (rawArgumentWord good) ∧
    (finished good (wmod 0)).mem 9=.val label ∧
    (finished good (wmod 0)).mem 10=.val (rawArgumentWord good) ∧
    (finished good (wmod 0)).mem 11=.val (bword true) ∧
    (finished good (wmod 0)).mem 12=.val (wmod 71) ∧
    (finished good (wmod 0)).stack=[.val (wmod 258),.val (wmod 513)] ∧
    (finished good (wmod 0)).callvalue=wmod 0 ∧
    (finished good (wmod 0)).store=(machine good (wmod 0)).store ∧
    (finished good (wmod 0)).bal=(machine good (wmod 0)).bal :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- A matched selector and allowed value still perform the head check first. -/
theorem matched_short_before_word_and_body :
    run whole.code {machine good (wmod 0) with
      mem := fun address => if address=7 then .val tag else if address=9 then .val (wmod 35) else .slot (.root 0)}=.revert := by
  rw [SelectorGateBody.executed 7 (Frag.init InputCtx) selectorIndex tag entry _ entryCore whole back
    (SelectorGateBody.whole_selected 7 (Frag.init InputCtx) selectorIndex tag entry _ entryCore)
    (SelectorGateBody.body_selected 7 (Frag.init InputCtx) entry _ entryCore) _ tag rfl,
    if_pos (rfl : tag.val=tag.val),existing_entry_code]
  rw [WordCarrierEntryBody.gated 8 (.enumBelow 3) false label payload _ payloadCore oldCompiled
    (WordCarrierEntryBody.selected 8 (.enumBelow 3) false label payload _ payloadCore)]
  change (if false || decide ((wmod 0).val=0) then
    run (WordCarrierEntryBody.Binding.selectedWhole 8 (.enumBelow 3) label payload _ payloadCore).code
      {machine good (wmod 0) with
        mem := fun address => if address=7 then .val tag else if address=9 then .val (wmod 35) else .slot (.root 0)}
    else .revert)=.revert
  rw [if_pos (by decide : (false || decide ((wmod 0).val=0))=true)]
  exact WordCarrierEntryBody.Binding.short_before_body 8 (.enumBelow 3) label payload _ payloadCore _
    (wmod 35) rfl (by decide)

private def rejecting : Prog C InputCtx InputCtx := .cons .revert .nil
private theorem rejectingCore : inFragP (Frag.init InputCtx) rejecting=some (Frag.init InputCtx) := by rfl
/-- Matching a selector does not imply body success. -/
theorem matching_reverting_body :
    run (SelectorGateBody.selectedWhole 7 (Frag.init InputCtx) selectorIndex tag rejecting _ rejectingCore).code
      (machine good (wmod 0))=.revert := by
  rw [SelectorGateBody.executed 7 (Frag.init InputCtx) selectorIndex tag rejecting _ rejectingCore _ _
    (SelectorGateBody.whole_selected 7 (Frag.init InputCtx) selectorIndex tag rejecting _ rejectingCore)
    (SelectorGateBody.body_selected 7 (Frag.init InputCtx) rejecting _ rejectingCore)
    (machine good (wmod 0)) (rawSelectorWord (frame good)) rfl,
    if_pos (by decide : tag.val=(rawSelectorWord (frame good)).val)]
  rfl

private def global := Source.SemanticsExamples.G0 .legacy
private def sourceTag := SourceRoutes.selectorWord global []
private def sourceWhole := SelectorGateBody.selectedWhole 7 (Frag.init InputCtx) selectorIndex sourceTag entry _ entryCore
private def sourceInput : Solidity.AbiEntry.Input :=
  {data := List.replicate 35 0++[2,0x77,0x88],free := 71}
private theorem source_actual (input : Solidity.AbiEntry.Input) (full : 4≤input.data.length) :
    run sourceWhole.code (machine input (wmod 0))=
      if global.selector []==(frame input).cd.take 4 then run oldCompiled.code (machine input (wmod 0)) else .revert := by
  rw [SelectorGateBody.source_executed global [] (frame input) full
    7 (Frag.init InputCtx) selectorIndex entry _ entryCore sourceWhole back
    (SelectorGateBody.whole_selected 7 (Frag.init InputCtx) selectorIndex sourceTag entry _ entryCore)
    (SelectorGateBody.body_selected 7 (Frag.init InputCtx) entry _ entryCore) (machine input (wmod 0)) rfl,
    existing_entry_code]

/-- The published model hash supplies inhabited match/miss predicate controls, not a Keccak claim. -/
theorem source_predicate_match_and_miss :
    (global.selector []==(frame sourceInput).cd.take 4)=true ∧
    (global.selector []==(frame miss).cd.take 4)=false ∧
    run sourceWhole.code (machine sourceInput (wmod 0))=.ok (finished sourceInput (wmod 0)) 0 ∧
    run sourceWhole.code (machine miss (wmod 0))=.revert := by
  refine ⟨by decide,by decide,?_,?_⟩
  · have matched : (global.selector []==(frame sourceInput).cd.take 4)=true := by decide
    have full : ¬(wmod sourceInput.size).val<36 := by decide
    have valid : (Solidity.AbiEntry.Kind.enumBelow 3).valid (rawArgumentWord sourceInput).val=true := by decide
    rw [source_actual sourceInput (by decide),if_pos matched,decoded,if_neg full,if_pos valid]
    rfl
  · have different : ¬(global.selector []==(frame miss).cd.take 4)=true := by decide
    rw [source_actual miss (by decide),if_neg different]

/-- info: 'Solidity.Backend.AbiEntry.SelectorGateBodyControls.source_predicate_match_and_miss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_predicate_match_and_miss
/-- info: 'Solidity.Backend.AbiEntry.SelectorGateBodyControls.matched_short_before_word_and_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matched_short_before_word_and_body
/-- info: 'Solidity.Backend.AbiEntry.SelectorGateBodyControls.matching_reverting_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matching_reverting_body
/-- info: 'Solidity.Backend.AbiEntry.SelectorGateBodyControls.existing_entry_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms existing_entry_code
/-- info: 'Solidity.Backend.AbiEntry.SelectorGateBodyControls.selected_and_executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected_and_executes
/-- info: 'Solidity.Backend.AbiEntry.SelectorGateBodyControls.wrong_selector_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_selector_rejected
/-- info: 'Solidity.Backend.AbiEntry.SelectorGateBodyControls.dirty_enum_after_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirty_enum_after_match
/-- info: 'Solidity.Backend.AbiEntry.SelectorGateBodyControls.matched_nonpayable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matched_nonpayable
/-- info: 'Solidity.Backend.AbiEntry.SelectorGateBodyControls.miss_before_any_entry_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms miss_before_any_entry_local
/-- info: 'Solidity.Backend.AbiEntry.SelectorGateBodyControls.raw_value_and_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_value_and_body
/-- info: 'Solidity.Backend.AbiEntry.SelectorGateBodyControls.protected_and_saved' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.SelectorGateBodyControls
