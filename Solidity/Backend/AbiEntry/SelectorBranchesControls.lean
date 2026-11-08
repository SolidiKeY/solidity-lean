import Solidity.Backend.AbiEntry.SelectorBranches
import Solidity.Backend.AbiEntry.SourceRoutesInterface

/-! Actual selector branches execute the existing decoder/body or a distinct
value-checked miss continuation. No branch run/poststate is assumed. -/
namespace Solidity.Backend.AbiEntry.SelectorBranchesControls
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
private def write : Prog C InputCtx InputCtx :=
  .cons (.assignLocal .here (.simple (.lit 77 (by decide)))) .nil
private theorem writeCore : inFragP (Frag.init InputCtx) write=some (Frag.init InputCtx) := by rfl
private def fallback := ValueGateBody.guard false write
private theorem fallbackCore : inFragP (Frag.init InputCtx) fallback=some (Frag.init InputCtx) :=
  ValueGateBody.admitted _ write false _ writeCore
private def left := SelectorBranches.selectedBranch 7 (Frag.init InputCtx) entry _ entryCore
private def right := SelectorBranches.selectedBranch 7 (Frag.init InputCtx) fallback _ fallbackCore
private def whole := SelectorBranches.selectedWhole 7 (Frag.init InputCtx) selectorIndex tag entry fallback _ _ entryCore fallbackCore
private def writeCompiled := ValueGateBody.selectedBody 7 (Frag.init InputCtx) write _ writeCore
private def oldCompiled := WordCarrierEntryBody.compiled 8 (.enumBelow 3) false label payload _ payloadCore
private def payloadCompiled := WordCarrierEntryBody.Binding.selectedBody 8 payload _ payloadCore

/-- Weakening adds an outer selector; the actual decoder code is unchanged at the shifted base. -/
theorem existing_entry_code : left.code=oldCompiled.code := by rfl

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
private def fallbackFinished (input : Solidity.AbiEntry.Input) (value : Fin W) : Machine :=
  {machine input value with mem := upd (machine input value).mem 9 (.val (wmod 77))}
private theorem actual (initial : Machine) (selector : Fin W)
    (selectorCell : initial.mem 7=.val selector) :
    run whole.code initial=if tag.val=selector.val then
      run (left.code++[.jump right.code.length]++right.code) initial else run right.code initial :=
  SelectorBranches.executed 7 (Frag.init InputCtx) selectorIndex tag entry fallback _ _ entryCore fallbackCore
    whole left right (SelectorBranches.whole_selected 7 (Frag.init InputCtx) selectorIndex tag entry fallback _ _ entryCore fallbackCore)
    (SelectorBranches.branch_selected 7 (Frag.init InputCtx) entry _ entryCore)
    (SelectorBranches.branch_selected 7 (Frag.init InputCtx) fallback _ fallbackCore) initial selector selectorCell
private theorem entry_run (input : Solidity.AbiEntry.Input) (value : Fin W) :
    run left.code (machine input value)=if false || decide (value.val=0) then
      if (wmod input.size).val<36 then .revert else
      if (Solidity.AbiEntry.Kind.enumBelow 3).valid (rawArgumentWord input).val then
        run payloadCompiled.code (bound input value) else .revert else .revert := by
  rw [existing_entry_code]
  exact WordCarrierEntryBody.executed 8 (.enumBelow 3) false label payload _ payloadCore oldCompiled payloadCompiled
    (WordCarrierEntryBody.selected 8 (.enumBelow 3) false label payload _ payloadCore)
    (WordCarrierEntryBody.Binding.body_selected 8 payload _ payloadCore) (machine input value) _ _ rfl rfl
private theorem fallback_run (initial : Machine) :
    run right.code initial=if false || decide (initial.callvalue.val=0) then
      .ok {initial with mem := upd initial.mem 9 (.val (wmod 77))} 0 else .revert := by
  exact ValueGateBody.executed 7 (Frag.init InputCtx) write false _ writeCore right writeCompiled
    (SelectorBranches.branch_selected 7 (Frag.init InputCtx) fallback _ fallbackCore)
    (ValueGateBody.body_selected 7 (Frag.init InputCtx) write _ writeCore) initial
private theorem good_entry : run left.code (machine good (wmod 0))=.ok (finished good (wmod 0)) 0 := by
  have full : ¬(wmod good.size).val<36 := by decide
  have valid : (Solidity.AbiEntry.Kind.enumBelow 3).valid (rawArgumentWord good).val=true := by decide
  rw [entry_run,ite_eq_right full,ite_eq_left valid]
  rfl

theorem public_selections :
    Compiler.compile 7 (Frag.init InputCtx) (SelectorBranches.program selectorIndex tag entry fallback)=some whole ∧
    Compiler.compile 7 (Frag.init InputCtx) entry=some left ∧
    Compiler.compile 7 (Frag.init InputCtx) fallback=some right :=
  ⟨SelectorBranches.whole_selected 7 (Frag.init InputCtx) selectorIndex tag entry fallback _ _ entryCore fallbackCore,
    SelectorBranches.branch_selected 7 (Frag.init InputCtx) entry _ entryCore,
    SelectorBranches.branch_selected 7 (Frag.init InputCtx) fallback _ fallbackCore⟩

theorem matched_executes_and_skips_miss :
    run whole.code (machine good (wmod 0))=.ok (finished good (wmod 0)) 0 := by
  rw [actual _ (rawSelectorWord (frame good)) rfl,
    ite_eq_left (by decide : tag.val=(rawSelectorWord (frame good)).val),List.append_assoc,run_append_ok good_entry]
  simp only [List.cons_append,List.nil_append,run,exec_cons_zero,Instr.step,Out.bind,exec_length]

theorem miss_executes_other_branch :
    run whole.code (machine miss (wmod 0))=.ok (fallbackFinished miss (wmod 0)) 0 := by
  rw [actual _ (rawSelectorWord (frame miss)) rfl,
    ite_eq_right (by decide : tag.val≠(rawSelectorWord (frame miss)).val),fallback_run]
  rfl

/-- Matching validation failure cannot fall through to an otherwise successful miss branch. -/
theorem dirty_match_terminal :
    run whole.code (machine dirty (wmod 0))=.revert ∧
    run right.code (machine dirty (wmod 0))=.ok (fallbackFinished dirty (wmod 0)) 0 := by
  have rejected : run left.code (machine dirty (wmod 0))=.revert := by
    have full : ¬(wmod dirty.size).val<36 := by decide
    have invalid : ¬(Solidity.AbiEntry.Kind.enumBelow 3).valid (rawArgumentWord dirty).val=true := by decide
    rw [entry_run,ite_eq_right full,ite_eq_right invalid]
    rfl
  constructor
  · rw [actual _ (rawSelectorWord (frame dirty)) rfl,
      ite_eq_left (by decide : tag.val=(rawSelectorWord (frame dirty)).val),List.append_assoc,run_append_revert rejected]
  · rw [fallback_run]
    rfl

theorem miss_nonpayable (value : Fin W) (nonzero : value.val≠0) :
    run whole.code (machine miss value)=.revert := by
  have blocked : (false || decide (value.val=0))=false := by simp only [Bool.false_or,decide_eq_false nonzero]
  rw [actual _ (rawSelectorWord (frame miss)) rfl,
    ite_eq_right (by decide : tag.val≠(rawSelectorWord (frame miss)).val),fallback_run]
  change (if false || decide (value.val=0) then _ else Out.revert)=Out.revert
  simp only [blocked,Bool.false_eq_true,ite_false]

/-- On a miss only the selector and value are read; malformed decoder locals are irrelevant. -/
theorem miss_ignores_entry_locals (initial : Machine)
    (selectorCell : initial.mem 7=.val (wmod 1)) (zeroValue : initial.callvalue.val=0) :
    run whole.code initial=.ok {initial with mem := upd initial.mem 9 (.val (wmod 77))} 0 := by
  rw [actual initial (wmod 1) selectorCell,ite_eq_right (by decide : tag.val≠(wmod 1).val),fallback_run]
  simp only [zeroValue,decide_true,Bool.false_or,ite_true]

theorem decoded_argument (fuel : Nat) :
    ∃ value : Solidity.AbiEntry.Word (.enumBelow 3),
      Solidity.AbiEntry.entry good (fuel+2) (singleWordParams (.enumBelow 3))=.ok (.cons (.val (.word value)) .nil) ∧
      (finished good (wmod 0)).mem 10=.val ⟨value.val,value.lt⟩ ∧
      run whole.code (machine good (wmod 0))=.ok (finished good (wmod 0)) 0 := by
  refine ⟨⟨Solidity.AbiEntry.load good.data 4,Solidity.AbiEntry.load_lt _ _,by decide⟩,
    SingleWordGate.entry_success good fuel (.enumBelow 3) (by decide) (by decide),?_,matched_executes_and_skips_miss⟩
  rfl

theorem protected_and_saved :
    (finished good (wmod 0)).mem 7=.val (rawSelectorWord (frame good)) ∧
    (finished good (wmod 0)).mem 8=.val (rawArgumentWord good) ∧
    (finished good (wmod 0)).mem 9=.val label ∧
    (finished good (wmod 0)).mem 9≠.val (wmod 77) ∧
    (finished good (wmod 0)).mem 10=.val (rawArgumentWord good) ∧
    (finished good (wmod 0)).mem 11=.val (bword true) ∧
    (finished good (wmod 0)).mem 12=.val (wmod 71) ∧
    (finished good (wmod 0)).stack=[.val (wmod 258),.val (wmod 513)] ∧
    (finished good (wmod 0)).store=(machine good (wmod 0)).store ∧
    (finished good (wmod 0)).bal=(machine good (wmod 0)).bal :=
  ⟨rfl,rfl,rfl,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.AbiEntry.SelectorBranchesControls.existing_entry_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms existing_entry_code
/-- info: 'Solidity.Backend.AbiEntry.SelectorBranchesControls.public_selections' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms public_selections
/-- info: 'Solidity.Backend.AbiEntry.SelectorBranchesControls.matched_executes_and_skips_miss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matched_executes_and_skips_miss
/-- info: 'Solidity.Backend.AbiEntry.SelectorBranchesControls.miss_executes_other_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms miss_executes_other_branch
/-- info: 'Solidity.Backend.AbiEntry.SelectorBranchesControls.dirty_match_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirty_match_terminal
/-- info: 'Solidity.Backend.AbiEntry.SelectorBranchesControls.miss_nonpayable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms miss_nonpayable
/-- info: 'Solidity.Backend.AbiEntry.SelectorBranchesControls.miss_ignores_entry_locals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms miss_ignores_entry_locals
/-- info: 'Solidity.Backend.AbiEntry.SelectorBranchesControls.decoded_argument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decoded_argument
/-- info: 'Solidity.Backend.AbiEntry.SelectorBranchesControls.protected_and_saved' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.SelectorBranchesControls
