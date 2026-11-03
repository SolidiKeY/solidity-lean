import Solidity.Yul.World.PhysicalCall

/-! An actual immediate answer of the existing pending-environment source
machine. No raw CALL dispatch/code/ABI equivalence is claimed. No owner edits. -/
namespace Solidity.Yul.World.PhysicalCompletion
open Solidity.Source
open Solidity.Roadmap (Outcome)
open Solidity.Yul.Views

def answerStrategy {E : Env} (G : Glob E) (out : Outcome) : Glob E :=
  {G with callee:=fun _=>.answer out}

theorem actual_answer_run {E} (G : Glob E) (s : EMState E []) (out : Outcome) (depth : Nat) (static : Bool) :
    (Source.envLoop (answerStrategy G out) 1 depth static).run s =
      (.ok out,(s.1,{s.2 with events:=s.2.events++[.answer out none]})) := rfl

/-- Executes the actual source environment branch. Physical journals are
unchanged by this no-credit/no-callback case, not erased from its result. -/
def environmentAnswer {E} (G : Glob E) (entry : EMState E [])
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects E.layout E.lay E.lay) (f : ResidualFrame) (out : Outcome) :=
  let run := (Source.envLoop (answerStrategy G out) 1 0 f.source.static).run entry
  match run.1 with
  | .error h => Except.error h
  | .ok actual => Except.ok (actual,finish entry b o f ⟨⟨run.2,r⟩,b⟩ [.event (.answer actual none)] actual)

theorem environmentAnswer_actual {E} (G : Glob E) (entry : EMState E [])
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects E.layout E.lay E.lay) (f : ResidualFrame) (out : Outcome) :
    environmentAnswer G entry r b o f out =
      .ok (out,finish entry b o f ⟨⟨(entry.1,{entry.2 with events:=entry.2.events++[.answer out none]}),r⟩,b⟩
        [.event (.answer out none)] out) := rfl

/-- Actual single-answer pending-environment source execution as a consumer
port. This does not implement general raw call dispatch or callbacks/credits. -/
def environmentInvoke {E} (G : Glob E) (out : Outcome) : Invoke E [] :=
  fun _ frame _ _ _ _ c =>
    let run := (Source.envLoop (answerStrategy G out) 1 0 frame.source.static).run c.1.1
    some ((run.1,⟨⟨run.2,c.1.2⟩,c.2⟩),[.event (.answer out none)])

theorem environmentInvoke_actual {E} (G : Glob E) (out : Outcome)
    (o : ObservedEffects E.layout E.lay E.lay) f kind target gas input (c : Carrier E []) :
    environmentInvoke G out o f kind target gas input c =
      some ((.ok out,⟨⟨(c.1.1.1,{c.1.1.2 with events:=c.1.1.2.events++[.answer out none]}),c.1.2⟩,c.2⟩),
        [.event (.answer out none)]) := rfl

/-- Explicit external-code input for the narrow witness: only0x20 has code;
other addresses answer empty-success. This is a Glob input, not another world. -/
def externalAnswerGlob {E} (G : Glob E) (out : Outcome) : Glob E :=
  {G with hasCode:=fun _ a=>decide (a.val=32),callee:=fun history=>
    match history.getLast? with
    | some (.call a _ _ _) => if a.val=32 then .answer out else .answer (.success [])
    | _ => .answer (.success [])}

theorem external_zero_no_code {E} (G : Glob E) out history :
    (externalAnswerGlob G out).hasCode history 0=false := rfl

theorem external_precompile_no_code {E} (G : Glob E) out history (a : Roadmap.Address)
    (precompile : Roadmap.Address.Precompile a) : (externalAnswerGlob G out).hasCode history a=false := by
  have not32 : a.val≠32 := by
    intro eq
    have same : a=(⟨32,by decide⟩ : Roadmap.Address) := Fin.ext eq
    rw [same] at precompile
    change false=true at precompile
    cases precompile
  exact decide_eq_false not32

theorem external_codeless_succeeds {E} (G : Glob E) out history (a : Roadmap.Address) value input static
    (noCode : (externalAnswerGlob G out).hasCode history a=false) :
    (externalAnswerGlob G out).callee (history++[.call a value input static])=.answer (.success []) := by
  have not32 : a.val≠32 := by
    intro eq
    change decide (a.val=32)=false at noCode
    simp only [eq,decide_true] at noCode
    cases noCode
  simp only [externalAnswerGlob,List.getLast?_concat,not32,if_false]

/-- A narrow actual source-call producer: STATICCALL to an external-code0x20
account with immediate answer. Zero/precompiles/known code are excluded by
actual classifiers. Source.callAddr performs the complete call/answer events
and source rollback. No fixed precompile is treated as environment code. -/
def staticEnvironmentInvoke {E} (G : Glob E) (out : Outcome) : Invoke E [] :=
  fun _ frame kind target _ input c =>
    match kind with
    | .staticcall =>
      if decide (target.val≠0) && !(Roadmap.Evm.Precompile.ofAddress? target.val).isSome &&
          (externalAnswerGlob G out).hasCode c.1.1.2.events target &&
          (frame.source.this == target) && frame.source.static &&
          (c.1.1.2.ex.world.accounts target).code.isNone then
        let F : Fr := ⟨frame.source.caller,frame.source.caller,0,true,"EnvironmentAnswer",true,0⟩
        let run := (Source.callAddr (externalAnswerGlob G out) F 2 target 0 input true).run c.1.1
        some ((run.1,⟨⟨run.2,c.1.2⟩,c.2⟩),[.event (.call target 0 input true),.event (.answer out none)])
      else none
    | .call | .delegatecall => none

theorem static_precompile_refusal {E} (G : Glob E) out (o : ObservedEffects E.layout E.lay E.lay)
    f (target : Roadmap.Address) gas input (c : Carrier E []) (precompile : Roadmap.Address.Precompile target) :
    staticEnvironmentInvoke G out o f .staticcall target gas input c=none := by
  change (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=true at precompile
  simp only [staticEnvironmentInvoke,precompile,Bool.not_true,Bool.and_false,Bool.false_and,Bool.false_eq_true,if_false]

theorem static_external_code_refusal {E} (G : Glob E) out (o : ObservedEffects E.layout E.lay E.lay)
    f (target : Roadmap.Address) gas input (c : Carrier E []) (not32 : target.val≠32) :
    staticEnvironmentInvoke G out o f .staticcall target gas input c=none := by
  simp only [staticEnvironmentInvoke,externalAnswerGlob,not32,decide_false,
    Bool.and_false,Bool.false_and,Bool.false_eq_true,if_false]

end Solidity.Yul.World.PhysicalCompletion
