import Solidity.Yul.World.CallerFrame

/-! One actual environment credit to a recognized source instance, then answer.
These are explicit Glob inputs, not supplied mutation lists or outcome laws.
General callbacks/callee adequacy and resource correspondence remain open. -/
namespace Solidity.Yul.World.CreditEnvironment
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion

/-- External code only at0x20; source contract index0 is Finite. Credits are
chosen by the actual source strategy after CALL, never replayed by an adapter. -/
def creditGlob {E} (G : Glob E) (out : Outcome) : Glob E :=
  {externalAnswerGlob G out with
    prog:={G.prog with contracts:=["Finite"]}
    callee:=fun history=>match history.getLast? with
      | some (.call a _ _ _) => if a.val=32 then .credit ⟨64,by decide⟩ 7 else .answer (.success [])
      | some (.credit a v) => if a.val=64 ∧ v.val=7 then .answer out else .answer (.success [])
      | _ => .answer (.success [])}

theorem codeless_succeeds {E} (G : Glob E) out history (a : Address) value input static
    (noCode : (creditGlob G out).hasCode history a=false) :
    (creditGlob G out).callee (history++[.call a value input static])=.answer (.success []) := by
  have not32 : a.val≠32 := by
    intro eq
    change decide (a.val=32)=false at noCode
    simp only [eq,decide_true] at noCode
    cases noCode
  simp only [creditGlob,List.getLast?_concat,not32,if_false]

theorem zero_no_code {E} (G : Glob E) out history : (creditGlob G out).hasCode history 0=false := rfl

theorem precompile_no_code {E} (G : Glob E) out history (a : Address) (precompile : Roadmap.Address.Precompile a) :
    (creditGlob G out).hasCode history a=false := external_precompile_no_code G out history a precompile

/-- Selected real source CALL producer. Source instance/code/classification and
credit range are checked before invocation. Refusal is not an EVM result.
The source horizon3 executes CALL→credit→answer; no existing fuel limit changes. -/
def invokeAt {E} (horizon : Nat) (G : Glob E) (out : Outcome) : Invoke E [] :=
  fun _ frame kind target _ input c=>
    match kind with
    | .call =>
      if decide (target.val≠0) && !(Roadmap.Evm.Precompile.ofAddress? target.val).isSome &&
          (creditGlob G out).hasCode c.1.1.2.events target &&
          (frame.source.this == target) && !frame.source.static && decide (frame.source.value.val=0) &&
          (c.1.1.2.ex.world.accounts target).code.isNone &&
          decide ((c.1.1.2.ex.world.accounts ⟨64,by decide⟩).code=some 0) &&
          decide ((c.1.1.2.ex.world.accounts ⟨64,by decide⟩).balance.val+7<2^256) then
        let F : Fr := {this:=frame.source.caller,sender:=frame.source.caller,value:=0,static:=false,contract:="EnvironmentCredit",checked:=true,depth:=0,cd:=[]}
        let run := (Source.callAddr (creditGlob G out) F horizon target 0 input false).run c.1.1
        some ((run.1,⟨⟨run.2,c.1.2⟩,c.2⟩),
          ((run.2.2.events.drop c.1.1.2.events.length).map Observation.event))
      else none
    | .staticcall | .delegatecall => none

/-- The selected completed case and its smaller real unfinished prefix. No
existing horizon/test limit is changed. Suffix comes from actual source events;
this template never executes LOG/emit or a callback. -/
def invoke {E} (G : Glob E) (out : Outcome) : Invoke E [] := invokeAt 3 G out
def prefixInvoke {E} (G : Glob E) (out : Outcome) : Invoke E [] := invokeAt 2 G out

def callerInvoke {E Γ} (G : Glob E) (out : Outcome) : Invoke E Γ := CallerFrame.liftInvoke (invoke G out)

theorem precompile_refusal {E} (G : Glob E) out o f (target : Address) gas input (c : Carrier E [])
    (precompile : Roadmap.Address.Precompile target) : invoke G out o f .call target gas input c=none := by
  change (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=true at precompile
  simp only [invoke,invokeAt,precompile,Bool.not_true,Bool.and_false,Bool.false_and,Bool.false_eq_true,if_false]

theorem static_kind_refusal {E} (G : Glob E) out o f target gas input (c : Carrier E []) :
    invoke G out o f .staticcall target gas input c=none := rfl

end Solidity.Yul.World.CreditEnvironment
