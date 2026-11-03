import Solidity.Yul.World.CallerFrameChecks

/-! Actual source reentry into the recognized Finite instance. This concrete
source environment has no fallback/function, so callback dispatch reverts; no
callback LOG/emit is erased by deriving the suffix from actual source events.
This is not a generic callback/deployed-program adequacy certificate. -/
namespace Solidity.Yul.World.Callback
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.Views.Controls
open Solidity.Yul.World.PhysicalCompletion

def callbackGlob (G : Glob packedTypedEnv) (out : Outcome) : Glob packedTypedEnv :=
  {CreditEnvironment.creditGlob G out with callee:=fun history=>match history.getLast? with
    | some (.call a _ _ _) => if a.val=32 then .reenter ⟨64,by decide⟩ ⟨32,by decide⟩ 7 [] false else .answer (.success [])
    | some (.reentered _) => .answer out
    | _ => .answer (.success [])}

theorem codeless_succeeds (G : Glob packedTypedEnv) out history (a : Address) value input static
    (noCode : (callbackGlob G out).hasCode history a=false) :
    (callbackGlob G out).callee (history++[.call a value input static])=.answer (.success []) := by
  have not32 : a.val≠32 := by
    intro eq
    change decide (a.val=32)=false at noCode
    simp only [eq,decide_true] at noCode
    cases noCode
  simp only [callbackGlob,List.getLast?_concat,not32,if_false]

theorem precompile_no_code (G : Glob packedTypedEnv) out history a (precompile : Roadmap.Address.Precompile a) :
    (callbackGlob G out).hasCode history a=false := external_precompile_no_code G out history a precompile

def invokeAt (horizon : Nat) (G : Glob packedTypedEnv) (out : Outcome) : Invoke packedTypedEnv [] :=
  fun _ frame kind target _ input c=>match kind with
    | .call =>
      if decide (target.val≠0) && !(Roadmap.Evm.Precompile.ofAddress? target.val).isSome &&
          (callbackGlob G out).hasCode c.1.1.2.events target &&
          (frame.source.this == target) && !frame.source.static && decide (frame.source.value.val=0) &&
          (c.1.1.2.ex.world.accounts target).code.isNone &&
          decide ((c.1.1.2.ex.world.accounts ⟨64,by decide⟩).code=some 0) &&
          decide ((c.1.1.2.ex.world.accounts ⟨64,by decide⟩).balance.val+7<2^256) then
        let F : Fr := ⟨frame.source.caller,frame.source.caller,0,false,"EnvironmentCallback",true,0⟩
        let run := (Source.callAddr (callbackGlob G out) F horizon target 0 input false).run c.1.1
        some ((run.1,⟨⟨run.2,c.1.2⟩,c.2⟩),(run.2.2.events.drop c.1.1.2.events.length).map Observation.event)
      else none
    | .staticcall | .delegatecall => none

def invoke (G : Glob packedTypedEnv) (out : Outcome) : Invoke packedTypedEnv [] := invokeAt 4 G out
def prefixInvoke (G : Glob packedTypedEnv) (out : Outcome) : Invoke packedTypedEnv [] := invokeAt 3 G out
def callerInvoke {Γ} (G : Glob packedTypedEnv) (out : Outcome) : Invoke packedTypedEnv Γ := CallerFrame.liftInvoke (invoke G out)

theorem precompile_refusal (G : Glob packedTypedEnv) out o f (target : Address) gas input (c : Carrier packedTypedEnv [])
    (precompile : Roadmap.Address.Precompile target) : invokeAt 4 G out o f .call target gas input c=none := by
  change (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=true at precompile
  simp only [invokeAt,precompile,Bool.not_true,Bool.and_false,Bool.false_and,Bool.false_eq_true,if_false]

end Solidity.Yul.World.Callback
