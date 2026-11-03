import Solidity.Yul.World.CallbackChecks
import Solidity.Yul.World.ModifierFrame

/-! Typed source-input fixture: a payable fallback with one zero-argument
modifier and real placeholder execution. Not a deployed-program certificate. -/
namespace Solidity.Yul.World.CallbackSuccess
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.Views.Controls
open Solidity.Yul.World.PhysicalCompletion

def fallbackDecl : Decl := ⟨.fallback,"fallback",some "Finite",false,
  .fallback .fbNoParams true (some .payable) .nil false none .none⟩
def modifierDecl : Decl := ⟨.modifier,"worldFrame",some "Finite",false,
  .modifier "worldFrame" (.some .nil) false none .none⟩
def env : Env := ⟨fallbackDecl::modifierDecl::packedTypedEnv.decls⟩

def modifierBody : RBody env := ⟨[],[],true,[],[],.stmt (.placeholder rfl) .nil,[]⟩
def fallbackBody : RBody env := ⟨[],[],false,[],[],.nil,[⟨modifierDecl,[],.nil⟩]⟩

def initial : Source.ExecState env.layout env.lay env.lay := ⟨⟨fun _=>Source.Account.empty _⟩,.empty,[]⟩
def callerExecution := (initial.apply (.account CallerFrameChecks.owner (fun a=>{a with balance:=11,nonce:=1}))).apply
  (.account CallerFrameChecks.receiver (fun a=>{a with balance:=23,nonce:=2,code:=some 0}))
def credited := callerExecution.apply (.account CallerFrameChecks.receiver (fun a=>a.withBalance 30))
def caller : Source.EMState env [.bytes .memory] :=
  ⟨CallerFrameChecks.caller.1,⟨callerExecution,CallerFrameChecks.caller.2.heap,
    CallerFrameChecks.caller.2.events,CallerFrameChecks.caller.2.logs,CallerFrameChecks.caller.2.fnLocals⟩⟩
def observed : ObservedEffects env.layout env.lay env.lay :=
  ⟨⟨caller.2.ex,CallerFrameChecks.observed.effects.logs,CallerFrameChecks.observed.effects.returndata⟩,
    CallerFrameChecks.observed.trace,CallerFrameChecks.observed.logs_eq⟩
def parent := caller.2.ex.enter CallerFrameChecks.owner CallerFrameChecks.sender 0 [] false

def callbackGlob (G : Glob env) (out : Outcome) : Glob env :=
  {CreditEnvironment.creditGlob G out with
    prog:={G.prog with contracts:=["Finite"],body:=fun d=>
      if d.name="fallback" then some fallbackBody else if d.name="worldFrame" then some modifierBody else none}
    callee:=fun history=>match history.getLast? with
      | some (.call a _ _ _) => if a.val=32 then .reenter CallerFrameChecks.receiver CallerFrameChecks.target 7 [] false else .answer (.success [])
      | some (.reentered _) => .answer out
      | _ => .answer (.success [])}

theorem modifier_resolves (G : Glob env) out :
    (callbackGlob G out).prog.body ((callbackGlob G out).dispatchMod "Finite" modifierDecl)=some modifierBody := rfl

theorem modifier_frame (G : Glob env) out (n : Nat) :
    ((Source.runMods (callbackGlob G out) {this:=CallerFrameChecks.receiver,sender:=CallerFrameChecks.target,value:=7,static:=false,contract:="Finite",checked:=true,depth:=2,cd:=[]}
      (n+2) fallbackBody [⟨modifierDecl,[],.nil⟩] (Source.L0 env)).run (Source.L0 env,caller.2)).2.2.fnLocals=caller.2.fnLocals :=
  ModifierFrame.zeroArg_fnLocals _ _ _ _ _ _ _ _ (modifier_resolves G out) rfl

def invokeAt (horizon : Nat) (G : Glob env) (out : Outcome) : Invoke env [] :=
  fun _ frame kind target _ input c=>match kind with
    | .call =>
      if decide (target.val≠0) && !(Roadmap.Evm.Precompile.ofAddress? target.val).isSome &&
          (callbackGlob G out).hasCode c.1.1.2.events target &&
          (frame.source.this == target) && !frame.source.static && decide (frame.source.value.val=0) &&
          (c.1.1.2.ex.world.accounts target).code.isNone &&
          decide ((c.1.1.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0) &&
          decide ((c.1.1.2.ex.world.accounts CallerFrameChecks.receiver).balance.val+7<2^256) then
        let F : Fr := {this:=frame.source.caller,sender:=frame.source.caller,value:=0,static:=false,contract:="ModifierCallback",checked:=true,depth:=0,cd:=[]}
        let run := (Source.callAddr (callbackGlob G out) F horizon target 0 input false).run c.1.1
        some ((run.1,⟨⟨run.2,c.1.2⟩,c.2⟩),(run.2.2.events.drop c.1.1.2.events.length).map Observation.event)
      else none
    | .staticcall | .delegatecall => none

def invoke (G : Glob env) (out : Outcome) : Invoke env [] := invokeAt 10 G out
def prefixInvoke (G : Glob env) (out : Outcome) : Invoke env [] := invokeAt 8 G out

def suffix (out : Outcome) : List Observation :=
  [.event (.call CallerFrameChecks.target 0 [17,34,51,68] false),
   .event (.reenter CallerFrameChecks.receiver CallerFrameChecks.target 7 [] false),
   .event (.reentered (.success [])),.event (.answer out none)]
def events (out : Outcome) : List Roadmap.Event := caller.2.events++
  [.call CallerFrameChecks.target 0 [17,34,51,68] false,
   .reenter CallerFrameChecks.receiver CallerFrameChecks.target 7 [] false,.reentered (.success []),.answer out none]

def after (out : Outcome) : Source.EMState env [.bytes .memory] :=
  ⟨caller.1,{caller.2 with events:=events out,ex:=match out with | .success _=>credited | .revert _=>caller.2.ex}⟩
def result (out : Outcome) : Result env [.bytes .memory] :=
  (⟨⟨after out,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩,
    ⟨⟨(after out).2.ex,committedLogs (observed.trace++suffix out),returnData out⟩,observed.trace++suffix out,rfl⟩)

theorem source_run (G : Glob env) (out : Outcome) :
    (Source.callAddr (callbackGlob G out) {this:=CallerFrameChecks.owner,sender:=CallerFrameChecks.owner,value:=0,static:=false,contract:="ModifierCallback",checked:=true,depth:=0,cd:=[]}
      10 CallerFrameChecks.target 0 [17,34,51,68] false).run (Source.L0 env,caller.2) =
      (.ok out,(Source.L0 env,(after out).2)) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp =>
    cases pipeline <;> cases out with
    | success data => rfl
    | revert data =>
      change ((Except.ok (Outcome.revert data) : Except Halt Outcome),(Source.L0 env,
        {caller.2 with ex:=credited.undo,events:=events (.revert data)})) = _
      rw [show credited.undo=caller.2.ex from Source.ExecState.undo_apply _ _]
      rfl

end Solidity.Yul.World.CallbackSuccess
