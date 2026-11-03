import Solidity.Yul.World.KnownCallChecks

/-! Selected source-backed STATICCALL; zero-value source transfer can record
no-op journal entries. World equality is distinct from journal equality. -/
namespace Solidity.Yul.World.KnownStatic
open Solidity.Source
open Solidity.Roadmap (Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.KnownCall (glob parentFrame entryExecution input caller observed parent)
open Solidity.Yul.World.CallbackSuccess (env)

def zeroMoved := (entryExecution.apply (.account CallerFrameChecks.owner (fun a=>a.withBalance 11))).apply
  (.account CallerFrameChecks.receiver (fun a=>a.withBalance 23))
def after {Γ} (s : Source.EMState env Γ) : Source.EMState env Γ := ⟨s.1,{s.2 with ex:=zeroMoved}⟩

theorem source_run (G : Glob env) (s : Source.EMState env []) (entry : s.2.ex=entryExecution) :
    (Source.callAddr (glob G) parentFrame 10 CallerFrameChecks.receiver 0 input true).run s=
      (.ok (.success []),after s) := by
  rcases s with ⟨l,⟨ex,h,events,logs,fn⟩⟩
  change ex=entryExecution at entry
  subst ex
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

def invokeAt (horizon : Nat) (G : Glob env) : Invoke env [] :=
  fun _ frame kind target _ bytes c=>match kind with
    | .staticcall =>
      if decide (target=CallerFrameChecks.receiver) &&
          !(Roadmap.Evm.Precompile.ofAddress? target.val).isSome &&
          decide (frame.source.this=target) && decide (frame.source.caller=CallerFrameChecks.owner) &&
          decide (frame.source.value.val=0) && frame.source.static &&
          decide ((c.1.1.2.ex.world.accounts target).code=some 0) then
        let run := (Source.callAddr (glob G) parentFrame horizon target 0 bytes true).run c.1.1
        some ((run.1,⟨⟨run.2,c.1.2⟩,c.2⟩),(run.2.2.events.drop c.1.1.2.events.length).map Observation.event)
      else none
    | .call | .delegatecall => none

def invoke (G : Glob env) : Invoke env [] := invokeAt 10 G

theorem invoke_empty (G : Glob env) (s : Source.EMState env []) (entry : s.2.ex=entryExecution)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) :
    invoke G o (enter s r (parent s) .staticcall CallerFrameChecks.receiver 0 input)
      .staticcall CallerFrameChecks.receiver 10000 input ⟨⟨s,r⟩,b⟩=
      some ((.ok (.success []),⟨⟨after s,r⟩,b⟩),[]) := by
  rcases s with ⟨l,⟨ex,h,events,logs,fn⟩⟩
  change ex=entryExecution at entry
  subst ex
  let src := (Source.callAddr (glob G) parentFrame 10 CallerFrameChecks.receiver 0 input true).run
    (l,⟨entryExecution,h,events,logs,fn⟩)
  change some ((src.1,(⟨⟨src.2,r⟩,b⟩ : Carrier env [])),(src.2.2.events.drop events.length).map Observation.event)=_
  have ran : src=(.ok (.success []),after (l,⟨entryExecution,h,events,logs,fn⟩)) := source_run G _ rfl
  rw [ran]
  simp only [after,List.drop_length,List.map_nil]

theorem invoke_actual (G : Glob env) {Γ} (s : Source.EMState env Γ) (entry : s.2.ex=entryExecution)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) :
    CallerFrame.liftInvoke (invoke G) o (enter s r (parent s) .staticcall CallerFrameChecks.receiver 0 input)
      .staticcall CallerFrameChecks.receiver 10000 input ⟨⟨s,r⟩,b⟩=
      some ((.ok (.success []),⟨⟨after s,r⟩,b⟩),[]) :=
  CallerFrame.liftInvoke_exact (invoke G) o (enter s r (parent s) .staticcall CallerFrameChecks.receiver 0 input)
    .staticcall CallerFrameChecks.receiver 10000 input ⟨⟨s,r⟩,b⟩ (.ok (.success []))
    ⟨⟨after (⟨Source.L0 env,s.2⟩ : Source.EMState env []),r⟩,b⟩ [] (invoke_empty G ⟨Source.L0 env,s.2⟩ entry r b o)

def result {Γ} (s : Source.EMState env Γ) (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal) (o : ObservedEffects env.layout env.lay env.lay) : Result env Γ :=
  (⟨⟨after s,r⟩,b⟩,⟨⟨zeroMoved,committedLogs o.trace,[]⟩,o.trace,rfl⟩)

theorem call_actual (G : Glob env) {Γ} (s : Source.EMState env Γ) (entry : s.2.ex=entryExecution)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex) :
    call (CallerFrame.liftInvoke (invoke G)) s r b o shared PhysicalCompletionChecks.memory (parent s)
      .staticcall CallerFrameChecks.receiver 10000 0 160 4=some (.ok (.success []),result s r b o) := by
  have loaded : PhysicalHeapPort.port.load PhysicalCompletionChecks.memory 160 4=some input := by
    rw [PhysicalHeapPort.load_view _ _ _ (by decide)]
    exact congrArg some (bytesObject_payload_list _ _ _ 128)
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded (invoke_actual G s entry r b o)]
  simp only [finish_success,List.append_nil,result,after]

theorem world_unchanged : zeroMoved.world=entryExecution.world := by
  apply congrArg Source.World.mk
  funext a
  by_cases receiver : a=CallerFrameChecks.receiver
  · subst a; rfl
  by_cases owner : a=CallerFrameChecks.owner
  · subst a; rfl
  change ((entryExecution.world.set CallerFrameChecks.owner
    ((entryExecution.world.accounts CallerFrameChecks.owner).withBalance 11)).set CallerFrameChecks.receiver
    (((entryExecution.world.set CallerFrameChecks.owner
      ((entryExecution.world.accounts CallerFrameChecks.owner).withBalance 11)).accounts CallerFrameChecks.receiver).withBalance 23)).accounts a=
    entryExecution.world.accounts a
  rw [Source.World.set_other _ receiver,Source.World.set_other _ owner]

theorem journal_not_unchanged : zeroMoved.journal.length=5 ∧ entryExecution.journal.length=3 ∧
    zeroMoved.journal≠entryExecution.journal := by
  refine ⟨rfl,rfl,?_⟩
  intro same
  have impossible : (5 : Nat)=3 := congrArg List.length same
  contradiction

theorem child_context {Γ} (s : Source.EMState env Γ) r :
    PhysicalSlotPort.sourceFrame (enter s r (parent s) .staticcall CallerFrameChecks.receiver 0 input).source "Finite" true 1=
      (⟨CallerFrameChecks.receiver,CallerFrameChecks.owner,0,true,"Finite",true,1⟩ : Fr) := rfl

theorem nested_static_source (G : Glob env) :
    (Source.callAddr (glob G) {parentFrame with static:=true} 10 CallerFrameChecks.receiver 0 input true).run
      (Source.L0 env,caller.2)=(.ok (.success []),(Source.L0 env,(after caller).2)) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem concrete (G : Glob env) :
    call (CallerFrame.liftInvoke (invoke G)) caller CallerFrameChecks.residual CallerFrameChecks.encoding observed rfl
      PhysicalCompletionChecks.memory (parent caller) .staticcall CallerFrameChecks.receiver 10000 0 160 4=
      some (.ok (.success []),result caller CallerFrameChecks.residual CallerFrameChecks.encoding observed) :=
  call_actual G caller rfl _ _ _ rfl

theorem whole_frame {Γ} (s : Source.EMState env Γ) r b o :
    (result s r b o).1.1.1.1=s.1 ∧ (result s r b o).1.1.1.2.heap=s.2.heap ∧
    (result s r b o).1.1.1.2.fnLocals=s.2.fnLocals ∧ (result s r b o).1.1.1.2.events=s.2.events ∧
    (result s r b o).1.1.1.2.logs=s.2.logs ∧ (result s r b o).1.1.2=r ∧ (result s r b o).1.2=b ∧
    (result s r b o).2.trace=o.trace ∧ (result s r b o).2.effects.returndata=[] :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem wrong_context_refusal (G : Glob env) : invoke G observed
    (enter caller CallerFrameChecks.residual {parent caller with this:=CallerFrameChecks.target} .staticcall CallerFrameChecks.receiver 0 input)
    .staticcall CallerFrameChecks.receiver 10000 input ⟨⟨⟨Source.L0 env,caller.2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=none := rfl

theorem nonstatic_frame_refusal (G : Glob env) : invoke G observed
    (enter caller CallerFrameChecks.residual (parent caller) .call CallerFrameChecks.receiver 0 input)
    .staticcall CallerFrameChecks.receiver 10000 input ⟨⟨⟨Source.L0 env,caller.2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=none := rfl

theorem unregistered_refusal (G : Glob env) : invoke G observed
    (enter KnownCall.unregistered CallerFrameChecks.residual (parent KnownCall.unregistered) .staticcall CallerFrameChecks.receiver 0 input)
    .staticcall CallerFrameChecks.receiver 10000 input ⟨⟨KnownCall.unregistered,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=none := rfl

end Solidity.Yul.World.KnownStatic
