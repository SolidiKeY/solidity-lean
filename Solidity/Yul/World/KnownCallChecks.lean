import Solidity.Yul.World.KnownCall

namespace Solidity.Yul.World.KnownCall
open Solidity.Source
open Solidity.Roadmap (Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.CallbackSuccess (env)

def caller : Source.EMState env [.bytes .memory] :=
  ⟨CallbackSuccess.caller.1,{CallbackSuccess.caller.2 with ex:=entryExecution}⟩
def observed : ObservedEffects env.layout env.lay env.lay :=
  ⟨⟨entryExecution,CallbackSuccess.observed.effects.logs,CallbackSuccess.observed.effects.returndata⟩,
    CallbackSuccess.observed.trace,CallbackSuccess.observed.logs_eq⟩

def parent {Γ} (s : Source.EMState env Γ) := s.2.ex.enter CallerFrameChecks.owner CallerFrameChecks.sender 0 [] false

theorem invoke_empty (G : Glob env) (s : Source.EMState env []) (entry : s.2.ex=entryExecution)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) :
    invoke G o (enter s r (parent s) .call CallerFrameChecks.receiver 7 input)
      .call CallerFrameChecks.receiver 10000 input ⟨⟨s,r⟩,b⟩=
      some ((.ok (.success []),⟨⟨after s,r⟩,b⟩),[]) := by
  rcases s with ⟨l,⟨ex,h,events,logs,fn⟩⟩
  change ex=entryExecution at entry
  subst ex
  let src := (Source.callAddr (glob G) parentFrame 10 CallerFrameChecks.receiver 7 input false).run
    (l,⟨entryExecution,h,events,logs,fn⟩)
  change some ((src.1,(⟨⟨src.2,r⟩,b⟩ : Carrier env [])),(src.2.2.events.drop events.length).map Observation.event)=_
  have ran : src=(.ok (.success []),after (l,⟨entryExecution,h,events,logs,fn⟩)) := source_run G _ rfl
  rw [ran]
  simp only [after,List.drop_length,List.map_nil]

theorem invoke_actual (G : Glob env) {Γ} (s : Source.EMState env Γ) (entry : s.2.ex=entryExecution)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) :
    CallerFrame.liftInvoke (invoke G) o (enter s r (parent s) .call CallerFrameChecks.receiver 7 input)
      .call CallerFrameChecks.receiver 10000 input ⟨⟨s,r⟩,b⟩=
      some ((.ok (.success []),⟨⟨after s,r⟩,b⟩),[]) :=
  CallerFrame.liftInvoke_exact (invoke G) o (enter s r (parent s) .call CallerFrameChecks.receiver 7 input)
    .call CallerFrameChecks.receiver 10000 input ⟨⟨s,r⟩,b⟩ (.ok (.success []))
    ⟨⟨after (⟨Source.L0 env,s.2⟩ : Source.EMState env []),r⟩,b⟩ []
    (invoke_empty G ⟨Source.L0 env,s.2⟩ entry r b o)

def result {Γ} (s : Source.EMState env Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal) (o : ObservedEffects env.layout env.lay env.lay) : Result env Γ :=
  (⟨⟨after s,r⟩,b⟩,⟨⟨moved,committedLogs o.trace,[]⟩,o.trace,rfl⟩)

theorem call_actual (G : Glob env) {Γ} (s : Source.EMState env Γ) (entry : s.2.ex=entryExecution)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex) :
    call (CallerFrame.liftInvoke (invoke G)) s r b o shared PhysicalCompletionChecks.memory (parent s)
      .call CallerFrameChecks.receiver 10000 7 160 4=some (.ok (.success []),result s r b o) := by
  have loaded : PhysicalHeapPort.port.load PhysicalCompletionChecks.memory 160 4=some input := by
    rw [PhysicalHeapPort.load_view _ _ _ (by decide)]
    exact congrArg some (bytesObject_payload_list _ _ _ 128)
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded (invoke_actual G s entry r b o)]
  simp only [finish_success,List.append_nil,result,after]

theorem balances_and_eligibility :
    (moved.world.accounts CallerFrameChecks.owner).balance=4 ∧
    (moved.world.accounts CallerFrameChecks.receiver).balance=30 ∧ moved.journal.length=5 ∧
    (moved.world.accounts CallerFrameChecks.receiver).code=some 0 ∧
    (moved.world.accounts CallerFrameChecks.receiver).nonce=2 ∧
    (moved.world.accounts CallerFrameChecks.owner).nonce=1 := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem concrete (G : Glob env) : call (CallerFrame.liftInvoke (invoke G)) caller CallerFrameChecks.residual
    CallerFrameChecks.encoding observed rfl PhysicalCompletionChecks.memory (parent caller)
    .call CallerFrameChecks.receiver 10000 7 160 4=
    some (.ok (.success []),result caller CallerFrameChecks.residual CallerFrameChecks.encoding observed) :=
  call_actual G caller rfl _ _ _ rfl

theorem whole_frame {Γ} (s : Source.EMState env Γ) r b o :
    (result s r b o).1.1.1.1=s.1 ∧ (result s r b o).1.1.1.2.heap=s.2.heap ∧
    (result s r b o).1.1.1.2.fnLocals=s.2.fnLocals ∧ (result s r b o).1.1.1.2.events=s.2.events ∧
    (result s r b o).1.1.1.2.logs=s.2.logs ∧ (result s r b o).1.1.2=r ∧ (result s r b o).1.2=b ∧
    (result s r b o).2.trace=o.trace ∧ (result s r b o).2.effects.returndata=[] :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem source_insufficient (G : Glob env) :
    (Source.callAddr (glob G) parentFrame 10 CallerFrameChecks.receiver 12 input false).run (Source.L0 env,caller.2)=
      (.ok (.revert []),(Source.L0 env,caller.2)) := rfl

theorem source_static_value (G : Glob env) :
    (Source.callAddr (glob G) {parentFrame with static:=true} 10 CallerFrameChecks.receiver 7 input false).run (Source.L0 env,caller.2)=
      (.error (.revert []),(Source.L0 env,caller.2)) := rfl

theorem source_depth (G : Glob env) :
    (Source.callAddr (glob G) {parentFrame with depth:=1024} 10 CallerFrameChecks.receiver 7 input false).run (Source.L0 env,caller.2)=
      (.ok (.revert []),(Source.L0 env,caller.2)) := rfl

theorem source_zero_horizon (G : Glob env) :
    (Source.callAddr (glob G) parentFrame 0 CallerFrameChecks.receiver 7 input false).run (Source.L0 env,caller.2)=
      (.error .timeout,(Source.L0 env,caller.2)) := rfl

theorem child_context {Γ} (s : Source.EMState env Γ) r :
    PhysicalSlotPort.sourceFrame (enter s r (parent s) .call CallerFrameChecks.receiver 7 input).source "Finite" true 1=
      ({this:=CallerFrameChecks.receiver,sender:=CallerFrameChecks.owner,value:=7,static:=false,contract:="Finite",checked:=true,depth:=1,cd:=input} : Fr) ∧
    (enter s r (parent s) .call CallerFrameChecks.receiver 7 input).source.mark=s.2.ex.journal.length ∧
    (enter s r (parent s) .call CallerFrameChecks.receiver 7 input).mark=r.journal.length := ⟨rfl,rfl,rfl⟩

theorem prefix_empty (G : Glob env) (s : Source.EMState env []) (entry : s.2.ex=entryExecution)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) :
    prefixInvoke G o (enter s r (parent s) .call CallerFrameChecks.receiver 7 input)
      .call CallerFrameChecks.receiver 10000 input ⟨⟨s,r⟩,b⟩=
      some ((.error .timeout,⟨⟨after s,r⟩,b⟩),[]) := by
  rcases s with ⟨l,⟨ex,h,events,logs,fn⟩⟩
  change ex=entryExecution at entry
  subst ex
  let src := (Source.callAddr (glob G) parentFrame 6 CallerFrameChecks.receiver 7 input false).run
    (l,⟨entryExecution,h,events,logs,fn⟩)
  change some ((src.1,(⟨⟨src.2,r⟩,b⟩ : Carrier env [])),(src.2.2.events.drop events.length).map Observation.event)=_
  have ran : src=(.error .timeout,after (l,⟨entryExecution,h,events,logs,fn⟩)) := source_timeout G _ rfl
  rw [ran]
  simp only [after,List.drop_length,List.map_nil]

theorem prefix_call (G : Glob env) :
    call (CallerFrame.liftInvoke (prefixInvoke G)) caller CallerFrameChecks.residual CallerFrameChecks.encoding
      observed rfl PhysicalCompletionChecks.memory (parent caller) .call CallerFrameChecks.receiver 10000 7 160 4=
      some (.error .timeout,pending observed ⟨⟨after caller,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ []) := by
  have loaded : PhysicalHeapPort.port.load PhysicalCompletionChecks.memory 160 4=some input := by
    rw [PhysicalHeapPort.load_view _ _ _ (by decide)]
    exact congrArg some (bytesObject_payload_list _ _ _ 128)
  have ran := CallerFrame.liftInvoke_exact (prefixInvoke G) observed
    (enter caller CallerFrameChecks.residual (parent caller) .call CallerFrameChecks.receiver 7 input)
    .call CallerFrameChecks.receiver 10000 input ⟨⟨caller,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩
    (.error .timeout) ⟨⟨after (⟨Source.L0 env,caller.2⟩ : Source.EMState env []),CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ []
    (prefix_empty G ⟨Source.L0 env,caller.2⟩ rfl _ _ observed)
  exact call_exact _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded ran

def poorExecution := entryExecution.apply (.account CallerFrameChecks.owner (fun a=>a.withBalance 6))
def poorCaller : Source.EMState env [.bytes .memory] := ⟨caller.1,{caller.2 with ex:=poorExecution}⟩
def poorObserved : ObservedEffects env.layout env.lay env.lay :=
  ⟨⟨poorExecution,observed.effects.logs,observed.effects.returndata⟩,observed.trace,observed.logs_eq⟩

theorem poor_source (G : Glob env) :
    (Source.callAddr (glob G) parentFrame 10 CallerFrameChecks.receiver 7 input false).run (Source.L0 env,poorCaller.2)=
      (.ok (.revert []),(Source.L0 env,poorCaller.2)) := rfl

theorem poor_invoke (G : Glob env) : CallerFrame.liftInvoke (invoke G) poorObserved
    (enter poorCaller CallerFrameChecks.residual (parent poorCaller) .call CallerFrameChecks.receiver 7 input)
    .call CallerFrameChecks.receiver 10000 input ⟨⟨poorCaller,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=
      some ((.ok (.revert []),⟨⟨poorCaller,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩),[]) := rfl

theorem poor_call (G : Glob env) :
    call (CallerFrame.liftInvoke (invoke G)) poorCaller CallerFrameChecks.residual CallerFrameChecks.encoding poorObserved rfl
      PhysicalCompletionChecks.memory (parent poorCaller) .call CallerFrameChecks.receiver 10000 7 160 4=
      some (.ok (.revert []),(⟨⟨poorCaller,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩,
        ⟨⟨poorExecution,committedLogs poorObserved.trace,[]⟩,poorObserved.trace,rfl⟩)) := by
  have loaded : PhysicalHeapPort.port.load PhysicalCompletionChecks.memory 160 4=some input := by
    rw [PhysicalHeapPort.load_view _ _ _ (by decide)]
    exact congrArg some (bytesObject_payload_list _ _ _ 128)
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded (poor_invoke G)]
  rfl

def unregisteredExecution := entryExecution.apply (.account CallerFrameChecks.receiver (fun a=>{a with code:=none}))
def unregistered : Source.EMState env [] := ⟨Source.L0 env,{caller.2 with ex:=unregisteredExecution}⟩
def debited := unregisteredExecution.apply (.account CallerFrameChecks.owner (fun a=>a.withBalance 4))

theorem unregistered_source (G : Glob env) :
    (Source.callAddr (glob G) parentFrame 10 CallerFrameChecks.receiver 7 input false).run unregistered=
      (.ok (.success []),(Source.L0 env,{unregistered.2 with ex:=debited,events:=unregistered.2.events++
        [.call CallerFrameChecks.receiver 7 input false,.answer (.success []) none]})) := rfl

theorem unregistered_refusal (G : Glob env) : invoke G observed
    (enter unregistered CallerFrameChecks.residual (parent unregistered) .call CallerFrameChecks.receiver 7 input)
    .call CallerFrameChecks.receiver 10000 input ⟨⟨unregistered,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=none := rfl

theorem static_refusal (G : Glob env) : invoke G observed
    (enter caller CallerFrameChecks.residual (parent caller) .staticcall CallerFrameChecks.receiver 7 input)
    .staticcall CallerFrameChecks.receiver 10000 input ⟨⟨⟨Source.L0 env,caller.2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=none := rfl

theorem wrong_context (G : Glob env) : invoke G observed
    (enter caller CallerFrameChecks.residual {parent caller with this:=CallerFrameChecks.target} .call CallerFrameChecks.receiver 7 input)
    .call CallerFrameChecks.receiver 10000 input ⟨⟨⟨Source.L0 env,caller.2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=none := rfl

theorem caller_eligible (G : Glob env) :
    (Source.instanceAt (glob G) CallerFrameChecks.owner).run (Source.L0 env,caller.2)=
      (.ok (some "Finite"),(Source.L0 env,caller.2)) := rfl

theorem output_empty : copyOutput (result caller CallerFrameChecks.residual CallerFrameChecks.encoding observed) rfl
    PhysicalCompletionChecks.placement 0 false [17,34,51,68] rfl PhysicalCompletionChecks.memory 1 2=
      (result caller CallerFrameChecks.residual CallerFrameChecks.encoding observed,
        some ((PhysicalCompletionChecks.memory,after caller),(CallerFrameChecks.residual,CallerFrameChecks.encoding),
          (result caller CallerFrameChecks.residual CallerFrameChecks.encoding observed).2)) := by
  exact empty_output _ rfl _ 0 false [17,34,51,68] rfl _ 1 2 rfl (by decide)
    (congrArg Fin.val (bytesObject_header _ _ _ 128)) (bytesObject_payload_list _ _ _ 128)

theorem invalid_zero_source : copyAfter (result caller CallerFrameChecks.residual CallerFrameChecks.encoding observed) rfl
    PhysicalCompletionChecks.placement 0 false [17,34,51,68] rfl PhysicalCompletionChecks.memory 1 1 0=
      (result caller CallerFrameChecks.residual CallerFrameChecks.encoding observed,none) :=
  copyAfter_bad_source _ rfl _ 0 false [17,34,51,68] rfl _ 1 1 0 (by decide)

theorem owner_memOK : Source.MemOK env PhysicalCompletionChecks.heap.ty (after caller) :=
by
  have ok := CallbackSuccess.owner_MemOK (.success [])
  exact ⟨⟨⟨ok.1.1.heap,ok.1.1.le⟩,ok.1.2⟩,ok.2.1,ok.2.2⟩

theorem source_input_aliases :
    (Source.bytesOfRV (E:=env) parentFrame 1 (.val (caller.1.get .here))).run caller=(.ok input,caller) ∧
    (Source.bytesOfRV (E:=env) parentFrame 1 (.val ((after caller).2.fnLocals.2.get .here))).run (after caller)=
      (.ok input,after caller) := ⟨rfl,rfl⟩

theorem full_prefix_control : observed.trace≠[] ∧ observed.effects.logs≠[] ∧ caller.2.fnLocals.1=[.bytes .memory] ∧
    entryExecution.journal.length=3 ∧ CallerFrameChecks.residual.journal.length=1 ∧
    CallerFrameChecks.encoding.journal.length=1 := ⟨by decide,by decide,rfl,rfl,rfl,rfl⟩

theorem dirty_timeout_buffer :
    (pending observed ⟨⟨after caller,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ []).2.effects.returndata=[9,8,7,6] ∧
    (result caller CallerFrameChecks.residual CallerFrameChecks.encoding observed).2.effects.returndata=[] ∧
    moved.journal.length=5 := ⟨rfl,rfl,rfl⟩

end Solidity.Yul.World.KnownCall
