import Solidity.Yul.World.PhysicalSlotPort
import Solidity.Yul.World.HeapWindowFrame

/-! Completion over the real physical carriers, never FrameAnswer.operations.
The supplied outcome/trace is a frame boundary, not a reachability certificate.
Source rollback uses its existing rollbackTo (including its actual heap policy).
Stuck/timeout are propagated by finishStep, never recoded as EVM failure. -/
namespace Solidity.Yul.World.PhysicalCompletion
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open Solidity.Yul.Views

abbrev Carrier (E : Env) (Γ : RCtx) :=
  (EMState E Γ × ResidualJournal complementCarrierOwnership) × BoolEncodingJournal

abbrev Result (E : Env) (Γ : RCtx) := Carrier E Γ × ObservedEffects E.layout E.lay E.lay

def enter {E Γ} (s : EMState E Γ) (r : ResidualJournal complementCarrierOwnership)
    (parent : CallFrame) (kind : CallKind) (callee : Address) (value : Word) (input : Bytes) : ResidualFrame :=
  ⟨childContext s.2.ex parent kind callee value input,r.journal.length⟩

def finish {E Γ} (entry : EMState E Γ) (before : BoolEncodingJournal)
    (observed : ObservedEffects E.layout E.lay E.lay) (frame : ResidualFrame)
    (current : Carrier E Γ) (suffix : List Observation) (outcome : Outcome) : Result E Γ :=
  let physical : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership := ⟨current.1.1.2.ex,current.1.2⟩
  let after := match outcome with
    | .success _ => companionCommit frame physical
    | .revert _ => companionRollback frame physical
  let source := match outcome with
    | .success _ => current.1.1
    | .revert _ => (Source.rollbackTo (frame.source.mark,entry.2.logs.length,entry.2.heap)).run current.1.1 |>.2
  let state : EMState E Γ := ⟨source.1,{source.2 with ex:=after.source}⟩
  let encoding := match outcome with
    | .success _ => current.2
    | .revert _ => boolEncodingRollback before.journal.length current.2
  let trace := match outcome with
    | .success _ => observed.trace ++ suffix
    | .revert _ => rollbackTrace observed.trace suffix
  (⟨⟨state,after.residual⟩,encoding⟩,⟨⟨state.2.ex,committedLogs trace,returnData outcome⟩,trace,rfl⟩)

/-- Pending state on a non-revert source halt, including all observations
and physical journals. It is not an EVM completion or committed outcome. -/
def pending {E Γ} (observed : ObservedEffects E.layout E.lay E.lay)
    (current : Carrier E Γ) (suffix : List Observation) : Result E Γ :=
  (current,⟨⟨current.1.1.2.ex,committedLogs (observed.trace++suffix),observed.effects.returndata⟩,
    observed.trace++suffix,rfl⟩)

/-- Source-style state-on-halt result. Non-revert errors never erase the full
carrier or pending trace, and are never reclassified as EVM reverts. -/
def finishStep {E Γ} (entry : EMState E Γ) (before : BoolEncodingJournal)
    (observed : ObservedEffects E.layout E.lay E.lay) (frame : ResidualFrame)
    (step : ((Except Halt Unit × EMState E Γ) × ResidualJournal complementCarrierOwnership) × BoolEncodingJournal)
    (suffix : List Observation) (outcome : Outcome) : Except Halt Outcome × Result E Γ :=
  let current : Carrier E Γ := ⟨⟨step.1.1.2,step.1.2⟩,step.2⟩
  match step.1.1.1 with
  | .ok _ => (.ok outcome,finish entry before observed frame current suffix outcome)
  | .error (.revert data) => (.ok (.revert data),finish entry before observed frame current suffix (.revert data))
  | .error other => (.error other,pending observed current suffix)

theorem finish_shared {E Γ} (s : EMState E Γ) b o f (c : Carrier E Γ) xs out :
    (finish s b o f c xs out).2.effects.execution = (finish s b o f c xs out).1.1.1.2.ex := rfl

theorem finish_data {E Γ} (s : EMState E Γ) b o f (c : Carrier E Γ) xs out :
    (finish s b o f c xs out).2.effects.returndata = returnData out := rfl

theorem finish_success {E Γ} (s : EMState E Γ) b o f (c : Carrier E Γ) xs data :
    finish s b o f c xs (.success data) =
      (c,⟨⟨c.1.1.2.ex,committedLogs (o.trace++xs),data⟩,o.trace++xs,rfl⟩) := by
  cases c with | mk c enc => cases c with | mk state residual => cases state; rfl

theorem finish_revert_trace {E Γ} (s : EMState E Γ) b o f (c : Carrier E Γ) xs data :
    (finish s b o f c xs (.revert data)).2.trace = rollbackTrace o.trace xs ∧
    (finish s b o f c xs (.revert data)).2.effects.logs = o.effects.logs := by
  exact ⟨rfl,(rollback_logs o.trace xs).trans o.logs_eq⟩

/-- Actual Source rollback retains events/locals/heap/function locals; it only
undoes execution and drops newest-first legacy logs to the recorded length. -/
theorem finish_revert_source {E Γ} (s : EMState E Γ) b o f (c : Carrier E Γ) xs data :
    let result := finish s b o f c xs (.revert data)
    result.1.1.1.1=c.1.1.1 ∧ result.1.1.1.2.heap=c.1.1.2.heap ∧
    result.1.1.1.2.events=c.1.1.2.events ∧ result.1.1.1.2.fnLocals=c.1.1.2.fnLocals ∧
    result.1.1.1.2.logs=c.1.1.2.logs.drop (c.1.1.2.logs.length-s.2.logs.length) := ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Concrete physical slot entry/step/completion. No arbitrary operation list. -/
def slot {E Γ ps ts q before} (F : Fr) (p : RepresentedSlotPlan ps ts q before)
    (s : EMState E Γ) (r : ResidualJournal complementCarrierOwnership)
    (o : ObservedEffects E.layout E.lay E.lay) (same : o.effects.execution=s.2.ex)
    (owner : q.address=F.this) (suffix : List Observation) (outcome : Outcome) :=
  let result := PhysicalSlotPort.step ps ts q before F p s r o same owner
  finishStep s before o (companionEnter ⟨s.2.ex,r⟩ F.this F.sender F.value [] F.static)
    result.1 (match result.1.1.1.1 with | .ok _ => suffix | .error _ => []) outcome

/-- General three-journal rollback law, instantiated below with the actual
represented action bodies. This is a proved run identity, not a callee law. -/
theorem finish_runs_revert {E Γ} (s : EMState E Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal) (o : ObservedEffects E.layout E.lay E.lay)
    (os : List (Source.Op E.layout E.lay E.lay)) (ws : List (ResidualKey complementCarrierOwnership × Word))
    (bs : List (OwnedByteKey × BoolTrueByte)) (a c : Address) (v : Word) (input : Bytes) (st : Bool)
    (xs : List Observation) (data : Bytes) :
    finish s b o (companionEnter ⟨s.2.ex,r⟩ a c v input st)
      ⟨⟨(s.1,{s.2 with ex:=s.2.ex.run os}),residualRun r ws⟩,boolEncodingRun b bs⟩ xs (.revert data) =
      (⟨⟨s,r⟩,b⟩,⟨⟨s.2.ex,committedLogs (rollbackTrace o.trace xs),data⟩,rollbackTrace o.trace xs,rfl⟩) := by
  have back := companionRollback_run (⟨s.2.ex,r⟩ : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership)
    os ws a c v input st
  change companionRollback _ ⟨s.2.ex.run os,residualRun r ws⟩ = _ at back
  simp only [finish,back,boolEncodingRollback_run]
  cases s with
  | mk l state =>
    cases state with
    | mk ex heap events logs fn =>
      change ((((l,(⟨ex,heap,events,logs.drop (logs.length-logs.length),fn⟩ : Source.St E)),r),b),_) = _
      simp only [Nat.sub_self,List.drop_zero,returnData]

theorem slot_revert {E Γ ps ts q before} (F : Fr) (p : RepresentedSlotPlan ps ts q before)
    (s : EMState E Γ) (r : ResidualJournal complementCarrierOwnership)
    (o : ObservedEffects E.layout E.lay E.lay) (same : o.effects.execution=s.2.ex)
    (owner : q.address=F.this) (xs : List Observation) (data : Bytes) (nonstatic : F.static=false) :
    slot F p s r o same owner xs (.revert data) =
      (.ok (.revert data),(⟨⟨s,r⟩,before⟩,
        ⟨⟨s.2.ex,committedLogs (rollbackTrace o.trace xs),data⟩,rollbackTrace o.trace xs,rfl⟩)) := by
  unfold slot PhysicalSlotPort.step
  rw [representedSourceStep_nonstatic F p s r nonstatic]
  change ((Except.ok (Outcome.revert data) : Except Halt Outcome),finish s before o _ _ xs (.revert data)) = _
  rw [show s.2.ex.apply p.packed.sourceOp = s.2.ex.run [p.packed.sourceOp] from rfl]
  simpa only [requestEncoding,residualRun] using
    congrArg (fun x : Result E Γ => ((Except.ok (Outcome.revert data) : Except Halt Outcome),x))
      (finish_runs_revert s r before o [p.packed.sourceOp] [p.packed.residualUpdate]
        (encodingWrites (selectedSlotPaths (if q.transient then ts q.address else ps q.address) q.slot)
          q.transient q.address (fun _ => q.raw) before) F.this F.sender F.value [] F.static xs data)

theorem slot_success {E Γ ps ts q before} (F : Fr) (p : RepresentedSlotPlan ps ts q before)
    (s : EMState E Γ) (r : ResidualJournal complementCarrierOwnership)
    (o : ObservedEffects E.layout E.lay E.lay) (same : o.effects.execution=s.2.ex)
    (owner : q.address=F.this) (xs : List Observation) (data : Bytes) (nonstatic : F.static=false) :
    let physical := PhysicalSlotPort.step ps ts q before F p s r o same owner
    slot F p s r o same owner xs (.success data) =
      (.ok (.success data),(⟨⟨physical.1.1.1.2,physical.1.1.2⟩,physical.1.2⟩,
        ⟨⟨physical.2.effects.execution,committedLogs (o.trace++xs),data⟩,o.trace++xs,rfl⟩)) := by
  unfold slot PhysicalSlotPort.step
  rw [representedSourceStep_nonstatic F p s r nonstatic]
  change (Except.ok (Outcome.success data),finish s before o _ _ xs (.success data)) = _
  rw [finish_success]

theorem slot_static {E Γ ps ts q before} (F : Fr) (p : RepresentedSlotPlan ps ts q before)
    (s : EMState E Γ) (r : ResidualJournal complementCarrierOwnership)
    (o : ObservedEffects E.layout E.lay E.lay) (same : o.effects.execution=s.2.ex)
    (owner : q.address=F.this) (xs : List Observation) (out : Outcome) (static : F.static=true) :
    slot F p s r o same owner xs out =
      (.ok (.revert []),(⟨⟨s,r⟩,before⟩,⟨⟨s.2.ex,committedLogs o.trace,[]⟩,o.trace,rfl⟩)) := by
  unfold slot PhysicalSlotPort.step
  rw [representedSourceStep_static F p s r static]
  change (Except.ok (Outcome.revert []),finish s before o _ ⟨⟨s,r⟩,before⟩ [] (.revert [])) = _
  have restore := finish_runs_revert s r before o [] [] [] F.this F.sender F.value [] F.static [] []
  simpa only [ExecState.run,residualRun,boolEncodingRun,rollbackTrace,discardLogs,List.append_nil] using
    congrArg (fun x : Result E Γ => ((Except.ok (Outcome.revert []) : Except Halt Outcome),x)) restore

end Solidity.Yul.World.PhysicalCompletion
