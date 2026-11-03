import Solidity.Yul.World.ScalarLocalEmit

/-! Actual indexed uint256 local selection and the owned full-log extension.
The supplied evaluated local vector and the outer caller frame stay distinct. -/
namespace Solidity.Yul.World.IndexedEmitPort
open Solidity.Source
open Solidity.Yul.Views
open Solidity.Roadmap (Bytes)
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.ScalarEmitPort (env eventDecl frame signature)

def selected {D Γ} (l : Locals D Γ) (i : Source.Idx Γ ReturningCall.uint) : Int :=
  match l.get i with | .int v _ => v

def args (indexed anonymous : Bool) {Γ : RCtx} (i : Source.Idx Γ ReturningCall.uint) :
    RConvArgs (env indexed anonymous) Γ [ReturningCall.uint] :=
  .cons (.local i) (by cases indexed <;> cases anonymous <;> decide) .nil

def statement (indexed anonymous : Bool) {Γ : RCtx} (i : Source.Idx Γ ReturningCall.uint) :
    RStmt (env indexed anonymous) [] false ⟨false,false⟩ Γ Γ :=
  .emit (eventDecl indexed anonymous) rfl (args indexed anonymous i)

theorem args_run {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (static : Bool) (st : St (env indexed anonymous)) :
    (Source.evalConvArgs G (frame static) 4 (args indexed anonymous i)).run ⟨l,st⟩=
      (.ok (.cons (l.get i) .nil),⟨l,st⟩) := rfl

theorem actual_at {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (st : St (env indexed anonymous)) :
    (Source.execS G (frame false) 5 0 none (statement indexed anonymous i) l).run ⟨Source.L0 (env indexed anonymous),st⟩=
      (.ok (.normal l),ScalarLocalEmit.after G (selected l i) ⟨Source.L0 (env indexed anonymous),st⟩) := by
  simp only [Source.execS,statement,Source.Hoare.run_bind,Source.run_sub]
  rw [args_run]
  simp only [selected]
  generalize h : l.get i=x
  cases x with
  | int v bound =>
    change ((.ok (.normal l) : Except Source.Halt (Source.Out (env indexed anonymous).layout Γ Γ)),
      (Source.L0 (env indexed anonymous),{st with logs:=(CallerFrameChecks.owner,
        G.selector (signature indexed anonymous)++((ScalarLocalEmit.data v++[])++[]))::st.logs}))=_
    simp only [List.append_nil]
    rfl

  | memRef bad _ => cases bad
  | storRef bad _ => cases bad
  | cdRef bad _ => cases bad

theorem actual_static {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (st : St (env indexed anonymous)) :
    (Source.execS G (frame true) 5 0 none (statement indexed anonymous i) l).run ⟨Source.L0 (env indexed anonymous),st⟩=
      (.error (.revert []),⟨Source.L0 (env indexed anonymous),st⟩) := by
  simp only [Source.execS,statement,Source.Hoare.run_bind,Source.run_sub]
  rw [args_run]
  generalize h : l.get i=x
  cases x with
  | int v bound => rfl
  | memRef bad _ => cases bad
  | storRef bad _ => cases bad
  | cdRef bad _ => cases bad

def source {indexed anonymous Γ Δ} (G : Glob (env indexed anonymous)) (static : Bool)
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (s : EMState (env indexed anonymous) Δ) :=
  (Source.EM.sub (Source.L0 (env indexed anonymous)) (Source.execS G (frame static) 5 0 none
    (statement indexed anonymous i) l)).run s

theorem source_run {indexed anonymous Γ Δ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (s : EMState (env indexed anonymous) Δ) :
    source G false l i s=(.ok (.normal l,Source.L0 (env indexed anonymous)),ScalarLocalEmit.after G (selected l i) s) := by
  unfold source
  rw [Source.run_sub,actual_at]
  rfl

theorem source_static {indexed anonymous Γ Δ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (s : EMState (env indexed anonymous) Δ) : source G true l i s=(.error (.revert []),s) := by
  unfold source
  rw [Source.run_sub,actual_static]

def encoding {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint) : Log :=
  ScalarLocalEmit.encoding G (selected l i)

def execute {indexed anonymous Γ Δ} (G : Glob (env indexed anonymous)) (static : Bool)
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (s : EMState (env indexed anonymous) Δ) (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (_shared : o.effects.execution=s.2.ex) :=
  let actual:=source G static l i s
  ((actual.1.map (fun _=>()),(⟨⟨actual.2,r⟩,b⟩ : Carrier (env indexed anonymous) Δ)),
    match actual.1 with | .ok _ => emitObserved o (encoding G l i) | .error _ => o)

theorem execute_run {indexed anonymous Γ Δ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (s : EMState (env indexed anonymous) Δ) (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :
    execute G false l i s r b o shared=((.ok (),⟨⟨ScalarLocalEmit.after G (selected l i) s,r⟩,b⟩),emitObserved o (encoding G l i)) := by
  unfold execute
  rw [source_run]
  rfl

theorem execute_static {indexed anonymous Γ Δ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (s : EMState (env indexed anonymous) Δ) (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :
    execute G true l i s r b o shared=((.error (.revert []),⟨⟨s,r⟩,b⟩),o) := by
  unfold execute
  rw [source_static]
  rfl

theorem caller_fields {indexed anonymous Γ Δ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (s : EMState (env indexed anonymous) Δ) :
    let out:=ScalarLocalEmit.after G (selected l i) s
    out.1=s.1 ∧ out.2.ex=s.2.ex ∧ out.2.heap=s.2.heap ∧ out.2.events=s.2.events ∧
      out.2.fnLocals=s.2.fnLocals ∧ out.2.logs=(CallerFrameChecks.owner,
        G.selector (signature indexed anonymous)++ScalarLocalEmit.data (selected l i))::s.2.logs := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem after_memOK {indexed anonymous Γ Δ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (H : Source.HeapTy) (s : EMState (env indexed anonymous) Δ) (ok : Source.MemOK (env indexed anonymous) H s) :
    Source.MemOK (env indexed anonymous) H (ScalarLocalEmit.after G (selected l i) s) :=
  ⟨⟨⟨ok.1.1.heap,ok.1.1.le⟩,ok.1.2⟩,ok.2⟩

theorem rollback_legacy {indexed anonymous Γ Δ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (s : EMState (env indexed anonymous) Δ) :
    (Source.rollbackTo (s.2.ex.journal.length,s.2.logs.length,s.2.heap)).run
      (ScalarLocalEmit.after G (selected l i) s)=(.ok (),s) := by
  change ((Except.ok () : Except Source.Halt Unit),
    (s.1,{s.2 with
      ex:=s.2.ex.undoN (s.2.ex.journal.length-s.2.ex.journal.length),
      logs:=((CallerFrameChecks.owner,G.selector (signature indexed anonymous)++ScalarLocalEmit.data (selected l i))::s.2.logs).drop
        ((s.2.logs.length+1)-s.2.logs.length)}))=_
  simp only [Nat.sub_self,ExecState.undoN,Nat.add_sub_cancel_left,List.drop]

theorem enclosing_revert {indexed anonymous Γ Δ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (s : EMState (env indexed anonymous) Δ) (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) (bytes : Bytes) :
    finish s b o (companionEnter ⟨s.2.ex,r⟩ CallerFrameChecks.owner CallerFrameChecks.sender 0 [] false)
      (execute G false l i s r b o shared).1.2 [.log (encoding G l i)] (.revert bytes)=
      (⟨⟨s,r⟩,b⟩,⟨⟨s.2.ex,committedLogs o.trace,bytes⟩,o.trace,rfl⟩) := by
  rw [execute_run]
  have companion := companionRollback_run (⟨s.2.ex,r⟩ : ResidualCompanion (env indexed anonymous).layout
    (env indexed anonymous).lay (env indexed anonymous).lay complementCarrierOwnership)
    [] [] CallerFrameChecks.owner CallerFrameChecks.sender 0 [] false
  have enc := boolEncodingRollback_run b []
  simp only [companionRunSource,companionRunResidual,ExecState.run,residualRun] at companion
  simp only [boolEncodingRun] at enc
  let f:=companionEnter (⟨s.2.ex,r⟩ : ResidualCompanion (env indexed anonymous).layout
    (env indexed anonymous).lay (env indexed anonymous).lay complementCarrierOwnership)
    CallerFrameChecks.owner CallerFrameChecks.sender 0 [] false
  have back : companionRollback f ⟨(ScalarLocalEmit.after G (selected l i) s).2.ex,r⟩=⟨s.2.ex,r⟩ := companion
  have rolled : (Source.rollbackTo (f.source.mark,s.2.logs.length,s.2.heap)).run (ScalarLocalEmit.after G (selected l i) s)=(.ok (),s) :=
    rollback_legacy G l i s
  change finish s b o f ⟨⟨ScalarLocalEmit.after G (selected l i) s,r⟩,b⟩ [.log (encoding G l i)] (.revert bytes)=_
  simp only [finish,back,enc,rolled,rollbackTrace,discardLogs,List.append_nil,returnData]

/-- Explicitly select the supplied caller's actual locals, without identifying
an unrelated evaluated vector with that caller frame. -/
def executeCaller {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (static : Bool)
    (s : EMState (env indexed anonymous) Γ) (i : Source.Idx Γ ReturningCall.uint)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) := execute G static s.1 i s r b o shared

theorem caller_execute_run {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (s : EMState (env indexed anonymous) Γ) (i : Source.Idx Γ ReturningCall.uint)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :
    executeCaller G false s i r b o shared=
      ((.ok (),⟨⟨ScalarLocalEmit.after G (selected s.1 i) s,r⟩,b⟩),emitObserved o (encoding G s.1 i)) :=
  execute_run G s.1 i s r b o shared

end Solidity.Yul.World.IndexedEmitPort
