import Solidity.Yul.World.GeneralReturningChecks

/-! Selected actual scalar Source.emit -> common full-log observation extension.
No Source runtime edit, inverse of legacy logs or second ABI is used. The
registered event's flags and actual uint256 constant determine the full topic
words and existing encoded word data. General event/argument/frontend/compiler
adequacy and the joint G01 theorem remain open. -/
namespace Solidity.Yul.World.ScalarEmitPort
open Solidity.Source
open Solidity.Roadmap (Word Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion

def eventDecl (indexed anonymous : Bool) : Decl := ⟨.event,"Notice",some "Finite",false,
  .event "Notice" (.cons (.eventParam (.elem (.int false 256 (by decide))) indexed (some "value")) .nil) anonymous⟩
def env (indexed anonymous : Bool) : Env := ⟨eventDecl indexed anonymous::ReturningCall.env.decls⟩
def statement (indexed anonymous : Bool) : RStmt (env indexed anonymous) [] false ⟨false,false⟩ [] [] :=
  .emit (eventDecl indexed anonymous) rfl (.cons (.const (Q.ofInt ReturningCall.value)) (by cases indexed <;> cases anonymous <;> decide) .nil)
def frame (static : Bool) : Fr := ⟨CallerFrameChecks.owner,CallerFrameChecks.sender,0,static,"Finite",true,0⟩
def signature (indexed anonymous : Bool) := sigOf (env indexed anonymous).layout "Notice" [ReturningCall.uint]
def legacy {indexed anonymous} (G : Glob (env indexed anonymous)) : Bytes := G.selector (signature indexed anonymous)++ReturningCall.output

def encoding {indexed anonymous} (G : Glob (env indexed anonymous)) : Log :=
  match indexed,anonymous with
  | false,false => ⟨CallerFrameChecks.owner,⟨1,by decide⟩,#v[G.fixed.hash (asciiBytes (signature false false))],ReturningCall.output⟩
  | true,false => ⟨CallerFrameChecks.owner,⟨2,by decide⟩,#v[G.fixed.hash (asciiBytes (signature true false)),toWord ReturningCall.value],[]⟩
  | false,true => ⟨CallerFrameChecks.owner,⟨0,by decide⟩,#v[],ReturningCall.output⟩
  | true,true => ⟨CallerFrameChecks.owner,⟨1,by decide⟩,#v[toWord ReturningCall.value],[]⟩

def after {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (s : EMState (env indexed anonymous) Γ) : EMState (env indexed anonymous) Γ :=
  ⟨s.1,{s.2 with logs:=(CallerFrameChecks.owner,legacy G)::s.2.logs}⟩

theorem registered (indexed anonymous : Bool) : (env indexed anonymous).decls.head?=some (eventDecl indexed anonymous) := rfl

theorem statement_run {indexed anonymous} (G : Glob (env indexed anonymous)) (s : EMState (env indexed anonymous) []) :
    (Source.execS G (frame false) 5 0 none (statement indexed anonymous) .nil).run s=
      (.ok (.normal .nil),after G s) := by
  cases indexed <;> cases anonymous <;> cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem statement_static {indexed anonymous} (G : Glob (env indexed anonymous)) (s : EMState (env indexed anonymous) []) :
    (Source.execS G (frame true) 5 0 none (statement indexed anonymous) .nil).run s=(.error (.revert []),s) := by
  cases indexed <;> cases anonymous <;> cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

/-- Actual owner local-frame boundary, never an assumed arbitrary producer. -/
def source {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (static : Bool) (s : EMState (env indexed anonymous) Γ) :=
  (Source.EM.sub (Source.L0 (env indexed anonymous)) (Source.execS G (frame static) 5 0 none (statement indexed anonymous) .nil)).run s

theorem source_run {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (s : EMState (env indexed anonymous) Γ) :
    source G false s=(.ok (.normal .nil,Source.L0 (env indexed anonymous)),after G s) := by
  unfold source
  rw [Source.run_sub,statement_run]
  rfl

theorem source_static {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (s : EMState (env indexed anonymous) Γ) :
    source G true s=(.error (.revert []),s) := by
  unfold source
  rw [Source.run_sub,statement_static]

/-- Owned observation extension, retaining the exact legacy Source result as
well as the complete common log. Initial shared execution is explicit. -/
def execute {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (static : Bool)
    (s : EMState (env indexed anonymous) Γ) (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (_shared : o.effects.execution=s.2.ex) :=
  let actual := source G static s
  ((actual.1.map (fun _=>()),(⟨⟨actual.2,r⟩,b⟩ : Carrier (env indexed anonymous) Γ)),
    match actual.1 with | .ok _ => emitObserved o (encoding G) | .error _ => o)

theorem execute_run {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (s : EMState (env indexed anonymous) Γ) (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :
    execute G false s r b o shared=((.ok (),⟨⟨after G s,r⟩,b⟩),emitObserved o (encoding G)) := by
  unfold execute
  rw [source_run]
  rfl

theorem execute_static {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (s : EMState (env indexed anonymous) Γ) (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :
    execute G true s r b o shared=((.error (.revert []),⟨⟨s,r⟩,b⟩),o) := by
  unfold execute
  rw [source_static]
  rfl

/-- Actual source/observation execution coupling of this chosen statement. -/
theorem execute_shared {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (static : Bool)
    (s : EMState (env indexed anonymous) Γ) (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :
    (execute G static s r b o shared).2.effects.execution=(execute G static s r b o shared).1.2.1.1.2.ex := by
  cases static with
  | false => rw [execute_run]; exact shared
  | true => rw [execute_static]; exact shared

theorem after_memOK {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (H : HeapTy) (s : EMState (env indexed anonymous) Γ) (ok : Source.MemOK (env indexed anonymous) H s) :
    Source.MemOK (env indexed anonymous) H (after G s) :=
  ⟨⟨⟨ok.1.1.heap,ok.1.1.le⟩,ok.1.2⟩,ok.2⟩

/-- Existing rollbackTo removes the ACTUAL newly prepended legacy log and
retains every other caller source field at its original frame-entry mark. -/
theorem rollback_legacy {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (s : EMState (env indexed anonymous) Γ) :
    (Source.rollbackTo (s.2.ex.journal.length,s.2.logs.length,s.2.heap)).run (after G s)=(.ok (),s) := by
  change ((Except.ok () : Except Halt Unit),
    (s.1,{s.2 with
      ex:=s.2.ex.undoN (s.2.ex.journal.length-s.2.ex.journal.length)
      logs:=((CallerFrameChecks.owner,legacy G)::s.2.logs).drop ((s.2.logs.length+1)-s.2.logs.length)}))=_
  simp only [Nat.sub_self,ExecState.undoN,Nat.add_sub_cancel_left,List.drop]

/-- Successful actual emit can be undone by an enclosing frame. Full source,
residual/owned journals and ordered caller observations are restored. The
observer's new log is not projected into the legacy byte-log representation. -/
theorem enclosing_revert {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (s : EMState (env indexed anonymous) Γ) (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) (data : Bytes) :
    finish s b o (companionEnter ⟨s.2.ex,r⟩ CallerFrameChecks.owner CallerFrameChecks.sender 0 [] false)
      (execute G false s r b o shared).1.2 [.log (encoding G)] (.revert data)=
      (⟨⟨s,r⟩,b⟩,⟨⟨s.2.ex,committedLogs o.trace,data⟩,o.trace,rfl⟩) := by
  rw [execute_run]
  have companion := companionRollback_run (⟨s.2.ex,r⟩ : ResidualCompanion (env indexed anonymous).layout
    (env indexed anonymous).lay (env indexed anonymous).lay complementCarrierOwnership)
    [] [] CallerFrameChecks.owner CallerFrameChecks.sender 0 [] false
  have enc := boolEncodingRollback_run b []
  simp only [companionRunSource,companionRunResidual,ExecState.run,residualRun] at companion
  simp only [boolEncodingRun] at enc
  let f := companionEnter (⟨s.2.ex,r⟩ : ResidualCompanion (env indexed anonymous).layout
    (env indexed anonymous).lay (env indexed anonymous).lay complementCarrierOwnership)
    CallerFrameChecks.owner CallerFrameChecks.sender 0 [] false
  have back : companionRollback f ⟨(after G s).2.ex,r⟩=⟨s.2.ex,r⟩ := companion
  have rolled : (Source.rollbackTo (f.source.mark,s.2.logs.length,s.2.heap)).run (after G s)=(.ok (),s) :=
    rollback_legacy G s
  change finish s b o f ⟨⟨after G s,r⟩,b⟩ [.log (encoding G)] (.revert data)=_
  simp only [finish,back,enc,rolled,rollbackTrace,discardLogs,List.append_nil,returnData]

theorem data_bound {indexed anonymous} (G : Glob (env indexed anonymous)) : (encoding G).data.length≤32 := by
  cases indexed <;> cases anonymous <;> simp only [encoding,List.length_nil,ReturningCall.output_length] <;> decide

/-- Separately constructed raw input encoding of this scalar's event data.
This is NOT asserted to be the view of an arbitrary caller s.heap. -/
def memory {indexed anonymous} (G : Glob (env indexed anonymous)) : ByteView :=
  bytesObjectView (encoding G).data (by have bound:=data_bound G; omega) (fun _=>0xa5) 128

def size {indexed anonymous} (G : Glob (env indexed anonymous)) : Word :=
  ⟨(encoding G).data.length,by have bound:=data_bound G; omega⟩

theorem raw_loaded {indexed anonymous} (G : Glob (env indexed anonymous)) :
    PhysicalHeapPort.port.load (memory G) 160 (size G)=some (encoding G).data := by
  rw [PhysicalHeapPort.load_view _ _ _ (by have bound:=data_bound G; change 160+(encoding G).data.length≤2^256; omega)]
  exact congrArg some (bytesObject_payload_list _ _ _ 128)

/-- Raw LOG0/1/2 loads the actual selected memory bytes and produces exactly
the same full log; no topic projection or legacy-log identity is used. -/
theorem raw_agreement {indexed anonymous} (G : Glob (env indexed anonymous))
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay) :
    logAdapter PhysicalHeapPort.port o (memory G) false (encoding G).emitter (encoding G).count (encoding G).topics 160 (size G)=
      some (emitObserved o (encoding G)) := by
  have actual := logAdapter_exact PhysicalHeapPort.port o (memory G) (encoding G).emitter
    (encoding G).count (encoding G).topics 160 (size G) (encoding G).data (raw_loaded G)
  exact actual

/-- Complete ordered observation equality for actual scalar Source emit in
this owned extension and the raw-log port on the actual encoded byte input. -/
theorem source_raw_observations {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (s : EMState (env indexed anonymous) Γ) (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :
    logAdapter PhysicalHeapPort.port o (memory G) false (encoding G).emitter (encoding G).count (encoding G).topics 160 (size G)=
      some (execute G false s r b o shared).2 := by
  rw [execute_run]
  exact raw_agreement G o

theorem legacy_length {indexed anonymous} (G : Glob (env indexed anonymous)) : (legacy G).length=36 := by
  simp only [legacy,List.length_append,Glob.selector,List.length_take,wordBytes_length,ReturningCall.output_length]
  rfl

/-- A direct legacy-data identity adapter would be wrong for every case here.
The real legacy log is retained, and common log encoding needs declaration,
flags, value and the full Fixed hash in the owned extension. -/
theorem legacy_not_data {indexed anonymous} (G : Glob (env indexed anonymous)) : legacy G≠(encoding G).data := by
  intro same
  have bound := data_bound G
  have lengths := congrArg List.length same
  rw [legacy_length] at lengths
  omega

theorem full_signature_topic (G : Glob (env false false)) :
    (encoding G).topics=#v[G.fixed.hash (asciiBytes (signature false false))] ∧ (encoding G).data=ReturningCall.output := ⟨rfl,rfl⟩

theorem indexed_topics (G : Glob (env true false)) :
    (encoding G).topics=#v[G.fixed.hash (asciiBytes (signature true false)),toWord ReturningCall.value] ∧ (encoding G).data=[] := ⟨rfl,rfl⟩

theorem anonymous_topics (G : Glob (env true true)) :
    (encoding G).topics=#v[toWord ReturningCall.value] ∧ (encoding G).data=[] := ⟨rfl,rfl⟩

end Solidity.Yul.World.ScalarEmitPort
