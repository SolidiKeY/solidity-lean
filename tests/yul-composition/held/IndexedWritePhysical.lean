import Solidity.Yul.Composition.PhysicalFrames
import Solidity.Yul.World.IndexedEmitHeap

/-! A represented write followed by an actual indexed-local emit. The enclosing
mark precedes BOTH operations. The common log is an explicit owner extension;
this is not the joint G01 or Source/Yul/compiler adequacy theorem. -/
namespace Solidity.Yul.Composition.IndexedWritePhysical
open Solidity.Source Solidity.Yul.Views Solidity.Yul.World
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.ScalarEmitPort
open Solidity.Roadmap (Address Word Bytes)

/-- Keep the complete ordered prefix and old returndata while sharing the actual
post-write execution. No trace or source outcome is supplied as a certificate. -/
def shifted {E Γ} (o : ObservedEffects E.layout E.lay E.lay) (s : EMState E Γ) :
    ObservedEffects E.layout E.lay E.lay :=
  ⟨⟨s.2.ex,o.effects.logs,o.effects.returndata⟩,o.trace,o.logs_eq⟩

def run {indexed anonymous Γ ps ts q before} (G : Glob (env indexed anonymous))
    (p : RepresentedSlotPlan ps ts q before) (s : EMState (env indexed anonymous) Γ)
    (r : ResidualJournal complementCarrierOwnership)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (i : Source.Idx Γ ReturningCall.uint) :=
  let w:=representedSourceStep ps ts q before (frame false) p s r
  IndexedEmitPort.executeCaller G false w.1.1.2 i w.1.2 w.2 (shifted o w.1.1.2) rfl

theorem run_actual {indexed anonymous Γ ps ts q before} (G : Glob (env indexed anonymous))
    (p : RepresentedSlotPlan ps ts q before) (s : EMState (env indexed anonymous) Γ)
    (r : ResidualJournal complementCarrierOwnership) (o) (i : Source.Idx Γ ReturningCall.uint) :
    let w:=representedSourceStep ps ts q before (frame false) p s r
    run G p s r o i=
      ((.ok (),⟨⟨ScalarLocalEmit.after G (IndexedEmitPort.selected w.1.1.2.1 i) w.1.1.2,w.1.2⟩,w.2⟩),
        emitObserved (shifted o w.1.1.2) (IndexedEmitPort.encoding G w.1.1.2.1 i)) :=
  IndexedEmitPort.caller_execute_run G _ i _ _ _ rfl

theorem run_reconstructed {indexed anonymous Γ ps ts q before} (G : Glob (env indexed anonymous))
    (p : RepresentedSlotPlan ps ts q before) (s : EMState (env indexed anonymous) Γ)
    (r : ResidualJournal complementCarrierOwnership) (o) (i : Source.Idx Γ ReturningCall.uint)
    (bank : q.transient=false) (separated : finiteSeparated (ps q.address)) :
    reencodePersistentSlot (representedBanks ps false (run G p s r o i).1.2.2)
      ⟨(run G p s r o i).1.2.1.1.2.ex,(run G p s r o i).1.2.1.2⟩ q.address q.slot=some q.raw := by
  rw [run_actual]
  exact represented_step_persistent_at_request (frame false) p s r rfl bank separated

theorem run_fields {indexed anonymous Γ ps ts q before} (G : Glob (env indexed anonymous))
    (p : RepresentedSlotPlan ps ts q before) (s : EMState (env indexed anonymous) Γ)
    (r : ResidualJournal complementCarrierOwnership) (o) (i : Source.Idx Γ ReturningCall.uint) :
    let result:=run G p s r o i
    result.1.2.1.1.1=s.1 ∧ result.1.2.1.1.2.heap=s.2.heap ∧
    result.1.2.1.1.2.fnLocals=s.2.fnLocals ∧ result.1.2.1.1.2.events=s.2.events ∧
    result.1.2.1.1.2.logs=(CallerFrameChecks.owner,
      G.selector (signature indexed anonymous)++ScalarLocalEmit.data (IndexedEmitPort.selected s.1 i))::s.2.logs ∧
    result.2.trace=o.trace++[.log (IndexedEmitPort.encoding G s.1 i)] ∧
    result.2.effects.returndata=o.effects.returndata := by
  rw [run_actual,representedSourceStep_nonstatic (frame false) p s r rfl]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Rollback is at the PRE-WRITE mark. The emit-only owner's theorem starts
later and deliberately retains the physical write, so it cannot replace this. -/
theorem outer_revert {indexed anonymous Γ ps ts q before} (G : Glob (env indexed anonymous))
    (p : RepresentedSlotPlan ps ts q before) (s : EMState (env indexed anonymous) Γ)
    (r : ResidualJournal complementCarrierOwnership) (o) (i : Source.Idx Γ ReturningCall.uint) (bytes : Bytes) :
    finish s before o (companionEnter ⟨s.2.ex,r⟩ (frame false).this (frame false).sender 0 [] false)
      (run G p s r o i).1.2 [.log (IndexedEmitPort.encoding G s.1 i)] (.revert bytes)=
      (⟨⟨s,r⟩,before⟩,⟨⟨s.2.ex,committedLogs o.trace,bytes⟩,o.trace,rfl⟩) := by
  rw [run_actual,representedSourceStep_nonstatic (frame false) p s r rfl]
  have back:=companionRollback_run (⟨s.2.ex,r⟩ : ResidualCompanion (env indexed anonymous).layout
    (env indexed anonymous).lay (env indexed anonymous).lay complementCarrierOwnership)
    [p.packed.sourceOp] [p.packed.residualUpdate] (frame false).this (frame false).sender 0 [] false
  change companionRollback _ ⟨s.2.ex.apply p.packed.sourceOp,residualWrite r p.packed.residualUpdate⟩=⟨s.2.ex,r⟩ at back
  simp only [finish,ScalarLocalEmit.after,back,requestEncoding,boolEncodingRollback_run,
    rollbackTrace,discardLogs,List.append_nil,returnData]
  cases s with
  | mk locals state =>
    cases state with
    | mk ex heap events logs fn =>
      change ((((locals,(⟨ex,heap,events,
        ((CallerFrameChecks.owner,G.selector (signature indexed anonymous)++ScalarLocalEmit.data (IndexedEmitPort.selected locals i))::logs).drop
          ((logs.length+1)-logs.length),fn⟩ : St (env indexed anonymous))),r),before),_) = _
      simp only [Nat.add_sub_cancel_left,List.drop]

/-- The public current-frame API agrees only after concrete preparation and
request/owner equality. An arbitrary plan does not establish admission. -/
theorem prepared_frame {indexed anonymous Γ ps ts q before}
    (p : RepresentedSlotPlan ps ts q before) (s : EMState (env indexed anonymous) Γ)
    (r : ResidualJournal complementCarrierOwnership)
    (prepared : prepareRepresentedSlot ps ts q before=some p) (owner : q.address=(frame false).this) :
    representedFrameWrite? ps ts (frame false) q.transient q.slot q.raw before s r=
      some (representedSourceStep ps ts q before (frame false) p s r) :=
  Solidity.Yul.Composition.prepared_frame_action ps ts q before (frame false) p prepared owner s r

theorem run_memOK {indexed anonymous Γ ps ts q before} (G : Glob (env indexed anonymous))
    (p : RepresentedSlotPlan ps ts q before) (s : EMState (env indexed anonymous) Γ)
    (r : ResidualJournal complementCarrierOwnership) (o) (i : Source.Idx Γ ReturningCall.uint)
    (H : Source.HeapTy) (ok : Source.MemOK (env indexed anonymous) H s) :
    Source.MemOK (env indexed anonymous) H (run G p s r o i).1.2.1.1 := by
  rw [run_actual]
  exact IndexedEmitPort.after_memOK G _ i H _ (representedSourceStep_MemOK H (frame false) p s r ok)

/-- Fresh paths are indexed by the ACTUAL extended producer environment. The
old originEnv/slot43 witness is not cast into this environment. -/
def flag {indexed anonymous} (a : Address) : ScalarPath (env indexed anonymous).layout ((env indexed anonymous).lay a) :=
  ⟨Solidity.Yul.Views.Controls.finiteFlag,7,boolField,boolCodec _,.bool⟩
def registry {indexed anonymous} (a : Address) := [flag (indexed:=indexed) (anonymous:=anonymous) a]
def request : PackedSlotRequest := ⟨false,CallerFrameChecks.owner,7,⟨0xab000002,by decide⟩⟩
def prepared (indexed anonymous : Bool) :=
  prepareRepresentedSlot (registry (indexed:=indexed) (anonymous:=anonymous)) registry request CallerFrameChecks.encoding

theorem prepared_some (indexed anonymous : Bool) : (prepared indexed anonymous).isSome := by
  cases indexed <;> cases anonymous <;> rfl

def plan (indexed anonymous : Bool) := (prepared indexed anonymous).get (prepared_some indexed anonymous)
def inputs {indexed anonymous} : Locals (env indexed anonymous).layout [.bytes .memory,ReturningCall.uint,ReturningCall.uint] :=
  .cons (.memRef rfl 0) (.cons (.int ReturningCall.value (by decide)) (.cons (.int 1 (by decide)) .nil))
def index : Source.Idx [.bytes .memory,ReturningCall.uint,ReturningCall.uint] ReturningCall.uint := .there .here

def caller {indexed anonymous} (G : Glob (env indexed anonymous)) :=
  (inputs (indexed:=indexed) (anonymous:=anonymous),
    {(ScalarEmitChecks.caller indexed anonymous).2 with heap:=IndexedEmitHeap.heap G inputs index})
def observed (indexed anonymous : Bool) := ScalarEmitChecks.observed indexed anonymous

theorem witness_reconstructed {indexed anonymous} (G : Glob (env indexed anonymous)) :
    reencodePersistentSlot (representedBanks registry false (run G (plan indexed anonymous) (caller G)
      CallerFrameChecks.residual (observed indexed anonymous) index).1.2.2)
      ⟨(run G (plan indexed anonymous) (caller G) CallerFrameChecks.residual (observed indexed anonymous) index).1.2.1.1.2.ex,
       (run G (plan indexed anonymous) (caller G) CallerFrameChecks.residual (observed indexed anonymous) index).1.2.1.2⟩
      CallerFrameChecks.owner 7=some request.raw := by
  apply run_reconstructed G (plan indexed anonymous) (caller G) CallerFrameChecks.residual (observed indexed anonymous) index rfl
  exact List.Pairwise.nil.cons (by intro x hx; cases hx)

theorem witness_rollback {indexed anonymous} (G : Glob (env indexed anonymous)) (bytes : Bytes) :
    finish (caller G) CallerFrameChecks.encoding (observed indexed anonymous)
      (companionEnter ⟨(caller G).2.ex,CallerFrameChecks.residual⟩ CallerFrameChecks.owner CallerFrameChecks.sender 0 [] false)
      (run G (plan indexed anonymous) (caller G) CallerFrameChecks.residual (observed indexed anonymous) index).1.2
      [.log (IndexedEmitPort.encoding G inputs index)] (.revert bytes)=
      (⟨⟨caller G,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩,
        ⟨⟨(caller G).2.ex,committedLogs (observed indexed anonymous).trace,bytes⟩,(observed indexed anonymous).trace,rfl⟩) :=
  outer_revert G (plan indexed anonymous) (caller G) CallerFrameChecks.residual (observed indexed anonymous) index bytes

theorem witness_current_frame {indexed anonymous} (G : Glob (env indexed anonymous)) :
    representedFrameWrite? registry registry (frame false) false 7 request.raw CallerFrameChecks.encoding
      (caller G) CallerFrameChecks.residual=
      some (representedSourceStep registry registry request CallerFrameChecks.encoding (frame false)
        (plan indexed anonymous) (caller G) CallerFrameChecks.residual) :=
  prepared_frame (plan indexed anonymous) (caller G) CallerFrameChecks.residual
    (Option.some_get (prepared_some indexed anonymous)).symm rfl

/-- The same actual post-write heap is realized by VY2's placement, not by an
invented equality between logical id zero and a physical pointer. -/
theorem witness_heap_log {indexed anonymous} (G : Glob (env indexed anonymous)) :
    let w:=representedSourceStep registry registry request CallerFrameChecks.encoding (frame false)
      (plan indexed anonymous) (caller G) CallerFrameChecks.residual
    logAdapter PhysicalHeapPort.port (shifted (observed indexed anonymous) w.1.1.2)
      (IndexedEmitHeap.physical G inputs index) false
      (IndexedEmitPort.encoding G inputs index).emitter (IndexedEmitPort.encoding G inputs index).count
      (IndexedEmitPort.encoding G inputs index).topics
      (PhysicalHeapPort.payloadOffset (IndexedEmitHeap.heap G inputs index) (IndexedEmitHeap.placement G inputs index)
        0 false (IndexedEmitPort.encoding G inputs index).data rfl)
      ⟨(IndexedEmitPort.encoding G inputs index).data.length,
        heapByte_length_bound (IndexedEmitHeap.heap G inputs index) (IndexedEmitHeap.placement G inputs index)
          0 false (IndexedEmitPort.encoding G inputs index).data rfl⟩ =
      some (run G (plan indexed anonymous) (caller G) CallerFrameChecks.residual (observed indexed anonymous) index).2 := by
  rw [run_actual,representedSourceStep_nonstatic (frame false) (plan indexed anonymous) (caller G) CallerFrameChecks.residual rfl]
  exact IndexedEmitMemory.raw_encoded G inputs index _ (IndexedEmitHeap.heap G inputs index)
    (IndexedEmitHeap.placement G inputs index) [IndexedEmitHeap.entry G inputs index]
    (by simp only [List.map_cons,List.map_nil,List.nodup_cons,List.not_mem_nil,List.nodup_nil,not_false_eq_true,and_self])
    (IndexedEmitHeap.entry G inputs index) (by exact List.mem_cons_self) _ rfl

theorem witness_actual_bool {indexed anonymous} (G : Glob (env indexed anonymous)) :
    ((run G (plan indexed anonymous) (caller G) CallerFrameChecks.residual (observed indexed anonymous) index).1.2.1.1.2.ex.world.accounts
      CallerFrameChecks.owner).storage.read Solidity.Yul.Views.Controls.finiteFlag=some (.bool true) := by
  rw [run_actual,representedSourceStep_nonstatic (frame false) (plan indexed anonymous) (caller G) CallerFrameChecks.residual rfl]
  cases indexed <;> cases anonymous <;> rfl

theorem witness_journals {indexed anonymous} (G : Glob (env indexed anonymous)) :
    let out:=run G (plan indexed anonymous) (caller G) CallerFrameChecks.residual (observed indexed anonymous) index
    out.1.2.1.1.2.ex.journal.length=(caller G).2.ex.journal.length+1 ∧
    out.1.2.1.2.journal.length=CallerFrameChecks.residual.journal.length+1 ∧
    out.1.2.2.journal.length=CallerFrameChecks.encoding.journal.length+1 := by
  rw [run_actual,representedSourceStep_nonstatic (frame false) (plan indexed anonymous) (caller G) CallerFrameChecks.residual rfl]
  cases indexed <;> cases anonymous <;> exact ⟨rfl,rfl,rfl⟩

theorem witness_aliases {indexed anonymous} (G : Glob (env indexed anonymous)) :
    let out:=(run G (plan indexed anonymous) (caller G) CallerFrameChecks.residual (observed indexed anonymous) index).1.2.1.1
    (Source.bytesOfRV (E:=env indexed anonymous) (frame false) 1 (.val (out.1.get .here))).run out =
      (.ok (IndexedEmitPort.encoding G inputs index).data,out) ∧
    (Source.bytesOfRV (E:=env indexed anonymous) (frame false) 1 (.val (out.2.fnLocals.2.get .here))).run out =
      (.ok (IndexedEmitPort.encoding G inputs index).data,out) := by
  simp only [run_actual,representedSourceStep_nonstatic (frame false) (plan indexed anonymous) (caller G) CallerFrameChecks.residual rfl]
  exact ⟨rfl,rfl⟩

theorem wrong_slot : request.slot ≠ (8 : Word) := by decide
theorem wrong_owner : request.address ≠ (32 : Address) := by decide
theorem lost_raw_byte : request.raw ≠ (⟨0xab000001,by decide⟩ : Word) := by decide
theorem lost_padding : request.raw ≠ (⟨2,by decide⟩ : Word) := by decide

theorem wrong_tail {indexed anonymous} :
    IndexedEmitPort.selected (inputs (indexed:=indexed) (anonymous:=anonymous)) (.there (.there .here)) ≠
      IndexedEmitPort.selected (inputs (indexed:=indexed) (anonymous:=anonymous)) index := by
  change (1 : Int) ≠ (ReturningCall.value : Int)
  decide

theorem full_topic (G : Glob (env true false)) :
    (IndexedEmitPort.encoding G inputs index).topics.get ⟨1,by change 1<2; decide⟩=toWord ReturningCall.value := rfl

theorem wrong_topic (G : Glob (env true false)) :
    (IndexedEmitPort.encoding G inputs index).topics.get ⟨1,by change 1<2; decide⟩≠toWord 1 := by
  rw [full_topic]
  decide

/-- Static emit refusal is a real Source error. The previous dynamic physical
write remains PENDING at this point, until an actual enclosing rollback. -/
theorem static_emit_pending {indexed anonymous Γ ps ts q before} (G : Glob (env indexed anonymous))
    (p : RepresentedSlotPlan ps ts q before) (s : EMState (env indexed anonymous) Γ)
    (r : ResidualJournal complementCarrierOwnership) (o) (i : Source.Idx Γ ReturningCall.uint) :
    let w:=representedSourceStep ps ts q before (frame false) p s r
    IndexedEmitPort.executeCaller G true w.1.1.2 i w.1.2 w.2 (shifted o w.1.1.2) rfl =
      ((.error (.revert []),⟨⟨w.1.1.2,w.1.2⟩,w.2⟩),shifted o w.1.1.2) :=
  IndexedEmitPort.execute_static G _ _ _ _ _ _ rfl

/-- Moving the rollback entry past the physical write restores the WRONG
state: the dirty logical bool remains present. -/
theorem late_mark_keeps_write {indexed anonymous Γ ps ts q before} (G : Glob (env indexed anonymous))
    (p : RepresentedSlotPlan ps ts q before) (s : EMState (env indexed anonymous) Γ)
    (r : ResidualJournal complementCarrierOwnership) (o) (i : Source.Idx Γ ReturningCall.uint) (bytes : Bytes) :
    let w:=representedSourceStep ps ts q before (frame false) p s r
    finish w.1.1.2 w.2 (shifted o w.1.1.2)
      (companionEnter ⟨w.1.1.2.2.ex,w.1.2⟩ CallerFrameChecks.owner CallerFrameChecks.sender 0 [] false)
      (run G p s r o i).1.2 [.log (IndexedEmitPort.encoding G w.1.1.2.1 i)] (.revert bytes)=
      (⟨⟨w.1.1.2,w.1.2⟩,w.2⟩,⟨⟨w.1.1.2.2.ex,committedLogs o.trace,bytes⟩,o.trace,rfl⟩) :=
  IndexedEmitPort.enclosing_revert G _ i _ _ _ _ rfl bytes

/-- Wrong slot/owner requests remain legal residual writes. These controls test
what ACTUALLY changes, rather than falsely claiming arbitrary slots are refused. -/
def otherSlot {indexed anonymous} (G : Glob (env indexed anonymous)) :=
  representedFrameWrite? registry registry (frame false) false 8 request.raw CallerFrameChecks.encoding
    (caller G) CallerFrameChecks.residual

def otherOwner {indexed anonymous} (G : Glob (env indexed anonymous)) :=
  representedFrameWrite? registry registry {frame false with this:=32} false 7 request.raw CallerFrameChecks.encoding
    (caller G) CallerFrameChecks.residual

theorem other_slot_actual {indexed anonymous} (G : Glob (env indexed anonymous)) :
    (otherSlot G).map (fun result=>
      (result.1.1.2.2.ex.world.accounts CallerFrameChecks.owner).storage.cell Solidity.Yul.Views.Controls.finiteFlag)=some none := by
  cases indexed <;> cases anonymous <;> rfl

theorem other_owner_actual {indexed anonymous} (G : Glob (env indexed anonymous)) :
    (otherOwner G).map (fun result=>
      ((result.1.1.2.2.ex.world.accounts CallerFrameChecks.owner).storage.cell Solidity.Yul.Views.Controls.finiteFlag,
       (result.1.1.2.2.ex.world.accounts 32).storage.cell Solidity.Yul.Views.Controls.finiteFlag))=
      some (none,some (.bool true)) := by
  cases indexed <;> cases anonymous <;> rfl

/-- Reusing the OLD owned-byte journal silently normalizes byte2 to byte1.
Full reconstruction therefore distinguishes equal logical bools. -/
theorem stale_encoding_actual {indexed anonymous} (G : Glob (env indexed anonymous)) :
    let out:=run G (plan indexed anonymous) (caller G) CallerFrameChecks.residual (observed indexed anonymous) index
    reencodePersistentSlot (representedBanks registry false CallerFrameChecks.encoding)
      ⟨out.1.2.1.1.2.ex,out.1.2.1.2⟩ CallerFrameChecks.owner 7=some (⟨0xab000001,by decide⟩ : Word) := by
  rw [run_actual,representedSourceStep_nonstatic (frame false) (plan indexed anonymous) (caller G) CallerFrameChecks.residual rfl]
  change reencodePersistentSlot (representedBanks (registry (indexed:=indexed) (anonymous:=anonymous)) false CallerFrameChecks.encoding)
    ⟨(ScalarEmitChecks.initial indexed anonymous).apply (plan indexed anonymous).packed.sourceOp,
      residualWrite CallerFrameChecks.residual (plan indexed anonymous).packed.residualUpdate⟩
    CallerFrameChecks.owner 7=some (⟨0xab000001,by decide⟩ : Word)
  cases indexed <;> cases anonymous <;> decide

theorem wrong_raw_reconstruction {indexed anonymous} (G : Glob (env indexed anonymous)) :
    let out:=run G (plan indexed anonymous) (caller G) CallerFrameChecks.residual (observed indexed anonymous) index
    reencodePersistentSlot (representedBanks registry false out.1.2.2)
      ⟨out.1.2.1.1.2.ex,out.1.2.1.2⟩ CallerFrameChecks.owner 7≠some (⟨2,by decide⟩ : Word) := by
  dsimp only
  rw [witness_reconstructed]
  decide

theorem static_write_refused {indexed anonymous} (G : Glob (env indexed anonymous)) :
    representedSourceStep registry registry request CallerFrameChecks.encoding (frame true)
      (plan indexed anonymous) (caller G) CallerFrameChecks.residual=
      (((.error (.revert []),caller G),CallerFrameChecks.residual),CallerFrameChecks.encoding) :=
  representedSourceStep_static (frame true) _ _ _ rfl

/-- Static emit is a static refusal AFTER a dynamic write here. It does not undo
the pending write; this explicit enclosing completion restores all three marks. -/
theorem static_emit_outer_revert {indexed anonymous Γ ps ts q before} (G : Glob (env indexed anonymous))
    (p : RepresentedSlotPlan ps ts q before) (s : EMState (env indexed anonymous) Γ)
    (r : ResidualJournal complementCarrierOwnership) (o) (i : Source.Idx Γ ReturningCall.uint) :
    let w:=representedSourceStep ps ts q before (frame false) p s r
    let failed:=IndexedEmitPort.executeCaller G true w.1.1.2 i w.1.2 w.2 (shifted o w.1.1.2) rfl
    finish s before o (companionEnter ⟨s.2.ex,r⟩ (frame false).this (frame false).sender 0 [] false)
      failed.1.2 [] (.revert [])=
      (⟨⟨s,r⟩,before⟩,⟨⟨s.2.ex,committedLogs o.trace,[]⟩,o.trace,rfl⟩) := by
  dsimp only
  rw [static_emit_pending,representedSourceStep_nonstatic (frame false) p s r rfl]
  simpa only [rollbackTrace,discardLogs,List.append_nil] using (finish_runs_revert s r before o [p.packed.sourceOp] [p.packed.residualUpdate]
    (encodingWrites (selectedSlotPaths (if q.transient then ts q.address else ps q.address) q.slot)
      q.transient q.address (fun _=>q.raw) before) (frame false).this (frame false).sender 0 [] false [] [])

def late {indexed anonymous} (G : Glob (env indexed anonymous)) (bytes : Bytes) :=
  let w:=representedSourceStep registry registry request CallerFrameChecks.encoding (frame false)
    (plan indexed anonymous) (caller G) CallerFrameChecks.residual
  finish w.1.1.2 w.2 (shifted (observed indexed anonymous) w.1.1.2)
    (companionEnter ⟨w.1.1.2.2.ex,w.1.2⟩ CallerFrameChecks.owner CallerFrameChecks.sender 0 [] false)
    (run G (plan indexed anonymous) (caller G) CallerFrameChecks.residual (observed indexed anonymous) index).1.2
    [.log (IndexedEmitPort.encoding G w.1.1.2.1 index)] (.revert bytes)

theorem late_mark_distinct {indexed anonymous} (G : Glob (env indexed anonymous)) (bytes : Bytes) :
    (late G bytes).1 ≠ (⟨⟨caller G,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ : Carrier (env indexed anonymous) _) := by
  unfold late
  rw [late_mark_keeps_write]
  intro equal
  have stored:=congrArg (fun c : Carrier (env indexed anonymous) [.bytes .memory,ReturningCall.uint,ReturningCall.uint] =>
    (c.1.1.2.ex.world.accounts CallerFrameChecks.owner).storage.cell Solidity.Yul.Views.Controls.finiteFlag) equal
  rw [representedSourceStep_nonstatic (frame false) (plan indexed anonymous) (caller G) CallerFrameChecks.residual rfl] at stored
  cases indexed <;> cases anonymous <;> cases stored

/-- Inhabited actual Source configuration, not an execution-agreement oracle.
The selected emit needs no function body; selectors use the approved Fixed hash. -/
def fixture (indexed anonymous viaIR : Bool) : Glob (env indexed anonymous) where
  prog := {
    body := fun _=>none
    consts := fun _=>none
    inits := fun _=>[]
    ctor := fun _=>none
    ctorLocals := fun _=>[]
    baseArgs := fun _=>[]
    contracts := ["Finite"] }
  pipeline := if viaIR then .viaIR else .legacy
  fixed := {
    evm := Solidity.Roadmap.Evm.withKeccak
    ledger := fun balance _ address=>balance address
    regionLen := 1
    rootSlots := 1 }
  balance0 := fun _=>0
  hasCode := fun _ _=>false
  callee := fun _=>.answer (.success [])
  timestamp := 0

theorem inhabited_rollback (indexed anonymous viaIR : Bool) :
    let G:=fixture indexed anonymous viaIR
    finish (caller G) CallerFrameChecks.encoding (observed indexed anonymous)
      (companionEnter ⟨(caller G).2.ex,CallerFrameChecks.residual⟩ CallerFrameChecks.owner CallerFrameChecks.sender 0 [] false)
      (run G (plan indexed anonymous) (caller G) CallerFrameChecks.residual (observed indexed anonymous) index).1.2
      [.log (IndexedEmitPort.encoding G inputs index)] (.revert [0xde,0xad])=
      (⟨⟨caller G,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩,
        ⟨⟨(caller G).2.ex,committedLogs (observed indexed anonymous).trace,[0xde,0xad]⟩,
          (observed indexed anonymous).trace,rfl⟩) := witness_rollback (fixture indexed anonymous viaIR) [0xde,0xad]

end Solidity.Yul.Composition.IndexedWritePhysical
