import Solidity.Yul.World.HeapWindowFrame
import Solidity.Yul.World.PhysicalPortChecks

/-! Inhabited actual-heap subwindow controls. No reachable-callee or compiler
certificate is inferred from these typed caller-memory operations. -/
namespace Solidity.Yul.World.HeapWindowChecks
open Solidity.Source
open Solidity.Source.StateExamples (addr)
open Solidity.Roadmap (Bytes Word)
open Solidity.Yul.Views
open Solidity.Yul.Views.Controls
open Solidity.Yul.World.HeapWindow

def n33 : Fin 34 := ⟨33,by decide⟩
def entry : Effects heapByteEnv.layout heapByteEnv.lay heapByteEnv.lay :=
  ⟨PhysicalPortChecks.callerState.2.ex,[],[9,0xad,0xbe,0xef,0xfa]⟩

def byteResult := (boundaryHeap n33).write 0
  (heapByteData heapByteEnv.layout false (splice (boundaryBytes n33) 31 [0xad,0xbe])) rfl

theorem byte_crosses_word : copyHeapWindow entry (boundaryHeap n33) (boundaryPlacement n33) 0 false (boundaryBytes n33) rfl
    (boundaryPhysical n33) 31 1 2 =
      some (Solidity.Backend.Environment.writeBytes (boundaryPhysical n33) 191 [0xad,0xbe],byteResult) :=
  copyHeapWindow_exact _ _ _ _ _ _ [0xad,0xbe] _ _ _ _ _ rfl (by decide)
    (congrArg Fin.val (bytesObject_header _ _ _ 128)) (bytesObject_payload_list _ _ _ 128)

def caller : Source.EMState heapByteEnv [.bytes .memory,.bytes .memory,.string .memory,.string .memory] :=
  ⟨retainedBothState.1,{retainedBothState.2 with
    ex := PhysicalPortChecks.callerState.2.ex,
    events := PhysicalPortChecks.callerState.2.events,
    logs := PhysicalPortChecks.callerState.2.logs}⟩

theorem caller_ok : Source.MemOK heapByteEnv byteHeap.ty caller := by
  have ok := retained_both_MemOK
  exact ⟨⟨⟨ok.1.1.heap,ok.1.1.le⟩,ok.1.2⟩,ok.2.1,ok.2.2⟩

def stringResult := retainedBothHeap.write 1
  (heapByteData heapByteEnv.layout true (splice retainedString64Bytes 31 [0xad,0xbe,0xef])) rfl

theorem string_reads :
    (mload realizedRetainedPhysical 256).val = retainedString64Bytes.length ∧
    readBytes realizedRetainedPhysical 288 retainedString64Bytes.length = retainedString64Bytes :=
  realized_retained_reads ⟨1,true,retainedString64Bytes,rfl⟩ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem string_crosses_word : copyHeapWindow entry retainedBothHeap realizedRetainedPlacement 1 true retainedString64Bytes rfl
    realizedRetainedPhysical 31 1 3 =
      some (Solidity.Backend.Environment.writeBytes realizedRetainedPhysical 319 [0xad,0xbe,0xef],stringResult) :=
  copyHeapWindow_exact _ _ _ _ _ _ [0xad,0xbe,0xef] _ _ _ _ _ rfl (by decide) string_reads.1 string_reads.2

def stateResult := withSourceHeap caller stringResult

theorem state_copy : copyStateWindow entry caller realizedRetainedPlacement 1 true retainedString64Bytes rfl
    realizedRetainedPhysical 31 1 3 =
      some (Solidity.Backend.Environment.writeBytes realizedRetainedPhysical 319 [0xad,0xbe,0xef],stateResult) :=
  copyStateWindow_exact _ _ _ _ _ _ [0xad,0xbe,0xef] _ _ _ _ _ rfl (by decide) string_reads.1 string_reads.2

theorem real_owner_memOK : Source.MemOK heapByteEnv byteHeap.ty stateResult :=
  copyStateWindow_memOK _ _ _ _ _ _ _ _ _ _ _ _ _ _ state_copy caller_ok

theorem full_source_prefix : stateResult.1 = caller.1 ∧ stateResult.2.ex=caller.2.ex ∧
    stateResult.2.events=caller.2.events ∧ stateResult.2.logs=caller.2.logs ∧ stateResult.2.fnLocals=caller.2.fnLocals :=
  copyStateWindow_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ state_copy

theorem source_alias :
    (Source.bytesOfRV (E:=heapByteEnv) byteReadFrame 1 (.val (stateResult.1.get (.there (.there .here))))).run stateResult =
      (.ok (splice retainedString64Bytes 31 [0xad,0xbe,0xef]),stateResult) := rfl

theorem shorter_prefix : copyHeapWindow entry byteHeap (bytePlacement 0) 0 false byteOld rfl bytePhysical 0 1 1 =
    some (Solidity.Backend.Environment.writeBytes bytePhysical 160 [0xad],
      byteHeap.write 0 (heapByteData heapByteEnv.layout false [0xad,0x22,0x33]) rfl) :=
  copyHeapWindow_exact _ _ _ _ _ _ [0xad] _ _ _ _ _ rfl (by decide)
    (actual_heap_reads ⟨0,false,byteOld,rfl⟩ List.mem_cons_self).1
    (actual_heap_reads ⟨0,false,byteOld,rfl⟩ List.mem_cons_self).2

theorem wrong_destination : copyHeapWindow entry byteHeap (bytePlacement 0) 0 false byteOld rfl bytePhysical 2 1 2 = none :=
  copyHeapWindow_destination _ _ _ _ _ _ _ _ _ _ _ (by decide)

theorem bad_source_zero : copyHeapWindow entry byteHeap (bytePlacement 0) 0 false byteOld rfl bytePhysical 3 6 0 = none :=
  copyHeapWindow_source _ _ _ _ _ _ _ _ _ _ _ (by decide)

theorem beyond_payload_zero : copyHeapWindow entry byteHeap (bytePlacement 0) 0 false byteOld rfl bytePhysical 4 5 0 = none :=
  copyHeapWindow_destination _ _ _ _ _ _ _ _ _ _ _ (by decide)

theorem exact_end_zero : copyHeapWindow entry (boundaryHeap n33) (boundaryPlacement n33) 0 false (boundaryBytes n33) rfl
    (boundaryPhysical n33) 33 5 0 = some (boundaryPhysical n33,boundaryHeap n33) :=
  copyHeapWindow_zero _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)
    (congrArg Fin.val (bytesObject_header _ _ _ 128)) (bytesObject_payload_list _ _ _ 128)

theorem unchanged_string_sides :
    (splice retainedString64Bytes 31 [0xad,0xbe,0xef]).length = retainedString64Bytes.length ∧
    (splice retainedString64Bytes 31 [0xad,0xbe,0xef]).take 31 = retainedString64Bytes.take 31 ∧
    (splice retainedString64Bytes 31 [0xad,0xbe,0xef]).drop 34 = retainedString64Bytes.drop 34 :=
  ⟨splice_length retainedString64Bytes [0xad,0xbe,0xef] 31 (by decide),splice_prefix retainedString64Bytes [0xad,0xbe,0xef] 31 (by decide),splice_suffix retainedString64Bytes [0xad,0xbe,0xef] 31 (by decide)⟩

theorem outside_and_other_cell :
    (copyHeapWindow entry retainedBothHeap realizedRetainedPlacement 1 true retainedString64Bytes rfl
      realizedRetainedPhysical 31 1 3).map (fun result => (result.1 318,result.2.get 2,result.2.ty,result.2.next)) =
      some (realizedRetainedPhysical 318,retainedBothHeap.get 2,retainedBothHeap.ty,retainedBothHeap.next) :=
  copyHeapWindow_frame _ _ _ _ 2 318 _ _ [0xad,0xbe,0xef] _ _ _ _ _ rfl (by decide) string_reads.1 string_reads.2 (by decide) (Or.inl (by decide))

theorem header_and_reserved :
    mload (Solidity.Backend.Environment.writeBytes realizedRetainedPhysical 319 [0xad,0xbe,0xef]) 256 =
      mload realizedRetainedPhysical 256 ∧
    ReservedOK (Solidity.Backend.Environment.writeBytes realizedRetainedPhysical 319 [0xad,0xbe,0xef]) 512 :=
  ⟨window_header _ 256 31 _,window_reserved retainedBothHeap realizedRetainedPlacement 1 true retainedString64Bytes [0xad,0xbe,0xef] rfl _ 31 realized_retained_reserved⟩

theorem other_typed_image :
    (MemoryImage.bytes (p:=realizedRetainedPlacement) byteOther (by decide)).Reads
      (Solidity.Backend.Environment.writeBytes realizedRetainedPhysical 319 [0xad,0xbe,0xef]) 384 := by
  have reads := realized_retained_reads ⟨2,false,byteOther,rfl⟩
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  exact window_other_image entry retainedBothHeap realizedRetainedPlacement 1 2 true retainedString64Bytes [0xad,0xbe,0xef]
    rfl realizedRetainedPhysical 31 1 3 rfl (by decide) string_reads.1 string_reads.2 _ stringResult string_crosses_word
    (MemoryImage.bytes byteOther (by decide)) rfl (by decide) reads

def observed : ObservedEffects heapByteEnv.layout heapByteEnv.lay heapByteEnv.lay :=
  ⟨⟨caller.2.ex,committedLogs Checks.callerTrace,entry.returndata⟩,Checks.callerTrace,rfl⟩
def residual : ResidualJournal complementCarrierOwnership :=
  residualWrite ⟨fun _=>0,[]⟩ (complementKey false (addr 1) 99,7)
def encoding : BoolEncodingJournal :=
  boolEncodingWrite boolEncodingInitial (⟨false,addr 1,100,⟨0,by decide⟩⟩,⟨⟨2,by decide⟩,by decide⟩)

theorem coupled_all_fields : copyCoupledWindow observed caller realizedRetainedPlacement 1 true retainedString64Bytes rfl
    residual encoding rfl realizedRetainedPhysical 31 1 3 =
    some ((Solidity.Backend.Environment.writeBytes realizedRetainedPhysical 319 [0xad,0xbe,0xef],stateResult),
      (residual,encoding),observed) :=
  copyCoupledWindow_exact _ _ _ _ _ _ [0xad,0xbe,0xef] _ _ _ rfl _ _ _ _ rfl (by decide) string_reads.1 string_reads.2

theorem actual_prefix_journals : caller.2.ex.journal.length=1 ∧ residual.journal.length=1 ∧ encoding.journal.length=1 ∧
    observed.trace=Checks.callerTrace := ⟨rfl,rfl,rfl,rfl⟩

theorem local_rule : AdapterRules.Box
    (AdapterRules.CopyStep PhysicalHeapPort.port (destination retainedBothHeap realizedRetainedPlacement 1 true retainedString64Bytes rfl 31 (by decide)) 1 3)
    (fun after => after.observed=observed ∧ after.memory=Solidity.Backend.Environment.writeBytes realizedRetainedPhysical 319 [0xad,0xbe,0xef])
    ⟨observed,realizedRetainedPhysical⟩ :=
  window_copy_rule _ _ _ _ _ _ [0xad,0xbe,0xef] _ _ _ _ _ rfl (by decide)

def callObserved : ObservedEffects heapByteEnv.layout heapByteEnv.lay heapByteEnv.lay := observed
def parent := caller.2.ex.enter (addr 1) (addr 3) 5 [] false

def afterCall := finishObserved callObserved
  (childContext caller.2.ex parent .delegatecall (addr 2) 0 retainedString64Bytes)
  (PhysicalPortChecks.callAnswer (addr 2) retainedString64Bytes)

/-- Scripted callee control: actual raw call port loads the real string image
and copies only the shorter returned prefix. Full trace is retained. -/
theorem raw_call_short_output :
    (callAdapter PhysicalHeapPort.port PhysicalPortChecks.callProducer callObserved realizedRetainedPhysical parent
      .delegatecall (addr 2) 100000 0 288 64 319 2).map
      (fun r => (r.observed.effects.returndata,r.observed.trace,r.copiedMemory)) =
      some (byteNew,afterCall.trace,some (Solidity.Backend.Environment.writeBytes realizedRetainedPhysical 319 [0x99,0x88])) := by
  have load : PhysicalHeapPort.port.load realizedRetainedPhysical 288 64 = some retainedString64Bytes := by
    rw [PhysicalHeapPort.load_view _ _ _ (by decide)]
    exact congrArg some string_reads.2
  rw [callAdapter_exact _ _ _ _ _ _ _ _ _ _ _ _ _ retainedString64Bytes
    (PhysicalPortChecks.callAnswer (addr 2) retainedString64Bytes) rfl rfl load rfl]
  rfl

theorem call_source_prefix : afterCall.effects.execution = caller.2.ex := by
  have restore := finishObserved_revert callObserved
    (childContext caller.2.ex parent .delegatecall (addr 2) 0 retainedString64Bytes)
    (PhysicalPortChecks.callAnswer (addr 2) retainedString64Bytes).operations
    (PhysicalPortChecks.callAnswer (addr 2) retainedString64Bytes).trace byteNew
  have state := congrArg (fun e : Effects heapByteEnv.layout heapByteEnv.lay heapByteEnv.lay => e.execution) restore.1
  exact state

theorem call_buffer_writeback : copyStateWindow afterCall.effects caller realizedRetainedPlacement 1 true retainedString64Bytes rfl
    realizedRetainedPhysical 31 0 2 =
      some (Solidity.Backend.Environment.writeBytes realizedRetainedPhysical 319 [0x99,0x88],
        withSourceHeap caller (retainedBothHeap.write 1
          (heapByteData heapByteEnv.layout true (splice retainedString64Bytes 31 [0x99,0x88])) rfl)) :=
  copyStateWindow_exact _ _ _ _ _ _ [0x99,0x88] _ _ _ _ _ rfl (by decide) string_reads.1 string_reads.2

theorem stale_buffer_refused :
    copyHeapWindow afterCall.effects retainedBothHeap realizedRetainedPlacement 1 true retainedString64Bytes rfl
      realizedRetainedPhysical 64 4 0 = none ∧
    copyHeapWindow entry retainedBothHeap realizedRetainedPlacement 1 true retainedString64Bytes rfl
      realizedRetainedPhysical 64 4 0 = some (realizedRetainedPhysical,retainedBothHeap) :=
  ⟨copyHeapWindow_source _ _ _ _ _ _ _ _ _ _ _ (by decide),
    copyHeapWindow_zero _ _ _ _ _ _ _ _ _ _ (by decide) (by decide) string_reads.1 string_reads.2⟩

theorem wrong_selected_object : copyHeapWindow entry retainedBothHeap realizedRetainedPlacement 0 false growBytes rfl
    realizedRetainedPhysical 31 1 3 = none :=
  copyHeapWindow_destination _ _ _ _ _ _ _ _ _ _ _ (by decide)

def postPlacement : Placement stringResult := windowPlacement retainedBothHeap realizedRetainedPlacement 1 true
  retainedString64Bytes [0xad,0xbe,0xef] rfl 31 (by decide)

theorem actual_post_placement : postPlacement.address=realizedRetainedPlacement.address ∧
    postPlacement.shape=realizedRetainedPlacement.shape ∧ postPlacement.free=realizedRetainedPlacement.free :=
  windowPlacement_choices _ _ _ _ _ _ _ _ _

end Solidity.Yul.World.HeapWindowChecks
