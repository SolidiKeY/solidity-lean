import Solidity.Backend.MemoryOps.PhysicalWorldUnwind
import Solidity.Lowering.V08.SourceEnvironmentControls

/-! Populated real Source world/transient writes, actual independent reason
execution in both pipelines, checked byte emitter and explicit caller restore.
These are linked component executions, NOT an automatic world/catch compiler. -/
namespace Solidity.Backend.MemoryOps.Physical.WorldControls
open Solidity
open Lowering.V08.SourceEnvironmentControls

def ops : List (Source.Op E.layout E.lay E.lay) :=
  [.account sender (fun a => {a with balance := 88}),
   .account self (fun a => {a with storage:=a.storage.write saved (.bool false)}),
   .transient self (fun s => s.write scratch (.bool false))]
def reached : Source.St E := {populated with ex:=populated.ex.run ops}
def reason : Roadmap.Bytes := [0,255,1]
def savedBytes : Environment.Memory := Environment.writeBytes (fun _ => 0) 64 (Semantics.wordBytes 7)
def liveBytes : Environment.Memory := Environment.writeBytes savedBytes 64 (Semantics.wordBytes 9)
def callerByte : Failure.Slice.Machine := ⟨[⟨77,by decide⟩,⟨88,by decide⟩],savedBytes⟩
def liveByte : Failure.Slice.Machine := ⟨[⟨11,by decide⟩,⟨22,by decide⟩],liveBytes⟩
def wordMachine : Evm.Machine := Evm.Memory.writeMachine Evm.Machine.init 2 (.val (Evm.wmod 7))
def represented (c : Nat) : Prop := False ∨ c=2

theorem initial_frame : WordFrame wordMachine savedBytes represented := by
  have h : WordFrame Evm.Machine.init (fun _ => 0) (fun _ => False) :=
    ⟨fun _ h => h.elim,fun _ h => h.elim⟩
  exact h.write 2 (Evm.wmod 7) (by decide)

def view (state : Source.St E) :=
  ((state.ex.world.accounts sender).balance,
   (state.ex.world.accounts self).balance,
   (state.ex.world.accounts self).storage.read saved,
   (state.ex.transient.cells self).read scratch,state.ex.journal.length,
   state.heap.next,state.heap.get 0,state.events,state.logs,state.fnLocals)

/-- Complete ordered source observations include both stores, journal, allocated
memory object, events/logs and saved function locals. Non-ex fields are retained. -/
theorem source_vectors :
    [view populated,view reached]=
      [(93,7,some (.bool true),some (.bool true),3,1,
        some ⟨.bytes .memory,.bytes [0,255]⟩,
        [.call self ⟨7,by decide⟩ [0,255] false],[(self,[171,0,255])],⟨[.bool],.cons (.bool true) .nil⟩),
       (88,7,some (.bool false),some (.bool false),6,1,
        some ⟨.bytes .memory,.bytes [0,255]⟩,
        [.call self ⟨7,by decide⟩ [0,255] false],[(self,[171,0,255])],⟨[.bool],.cons (.bool true) .nil⟩)] := by
  rfl

/-- Apply the generic initial-to-reached bridge, not a supplied final relation. -/
theorem source_and_byte_unwind (pipeline : Roadmap.Pipeline) (horizon : Nat) :
    (Source.evalE (global pipeline) frame (horizon+5)
      (Lowering.V08.SourceFailures.reason reason)).run (locals,reached)=
        (.error (.revert (Source.errorData reason)),(locals,reached)) ∧
    (populated.ex.enter frame.this frame.sender frame.value frame.cd frame.static).rollback
      reached.ex=populated.ex ∧
    Failure.Local.execute (Failure.Local.save (worldJournal populated.ex callerByte))
      64 (.reason reason) (worldJournal reached.ex liveByte)=
      some (worldJournal populated.ex callerByte,.revert (Source.errorData reason)) := by
  exact source_reason_world_unwind (global pipeline) frame horizon locals populated ops callerByte liveByte
    64 reason (by unfold Failure.Fits; decide +kernel) (by decide)

/-- Actual terminal stops before INVALID; all encoded bytes are present in live
memory. Caller byte image/tail differ and are restored only by the explicit API. -/
theorem live_payload_and_caller :
    Failure.Slice.checkedRun (Failure.emit 64 (.reason reason) ++ [.op .INVALID]) liveByte=
      some (⟨liveByte.stack,Failure.Slice.putBytes liveBytes 64 (Source.errorData reason)⟩,
        some (.revert (Source.errorData reason))) ∧
    Failure.Slice.getBytes (Failure.Slice.putBytes liveBytes 64 (Source.errorData reason))
      64 (Source.errorData reason).length=Source.errorData reason ∧
    WordFrame wordMachine callerByte.memory represented ∧
    callerByte.stack=[⟨77,by decide⟩,⟨88,by decide⟩] ∧
    liveByte.stack=[⟨11,by decide⟩,⟨22,by decide⟩] :=
  ⟨reason_live_bytes 64 reason liveByte [.op .INVALID] (by unfold Failure.Fits; decide +kernel) (by decide),
    Failure.Slice.getBytes_putBytes _ _ _,initial_frame,rfl,rfl⟩

/-- Dirty Source state survives the actual revert; an automatic rollback claim
is false. Both pipelines also preserve this prefix on insufficient horizon. -/
theorem not_automatic_and_timeout (pipeline : Roadmap.Pipeline) :
    reached.ex≠populated.ex ∧
    (Source.evalE (global pipeline) frame 2
      (Lowering.V08.SourceFailures.reason reason)).run (locals,reached)=
        (.error .timeout,(locals,reached)) := by
  constructor
  · intro same
    have h := congrArg (fun s : Source.ExecState E.layout E.lay E.lay =>
      (s.world.accounts sender).balance) same
    change (88 : Nat)=93 at h
    contradiction
  · exact Lowering.V08.SourceFailures.reason_low_horizon (global pipeline) frame reason locals reached

/-- Concrete wrong restored-memory substitution loses the live ABI payload. -/
theorem wrong_caller_payload :
    Environment.readMemory savedBytes 64 (Source.errorData reason).length ≠ Source.errorData reason := by
  intro same
  have h := congrArg (fun bs : List UInt8 => bs[0]?) same
  change some (0 : UInt8)=some (8 : UInt8) at h
  contradiction

/-- This actual evaluator rollback trims newly prepended logs and world writes,
but keeps newly allocated Source memory. No heap rollback is fabricated. -/
theorem source_rollback_heap_boundary :
    let fresh := (populated.heap.alloc ⟨.bytes .memory,.bytes [9]⟩).1
    let dirty := {populated with ex:=populated.ex.run ops, logs:=(self,[222])::populated.logs, heap:=fresh}
    (Source.rollbackTo (populated.ex.journal.length,populated.logs.length,populated.heap) :
      Source.EM E [.bool] Unit).run (locals,dirty)=
        (.ok (),(locals,{populated with heap:=fresh})) ∧
    fresh.next=2 ∧ populated.heap.next=1 ∧ fresh.get 1=some ⟨.bytes .memory,.bytes [9]⟩ := by
  dsimp only
  exact ⟨source_rollback_to locals populated ops [(self,[222])] _,rfl,rfl,rfl⟩

/-- Direct inhabited application of the generic physical observer restoration. -/
theorem restored_numeric_observer :
    ∃ output, Failure.Local.execute (Failure.Local.save (worldJournal populated.ex callerByte))
      64 (.reason reason) (worldJournal reached.ex liveByte)=
        some (output,.revert (Source.errorData reason)) ∧
      WordFrame wordMachine output.machine.memory represented ∧
      output.machine=callerByte ∧ output.persistent=populated.ex.world ∧
      output.transient=populated.ex.transient :=
  world_reason_restored_frame populated.ex ops callerByte liveByte wordMachine represented initial_frame
    64 reason (by unfold Failure.Fits; decide +kernel) (by decide)

private def prefixWord : Evm.Machine := Evm.Memory.writeMachine wordMachine 2 (.val (Evm.wmod 8))
private def prefixBytes : Environment.Memory := Environment.writeBytes savedBytes 64 (Semantics.wordBytes 8)
private def dirtyWord : Evm.Machine := Evm.Memory.writeMachine prefixWord 2 (.val (Evm.wmod 9))
private def dirtyBytes : Environment.Memory := Environment.writeBytes prefixBytes 64 (Semantics.wordBytes 9)
private def savedPrefix : Failure.Slice.Machine := ⟨callerByte.stack,prefixBytes⟩
private def dirtyPrefix : Failure.Slice.Machine := ⟨liveByte.stack,dirtyBytes⟩

private theorem written_read (memory : Environment.Memory) (n : Nat) :
    Environment.readMemory (Environment.writeBytes memory 64 (Semantics.wordBytes n)) 64 32=
      Semantics.wordBytes n := by
  simpa only [Environment.wordBytes_length] using Environment.read_written (Semantics.wordBytes n) 64 memory

/-- Actual word/byte prefix saves8 and a real second store reaches9. Two
SEPARATE terminal observations start at that dirty state: raw REVERT reads9,
while the independently invoked ABI-reason emitter unwinds to saved8. No byte
program continues after REVERT. Source remains dirty in both pipelines; all
older full vectors stay unchanged. This is not a call/transaction trace. -/
theorem saved_prefix_unwind (pipeline : Roadmap.Pipeline) (horizon : Nat) :
    (Source.evalE (global pipeline) frame (horizon+5)
      (Lowering.V08.SourceFailures.reason reason)).run (locals,reached)=
        (.error (.revert (Source.errorData reason)),(locals,reached)) ∧
    Evm.run [.mstoreAt] ((wordMachine.push (.val (Evm.wmod 8))).push (.val (Evm.wmod 2)))=
      .ok prefixWord 0 ∧
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU 64 (by decide)::lenU 8 (by decide)::[lenU 77 (by decide),lenU 88 (by decide)],savedBytes⟩=
        some ⟨[lenU 77 (by decide),lenU 88 (by decide)],prefixBytes⟩ ∧
    Evm.run [.mstoreAt] ((prefixWord.push (.val (Evm.wmod 9))).push (.val (Evm.wmod 2)))=
      .ok dirtyWord 0 ∧
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU 64 (by decide)::lenU 9 (by decide)::[lenU 11 (by decide),lenU 22 (by decide)],prefixBytes⟩=
        some ⟨[lenU 11 (by decide),lenU 22 (by decide)],dirtyBytes⟩ ∧
    Failure.Slice.run [.op .REVERT,.op .INVALID]
      ⟨(⟨64,by decide⟩ : Roadmap.Word)::(⟨32,by decide⟩ : Roadmap.Word)::dirtyPrefix.stack,dirtyBytes⟩=
        some (dirtyPrefix,some (.revert (Semantics.wordBytes 9))) ∧
    [wordMachine.mem 2,prefixWord.mem 2,dirtyWord.mem 2]=
      [.val (Evm.wmod 7),.val (Evm.wmod 8),.val (Evm.wmod 9)] ∧
    [Environment.readMemory savedBytes 64 32,Environment.readMemory prefixBytes 64 32,
      Environment.readMemory dirtyBytes 64 32]=[Semantics.wordBytes 7,Semantics.wordBytes 8,Semantics.wordBytes 9] ∧
    prefixWord.stack=wordMachine.stack ∧ dirtyWord.stack=wordMachine.stack ∧
    (∀ c,c≠2 → prefixWord.mem c=wordMachine.mem c ∧ dirtyWord.mem c=wordMachine.mem c) ∧
    (∀ a,a<64 ∨ 96≤a → prefixBytes a=savedBytes a ∧ dirtyBytes a=savedBytes a) ∧
    ∃ output,Failure.Local.execute (Failure.Local.save (worldJournal populated.ex savedPrefix))
      64 (.reason reason) (worldJournal reached.ex dirtyPrefix)=
        some (output,.revert (Source.errorData reason)) ∧
      WordFrame prefixWord output.machine.memory (fun c => represented c ∨ c=2) ∧
      output.machine=savedPrefix ∧ output.persistent=populated.ex.world ∧
      output.transient=populated.ex.transient := by
  have result := world_reason_saved_store populated.ex ops wordMachine savedBytes represented
    (Evm.wmod 2) (Evm.wmod 8) callerByte.stack initial_frame (by decide) dirtyPrefix
    64 reason (by unfold Failure.Fits;decide +kernel) (by decide)
  obtain ⟨hw,hb,out,run,restored,hm,hp,ht⟩ := result
  refine ⟨(source_and_byte_unwind pipeline horizon).1,hw,hb,
    word_mstore prefixWord (Evm.wmod 2) (Evm.wmod 9),
    byte_mstore prefixBytes [lenU 11 (by decide),lenU 22 (by decide)] (Evm.wmod 2) (Evm.wmod 9) (by decide),
    ?_,rfl,?_,rfl,rfl,?_,?_,out,run,restored,hm,hp,ht⟩
  · exact revert_written_word prefixBytes (Evm.wmod 2) (Evm.wmod 9) (by decide) dirtyPrefix.stack [.op .INVALID]
  · rw [show Environment.readMemory savedBytes 64 32=Semantics.wordBytes 7 from written_read _ 7,
      show Environment.readMemory prefixBytes 64 32=Semantics.wordBytes 8 from written_read _ 8,
      show Environment.readMemory dirtyBytes 64 32=Semantics.wordBytes 9 from written_read _ 9]
  · intro c hc
    exact ⟨Evm.upd_other _ _ hc,(Evm.upd_other _ _ hc).trans (Evm.upd_other _ _ hc)⟩
  · intro a ha
    have first : prefixBytes a=savedBytes a := Environment.writeBytes_frame _ _ a _
      (by simp only [Environment.wordBytes_length];omega)
    have second : dirtyBytes a=prefixBytes a := Environment.writeBytes_frame _ _ a _
      (by simp only [Environment.wordBytes_length];omega)
    exact ⟨first,second.trans first⟩

/-- Restoring the dirty child or the pre-prefix caller is observably wrong. -/
theorem saved_prefix_wrong_restoration :
    Environment.readMemory prefixBytes 64 32≠Environment.readMemory dirtyBytes 64 32 ∧
    Environment.readMemory prefixBytes 64 32≠Environment.readMemory savedBytes 64 32 := by
  rw [show Environment.readMemory prefixBytes 64 32=Semantics.wordBytes 8 from written_read _ 8,
    show Environment.readMemory dirtyBytes 64 32=Semantics.wordBytes 9 from written_read _ 9,
    show Environment.readMemory savedBytes 64 32=Semantics.wordBytes 7 from written_read _ 7]
  decide

/-- info: 'Solidity.Backend.MemoryOps.Physical.WorldControls.saved_prefix_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms saved_prefix_unwind
/-- info: 'Solidity.Backend.MemoryOps.Physical.WorldControls.saved_prefix_wrong_restoration' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms saved_prefix_wrong_restoration

/-- info: 'Solidity.Backend.MemoryOps.Physical.WorldControls.restored_numeric_observer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms restored_numeric_observer
/-- info: 'Solidity.Backend.MemoryOps.Physical.WorldControls.initial_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initial_frame
/-- info: 'Solidity.Backend.MemoryOps.Physical.WorldControls.source_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_vectors
/-- info: 'Solidity.Backend.MemoryOps.Physical.WorldControls.source_and_byte_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_and_byte_unwind
/-- info: 'Solidity.Backend.MemoryOps.Physical.WorldControls.live_payload_and_caller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms live_payload_and_caller
/-- info: 'Solidity.Backend.MemoryOps.Physical.WorldControls.not_automatic_and_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_automatic_and_timeout
/-- info: 'Solidity.Backend.MemoryOps.Physical.WorldControls.wrong_caller_payload' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms wrong_caller_payload
/-- info: 'Solidity.Backend.MemoryOps.Physical.WorldControls.source_rollback_heap_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_rollback_heap_boundary
end Solidity.Backend.MemoryOps.Physical.WorldControls
