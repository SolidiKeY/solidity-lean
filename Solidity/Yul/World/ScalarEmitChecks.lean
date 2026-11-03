import Solidity.Yul.World.ScalarEmitPort

namespace Solidity.Yul.World.ScalarEmitChecks
open Solidity.Source
open Solidity.Roadmap (Word Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.ScalarEmitPort

def initial (indexed anonymous : Bool) : ExecState (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay :=
  (⟨⟨fun _=>Account.empty _⟩,.empty,[]⟩ : ExecState (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay).apply
    (.account CallerFrameChecks.owner (fun a=>{a with nonce:=3,balance:=17,code:=some 0}))
def heap (indexed anonymous : Bool) : Source.Heap (env indexed anonymous).layout :=
  ((Source.Heap.empty : Source.Heap (env indexed anonymous).layout).alloc ⟨.bytes .memory,.bytes [0xde,0xad,0xbe,0xef]⟩).1
def locals (indexed anonymous : Bool) : Locals (env indexed anonymous).layout [.bytes .memory] := .cons (.memRef rfl 0) .nil

def caller (indexed anonymous : Bool) : EMState (env indexed anonymous) [.bytes .memory] :=
  ⟨locals indexed anonymous,⟨initial indexed anonymous,heap indexed anonymous,
    interactionEvents GeneralReturningChecks.tracePrefix,[(CallerFrameChecks.owner,[0x70])],
    ⟨[.bytes .memory],locals indexed anonymous⟩⟩⟩
def observed (indexed anonymous : Bool) : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay :=
  ⟨⟨initial indexed anonymous,committedLogs GeneralReturningChecks.tracePrefix,[9,8,7,6]⟩,
    GeneralReturningChecks.tracePrefix,rfl⟩

theorem caller_memOK (indexed anonymous : Bool) :
    Source.MemOK (env indexed anonymous) (heap indexed anonymous).ty (caller indexed anonymous) := by
  have ok : HeapOK (E:=env indexed anonymous) (heap indexed anonymous) := HeapOK.alloc HeapOK.empty (.bytes [0xde,0xad,0xbe,0xef])
  have shaped : HeapShaped (E:=env indexed anonymous) (heap indexed anonymous) :=
    HeapShaped.alloc (E:=env indexed anonymous) (x:=⟨.bytes .memory,.bytes [0xde,0xad,0xbe,0xef]⟩) HeapShaped.empty trivial
  have inner : HeapInner (E:=env indexed anonymous) (heap indexed anonymous) :=
    HeapInner.alloc (E:=env indexed anonymous) (x:=⟨.bytes .memory,.bytes [0xde,0xad,0xbe,0xef]⟩) HeapInner.empty trivial
  exact ⟨⟨⟨ok,HeapTy.Le.refl _⟩,⟨⟨.bytes .memory,rfl,rfl⟩,trivial⟩⟩,shaped,inner⟩

theorem success {indexed anonymous} (G : Glob (env indexed anonymous)) :
    execute G false (caller indexed anonymous) CallerFrameChecks.residual CallerFrameChecks.encoding (observed indexed anonymous) rfl=
      ((.ok (),⟨⟨after G (caller indexed anonymous),CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩),
        emitObserved (observed indexed anonymous) (encoding G)) := execute_run G _ _ _ _ rfl

theorem source_and_raw {indexed anonymous} (G : Glob (env indexed anonymous)) :
    logAdapter PhysicalHeapPort.port (observed indexed anonymous) (memory G) false
      (encoding G).emitter (encoding G).count (encoding G).topics 160 (size G)=
      some (execute G false (caller indexed anonymous) CallerFrameChecks.residual CallerFrameChecks.encoding
        (observed indexed anonymous) rfl).2 := source_raw_observations G _ _ _ _ rfl

theorem complete_order {indexed anonymous} (G : Glob (env indexed anonymous)) :
    (execute G false (caller indexed anonymous) CallerFrameChecks.residual CallerFrameChecks.encoding
      (observed indexed anonymous) rfl).2.trace=
      [.event (.credit CallerFrameChecks.receiver 2),.log CallerFrameChecks.log,
       .event (.credit CallerFrameChecks.owner 5),.log GeneralReturningChecks.extraLog,.log (encoding G)] := by
  rw [execute_run]
  rfl

theorem full_caller_fields {indexed anonymous} (G : Glob (env indexed anonymous)) :
    (after G (caller indexed anonymous)).1=(caller indexed anonymous).1 ∧
    (after G (caller indexed anonymous)).2.heap=heap indexed anonymous ∧
    (after G (caller indexed anonymous)).2.fnLocals=(caller indexed anonymous).2.fnLocals ∧
    (after G (caller indexed anonymous)).2.events=(caller indexed anonymous).2.events ∧
    (after G (caller indexed anonymous)).2.ex=initial indexed anonymous ∧
    (after G (caller indexed anonymous)).2.logs=
      (CallerFrameChecks.owner,legacy G)::(caller indexed anonymous).2.logs ∧
    (emitObserved (observed indexed anonymous) (encoding G)).effects.returndata=[9,8,7,6] := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem aliases {indexed anonymous} (G : Glob (env indexed anonymous)) :
    (Source.bytesOfRV (E:=env indexed anonymous) (frame false) 1 (.val ((after G (caller indexed anonymous)).1.get .here))).run
      (after G (caller indexed anonymous))=(.ok [0xde,0xad,0xbe,0xef],after G (caller indexed anonymous)) ∧
    (Source.bytesOfRV (E:=env indexed anonymous) (frame false) 1 (.val ((after G (caller indexed anonymous)).2.fnLocals.2.get .here))).run
      (after G (caller indexed anonymous))=(.ok [0xde,0xad,0xbe,0xef],after G (caller indexed anonymous)) := ⟨rfl,rfl⟩

theorem success_memOK {indexed anonymous} (G : Glob (env indexed anonymous)) :
    Source.MemOK (env indexed anonymous) (heap indexed anonymous).ty (after G (caller indexed anonymous)) :=
  after_memOK G _ _ (caller_memOK indexed anonymous)

theorem static_source {indexed anonymous} (G : Glob (env indexed anonymous)) :
    execute G true (caller indexed anonymous) CallerFrameChecks.residual CallerFrameChecks.encoding (observed indexed anonymous) rfl=
      ((.error (.revert []),⟨⟨caller indexed anonymous,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩),observed indexed anonymous) :=
  execute_static G _ _ _ _ rfl

theorem static_raw {indexed anonymous} (G : Glob (env indexed anonymous)) :
    logAdapter PhysicalHeapPort.port (observed indexed anonymous) (memory G) true
      (encoding G).emitter (encoding G).count (encoding G).topics 160 (size G)=none := rfl

theorem rollback {indexed anonymous} (G : Glob (env indexed anonymous)) :
    finish (caller indexed anonymous) CallerFrameChecks.encoding (observed indexed anonymous)
      (companionEnter ⟨initial indexed anonymous,CallerFrameChecks.residual⟩ CallerFrameChecks.owner CallerFrameChecks.sender 0 [] false)
      (execute G false (caller indexed anonymous) CallerFrameChecks.residual CallerFrameChecks.encoding
        (observed indexed anonymous) rfl).1.2 [.log (encoding G)] (.revert [0xfa,0xfb])=
      (⟨⟨caller indexed anonymous,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩,
        ⟨⟨initial indexed anonymous,committedLogs GeneralReturningChecks.tracePrefix,[0xfa,0xfb]⟩,GeneralReturningChecks.tracePrefix,rfl⟩) :=
  enclosing_revert G _ _ _ _ rfl [0xfa,0xfb]

theorem nonempty_frames (indexed anonymous : Bool) :
    (initial indexed anonymous).journal.length=1 ∧ CallerFrameChecks.residual.journal.length=1 ∧
    CallerFrameChecks.encoding.journal.length=1 ∧ (heap indexed anonymous).next=1 ∧
    (caller indexed anonymous).2.logs.length=1 := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem all_four_cases (G00 : Glob (env false false)) (G10 : Glob (env true false))
    (G01 : Glob (env false true)) (G11 : Glob (env true true)) :
    (encoding G00).count.val=1 ∧ (encoding G00).data=ReturningCall.output ∧
    (encoding G10).count.val=2 ∧ (encoding G10).data=[] ∧
    (encoding G01).count.val=0 ∧ (encoding G01).data=ReturningCall.output ∧
    (encoding G11).count.val=1 ∧ (encoding G11).data=[] := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem legacy_identity_refused {indexed anonymous} (G : Glob (env indexed anonymous)) :
    (legacy G).length=36 ∧ legacy G≠(encoding G).data := ⟨legacy_length G,legacy_not_data G⟩

/-- Exact full-list negatives: neither a missing new log nor reordered prefix
can pass as the successful scalar observation. -/
theorem wrong_order {indexed anonymous} (G : Glob (env indexed anonymous)) :
    (emitObserved (observed indexed anonymous) (encoding G)).trace≠GeneralReturningChecks.tracePrefix ∧
    (emitObserved (observed indexed anonymous) (encoding G)).trace≠
      [.log CallerFrameChecks.log,.event (.credit CallerFrameChecks.receiver 2),
       .event (.credit CallerFrameChecks.owner 5),.log GeneralReturningChecks.extraLog,.log (encoding G)] := by
  constructor
  · intro same
    have length : (5 : Nat)=4 := congrArg List.length same
    exact (by decide : (5 : Nat)≠4) length
  · intro same
    have head := congrArg List.head? same
    change some (Observation.event (.credit CallerFrameChecks.receiver 2))=some (.log CallerFrameChecks.log) at head
    cases head

end Solidity.Yul.World.ScalarEmitChecks
