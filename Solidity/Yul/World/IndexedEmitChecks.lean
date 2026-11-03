import Solidity.Yul.World.IndexedEmitHeap

namespace Solidity.Yul.World.IndexedEmitChecks
open Solidity.Source
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.IndexedEmitPort
open Solidity.Yul.World.ScalarEmitPort (env)

def inputs (indexed anonymous : Bool) : Locals (env indexed anonymous).layout
    [ReturningCall.uint,.bool,ReturningCall.uint,ReturningCall.uint] :=
  .cons (.int 1 (by decide)) (.cons (.bool true) (.cons (.int ReturningCall.value (by decide)) (.cons (.int 256 (by decide)) .nil)))
def index : Source.Idx [ReturningCall.uint,.bool,ReturningCall.uint,ReturningCall.uint] ReturningCall.uint := .there (.there .here)

theorem nonhead_value (indexed anonymous : Bool) : selected (inputs indexed anonymous) index=ReturningCall.value := rfl

theorem actual_nonhead {indexed anonymous} (G : Glob (env indexed anonymous)) :
    source G false (inputs indexed anonymous) index (ScalarEmitChecks.caller indexed anonymous)=
      (.ok (.normal (inputs indexed anonymous),Source.L0 (env indexed anonymous)),
        ScalarLocalEmit.after G ReturningCall.value (ScalarEmitChecks.caller indexed anonymous)) := source_run G _ _ _

theorem full_order {indexed anonymous} (G : Glob (env indexed anonymous)) :
    (execute G false (inputs indexed anonymous) index (ScalarEmitChecks.caller indexed anonymous)
      CallerFrameChecks.residual CallerFrameChecks.encoding (ScalarEmitChecks.observed indexed anonymous) rfl).2.trace=
      [.event (.credit CallerFrameChecks.receiver 2),.log CallerFrameChecks.log,
       .event (.credit CallerFrameChecks.owner 5),.log GeneralReturningChecks.extraLog,
       .log (encoding G (inputs indexed anonymous) index)] := by
  rw [execute_run]
  rfl

theorem static_source {indexed anonymous} (G : Glob (env indexed anonymous)) :
    execute G true (inputs indexed anonymous) index (ScalarEmitChecks.caller indexed anonymous)
      CallerFrameChecks.residual CallerFrameChecks.encoding (ScalarEmitChecks.observed indexed anonymous) rfl=
      ((.error (.revert []),⟨⟨ScalarEmitChecks.caller indexed anonymous,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩),
        ScalarEmitChecks.observed indexed anonymous) := execute_static G _ _ _ _ _ _ rfl

theorem rollback {indexed anonymous} (G : Glob (env indexed anonymous)) :
    finish (ScalarEmitChecks.caller indexed anonymous) CallerFrameChecks.encoding (ScalarEmitChecks.observed indexed anonymous)
      (companionEnter ⟨ScalarEmitChecks.initial indexed anonymous,CallerFrameChecks.residual⟩ CallerFrameChecks.owner CallerFrameChecks.sender 0 [] false)
      (execute G false (inputs indexed anonymous) index (ScalarEmitChecks.caller indexed anonymous)
        CallerFrameChecks.residual CallerFrameChecks.encoding (ScalarEmitChecks.observed indexed anonymous) rfl).1.2
      [.log (encoding G (inputs indexed anonymous) index)] (.revert [0xfa,0xfb])=
      (⟨⟨ScalarEmitChecks.caller indexed anonymous,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩,
        ⟨⟨ScalarEmitChecks.initial indexed anonymous,committedLogs GeneralReturningChecks.tracePrefix,[0xfa,0xfb]⟩,
          GeneralReturningChecks.tracePrefix,rfl⟩) := enclosing_revert G _ _ _ _ _ _ rfl [0xfa,0xfb]

def heap_source_raw {indexed anonymous} (G : Glob (env indexed anonymous)) :=
  IndexedEmitHeap.source_heap_raw G (inputs indexed anonymous) index

def heap_aliases {indexed anonymous} (G : Glob (env indexed anonymous)) :=
  IndexedEmitHeap.aliases G (inputs indexed anonymous) index

def heap_memOK {indexed anonymous} (G : Glob (env indexed anonymous)) :=
  IndexedEmitHeap.caller_memOK G (inputs indexed anonymous) index

theorem wrong_head_data (G : Glob (env false false)) :
    (encoding G (inputs false false) .here).data≠(encoding G (inputs false false) index).data := by
  change ScalarLocalEmit.data 1≠ScalarLocalEmit.data ReturningCall.value
  decide

theorem wrong_tail_data (G : Glob (env false true)) :
    (encoding G (inputs false true) (.there (.there (.there .here)))).data≠(encoding G (inputs false true) index).data := by
  change ScalarLocalEmit.data 256≠ScalarLocalEmit.data ReturningCall.value
  decide

theorem full_indexed_topic (G : Glob (env true false)) :
    (encoding G (inputs true false) index).topics=
      #v[G.fixed.hash (asciiBytes (ScalarEmitPort.signature true false)),intWord ReturningCall.value] ∧
    (encoding G (inputs true false) index).data=[] := ⟨rfl,rfl⟩

theorem wrong_head_topic (G : Glob (env true true)) :
    (encoding G (inputs true true) .here).topics≠(encoding G (inputs true true) index).topics := by
  change (#v[intWord 1] : Vector _ 1)≠#v[intWord ReturningCall.value]
  decide

def maxValue : Int := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def boundaryInputs (indexed anonymous : Bool) : Locals (env indexed anonymous).layout [ReturningCall.uint,ReturningCall.uint] :=
  .cons (.int 0 (by decide)) (.cons (.int maxValue (by decide)) .nil)

theorem zero_boundary (G : Glob (env false false)) :
    (encoding G (boundaryInputs false false) .here).data=List.replicate 32 0 := by
  change ScalarLocalEmit.data 0=List.replicate 32 0
  decide

theorem max_boundary (G : Glob (env false true)) :
    (encoding G (boundaryInputs false true) (.there .here)).data=List.replicate 32 255 := by
  change ScalarLocalEmit.data maxValue=List.replicate 32 255
  decide

theorem max_topic (G : Glob (env true true)) :
    (encoding G (boundaryInputs true true) (.there .here)).topics=#v[intWord maxValue] := rfl

/-- Wrong window controls retain the full observation, including the prefix. -/
theorem missing_window (G : Glob (env false false)) :
    logAdapter PhysicalHeapPort.port (ScalarEmitChecks.observed false false)
      (IndexedEmitMemory.memory G (inputs false false) index) false (encoding G (inputs false false) index).emitter
      (encoding G (inputs false false) index).count (encoding G (inputs false false) index).topics 160 0≠
      some (emitObserved (ScalarEmitChecks.observed false false) (encoding G (inputs false false) index)) :=
  IndexedEmitMemory.wrong_window G _ _ _ _ 160 0 [] rfl (by change []≠ScalarLocalEmit.data ReturningCall.value; decide)

theorem truncated_window (G : Glob (env false false)) :
    logAdapter PhysicalHeapPort.port (ScalarEmitChecks.observed false false)
      (IndexedEmitMemory.memory G (inputs false false) index) false (encoding G (inputs false false) index).emitter
      (encoding G (inputs false false) index).count (encoding G (inputs false false) index).topics 160 31≠
      some (emitObserved (ScalarEmitChecks.observed false false) (encoding G (inputs false false) index)) :=
  IndexedEmitMemory.wrong_window G _ _ _ _ 160 31
    (readBytes (IndexedEmitMemory.memory G (inputs false false) index) 160 31)
    (PhysicalHeapPort.load_view _ _ _ (by decide)) (by
      intro same
      have lengths:=congrArg List.length same
      simp only [readBytes,List.length_map,List.length_range,encoding,ScalarLocalEmit.encoding,ScalarLocalEmit.data,wordBytes_length] at lengths
      contradiction)

theorem wrong_region (G : Glob (env false false)) :
    logAdapter PhysicalHeapPort.port (ScalarEmitChecks.observed false false)
      (IndexedEmitMemory.memory G (inputs false false) index) false (encoding G (inputs false false) index).emitter
      (encoding G (inputs false false) index).count (encoding G (inputs false false) index).topics 161 32≠
      some (emitObserved (ScalarEmitChecks.observed false false) (encoding G (inputs false false) index)) :=
  IndexedEmitMemory.wrong_window G _ _ _ _ 161 32
    (readBytes (IndexedEmitMemory.memory G (inputs false false) index) 161 32)
    (PhysicalHeapPort.load_view _ _ _ (by decide)) (by
      change readBytes (bytesObjectView (ScalarLocalEmit.data ReturningCall.value) (by decide) (fun _=>0xa5) 128) 161 32≠
        ScalarLocalEmit.data ReturningCall.value
      decide)

theorem actual_caller_index {indexed anonymous} (G : Glob (env indexed anonymous)) :
    let s : EMState (env indexed anonymous) [ReturningCall.uint,.bool,ReturningCall.uint,ReturningCall.uint] :=
      ⟨inputs indexed anonymous,(ScalarEmitChecks.caller indexed anonymous).2⟩
    executeCaller G false s index CallerFrameChecks.residual CallerFrameChecks.encoding (ScalarEmitChecks.observed indexed anonymous) rfl=
      ((.ok (),⟨⟨ScalarLocalEmit.after G ReturningCall.value s,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩),
        emitObserved (ScalarEmitChecks.observed indexed anonymous) (encoding G s.1 index)) := caller_execute_run G _ _ _ _ _ rfl

theorem max_source {indexed anonymous} (G : Glob (env indexed anonymous)) :
    source G false (boundaryInputs indexed anonymous) (.there .here) (ScalarEmitChecks.caller indexed anonymous)=
      (.ok (.normal (boundaryInputs indexed anonymous),Source.L0 (env indexed anonymous)),
        ScalarLocalEmit.after G maxValue (ScalarEmitChecks.caller indexed anonymous)) := source_run G _ _ _

end Solidity.Yul.World.IndexedEmitChecks
