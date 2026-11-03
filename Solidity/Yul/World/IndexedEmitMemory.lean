import Solidity.Yul.World.IndexedEmitPort

/-! Actual indexed-local data and full raw-log agreement. Heap/byte relations
are explicit input facts about the existing producer carriers, not adequacy. -/
namespace Solidity.Yul.World.IndexedEmitMemory
open Solidity.Source
open Solidity.Yul.Views
open Solidity.Roadmap (Bytes Word)
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.IndexedEmitPort
open Solidity.Yul.World.ScalarEmitPort (env)

theorem data_bound {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint) :
    (encoding G l i).data.length≤32 := by
  cases indexed <;> cases anonymous <;>
    simp only [encoding,ScalarLocalEmit.encoding,ScalarLocalEmit.data,wordBytes_length,List.length_nil] <;> decide

/-- Constructed matching bytes are explicit; this is not arbitrary heap agreement. -/
def memory {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint) : ByteView :=
  bytesObjectView (encoding G l i).data (by have bound:=data_bound G l i; omega) (fun _=>0xa5) 128

def size {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint) : Word :=
  ⟨(encoding G l i).data.length,by have bound:=data_bound G l i; omega⟩

theorem loaded {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint) :
    PhysicalHeapPort.port.load (memory G l i) 160 (size G l i)=some (encoding G l i).data := by
  rw [PhysicalHeapPort.load_view _ _ _ (by have bound:=data_bound G l i; change 160+(encoding G l i).data.length≤2^256; omega)]
  exact congrArg some (bytesObject_payload_list _ _ _ 128)

theorem raw_matched {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (m : ByteView) (offset count : Word) (range : offset.val+count.val≤2^256)
    (bytes : readBytes m offset.val count.val=(encoding G l i).data) :
    logAdapter PhysicalHeapPort.port o m false (encoding G l i).emitter (encoding G l i).count
      (encoding G l i).topics offset count=some (emitObserved o (encoding G l i)) := by
  have actual:=PhysicalHeapPort.load_view m offset count range
  rw [bytes] at actual
  exact logAdapter_exact _ _ _ _ _ _ _ _ _ actual

theorem raw_agreement {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay) :
    logAdapter PhysicalHeapPort.port o (memory G l i) false (encoding G l i).emitter (encoding G l i).count
      (encoding G l i).topics 160 (size G l i)=some (emitObserved o (encoding G l i)) :=
  logAdapter_exact _ _ _ _ _ _ _ _ _ (loaded G l i)

/-- Real VY2 heap realization, membership/placement and exact selected bytes.
No assumption that the caller's heap or memory realizes arbitrary values. -/
theorem raw_encoded {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (h : Source.Heap (env indexed anonymous).layout) (p : Placement h) (es : List (HeapByteEntry h))
    (distinct : (es.map HeapByteEntry.id).Nodup) (e : HeapByteEntry h) (member : e∈es) (base : ByteView)
    (bytes : e.bytes=(encoding G l i).data) :
    logAdapter PhysicalHeapPort.port o (encodeByteHeap p es base) false (encoding G l i).emitter
      (encoding G l i).count (encoding G l i).topics
      (PhysicalHeapPort.payloadOffset h p e.id e.string e.bytes e.found)
      ⟨e.bytes.length,heapByte_length_bound h p e.id e.string e.bytes e.found⟩=
        some (emitObserved o (encoding G l i)) := by
  have loaded:=PhysicalHeapPort.load_encoded h p es distinct e member base
  have raw:=logAdapter_exact PhysicalHeapPort.port o (encodeByteHeap p es base) (encoding G l i).emitter
    (encoding G l i).count (encoding G l i).topics (PhysicalHeapPort.payloadOffset h p e.id e.string e.bytes e.found)
    ⟨e.bytes.length,heapByte_length_bound h p e.id e.string e.bytes e.found⟩ e.bytes loaded
  have sameLog : (⟨(encoding G l i).emitter,(encoding G l i).count,(encoding G l i).topics,e.bytes⟩ : Log)=encoding G l i := by rw [bytes]
  exact raw.trans (congrArg some (congrArg (emitObserved o) sameLog))

theorem source_raw {indexed anonymous Γ Δ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (s : EMState (env indexed anonymous) Δ) r b
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :
    logAdapter PhysicalHeapPort.port o (memory G l i) false (encoding G l i).emitter (encoding G l i).count
      (encoding G l i).topics 160 (size G l i)=some (execute G false l i s r b o shared).2 := by
  rw [execute_run]
  exact raw_agreement G l i o

theorem raw_static {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (m : ByteView) (offset count : Word) :
    logAdapter PhysicalHeapPort.port o m true (encoding G l i).emitter (encoding G l i).count
      (encoding G l i).topics offset count=none := rfl

theorem wrong_window {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (m : ByteView) (offset count : Word) (wrong : Bytes)
    (loaded : PhysicalHeapPort.port.load m offset count=some wrong) (different : wrong≠(encoding G l i).data) :
    logAdapter PhysicalHeapPort.port o m false (encoding G l i).emitter (encoding G l i).count
      (encoding G l i).topics offset count≠some (emitObserved o (encoding G l i)) := by
  rw [logAdapter_exact _ _ _ _ _ _ _ _ _ loaded]
  intro same
  have trace:=congrArg (fun x=>x.trace) (Option.some.inj same)
  change o.trace++[.log ⟨(encoding G l i).emitter,(encoding G l i).count,(encoding G l i).topics,wrong⟩]=
    o.trace++[.log (encoding G l i)] at trace
  have single:=List.append_cancel_left trace
  exact different (congrArg Log.data (Observation.log.inj (List.cons.inj single).1))

end Solidity.Yul.World.IndexedEmitMemory
