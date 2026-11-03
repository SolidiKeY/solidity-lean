import Solidity.Yul.World.MemoryEventWitness

namespace Solidity.Yul.World.MemoryEventRaw
open Solidity.Source
open Solidity.Roadmap (Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StaticEventEncoding (Split metadata topics)
open Solidity.Yul.World.MemoryEventControls

/-- Actual source heap byte/string payload, excluding its physical length word. -/
theorem hash_encoded {E} (G : Glob E) (h : Source.Heap E.layout) (p : Placement h)
    (entries : List (HeapByteEntry h)) (distinct : (entries.map HeapByteEntry.id).Nodup)
    (e : HeapByteEntry h) (member : e∈entries) (base : ByteView) :
    keccak256 G.fixed.evm (encodeByteHeap p entries base) (p.address e.id+32) e.bytes.length=G.fixed.hash e.bytes :=
  MemoryEventTopic.raw_hash G _ _ _ _ (encodeByteHeap_reads p entries distinct base e member).2

def reference {D} {h : Source.Heap D} (e : HeapByteEntry h) : Source.Val D (heapByteType e.string) :=
  .memRef (by cases e.string <;> rfl) e.id

theorem topic_entry {E Γ} (G : Glob E) (F : Fr) (n : Nat) (s : EMState E Γ)
    (p : Placement s.2.heap) (entries : List (HeapByteEntry s.2.heap))
    (distinct : (entries.map HeapByteEntry.id).Nodup) (e : HeapByteEntry s.2.heap) (member : e∈entries)
    (base : ByteView) :
    (MemoryEventTopic.topic G F n (reference e)).run s=
      (.ok (some (keccak256 G.fixed.evm (encodeByteHeap p entries base) (p.address e.id+32) e.bytes.length)),s) := by
  rw [hash_encoded G s.2.heap p entries distinct e member base]
  cases e with
  | mk id string bytes found =>
    cases string with
    | false => exact MemoryEventTopic.bytes_topic G F n id bytes s found
    | true => exact MemoryEventTopic.string_topic G F n id bytes s found

/-- Full dynamic Source observer and raw LOG agree under actual bounded data
bytes. This does not assert arbitrary caller heap allocation/ABI layout. -/
theorem mixed_log {anonymous Δ} (G : Glob (env anonymous)) (F : Fr) (s : EMState (env anonymous) Δ)
    (tagFound : s.2.heap.get 0=some ⟨.bytes .memory,.bytes tag⟩)
    (labelFound : s.2.heap.get 1=some ⟨.string .memory,.string label⟩)
    (dataFound : s.2.heap.get 2=some ⟨.bytes .memory,.bytes blob⟩)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env anonymous).layout (env anonymous).lay (env anonymous).lay)
    (shared : o.effects.execution=s.2.ex) (normal : F.static=false) (m : ByteView)
    (offset size : Solidity.Roadmap.Word) (range : offset.val+size.val≤2^256)
    (bytes : readBytes m offset.val size.val=data) :
    logAdapter PhysicalHeapPort.port o m false F.this (MemoryEventPortControls.log G F).count
      (MemoryEventPortControls.log G F).topics offset size=
      some (MemoryEventPortControls.run G F s tagFound labelFound dataFound r b o shared).2 := by
  rw [MemoryEventPortControls.run_exact G F s tagFound labelFound dataFound r b o shared normal]
  exact StaticEventRaw.encoded_log (MemoryEventPortControls.log G F) o m offset size range bytes
theorem source_log_agreement {E Γ Δ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (typed : event.paramTys E=some ts) (args : RConvArgs E Γ ts) (l : Locals E.layout Γ) (localArgs : LocalEventBoundary.LocalArguments args)
    (s : EMState E Δ) (vs : Vals E.layout ts)
    (evaluated : (Source.evalConvArgs G F n args).run ⟨l,s.2⟩=(.ok vs,⟨l,s.2⟩))
    (legacy : Bytes) (fullCodec : (Source.encodeVals F n false vs.toR).run ⟨Source.L0 E,s.2⟩=(.ok legacy,⟨Source.L0 E,s.2⟩))
    (flags : List Bool) (anonymous : Bool) (shape : metadata event=some (flags,anonymous))
    (part : Split E.layout) (partition : (MemoryEventEncoding.split G F n flags vs).run s=(.ok (some part),s))
    (data : Bytes) (codec : (Source.encodeVals F n false part.2.2.toR).run s=(.ok data,s))
    (fits : (topics (ts:=ts) G event anonymous part).length<5)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects E.layout E.lay E.lay) (shared : o.effects.execution=s.2.ex) (normal : F.static=false)
    (m : ByteView) (offset size : Solidity.Roadmap.Word) (range : offset.val+size.val≤2^256)
    (bytes : readBytes m offset.val size.val=data) :
    let result:=StaticEventEncoding.resultLog (ts:=ts) G F event anonymous part fits data
    logAdapter PhysicalHeapPort.port o m false result.emitter result.count result.topics offset size=
      some (MemoryEventPort.execute G F n event typed args l localArgs s vs evaluated legacy fullCodec flags anonymous shape part partition data codec fits r b o shared).2 := by
  dsimp only
  rw [MemoryEventPort.execute_normal G F n event typed args l localArgs s vs evaluated legacy fullCodec flags anonymous shape part partition data codec fits r b o shared normal]
  exact StaticEventRaw.encoded_log _ o m offset size range bytes
end Solidity.Yul.World.MemoryEventRaw
