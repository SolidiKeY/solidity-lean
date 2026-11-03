import Solidity.Yul.World.StaticEventPortControls

/-! Full-log raw agreement over actual bounded loads/encoded heap views.
No arbitrary caller heap agreement or compilation adequacy is assumed. -/
namespace Solidity.Yul.World.StaticEventRaw
open Solidity.Source
open Solidity.Roadmap (Word Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StaticEventArgs
open Solidity.Yul.World.StaticEventEncoding

theorem encoded_log {D L T} (event : Log) (o : ObservedEffects D L T)
    (m : ByteView) (offset size : Word) (range : offset.val+size.val≤2^256)
    (bytes : readBytes m offset.val size.val=event.data) :
    logAdapter PhysicalHeapPort.port o m false event.emitter event.count event.topics offset size=
      some (emitObserved o event) := by
  have loaded:=PhysicalHeapPort.load_view m offset size range
  exact logAdapter_exact _ _ _ _ _ _ _ _ _ (loaded.trans (congrArg some bytes))

/-- Formatter execution and raw observation agree for arbitrary admitted static
argument lists, full topic words and actual data-window contents. -/
theorem encoding_agreement {E Γ ts} (G : Glob E) (F : Fr) (n : Nat) (declaration : Decl)
    (typed : declaration.paramTys E=some ts) (vs : Vals E.layout ts) (s : EMState E Γ)
    (flags : List Bool) (anonymous : Bool) (shape : metadata declaration=some (flags,anonymous))
    (part : Split E.layout) (partition : split flags vs=some part)
    (words : List Word) (computed : words? part.2.2=some words)
    (fits : (topics (ts:=ts) G declaration anonymous part).length<5)
    (o : ObservedEffects E.layout E.lay E.lay) (m : ByteView) (offset size : Word)
    (range : offset.val+size.val≤2^256)
    (bytes : readBytes m offset.val size.val=Source.abiLayout (words.map (fun w=>(false,wordBytes w)))) :
    let event:=resultLog (ts:=ts) G F declaration anonymous part fits
      (Source.abiLayout (words.map (fun w=>(false,wordBytes w))))
    (encode G F n declaration typed vs).run s=(.ok (some event),s) ∧
      logAdapter PhysicalHeapPort.port o m false event.emitter event.count event.topics offset size=some (emitObserved o event) :=
  ⟨encode_exact G F n declaration typed vs s flags anonymous shape part partition words computed fits,
    encoded_log _ o m offset size range bytes⟩

theorem encoded_heap {D L T} (event : Log) (o : ObservedEffects D L T)
    (h : Source.Heap D) (p : Placement h) (entries : List (HeapByteEntry h))
    (distinct : (entries.map HeapByteEntry.id).Nodup) (e : HeapByteEntry h) (member : e∈entries)
    (base : ByteView) (bytes : e.bytes=event.data) :
    logAdapter PhysicalHeapPort.port o (encodeByteHeap p entries base) false event.emitter event.count event.topics
      (PhysicalHeapPort.payloadOffset h p e.id e.string e.bytes e.found)
      ⟨e.bytes.length,heapByte_length_bound h p e.id e.string e.bytes e.found⟩=some (emitObserved o event) := by
  have loaded:=PhysicalHeapPort.load_encoded h p entries distinct e member base
  exact logAdapter_exact _ _ _ _ _ _ _ _ _ (loaded.trans (congrArg some bytes))

/-- Actual heterogeneous Source execution, complete ordered observer and a real
VY2 view of the same caller heap. Placement/payload matching is explicit. -/
theorem mixed_source_heap {anonymous Δ} (G : Glob (StaticEventControls.env anonymous)) (F : Fr)
    (s : EMState (StaticEventControls.env anonymous) Δ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (StaticEventControls.env anonymous).layout (StaticEventControls.env anonymous).lay
      (StaticEventControls.env anonymous).lay) (shared : o.effects.execution=s.2.ex) (normal : F.static=false)
    (p : Placement s.2.heap) (entries : List (HeapByteEntry s.2.heap))
    (distinct : (entries.map HeapByteEntry.id).Nodup) (e : HeapByteEntry s.2.heap) (member : e∈entries)
    (base : ByteView) (bytes : e.bytes=ReturningCall.output) :
    logAdapter PhysicalHeapPort.port o (encodeByteHeap p entries base) false F.this
      (StaticEventPortControls.log G F).count (StaticEventPortControls.log G F).topics
      (PhysicalHeapPort.payloadOffset s.2.heap p e.id e.string e.bytes e.found)
      ⟨e.bytes.length,heapByte_length_bound s.2.heap p e.id e.string e.bytes e.found⟩=
      some (StaticEventPortControls.run G F s r b o shared).2 := by
  rw [StaticEventPortControls.run_exact G F s r b o shared normal]
  exact encoded_heap (StaticEventPortControls.log G F) o s.2.heap p entries distinct e member base bytes

/-- Explicit inhabited byte view; not a claim that every caller heap contains
this encoding. The encoded_heap/mixed_source_heap theorems state that relation. -/
def memory : ByteView := bytesObjectView ReturningCall.output (by decide) (fun _=>0xa5) 128

theorem loaded : PhysicalHeapPort.port.load memory 160 32=some ReturningCall.output := by
  rw [PhysicalHeapPort.load_view _ _ _ (by decide)]
  exact congrArg some (bytesObject_payload_list _ _ _ 128)

theorem mixed_view {anonymous Δ} (G : Glob (StaticEventControls.env anonymous)) (F : Fr)
    (s : EMState (StaticEventControls.env anonymous) Δ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (StaticEventControls.env anonymous).layout (StaticEventControls.env anonymous).lay
      (StaticEventControls.env anonymous).lay) (shared : o.effects.execution=s.2.ex) (normal : F.static=false) :
    logAdapter PhysicalHeapPort.port o memory false F.this (StaticEventPortControls.log G F).count
      (StaticEventPortControls.log G F).topics 160 32=some (StaticEventPortControls.run G F s r b o shared).2 := by
  rw [StaticEventPortControls.run_exact G F s r b o shared normal]
  exact logAdapter_exact _ _ _ _ _ _ _ _ _ loaded

theorem wrong_region : readBytes memory 288 32≠ReturningCall.output := by decide

theorem wrong_anonymous_topics (G : Glob (StaticEventControls.env true)) (F : Fr) :
    (StaticEventPortControls.log G F).topics.toList≠[(0x70 : Word),1] := by
  change ([1,0x70] : List Word)≠[0x70,1]
  decide
theorem source_heap_agreement {E Γ Δ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (typed : event.paramTys E=some ts) (args : RConvArgs E Γ ts) (l : Locals E.layout Γ)
    (s : EMState E Δ) (vs : Vals E.layout ts)
    (evaluated : (Source.evalConvArgs G F n args).run ⟨l,s.2⟩=(.ok vs,⟨l,s.2⟩))
    (words : List Word) (computed : words? vs=some words) (normal : F.static=false)
    (flags : List Bool) (anonymous : Bool) (shape : metadata event=some (flags,anonymous))
    (part : Split E.layout) (partition : split flags vs=some part)
    (dataWords : List Word) (dataComputed : words? part.2.2=some dataWords)
    (fits : (topics (ts:=ts) G event anonymous part).length<5)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects E.layout E.lay E.lay) (shared : o.effects.execution=s.2.ex)
    (p : Placement s.2.heap) (entries : List (HeapByteEntry s.2.heap))
    (distinct : (entries.map HeapByteEntry.id).Nodup) (e : HeapByteEntry s.2.heap) (member : e∈entries)
    (base : ByteView) (bytes : e.bytes=Source.abiLayout (dataWords.map (fun w=>(false,wordBytes w)))) :
    let result:=resultLog (ts:=ts) G F event anonymous part fits (Source.abiLayout (dataWords.map (fun w=>(false,wordBytes w))))
    logAdapter PhysicalHeapPort.port o (encodeByteHeap p entries base) false result.emitter result.count result.topics
      (PhysicalHeapPort.payloadOffset s.2.heap p e.id e.string e.bytes e.found)
      ⟨e.bytes.length,heapByte_length_bound s.2.heap p e.id e.string e.bytes e.found⟩=
      some (StaticEventPort.execute G F n event typed args l s vs evaluated flags anonymous shape part partition fits r b o shared).2 := by
  dsimp only
  rw [StaticEventPort.execute_normal G F n event typed args l s vs evaluated words computed normal flags anonymous shape part partition dataWords dataComputed fits r b o shared]
  exact encoded_heap (resultLog (ts:=ts) G F event anonymous part fits (Source.abiLayout (dataWords.map (fun w=>(false,wordBytes w))))) o s.2.heap p entries distinct e member base bytes
end Solidity.Yul.World.StaticEventRaw
