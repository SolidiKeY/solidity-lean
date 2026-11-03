import Solidity.Yul.Adapters.MemoryAgreement
import Solidity.Yul.Adapters.P6ByteMemory
import Solidity.Yul.Adapters.SourceSliceFrame
import Solidity.Yul.Views.EnumeratedMemory

/-! Construct the actual P6 byte frame from a computed, complete ordinary
Source heap inventory. Allocation provenance remains the existing Placement
and RetainedAllocation input, not a conclusion about arbitrary executions. -/
namespace Solidity.Yul.Adapters.FrameHeap
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views
variable {C : Contract} {Δ : Ctx}

theorem encoded_fits {D : Source.Layout} {h : Source.Heap D}
    (carrier : FrameMem C Δ) (p : Placement h) (es : List (MixedHeapEntry p))
    (residual : ByteView) (fits : MemoryAgreement.Fits carrier residual)
    (room : p.free.val≤carrier.highWaterWords*32) :
    MemoryAgreement.Fits carrier (encodeMixedHeap p es residual) := by
  intro k high
  rw [encodeMixedHeap_residual]
  · exact fits k high
  · intro e member
    have present : (h.cells e.id).isSome := by
      change (h.get e.id).isSome=true
      rw [e.found];rfl
    have endBound:=p.ends e.id present
    have span:=e.image.fits p e.id e.found
    right
    omega

/-- Projection for actual entries; completeness is checked by prepareFrame,
not inferred by this internal construction from a filtered list. -/
def frameOf {D : Source.Layout} {h : Source.Heap D}
    (carrier : FrameMem C Δ) (p : Placement h) (es : List (MixedHeapEntry p))
    (residual : ByteView) (fits : MemoryAgreement.Fits carrier residual)
    (room : p.free.val≤carrier.highWaterWords*32) : FrameMem C Δ :=
  MemoryAgreement.writeback carrier (encodeMixedHeap p es residual)
    (encoded_fits carrier p es residual fits room)

/-- Exact unsupported occupied-ID errors are retained; an occupied cell is not
silently skipped and called a whole heap. No new traversal bound. -/
def prepareFrame {D : Source.Layout} {h : Source.Heap D}
    (carrier : FrameMem C Δ) (p : Placement h) (residual : ByteView)
    (fits : MemoryAgreement.Fits carrier residual) (room : p.free.val≤carrier.highWaterWords*32) :
    Except (List Nat) (FrameMem C Δ) :=
  (prepareHeapInventory p).map (fun es=>frameOf carrier p es residual fits room)

theorem frameOf_bytes {D : Source.Layout} {h : Source.Heap D}
    (carrier : FrameMem C Δ) (p : Placement h) (es : List (MixedHeapEntry p))
    (residual : ByteView) (fits : MemoryAgreement.Fits carrier residual)
    (room : p.free.val≤carrier.highWaterWords*32) :
    frameBytes (frameOf carrier p es residual fits room)=encodeMixedHeap p es residual :=
  MemoryAgreement.encode_decode _ _ _

/-- Constructive complete-heap physical realization and WHOLE actual Source
roundtrip for the existing canonical supported ordinary profile. No supplied
inventory, coverage, view equality, inverse or final-state adequacy premise. -/
theorem owner_roundtrip {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin)
    (p : Placement s.2.heap) (history : RetainedAllocation allocated p)
    (ok : Source.MemOK E H s)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (carrier : FrameMem C Δ) (residual : ByteView) (fits : MemoryAgreement.Fits carrier residual)
    (room : p.free.val≤carrier.highWaterWords*32) :
    ∃ image : FrameMem C Δ,
      prepareFrame carrier p residual fits room=.ok image ∧
      CoversMixedHeap (generatedHeapEntries p) ∧
      ((generatedHeapEntries p).map MixedHeapEntry.id).Nodup ∧
      frameBytes image=encodeMixedHeap p (generatedHeapEntries p) residual ∧
      enumeratedMemoryWriteback s allocated p history (frameBytes image)=.ok (some (.ok (),s)) ∧
      image.st=carrier.st ∧ image.key=carrier.key ∧ image.capacity=carrier.capacity ∧
      image.highWaterWords=carrier.highWaterWords := by
  have computed:=ownerMemOK_prepares_inventory H s p ok supported
  have facts:=prepareHeapInventory_ok p (generatedHeapEntries p) computed
  let image:=frameOf carrier p (generatedHeapEntries p) residual fits room
  have bytes : frameBytes image=encodeMixedHeap p (generatedHeapEntries p) residual := frameOf_bytes _ _ _ _ _ _
  refine ⟨image,?_,facts.2.1,facts.2.2,bytes,?_,rfl,rfl,rfl,rfl⟩
  · unfold prepareFrame
    rw [computed];rfl
  · rw [bytes]
    exact (ownerMemory_unchanged H s allocated p history residual ok supported).2

/-- Exact reserved words and ALL residual bytes follow from the constructed
view, independently of source contents or allocator execution. -/
theorem frame_reserved {D : Source.Layout} {h : Source.Heap D}
    (carrier : FrameMem C Δ) (p : Placement h) (es : List (MixedHeapEntry p))
    (residual : ByteView) (fits : MemoryAgreement.Fits carrier residual)
    (room : p.free.val≤carrier.highWaterWords*32) (reserved : ReservedOK residual p.free) :
    ReservedOK (frameBytes (frameOf carrier p es residual fits room)) p.free := by
  rw [frameOf_bytes]
  exact encodeMixedHeap_reserved p es residual reserved

theorem frame_residual {D : Source.Layout} {h : Source.Heap D}
    (carrier : FrameMem C Δ) (p : Placement h) (es : List (MixedHeapEntry p))
    (residual : ByteView) (fits : MemoryAgreement.Fits carrier residual)
    (room : p.free.val≤carrier.highWaterWords*32) (k : Nat)
    (outside : ∀ e∈es,k<p.address e.id ∨ p.address e.id+e.image.span≤k) :
    frameBytes (frameOf carrier p es residual fits room) k=residual k := by
  rw [frameOf_bytes]
  exact encodeMixedHeap_residual p es residual k outside
/-- Actual computed preparation/decoding retains its nested error/None/Source
result distinctions. No failure is reclassified as a Yul execution result. -/
def writeback {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (image : FrameMem C Δ) :=
  enumeratedMemoryWriteback s allocated p history (frameBytes image)

/-- Reached actual Source heap and retained Placement plus COMPLETE raw view.
Neither the final heap/view nor its safety is an input obligation. -/
theorem reached {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (image : FrameMem C Δ)
    (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : writeback s allocated p history image=.ok (some result)) :
    ∃ realized : InventoryRealization allocated,
      result=(.ok (),withSourceHeap s realized.heap) ∧ CoversMixedHeap realized.entries ∧
      (realized.entries.map MixedHeapEntry.id).Nodup ∧
      encodeMixedHeap realized.placement realized.entries (frameBytes image)=frameBytes image ∧
      realized.heap.ty=s.2.heap.ty ∧ realized.heap.next=s.2.heap.next ∧
      realized.placement.address=p.address ∧ realized.placement.free=p.free ∧
      (∀ H : Source.HeapTy,Source.MemOK E H s → Source.MemOK E H result.2) := by
  obtain ⟨realized,run,coverage,distinct,raw⟩:=enumeratedMemoryWriteback_view s allocated p history _ result step
  obtain ⟨other,runOther,_,types,next,_,_,_⟩:=enumeratedMemoryWriteback_realization s allocated p history _ result step
  have heaps : realized.heap=other.heap := congrArg (fun r : Except Source.Halt Unit × Source.EMState E Γ=>r.2.2.heap)
    (run.symm.trans runOther)
  refine ⟨realized,run,coverage,distinct,raw,?_,?_,?_,?_,?_⟩
  · rw [heaps];exact types
  · rw [heaps];exact next
  · exact realized.history.addresses.trans history.addresses.symm
  · exact realized.history.free.trans history.free.symm
  · intro H ok
    exact enumeratedMemoryWriteback_MemOK H s allocated p history _ result step ok
/-- A successful actual Source writeback can be encoded back into the WHOLE
input physical frame, including residual bytes and all frame metadata. The
only extra bound is the actual reached frame's existing placement capacity;
it is not an allocation provenance or universal dirty-representation claim. -/
theorem reached_frame_roundtrip {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (image : FrameMem C Δ)
    (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : writeback s allocated p history image=.ok (some result))
    (room : p.free.val≤image.highWaterWords*32) :
    ∃ realized : InventoryRealization allocated,
      result=(.ok (),withSourceHeap s realized.heap) ∧
      ∃ reachedRoom : realized.placement.free.val≤image.highWaterWords*32,
        frameOf image realized.placement realized.entries (frameBytes image)
          (MemoryAgreement.fits_view image) reachedRoom=image := by
  obtain ⟨realized,run,coverage,distinct,raw,types,next,addresses,free,ok⟩ :=
    reached s allocated p history image result step
  refine ⟨realized,run,?_,?_⟩
  · exact free ▸ room
  · exact MemoryAgreement.unchanged image _ _ raw

/-- A disjoint raw byte write preserves every actual constructor read of one
object. This is a byte-range premise, not an assumed final source/view law. -/
theorem image_reads_disjoint_write {D : Source.Layout} {h : Source.Heap D}
    {p : Placement h} {τ : Source.STy} {d : Source.Data D τ}
    (image : MemoryImage p d) (m : ByteView) (base offset : Nat) (bs : List UInt8)
    (outside : base+image.span≤offset ∨ offset+bs.length≤base)
    (reads : image.Reads m base) : image.Reads (Environment.writeBytes m offset bs) base := by
  apply image.reads_congr _ m base
  · intro i hi
    exact Environment.writeBytes_frame bs offset (base+i) m (by omega)
  · exact reads

/-- Write an arbitrary finite byte sequence in the complement of the
computed complete object inventory. Every actual Source cell and all
administrative state remain exactly unchanged; the changed residual map is
NOT discarded. Canonical type support and actual initial owner MemOK are
used to derive the inventory/read facts, not supplied as an inverse law.
Object-complement separation alone can include reserved words: this law does
not conclude ReservedOK, frame Fits or memory-safe operation legality. -/
theorem residual_bytes_unchanged {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin)
    (p : Placement s.2.heap) (history : RetainedAllocation allocated p)
    (residual : ByteView) (ok : Source.MemOK E H s)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (offset : Nat) (bs : List UInt8)
    (outside : ∀ e∈generatedHeapEntries p,
      p.address e.id+e.image.span≤offset ∨ offset+bs.length≤p.address e.id) :
    enumeratedMemoryWriteback s allocated p history
      (Environment.writeBytes (encodeMixedHeap p (generatedHeapEntries p) residual) offset bs)=
      .ok (some (.ok (),s)) := by
  have prepared := ownerMemOK_prepares_inventory H s p ok supported
  have facts := prepareHeapInventory_ok p _ prepared
  unfold enumeratedMemoryWriteback
  rw [prepared]
  apply congrArg Except.ok
  apply inventoryStateWriteback_unchanged s allocated p history _ facts.2.1
  · intro e member
    exact supported e.id e.ty e.data e.found
  · intro e member
    exact image_reads_disjoint_write e.image _ _ offset bs (outside e member)
      (encodeMixedHeap_reads p _ facts.2.2 residual e member)

/-- An actual bounded P6 byte write in the computed object complement keeps
the WHOLE Source state, while retaining its changed raw bytes. The actual
span carries capacity; separation does not imply ReservedOK or operation
admissibility and no allocation/reachability theorem is inferred. -/
theorem residual_span_unchanged {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin)
    (p : Placement s.2.heap) (history : RetainedAllocation allocated p)
    (residual : ByteView) (ok : Source.MemOK E H s)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (carrier : FrameMem C Δ) (fits : MemoryAgreement.Fits carrier residual)
    (room : p.free.val≤carrier.highWaterWords*32)
    (span : ByteSpan (frameOf carrier p (generatedHeapEntries p) residual fits room).capacity)
    (bytes : List UInt8) (length : bytes.length=span.length.val.toNat)
    (outside : ∀ e∈generatedHeapEntries p,
      p.address e.id+e.image.span≤span.offset.val.toNat ∨
      span.offset.val.toNat+bytes.length≤p.address e.id) :
    let initial := frameOf carrier p (generatedHeapEntries p) residual fits room
    let reached := P6ByteMemory.writeSpan initial span bytes length
    writeback s allocated p history reached=.ok (some (.ok (),s)) ∧
      frameBytes reached=Environment.writeBytes (encodeMixedHeap p (generatedHeapEntries p) residual)
        span.offset.val.toNat bytes := by
  dsimp only
  have image := P6ByteMemory.write_image
    (frameOf carrier p (generatedHeapEntries p) residual fits room) span bytes length
  rw [frameOf_bytes] at image
  refine ⟨?_,image⟩
  unfold writeback
  rw [image]
  exact residual_bytes_unchanged H s allocated p history residual ok supported
    span.offset.val.toNat bytes outside

/-- Copy an actual Source calldata slice into the computed object complement.
Source evaluation, complete raw image, readback and whole-state heap writeback
are derived together. Bounds are the actual reference/span bounds; no source
admission, allocator or reserved-word safety is inferred from separation. -/
theorem calldata_residual_unchanged {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin)
    (p : Placement s.2.heap) (history : RetainedAllocation allocated p)
    (residual : ByteView) (ok : Source.MemOK E H s)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (carrier : FrameMem C Δ) (fits : MemoryAgreement.Fits carrier residual)
    (room : p.free.val≤carrier.highWaterWords*32)
    (span : ByteSpan (frameOf carrier p (generatedHeapEntries p) residual fits room).capacity)
    (F : Source.Fr) (fuel off len start finish : Nat) (toEnd : Bool)
    (reference : off+len≤F.cd.length) (ordered : start≤if toEnd then len else finish)
    (bound : (if toEnd then len else finish)≤len)
    (length : span.length.val.toNat=(if toEnd then len else finish)-start)
    (outside : ∀ e∈generatedHeapEntries p,
      p.address e.id+e.image.span≤span.offset.val.toNat ∨
      span.offset.val.toNat+span.length.val.toNat≤p.address e.id) :
    let initial := frameOf carrier p (generatedHeapEntries p) residual fits room
    let payload := (F.cd.drop (off+start)).take ((if toEnd then len else finish)-start)
    ∃ image : FrameMem C Δ,
      (SourceSliceFrame.consume initial span F fuel off len start finish toEnd).run s=
        (.ok (payload,some image),s) ∧
      writeback s allocated p history image=.ok (some (.ok (),s)) ∧
      frameBytes image=Environment.writeBytes (encodeMixedHeap p (generatedHeapEntries p) residual)
        span.offset.val.toNat payload ∧
      Environment.readMemory (frameBytes image) span.offset.val.toNat span.length.val.toNat=payload := by
  dsimp only
  obtain ⟨image,run,raw,read,metadata⟩ := SourceSliceFrame.consume_image
    (frameOf carrier p (generatedHeapEntries p) residual fits room) span F
    fuel off len start finish toEnd s reference ordered bound length
  rw [frameOf_bytes] at raw
  refine ⟨image,run,?_,raw,read⟩
  unfold writeback
  rw [raw]
  apply residual_bytes_unchanged H s allocated p history residual ok supported
  intro e member
  have sameLength := (SourceSliceFrame.bounded_payload_length F off len start finish toEnd
    reference ordered bound).trans length.symm
  rw [sameLength]
  exact outside e member

end Solidity.Yul.Adapters.FrameHeap
