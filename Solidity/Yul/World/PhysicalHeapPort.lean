import Solidity.Yul.World.ByteMemory
import Solidity.Yul.World.AdapterRules
import Solidity.Yul.Views.ByteHeapRealization
import Solidity.Yul.Views.MemoryImages
import Solidity.Yul.Views.HeapByteMemOK

/-! Actual VY2 heap views consumed by raw-world ports. No second memory/state,
allocation policy or assumed universal MemOK/world adequacy. -/
namespace Solidity.Yul.World.PhysicalHeapPort
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
open Solidity.Yul.Views
open Solidity.Backend.Environment (writeBytes readMemory)
variable {D : Source.Layout} {L T : Address → Source.SPath → Source.STy}

/-- ByteView is definitionally the existing byte port's carrier. -/
abbrev port : BytePort ByteView := TargetMemory.port

theorem load_view (m : ByteView) (offset size : Word) (range : offset.val + size.val ≤ 2^256) :
    port.load m offset size = some (readBytes m offset.val size.val) :=
  TargetMemory.load_exact m offset size range

theorem payload_end (h : Source.Heap D) (p : Placement h) (a : Nat) (string : Bool) (bs : Bytes)
    (found : h.get a = some ⟨heapByteType string,heapByteData D string bs⟩) :
    p.address a + 32 + bs.length ≤ p.free.val := by
  have present : (h.cells a).isSome := by change (h.get a).isSome = true; rw [found]; rfl
  have bound := p.ends a present
  rw [heapByte_placement_shape h p a string bs found] at bound
  have live := byte_shape_live_bound bs.length
  omega

def payloadOffset (h : Source.Heap D) (p : Placement h) (a : Nat) (string : Bool) (bs : Bytes)
    (found : h.get a = some ⟨heapByteType string,heapByteData D string bs⟩) : Word :=
  ⟨p.address a + 32,by have he := payload_end h p a string bs found; have hf := p.free.isLt; omega⟩

theorem load_encoded (h : Source.Heap D) (p : Placement h) (es : List (HeapByteEntry h))
    (distinct : (es.map HeapByteEntry.id).Nodup) (e : HeapByteEntry h) (member : e ∈ es) (m : ByteView) :
    port.load (encodeByteHeap p es m) (payloadOffset h p e.id e.string e.bytes e.found)
      ⟨e.bytes.length,heapByte_length_bound h p e.id e.string e.bytes e.found⟩ = some e.bytes := by
  rw [load_view _ _ _ (by have he := payload_end h p e.id e.string e.bytes e.found; have hf := p.free.isLt; dsimp only [payloadOffset]; omega)]
  exact congrArg some (encodeByteHeap_reads p es distinct m e member).2

/-- Actual strict source window, concrete byte write, then actual source-heap
writeback. Both physical memory and the complete typed heap are returned. -/
def copyWriteback (entry : Effects D L T) (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old : Bytes)
    (found : h.get a = some ⟨heapByteType string,heapByteData D string old⟩)
    (m : ByteView) (source size : Word) : Option (ByteView × Source.Heap D) := do
  let after ← copyReturndata port entry m (payloadOffset h p a string old found) source size
  let heap ← heapByteWriteback h p a string old found after
  pure (after,heap)

/-- Same-length selected payload copy cannot touch its header. Layout, source
window and length premises are real; no growth/allocator theorem is inferred. -/
theorem copyWriteback_exact (entry : Effects D L T) (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old bytes : Bytes)
    (found : h.get a = some ⟨heapByteType string,heapByteData D string old⟩)
    (m : ByteView) (source size : Word)
    (window : returnWindow entry.returndata source.val size.val = some bytes)
    (same : bytes.length = old.length) (header : (mload m (p.address a)).val = old.length) :
    copyWriteback entry h p a string old found m source size =
      some (writeBytes m (p.address a + 32) bytes,
        h.write a (heapByteData D string bytes) (heap_ty_of_get h a _ _ found)) := by
  have range : (payloadOffset h p a string old found).val + bytes.length ≤ 2^256 := by
    have he := payload_end h p a string old found
    have hf := p.free.isLt
    dsimp only [payloadOffset]
    omega
  have keep : mload (writeBytes m (p.address a + 32) bytes) (p.address a) = mload m (p.address a) := by
    apply mload_congr
    intro i
    exact Solidity.Backend.Environment.writeBytes_frame _ _ _ _ (Or.inl (by have hi := i.isLt; omega))
  have head : (mload (writeBytes m (p.address a + 32) bytes) (p.address a)).val = old.length :=
    (congrArg Fin.val keep).trans header
  have payload : readBytes (writeBytes m (p.address a + 32) bytes) (p.address a + 32) bytes.length = bytes :=
    Solidity.Backend.Environment.read_written _ _ _
  have stored : port.store m (payloadOffset h p a string old found) bytes =
      some (writeBytes m (p.address a + 32) bytes) :=
    TargetMemory.store_exact m (payloadOffset h p a string old found) bytes range
  simp only [copyWriteback,copyReturndata_exact _ _ _ _ _ _ _ window,
    stored,bind,Option.bind_some,heapByteWriteback,head,if_true]
  rw [decodeHeapByte_data,head,← same,payload]
  rfl

/-- No successful copy exists when the last-frame source window is invalid,
even for size0. A bad request is not silently converted to a heap no-op. -/
theorem copyWriteback_bounds (entry : Effects D L T) (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old : Bytes)
    (found : h.get a = some ⟨heapByteType string,heapByteData D string old⟩)
    (m : ByteView) (source size : Word) (bad : entry.returndata.length < source.val + size.val) :
    copyWriteback entry h p a string old found m source size = none := by
  simp only [copyWriteback,copyReturndata_bounds _ _ _ _ _ _ bad,bind,Option.bind_none]

theorem copyWriteback_frame (entry : Effects D L T) (h : Source.Heap D) (p : Placement h)
    (a other i : Nat) (string : Bool) (old bytes : Bytes)
    (found : h.get a = some ⟨heapByteType string,heapByteData D string old⟩)
    (m : ByteView) (source size : Word)
    (window : returnWindow entry.returndata source.val size.val = some bytes)
    (same : bytes.length = old.length) (header : (mload m (p.address a)).val = old.length)
    (different : other ≠ a) (outside : i < p.address a + 32 ∨ p.address a + 32 + bytes.length ≤ i) :
    (copyWriteback entry h p a string old found m source size).map
      (fun result => (result.1 i,result.2.get other,result.2.ty,result.2.next)) =
      some (m i,h.get other,h.ty,h.next) := by
  rw [copyWriteback_exact entry h p a string old bytes found m source size window same header]
  simp only [Option.map_some,Solidity.Backend.Environment.writeBytes_frame _ _ _ _ outside,
    Source.Heap.write_other h different]
  have types : (h.write a (heapByteData D string bytes) (heap_ty_of_get h a _ _ found)).ty = h.ty :=
    funext (fun b => Source.Heap.write_ty h a b _ _)
  rw [types]
  rfl

/-- Reuse the real V04b state writeback; all non-heap fields stay in the
original EMState. No Source-world journal is substituted for physical memory. -/
def copyStateWriteback {E : Source.Env} {Γ : Source.RCtx}
    (entry : Effects E.layout E.lay E.lay) (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (a : Nat) (string : Bool) (old : Bytes)
    (found : s.2.heap.get a = some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (m : ByteView) (source size : Word) : Option (ByteView × Source.EMState E Γ) := do
  let after ← copyReturndata port entry m (payloadOffset s.2.heap p a string old found) source size
  let state ← heapByteStateWriteback s p a string old found after
  pure (after,state)

theorem copyStateWriteback_memOK {E : Source.Env} {Γ : Source.RCtx}
    (H : Source.HeapTy) (entry : Effects E.layout E.lay E.lay) (s out : Source.EMState E Γ)
    (p : Placement s.2.heap) (a : Nat) (string : Bool) (old : Bytes)
    (found : s.2.heap.get a = some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (m after : ByteView) (source size : Word)
    (success : copyStateWriteback entry s p a string old found m source size = some (after,out))
    (ok : Source.MemOK E H s) : Source.MemOK E H out := by
  obtain ⟨mid,hc,rest⟩ := Option.bind_eq_some_iff.mp success
  obtain ⟨state,hw,pair⟩ := Option.bind_eq_some_iff.mp rest
  have eq := Option.some.inj pair
  cases eq
  exact heapByteStateWriteback_MemOK E H s out p a string old found after hw ok

theorem copyStateWriteback_prefix {E : Source.Env} {Γ : Source.RCtx}
    (entry : Effects E.layout E.lay E.lay) (s out : Source.EMState E Γ)
    (p : Placement s.2.heap) (a : Nat) (string : Bool) (old : Bytes)
    (found : s.2.heap.get a = some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (m after : ByteView) (source size : Word)
    (success : copyStateWriteback entry s p a string old found m source size = some (after,out)) :
    out.1 = s.1 ∧ out.2.ex = s.2.ex ∧ out.2.events = s.2.events ∧ out.2.logs = s.2.logs := by
  obtain ⟨mid,hc,rest⟩ := Option.bind_eq_some_iff.mp success
  obtain ⟨state,hw,pair⟩ := Option.bind_eq_some_iff.mp rest
  have eq := Option.some.inj pair
  cases eq
  obtain ⟨heap,hheap,he⟩ := Option.map_eq_some_iff.mp hw
  subst out
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem copyWriteback_reserved (h : Source.Heap D) (p : Placement h) (a : Nat) (string : Bool) (old bytes : Bytes)
    (found : h.get a = some ⟨heapByteType string,heapByteData D string old⟩)
    (m : ByteView) (reserved : ReservedOK m p.free) : ReservedOK (writeBytes m (p.address a + 32) bytes) p.free := by
  have present : (h.cells a).isSome := by change (h.get a).isSome = true; rw [found]; rfl
  have start := p.starts a present
  constructor
  · have keep := mload_congr (writeBytes m (p.address a + 32) bytes) m 64
      (fun i => Solidity.Backend.Environment.writeBytes_frame _ _ _ _ (Or.inl (by have hi:=i.isLt; omega)))
    exact (congrArg Fin.val keep).trans reserved.1
  · intro i
    rw [Solidity.Backend.Environment.writeBytes_frame _ _ _ _ (Or.inl (by have hi:=i.isLt; omega))]
    exact reserved.2 i

/-- Lean-only exact normal raw-copy rule instantiated with the ACTUAL VY2
ByteView. Source heap writeback/MemOK are separate proved obligations above. -/
theorem raw_copy_rule (entry : ObservedEffects D L T) (m : ByteView) (destination source size : Word)
    (bytes : Bytes) (window : returnWindow entry.effects.returndata source.val size.val = some bytes)
    (range : destination.val + bytes.length ≤ 2^256) :
    AdapterRules.Box (AdapterRules.CopyStep port destination source size)
      (fun after => after.observed = entry ∧ after.memory = writeBytes m destination.val bytes) ⟨entry,m⟩ := by
  apply AdapterRules.copy_step_eq
  rw [copyReturndata_exact _ _ _ _ _ _ _ window]
  exact TargetMemory.store_exact _ _ _ range

/-- A selected raw-copy effect preserves every read of another actual typed
MemoryImage, using Placement separation rather than a supplied frame law. -/
theorem copyWriteback_other_image (entry : Effects D L T) (h : Source.Heap D) (p : Placement h)
    (a other : Nat) (string : Bool) (old bytes : Bytes)
    (found : h.get a = some ⟨heapByteType string,heapByteData D string old⟩)
    (m : ByteView) (source size : Word)
    (window : returnWindow entry.returndata source.val size.val = some bytes)
    (same : bytes.length = old.length) (header : (mload m (p.address a)).val = old.length)
    (after : ByteView) (out : Source.Heap D)
    (success : copyWriteback entry h p a string old found m source size = some (after,out))
    {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d)
    (otherFound : h.get other = some ⟨τ,d⟩) (different : other ≠ a)
    (reads : image.Reads m (p.address other)) : image.Reads after (p.address other) := by
  rw [copyWriteback_exact entry h p a string old bytes found m source size window same header] at success
  have pair := Prod.mk.inj (Option.some.inj success)
  rw [← pair.1]
  have present : (h.cells a).isSome := by change (h.get a).isSome = true; rw [found]; rfl
  have otherPresent : (h.cells other).isSome := by change (h.get other).isSome = true; rw [otherFound]; rfl
  have live : 32 + bytes.length ≤ (p.shape a).size := by
    rw [heapByte_placement_shape h p a string old found,same]
    exact byte_shape_live_bound old.length
  have fit := image.fits p other otherFound
  apply image.reads_congr _ m _ _ reads
  intro i hi
  apply Solidity.Backend.Environment.writeBytes_frame
  rcases p.separate a other present otherPresent (fun eq => different eq.symm) with before | behind
  · exact Or.inr (by omega)
  · exact Or.inl (by omega)

end Solidity.Yul.World.PhysicalHeapPort
