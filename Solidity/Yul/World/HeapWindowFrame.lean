import Solidity.Yul.World.HeapWindowPort

namespace Solidity.Yul.World.HeapWindow
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
open Solidity.Yul.Views
open Solidity.Backend.Environment (writeBytes)
variable {D : Source.Layout} {L T : Address → Source.SPath → Source.STy}

theorem window_header (m : ByteView) (base offset : Nat) (bytes : Bytes) :
    mload (writeBytes m (base+32+offset) bytes) base = mload m base :=
  mload_congr _ _ _ (fun i => Solidity.Backend.Environment.writeBytes_frame _ _ _ _ (Or.inl (by have hi:=i.isLt; omega)))

theorem window_reserved (h : Source.Heap D) (p : Placement h) (a : Nat) (string : Bool) (old bytes : Bytes)
    (found : h.get a = some ⟨heapByteType string,heapByteData D string old⟩)
    (m : ByteView) (offset : Nat) (reserved : ReservedOK m p.free) :
    ReservedOK (writeBytes m (p.address a+32+offset) bytes) p.free := by
  have present : (h.cells a).isSome := by change (h.get a).isSome=true; rw [found]; rfl
  have start := p.starts a present
  constructor
  · have keep := mload_congr (writeBytes m (p.address a+32+offset) bytes) m 64
      (fun i => Solidity.Backend.Environment.writeBytes_frame _ _ _ _ (Or.inl (by have hi:=i.isLt; omega)))
    exact (congrArg Fin.val keep).trans reserved.1
  · intro i
    rw [Solidity.Backend.Environment.writeBytes_frame _ _ _ _ (Or.inl (by have hi:=i.isLt; omega))]
    exact reserved.2 i

theorem window_other_image (entry : Effects D L T) (h : Source.Heap D) (p : Placement h)
    (a other : Nat) (string : Bool) (old bytes : Bytes) (found)
    (m : ByteView) (offset source size : Word)
    (window : returnWindow entry.returndata source.val size.val = some bytes)
    (inside : offset.val + bytes.length ≤ old.length)
    (header : (mload m (p.address a)).val = old.length) (payload : readBytes m (p.address a+32) old.length = old)
    (after : ByteView) (out : Source.Heap D)
    (success : copyHeapWindow entry h p a string old found m offset source size = some (after,out))
    {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d)
    (otherFound : h.get other = some ⟨τ,d⟩) (different : other ≠ a)
    (reads : image.Reads m (p.address other)) : image.Reads after (p.address other) := by
  rw [copyHeapWindow_exact _ _ _ _ _ _ _ _ _ _ _ _ window inside header payload] at success
  have pair := Prod.mk.inj (Option.some.inj success)
  rw [← pair.1]
  have present : (h.cells a).isSome := by change (h.get a).isSome=true; rw [found]; rfl
  have otherPresent : (h.cells other).isSome := by change (h.get other).isSome=true; rw [otherFound]; rfl
  have live : 32 + offset.val + bytes.length ≤ (p.shape a).size := by
    rw [heapByte_placement_shape h p a string old found]
    have fit := byte_shape_live_bound old.length
    omega
  have fit := image.fits p other otherFound
  apply image.reads_congr _ m _ _ reads
  intro i hi
  apply Solidity.Backend.Environment.writeBytes_frame
  rcases p.separate a other present otherPresent (fun eq => different eq.symm) with before | behind
  · exact Or.inr (by omega)
  · exact Or.inl (by omega)

theorem copyCoupledWindow_exact {E : Source.Env} {Γ : Source.RCtx}
    (entry : ObservedEffects E.layout E.lay E.lay) (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (a : Nat) (string : Bool) (old bytes : Bytes) (found)
    (r : ResidualJournal complementCarrierOwnership) (encoding : BoolEncodingJournal)
    (sameExecution : entry.effects.execution = s.2.ex) (m : ByteView) (offset source size : Word)
    (window : returnWindow entry.effects.returndata source.val size.val = some bytes)
    (inside : offset.val + bytes.length ≤ old.length)
    (header : (mload m (p.address a)).val = old.length) (payload : readBytes m (p.address a+32) old.length = old) :
    copyCoupledWindow entry s p a string old found r encoding sameExecution m offset source size =
      some ((writeBytes m (p.address a+32+offset.val) bytes,
        withSourceHeap s (s.2.heap.write a (heapByteData E.layout string (splice old offset.val bytes)) (heap_ty_of_get _ a _ _ found))),
        (r,encoding),entry) := by
  rw [copyCoupledWindow,copyStateWindow_exact _ _ _ _ _ _ _ _ _ _ _ _ window inside header payload]
  rfl

/-- Local normal-return copy rule for the real port and derived placement
address. This does not claim source dl/G51 or actual callee reachability. -/
theorem window_copy_rule (entry : ObservedEffects D L T) (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old bytes : Bytes) (found) (m : ByteView) (offset source size : Word)
    (window : returnWindow entry.effects.returndata source.val size.val = some bytes)
    (inside : offset.val + bytes.length ≤ old.length) :
    AdapterRules.Box
      (AdapterRules.CopyStep PhysicalHeapPort.port (destination h p a string old found offset (by omega)) source size)
      (fun after => after.observed=entry ∧ after.memory=writeBytes m (p.address a+32+offset.val) bytes) ⟨entry,m⟩ := by
  apply PhysicalHeapPort.raw_copy_rule
  · exact window
  · have endBound := PhysicalHeapPort.payload_end h p a string old found
    have free := p.free.isLt
    dsimp only [destination]
    omega

theorem copyHeapWindow_zero (entry : Effects D L T) (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old : Bytes) (found) (m : ByteView) (offset source : Word)
    (sourceBound : source.val ≤ entry.returndata.length) (inside : offset.val ≤ old.length)
    (header : (mload m (p.address a)).val = old.length) (payload : readBytes m (p.address a+32) old.length = old) :
    copyHeapWindow entry h p a string old found m offset source 0 = some (m,h) := by
  have window : returnWindow entry.returndata source.val 0 = some [] := by
    simp only [returnWindow,Nat.add_zero,sourceBound,if_true,List.take_zero]
  rw [copyHeapWindow_exact _ _ _ _ _ _ [] _ _ _ _ _ window (by simpa only [List.length_nil,Nat.add_zero] using inside) header payload]
  simp only [Solidity.Backend.Environment.writeBytes,splice_empty,heap_write_unchanged h a _ _ found]

/-- Reuse the producer's actual placement transport for the new typed heap;
never reuse an old heap-indexed placement by an unproved identification. -/
def windowPlacement (h : Source.Heap D) (p : Placement h) (a : Nat) (string : Bool) (old bytes : Bytes)
    (found : h.get a = some ⟨heapByteType string,heapByteData D string old⟩)
    (offset : Word) (inside : offset.val + bytes.length ≤ old.length) :
    Placement (h.write a (heapByteData D string (splice old offset.val bytes)) (heap_ty_of_get h a _ _ found)) :=
  heapWritePlacement h p a (heapByteData D string (splice old offset.val bytes)) (heap_ty_of_get h a _ _ found) (by
    rw [heapByte_placement_shape h p a string old found]
    simpa only [splice_length old bytes offset.val inside] using heapByteData_shape D string (splice old offset.val bytes))

theorem windowPlacement_choices (h : Source.Heap D) (p : Placement h) (a : Nat) (string : Bool) (old bytes : Bytes)
    (found : h.get a = some ⟨heapByteType string,heapByteData D string old⟩)
    (offset : Word) (inside : offset.val + bytes.length ≤ old.length) :
    (windowPlacement h p a string old bytes found offset inside).address=p.address ∧
    (windowPlacement h p a string old bytes found offset inside).shape=p.shape ∧
    (windowPlacement h p a string old bytes found offset inside).free=p.free := ⟨rfl,rfl,rfl⟩

end Solidity.Yul.World.HeapWindow
