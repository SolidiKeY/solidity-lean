import Solidity.Yul.World.HeapWindowBytes
import Solidity.Yul.Views.OwnedBoolFrame

/-! Owned partial-payload returndata copy, distinct from the old whole-object
operation. Destination ownership is checked; strict source bounds never pad. -/
namespace Solidity.Yul.World.HeapWindow
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
open Solidity.Yul.Views
open Solidity.Backend.Environment (writeBytes)
variable {D : Source.Layout} {L T : Address → Source.SPath → Source.STy}

def destination (h : Source.Heap D) (p : Placement h) (a : Nat) (string : Bool) (old : Bytes)
    (found : h.get a = some ⟨heapByteType string,heapByteData D string old⟩)
    (offset : Word) (inside : offset.val ≤ old.length) : Word :=
  ⟨p.address a + 32 + offset.val,by
    have endBound := PhysicalHeapPort.payload_end h p a string old found
    have free := p.free.isLt
    omega⟩

def copyMemoryWindow (entry : Effects D L T) (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old : Bytes)
    (found : h.get a = some ⟨heapByteType string,heapByteData D string old⟩)
    (m : ByteView) (offset source size : Word) : Option ByteView :=
  if inside : offset.val + size.val ≤ old.length then
    copyReturndata PhysicalHeapPort.port entry m (destination h p a string old found offset (by omega)) source size
  else none

theorem copyMemoryWindow_destination (entry : Effects D L T) (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old : Bytes) (found : h.get a = some ⟨heapByteType string,heapByteData D string old⟩) (m : ByteView) (offset source size : Word)
    (outside : ¬ offset.val + size.val ≤ old.length) :
    copyMemoryWindow entry h p a string old found m offset source size = none := by
  simp only [copyMemoryWindow,outside,dite_false]

theorem copyMemoryWindow_source (entry : Effects D L T) (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old : Bytes) (found : h.get a = some ⟨heapByteType string,heapByteData D string old⟩) (m : ByteView) (offset source size : Word)
    (bad : entry.returndata.length < source.val + size.val) :
    copyMemoryWindow entry h p a string old found m offset source size = none := by
  unfold copyMemoryWindow
  split
  · exact copyReturndata_bounds _ _ _ _ _ _ bad
  · rfl

theorem copyMemoryWindow_exact (entry : Effects D L T) (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old bytes : Bytes) (found : h.get a = some ⟨heapByteType string,heapByteData D string old⟩) (m : ByteView) (offset source size : Word)
    (window : returnWindow entry.returndata source.val size.val = some bytes)
    (inside : offset.val + bytes.length ≤ old.length) :
    copyMemoryWindow entry h p a string old found m offset source size =
      some (writeBytes m (p.address a + 32 + offset.val) bytes) := by
  have length := returnWindow_length _ _ _ _ window
  have bound : offset.val + size.val ≤ old.length := by omega
  have range : (destination h p a string old found offset (by omega)).val + bytes.length ≤ 2^256 := by
    have endBound := PhysicalHeapPort.payload_end h p a string old found
    have free := p.free.isLt
    dsimp only [destination]
    omega
  rw [copyMemoryWindow,dif_pos bound,copyReturndata_exact _ _ _ _ _ _ _ window]
  exact TargetMemory.store_exact m _ bytes range

def copyHeapWindow (entry : Effects D L T) (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old : Bytes) (found : h.get a = some ⟨heapByteType string,heapByteData D string old⟩) (m : ByteView) (offset source size : Word) :
    Option (ByteView × Source.Heap D) := do
  let after ← copyMemoryWindow entry h p a string old found m offset source size
  let heap ← heapByteWriteback h p a string old found after
  pure (after,heap)

theorem copyHeapWindow_exact (entry : Effects D L T) (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old bytes : Bytes) (found : h.get a = some ⟨heapByteType string,heapByteData D string old⟩) (m : ByteView) (offset source size : Word)
    (window : returnWindow entry.returndata source.val size.val = some bytes)
    (inside : offset.val + bytes.length ≤ old.length)
    (header : (mload m (p.address a)).val = old.length)
    (reads : readBytes m (p.address a + 32) old.length = old) :
    copyHeapWindow entry h p a string old found m offset source size =
      some (writeBytes m (p.address a + 32 + offset.val) bytes,
        h.write a (heapByteData D string (splice old offset.val bytes)) (heap_ty_of_get h a _ _ found)) := by
  have keep := mload_congr (writeBytes m (p.address a + 32 + offset.val) bytes) m (p.address a)
    (fun i => Solidity.Backend.Environment.writeBytes_frame _ _ _ _ (Or.inl (by have hi:=i.isLt; omega)))
  have head := (congrArg Fin.val keep).trans header
  simp only [copyHeapWindow,copyMemoryWindow_exact _ _ _ _ _ _ _ _ _ _ _ _ window inside,
    bind,Option.bind_some,heapByteWriteback,head,if_true]
  rw [decodeHeapByte_data,head,read_splice m (p.address a + 32) old bytes offset.val reads inside]
  rfl

theorem copyHeapWindow_destination (entry : Effects D L T) (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old : Bytes) (found) (m : ByteView) (offset source size : Word)
    (outside : ¬ offset.val + size.val ≤ old.length) :
    copyHeapWindow entry h p a string old found m offset source size = none := by
  simp only [copyHeapWindow,copyMemoryWindow_destination _ _ _ _ _ _ _ _ _ _ _ outside,bind,Option.bind_none]

theorem copyHeapWindow_source (entry : Effects D L T) (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old : Bytes) (found) (m : ByteView) (offset source size : Word)
    (bad : entry.returndata.length < source.val + size.val) :
    copyHeapWindow entry h p a string old found m offset source size = none := by
  simp only [copyHeapWindow,copyMemoryWindow_source _ _ _ _ _ _ _ _ _ _ _ bad,bind,Option.bind_none]

/-- Every byte outside the actual subwindow, and every other heap cell/type,
remains unchanged; the source object retains its original length. -/
theorem copyHeapWindow_frame (entry : Effects D L T) (h : Source.Heap D) (p : Placement h)
    (a other i : Nat) (string : Bool) (old bytes : Bytes) (found) (m : ByteView) (offset source size : Word)
    (window : returnWindow entry.returndata source.val size.val = some bytes)
    (inside : offset.val + bytes.length ≤ old.length)
    (header : (mload m (p.address a)).val = old.length) (reads : readBytes m (p.address a+32) old.length = old)
    (different : other ≠ a)
    (outside : i < p.address a+32+offset.val ∨ p.address a+32+offset.val+bytes.length ≤ i) :
    (copyHeapWindow entry h p a string old found m offset source size).map
      (fun result => (result.1 i,result.2.get other,result.2.ty,result.2.next)) = some (m i,h.get other,h.ty,h.next) := by
  rw [copyHeapWindow_exact _ _ _ _ _ _ _ _ _ _ _ _ window inside header reads]
  simp only [Option.map_some,Solidity.Backend.Environment.writeBytes_frame _ _ _ _ outside,Source.Heap.write_other h different]
  have types : (h.write a (heapByteData D string (splice old offset.val bytes)) (heap_ty_of_get h a _ _ found)).ty = h.ty :=
    funext (fun b => Source.Heap.write_ty h a b _ _)
  rw [types]
  rfl

def copyStateWindow {E : Source.Env} {Γ : Source.RCtx}
    (entry : Effects E.layout E.lay E.lay) (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (a : Nat) (string : Bool) (old : Bytes)
    (found : s.2.heap.get a = some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (m : ByteView) (offset source size : Word) : Option (ByteView × Source.EMState E Γ) := do
  let after ← copyMemoryWindow entry s.2.heap p a string old found m offset source size
  let state ← heapByteStateWriteback s p a string old found after
  pure (after,state)

theorem copyStateWindow_heap {E : Source.Env} {Γ : Source.RCtx}
    (entry : Effects E.layout E.lay E.lay) (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (a : Nat) (string : Bool) (old : Bytes) (found) (m : ByteView) (offset source size : Word) :
    copyStateWindow entry s p a string old found m offset source size =
      (copyHeapWindow entry s.2.heap p a string old found m offset source size).map
        (fun result => (result.1,withSourceHeap s result.2)) := by
  unfold copyStateWindow copyHeapWindow heapByteStateWriteback
  cases copyMemoryWindow entry s.2.heap p a string old found m offset source size with
  | none => rfl
  | some after =>
    simp only [bind,Option.bind_some]
    cases heapByteWriteback s.2.heap p a string old found after <;> rfl

theorem copyStateWindow_exact {E : Source.Env} {Γ : Source.RCtx}
    (entry : Effects E.layout E.lay E.lay) (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (a : Nat) (string : Bool) (old bytes : Bytes) (found) (m : ByteView) (offset source size : Word)
    (window : returnWindow entry.returndata source.val size.val = some bytes)
    (inside : offset.val + bytes.length ≤ old.length)
    (header : (mload m (p.address a)).val = old.length) (reads : readBytes m (p.address a+32) old.length = old) :
    copyStateWindow entry s p a string old found m offset source size =
      some (writeBytes m (p.address a+32+offset.val) bytes,
        withSourceHeap s (s.2.heap.write a (heapByteData E.layout string (splice old offset.val bytes)) (heap_ty_of_get _ a _ _ found))) := by
  rw [copyStateWindow_heap,copyHeapWindow_exact _ _ _ _ _ _ _ _ _ _ _ _ window inside header reads]
  rfl

theorem copyStateWindow_memOK {E : Source.Env} {Γ : Source.RCtx}
    (H : Source.HeapTy) (entry : Effects E.layout E.lay E.lay) (s out : Source.EMState E Γ)
    (p : Placement s.2.heap) (a : Nat) (string : Bool) (old : Bytes) (found)
    (m after : ByteView) (offset source size : Word)
    (success : copyStateWindow entry s p a string old found m offset source size = some (after,out))
    (ok : Source.MemOK E H s) : Source.MemOK E H out := by
  obtain ⟨mid,hc,rest⟩ := Option.bind_eq_some_iff.mp success
  obtain ⟨state,hw,pair⟩ := Option.bind_eq_some_iff.mp rest
  have eq := Option.some.inj pair
  cases eq
  exact heapByteStateWriteback_MemOK E H s out p a string old found after hw ok

theorem copyStateWindow_prefix {E : Source.Env} {Γ : Source.RCtx}
    (entry : Effects E.layout E.lay E.lay) (s out : Source.EMState E Γ)
    (p : Placement s.2.heap) (a : Nat) (string : Bool) (old : Bytes) (found)
    (m after : ByteView) (offset source size : Word)
    (success : copyStateWindow entry s p a string old found m offset source size = some (after,out)) :
    out.1 = s.1 ∧ out.2.ex = s.2.ex ∧ out.2.events = s.2.events ∧ out.2.logs = s.2.logs ∧ out.2.fnLocals = s.2.fnLocals := by
  obtain ⟨mid,hc,rest⟩ := Option.bind_eq_some_iff.mp success
  obtain ⟨state,hw,pair⟩ := Option.bind_eq_some_iff.mp rest
  have eq := Option.some.inj pair
  cases eq
  obtain ⟨heap,hheap,he⟩ := Option.map_eq_some_iff.mp hw
  subst out
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Carry actual residual and owned-byte journals and full observations through
this caller-memory action. No execution-only projection substitutes for them. -/
def copyCoupledWindow {E : Source.Env} {Γ : Source.RCtx}
    (entry : ObservedEffects E.layout E.lay E.lay) (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (a : Nat) (string : Bool) (old : Bytes) (found : s.2.heap.get a = some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (r : ResidualJournal complementCarrierOwnership) (encoding : BoolEncodingJournal)
    (_sameExecution : entry.effects.execution = s.2.ex) (m : ByteView) (offset source size : Word) :=
  (copyStateWindow entry.effects s p a string old found m offset source size).map
    (fun result => (result,(r,encoding),entry))

end Solidity.Yul.World.HeapWindow
