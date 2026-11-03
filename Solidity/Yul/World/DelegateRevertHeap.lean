import Solidity.Yul.World.DelegateRevertPort
namespace Solidity.Yul.World.DelegateRevertHeap
open Solidity.Source
open Solidity.Roadmap (Word Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Backend.Environment (writeBytes)

def copied {Γ} (s : EMState env Γ) (e : HeapByteEntry s.2.heap) (offset : Word) (bytes : Bytes) : EMState env Γ :=
  withSourceHeap s (s.2.heap.write e.id (heapByteData env.layout e.string (HeapWindow.splice e.bytes offset.val bytes))
    (heap_ty_of_get _ e.id _ _ e.found))

theorem image_exact {Γ} (G : Glob env) (s : EMState env Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal) (o : ObservedEffects env.layout env.lay env.lay) (p : Placement s.2.heap)
    (e : HeapByteEntry s.2.heap) (m : ByteView) (offset : Word) (bytes : Bytes) :
    HeapOutputTransport.image (DelegateRevertPort.completed G s r b o) s.2.heap
      (DelegateRevertPort.heap_eq G s r b o) p e m offset bytes=
      (DelegateRevertPort.completed G s r b o,some ((writeBytes m (p.address e.id+32+offset.val) bytes,
        copied s e offset bytes),(r,b),(DelegateRevertPort.completed G s r b o).2)) := rfl

theorem fields {Γ} (s : EMState env Γ) (e : HeapByteEntry s.2.heap) (offset : Word) (bytes : Bytes) :
    (copied s e offset bytes).1=s.1 ∧ (copied s e offset bytes).2.ex=s.2.ex ∧
    (copied s e offset bytes).2.events=s.2.events ∧ (copied s e offset bytes).2.logs=s.2.logs ∧
    (copied s e offset bytes).2.fnLocals=s.2.fnLocals ∧ (copied s e offset bytes).2.heap.next=s.2.heap.next :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem alias {Γ} (s : EMState env Γ) (e : HeapByteEntry s.2.heap) (offset : Word) (bytes : Bytes)
    (a : Nat) (same : a=e.id) :
    (copied s e offset bytes).2.heap.get a=some ⟨heapByteType e.string,
      heapByteData env.layout e.string (HeapWindow.splice e.bytes offset.val bytes)⟩ := by
  rw [same]
  exact Source.Heap.write_get s.2.heap e.id
    (heapByteData env.layout e.string (HeapWindow.splice e.bytes offset.val bytes)) (heap_ty_of_get _ e.id _ _ e.found)

theorem other {Γ} (s : EMState env Γ) (e : HeapByteEntry s.2.heap) (offset : Word) (bytes : Bytes)
    (a : Nat) (different : a≠e.id) : (copied s e offset bytes).2.heap.get a=s.2.heap.get a :=
  Source.Heap.write_other s.2.heap different
    (heapByteData env.layout e.string (HeapWindow.splice e.bytes offset.val bytes)) (heap_ty_of_get _ e.id _ _ e.found)

theorem types {Γ} (s : EMState env Γ) (e : HeapByteEntry s.2.heap) (offset : Word) (bytes : Bytes) :
    (copied s e offset bytes).2.heap.ty=s.2.heap.ty := by
  funext a
  exact Source.Heap.write_ty s.2.heap e.id a
    (heapByteData env.layout e.string (HeapWindow.splice e.bytes offset.val bytes)) (heap_ty_of_get _ e.id _ _ e.found)

theorem memOK {Γ} (s : EMState env Γ) (e : HeapByteEntry s.2.heap) (offset : Word) (bytes : Bytes)
    (H : Source.HeapTy) (ok : Source.MemOK env H s) : Source.MemOK env H (copied s e offset bytes) :=
  heapByte_write_MemOK env H s e.id e.string (HeapWindow.splice e.bytes offset.val bytes) (heap_ty_of_get _ e.id _ _ e.found) ok

theorem image_empty {Γ} (G : Glob env) (s : EMState env Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal) (o : ObservedEffects env.layout env.lay env.lay) (p : Placement s.2.heap)
    (e : HeapByteEntry s.2.heap) (m : ByteView) (offset : Word) :
    HeapOutputTransport.image (DelegateRevertPort.completed G s r b o) s.2.heap
      (DelegateRevertPort.heap_eq G s r b o) p e m offset []=
      (DelegateRevertPort.completed G s r b o,some ((m,s),(r,b),(DelegateRevertPort.completed G s r b o).2)) := by
  rw [image_exact]
  simp only [Solidity.Backend.Environment.writeBytes,copied,HeapWindow.splice_empty,
    heap_write_unchanged _ _ _ _ e.found,withSourceHeap_unchanged]
end Solidity.Yul.World.DelegateRevertHeap
