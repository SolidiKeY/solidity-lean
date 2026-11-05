import Solidity.Yul.Views.HeapBytePlacement

/-! Concrete transport of the ACTUAL owner MemOK for selected byte/string writes.
This is not all assembly or a whole-memory realization/allocator theorem. Source
locals, world, observations and non-heap state remain the original typed fields. -/
namespace Solidity.Yul.Views

def withSourceHeap {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (heap : Source.Heap E.layout) : Source.EMState E Γ := ⟨s.1, {s.2 with heap := heap}⟩

theorem withSourceHeap_unchanged {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ) :
    withSourceHeap s s.2.heap = s := by
  cases s with
  | mk l s => cases s; rfl

theorem heapByteData_OK (E : Source.Env) (H : Source.HeapTy) (string : Bool) (bs : List UInt8) :
    Source.DataOK E H (heapByteData E.layout string bs) := by
  cases string
  · exact .bytes _
  · exact .string _

theorem heapByte_write_MemOK (E : Source.Env) {Γ : Source.RCtx} (H : Source.HeapTy)
    (s : Source.EMState E Γ) (a : Nat) (string : Bool) (bs : List UInt8)
    (ht : s.2.heap.ty a = some (heapByteType string)) (ok : Source.MemOK E H s) :
    Source.MemOK E H (withSourceHeap s (s.2.heap.write a (heapByteData E.layout string bs) ht)) := by
  have he : (s.2.heap.write a (heapByteData E.layout string bs) ht).ty = s.2.heap.ty :=
    funext (fun b => Source.Heap.write_ty _ _ b _ _)
  have top : Source.Data.Top (E := E) (heapByteData E.layout string bs) := by cases string <;> trivial
  have inner : Source.Data.Inner (E := E) (heapByteData E.layout string bs) := by cases string <;> trivial
  refine ⟨⟨⟨Source.HeapOK.write ok.1.1.heap ht (heapByteData_OK E _ string bs), ?_⟩, ?_⟩,
    Source.HeapShaped.write ok.2.1 ht top, Source.HeapInner.write ok.2.2 ht inner⟩
  · change H.Le (s.2.heap.write a (heapByteData E.layout string bs) ht).ty
    rw [he]
    exact ok.1.1.le
  · change Source.LocalsOK E (s.2.heap.write a (heapByteData E.layout string bs) ht).ty s.1
    rw [he]
    exact ok.1.2

def heapByteStateWriteback {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (a : Nat) (string : Bool) (old : List UInt8)
    (found : s.2.heap.get a = some ⟨heapByteType string, heapByteData E.layout string old⟩)
    (m : ByteView) : Option (Source.EMState E Γ) :=
  (heapByteWriteback s.2.heap p a string old found m).map (withSourceHeap s)

theorem heapByteStateWriteback_MemOK (E : Source.Env) {Γ : Source.RCtx} (H : Source.HeapTy)
    (s out : Source.EMState E Γ) (p : Placement s.2.heap) (a : Nat) (string : Bool) (old : List UInt8)
    (found : s.2.heap.get a = some ⟨heapByteType string, heapByteData E.layout string old⟩)
    (m : ByteView) (e : heapByteStateWriteback s p a string old found m = some out)
    (ok : Source.MemOK E H s) : Source.MemOK E H out := by
  obtain ⟨heap, hw, hs⟩ := Option.map_eq_some_iff.mp e
  subst out
  rw [(heapByteWriteback_success s.2.heap p a string old found m heap hw).2, decodeHeapByte_data]
  exact heapByte_write_MemOK E H s a string _ _ ok

theorem heapByteStateWriteback_unchanged {E : Source.Env} {Γ : Source.RCtx}
    (s : Source.EMState E Γ) (p : Placement s.2.heap) (a : Nat) (string : Bool) (old : List UInt8)
    (found : s.2.heap.get a = some ⟨heapByteType string, heapByteData E.layout string old⟩)
    (m : ByteView) (header : (mload m (p.address a)).val = old.length)
    (payload : readBytes m (p.address a + 32) old.length = old) :
    heapByteStateWriteback s p a string old found m = some s := by
  simp only [heapByteStateWriteback, heapByteWriteback_unchanged _ _ _ _ _ found m header payload,
    Option.map_some, withSourceHeap_unchanged]

/-- Concrete selected-object relation defined by the implemented writeback. -/
def heapByteStateStep (E : Source.Env) (Γ : Source.RCtx) (a : Nat) (string : Bool)
    (old : List UInt8) (m : ByteView) (before after : Source.EMState E Γ) : Prop :=
  ∃ p : Placement before.2.heap,
    ∃ found : before.2.heap.get a = some ⟨heapByteType string, heapByteData E.layout string old⟩,
      heapByteStateWriteback before p a string old found m = some after

theorem heapByteStateStep_preserves (E : Source.Env) (Γ : Source.RCtx) (a : Nat)
    (string : Bool) (old : List UInt8) (m : ByteView) :
    PreservesMemOK E (heapByteStateStep E Γ a string old m) := by
  intro H before after ok step
  obtain ⟨p, found, hw⟩ := step
  exact heapByteStateWriteback_MemOK E H before after p a string old found m hw ok

end Solidity.Yul.Views
