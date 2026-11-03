import Solidity.Yul.Views.HeapByteAllocation
import Solidity.Yul.Views.InventorySourceReads

namespace Solidity.Yul.Views

theorem byteAllocatedState_new {E Γ} (s : Source.EMState E Γ) (string : Bool) (bs : List UInt8) :
    (byteAllocatedState s string bs).2.heap.get s.2.heap.next=
      some ⟨heapByteType string,heapByteData E.layout string bs⟩ :=
  Source.Heap.alloc_get s.2.heap _

theorem byteAllocatedState_other {E Γ} (s : Source.EMState E Γ) (string : Bool) (bs : List UInt8)
    (a : Nat) (present : (s.2.heap.cells a).isSome) :
    (byteAllocatedState s string bs).2.heap.get a=s.2.heap.get a :=
  Source.Heap.alloc_other s.2.heap _ (occupied_ne_next s.2.heap a present)

theorem byteAllocatedState_observations {E Γ} (s : Source.EMState E Γ) (string : Bool) (bs : List UInt8) :
    (byteAllocatedState s string bs).1=s.1 ∧
    (byteAllocatedState s string bs).2.ex=s.2.ex ∧
    (byteAllocatedState s string bs).2.events=s.2.events ∧
    (byteAllocatedState s string bs).2.logs=s.2.logs ∧
    (byteAllocatedState s string bs).2.fnLocals=s.2.fnLocals ∧
    (byteAllocatedState s string bs).2.heap.next=s.2.heap.next+1 := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem byteAllocatedState_read_new {E Γ} (s : Source.EMState E Γ) (string : Bool) (bs : List UInt8) :
    (Source.heapBytes s.2.heap.next).run (byteAllocatedState s string bs)=
      (.ok bs,byteAllocatedState s string bs) := by
  apply heapBytes_known
  cases string
  · exact Or.inr (byteAllocatedState_new s false bs)
  · exact Or.inl (byteAllocatedState_new s true bs)

theorem byteAllocatedState_read_old {E Γ} (s : Source.EMState E Γ) (string oldString : Bool)
    (bs old : List UInt8) (a : Nat)
    (found : s.2.heap.get a=some ⟨heapByteType oldString,heapByteData E.layout oldString old⟩) :
    (Source.heapBytes a).run (byteAllocatedState s string bs)=
      (.ok old,byteAllocatedState s string bs) := by
  have present : (s.2.heap.cells a).isSome := by change (s.2.heap.get a).isSome=true; rw [found]; rfl
  have after := (byteAllocatedState_other s string bs a present).trans found
  apply heapBytes_known
  cases oldString
  · exact Or.inr after
  · exact Or.inl after

/-- Actual pointer reads at EVERY owner horizon; no current allocation order
or replacement observation type is imposed. The same theorem serves aliases. -/
theorem byteAllocatedState_new_pointer {E Γ} (s : Source.EMState E Γ) (F : Source.Fr)
    (n : Nat) (string : Bool) (bs : List UInt8) :
    (Source.bytesOfRV F n (.val (Source.Val.memRef (heapByteType_memory string) s.2.heap.next))).run
      (byteAllocatedState s string bs)=(.ok bs,byteAllocatedState s string bs) :=
  byteAllocatedState_read_new s string bs

theorem byteAllocatedState_old_pointer {E Γ} (s : Source.EMState E Γ) (F : Source.Fr) (n : Nat)
    (string oldString : Bool) (bs old : List UInt8) (a : Nat)
    (found : s.2.heap.get a=some ⟨heapByteType oldString,heapByteData E.layout oldString old⟩) :
    (Source.bytesOfRV F n (.val (Source.Val.memRef (heapByteType_memory oldString) a))).run
      (byteAllocatedState s string bs)=(.ok old,byteAllocatedState s string bs) :=
  byteAllocatedState_read_old s string oldString bs old a found

end Solidity.Yul.Views
