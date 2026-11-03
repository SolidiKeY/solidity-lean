import Solidity.Yul.World.IndexedEmitMemory

/-! Inhabited real matching source-heap realization for selected-local logs.
Only this explicitly constructed heap/placement is certified, not all heaps. -/
namespace Solidity.Yul.World.IndexedEmitHeap
open Solidity.Source
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.IndexedEmitPort
open Solidity.Yul.World.ScalarEmitPort (env)

def heap {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint) : Source.Heap (env indexed anonymous).layout :=
  (Source.Heap.empty.alloc ⟨.bytes .memory,.bytes (encoding G l i).data⟩).1

theorem present_zero {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (a : Nat) (h : ((heap G l i).cells a).isSome) : a=0 := by
  by_cases same : a=0
  · exact same
  · simp only [heap,Source.Heap.alloc,Source.Heap.empty,if_neg same,Option.isSome_none,Bool.false_eq_true] at h

def placement {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint) : Placement (heap G l i) where
  address _:=128
  shape _:=.bytes (encoding G l i).data.length
  free:=⟨128+(MemoryShape.bytes (encoding G l i).data.length).size,by
    change 128+(32+((encoding G l i).data.length+31)/32*32)<2^256
    have bound:=IndexedEmitMemory.data_bound G l i
    omega⟩
  free_start:=by change 128≤128+(MemoryShape.bytes (encoding G l i).data.length).size; omega
  distinct a b ha hb _ := (present_zero G l i a ha).trans (present_zero G l i b hb).symm
  typed a τ d found := by
    by_cases same : a=0
    · subst a
      change some (⟨.bytes .memory,.bytes (encoding G l i).data⟩ : Σ σ,Source.Data (env indexed anonymous).layout σ)=some ⟨τ,d⟩ at found
      cases found
      exact HasMemoryShape.bytes (encoding G l i).data
    · simp only [heap,Source.Heap.alloc,Source.Heap.empty,if_neg same] at found
      cases found
  starts _ _:=by decide
  ends _ _:=Nat.le_refl _
  separate a b ha hb hn := False.elim (hn ((present_zero G l i a ha).trans (present_zero G l i b hb).symm))

def entry {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint) : HeapByteEntry (heap G l i) :=
  ⟨0,false,(encoding G l i).data,rfl⟩

def physical {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint) : ByteView :=
  encodeByteHeap (placement G l i) [entry G l i]
    (mstore (mstore (fun _=>0xa5) 64 (placement G l i).free) 96 0)

def caller {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint) : EMState (env indexed anonymous) [.bytes .memory] :=
  ⟨ScalarEmitChecks.locals indexed anonymous,{(ScalarEmitChecks.caller indexed anonymous).2 with heap:=heap G l i}⟩

theorem caller_memOK {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint) :
    Source.MemOK (env indexed anonymous) (heap G l i).ty (caller G l i) := by
  have ok : HeapOK (E:=env indexed anonymous) (heap G l i) := HeapOK.alloc HeapOK.empty (.bytes (encoding G l i).data)
  have shaped : HeapShaped (E:=env indexed anonymous) (heap G l i) :=
    HeapShaped.alloc (E:=env indexed anonymous) (x:=⟨.bytes .memory,.bytes (encoding G l i).data⟩) HeapShaped.empty trivial
  have inner : HeapInner (E:=env indexed anonymous) (heap G l i) :=
    HeapInner.alloc (E:=env indexed anonymous) (x:=⟨.bytes .memory,.bytes (encoding G l i).data⟩) HeapInner.empty trivial
  exact ⟨⟨⟨ok,HeapTy.Le.refl _⟩,⟨⟨.bytes .memory,rfl,rfl⟩,trivial⟩⟩,shaped,inner⟩

theorem source_heap_raw {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint) :
    logAdapter PhysicalHeapPort.port (ScalarEmitChecks.observed indexed anonymous) (physical G l i) false
      (encoding G l i).emitter (encoding G l i).count (encoding G l i).topics
      (PhysicalHeapPort.payloadOffset (heap G l i) (placement G l i) 0 false (encoding G l i).data rfl)
      ⟨(encoding G l i).data.length,heapByte_length_bound (heap G l i) (placement G l i) 0 false (encoding G l i).data rfl⟩=
        some (execute G false l i (caller G l i) CallerFrameChecks.residual CallerFrameChecks.encoding
          (ScalarEmitChecks.observed indexed anonymous) rfl).2 := by
  rw [execute_run]
  exact IndexedEmitMemory.raw_encoded G l i _ (heap G l i) (placement G l i) [entry G l i]
    (by simp only [List.map_cons,List.map_nil,List.nodup_cons,List.not_mem_nil,List.nodup_nil,not_false_eq_true,and_self])
    (entry G l i) (by exact List.mem_cons_self) _ rfl

theorem aliases {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint) :
    (Source.bytesOfRV (E:=env indexed anonymous) (ScalarEmitPort.frame false) 1
      (.val ((caller G l i).1.get .here))).run (caller G l i)=(.ok (encoding G l i).data,caller G l i) ∧
    (Source.bytesOfRV (E:=env indexed anonymous) (ScalarEmitPort.frame false) 1
      (.val ((caller G l i).2.fnLocals.2.get .here))).run (caller G l i)=(.ok (encoding G l i).data,caller G l i) := ⟨rfl,rfl⟩

end Solidity.Yul.World.IndexedEmitHeap
