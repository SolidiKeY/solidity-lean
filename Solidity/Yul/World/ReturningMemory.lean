import Solidity.Yul.World.ReturningCall

/-! Two actual byte-heap objects: selector input and independent output buffer.
The view is the producer's encodeByteHeap, with actual placement witnesses. -/
namespace Solidity.Yul.World.ReturningCall
open Solidity.Source
open Solidity.Roadmap (Bytes)
open Solidity.Yul.Views

def old : Bytes := [0xa1,0xb2,0xc3,0xd4,0xe5,0xf6]
def heap (G : Glob env) : Source.Heap env.layout :=
  (((Source.Heap.empty.alloc ⟨.bytes .memory,.bytes (input G)⟩).1).alloc ⟨.bytes .memory,.bytes old⟩).1
def shape (a : Nat) : MemoryShape := if a=0 then .bytes 4 else .bytes 6

theorem shape_size (a : Nat) : (shape a).size=64 := by
  unfold shape
  split <;> rfl

def placement (G : Glob env) : Placement (heap G) where
  address a := 128+a*128
  shape := shape
  free := ⟨384,by decide⟩
  free_start := by decide
  distinct a b _ _ equal := by omega
  typed a τ d found := by
    cases a with
    | zero =>
      change some (⟨.bytes .memory,.bytes (input G)⟩ : Σ σ,Source.Data env.layout σ)=some ⟨τ,d⟩ at found
      cases found
      simpa only [input_length] using (HasMemoryShape.bytes (input G))
    | succ a =>
      cases a with
      | zero =>
        change some (⟨.bytes .memory,.bytes old⟩ : Σ σ,Source.Data env.layout σ)=some ⟨τ,d⟩ at found
        cases found
        exact .bytes _
      | succ a =>
        have absent := (heap G).bounded (a+2) (by change 2≤a+2; omega)
        change (heap G).cells (a+2)=some ⟨τ,d⟩ at found
        rw [absent] at found
        cases found
  starts _ _ := by omega
  ends a live := by
    have small : a<2 := by
      apply Nat.lt_of_not_le
      intro hn
      have absent := (heap G).bounded a (by change 2≤a; exact hn)
      rw [absent] at live
      cases live
    rw [shape_size]
    change 128+a*128+64≤384
    omega
  separate a b _ _ ne := by
    rw [shape_size,shape_size]
    omega

def inputEntry (G : Glob env) : HeapByteEntry (heap G) := ⟨0,false,input G,rfl⟩
def outputEntry (G : Glob env) : HeapByteEntry (heap G) := ⟨1,false,old,rfl⟩
def entries (G : Glob env) := [inputEntry G,outputEntry G]

theorem distinct (G : Glob env) : ((entries G).map HeapByteEntry.id).Nodup := by
  change [0,1].Nodup
  decide

def reserved : ByteView := mstore (mstore (fun _=>0xa5) 64 384) 96 0
def memory (G : Glob env) : ByteView := encodeByteHeap (placement G) (entries G) reserved

theorem input_reads (G : Glob env) : (inputEntry G).Reads (placement G) (memory G) :=
  encodeByteHeap_reads _ _ (distinct G) _ _ (by exact List.mem_cons_self)

theorem output_reads (G : Glob env) : (outputEntry G).Reads (placement G) (memory G) :=
  encodeByteHeap_reads _ _ (distinct G) _ _ (by exact List.mem_cons_of_mem _ List.mem_cons_self)

theorem input_load (G : Glob env) : PhysicalHeapPort.port.load (memory G) 160 4=some (input G) := by
  have actual := PhysicalHeapPort.load_encoded (heap G) (placement G) (entries G) (distinct G) (inputEntry G)
    (by exact List.mem_cons_self) reserved
  simpa only [inputEntry,input_length,PhysicalHeapPort.payloadOffset] using actual

end Solidity.Yul.World.ReturningCall
