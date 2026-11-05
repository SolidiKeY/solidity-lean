import Solidity.Yul.Adapters.P6CopySource
import Solidity.Yul.Adapters.P6HistoryHashRef

/-! Construct byte-object updates from actual copy readback and the unchanged
length header. This reuses canonical snapshotBytes and real retained-capacity
guards; no output Source/view law or dirty-byte cleaning policy is assumed. -/
namespace Solidity.Yul.Adapters.P6ByteCopyPreparation
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage

/-- Every copied byte comes from the old source snapshot, including overlap. -/
theorem copied_byte {C : Contract} {Δ : Ctx} (μ : FrameMem C Δ)
    (source destination : ByteSpan μ.capacity) (same : source.length=destination.length)
    (i : Nat) (inside : i<source.length.val.toNat) :
    frameBytes (P6ByteMemory.copySnapshot μ source destination same) (destination.offset.val.toNat+i)=
      frameBytes μ (source.offset.val.toNat+i) := by
  have copied := P6ByteMemory.copy_readback μ source destination same
  rw [frame_snapshot_read] at copied
  have hi : i<destination.length.val.toNat := by rw [←same];exact inside
  have selected := congrArg (fun bs : List UInt8 => bs[i]?) copied
  simpa only [Environment.readMemory,List.getElem?_map,List.getElem?_range,hi,inside,if_true,
    Option.map_some,Option.some.injEq] using selected

/-- Header and payload facts determine the actual typed byte update. Padding
is not part of the Source byte data, and the original allocated extent remains
the real acceptance guard. Every payload byte, including 0/255, is canonical. -/
theorem byte_update_exists {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (es : List (MixedHeapEntry p))
    (root : Nat) (old : Source.Data E.layout (.bytes .memory))
    (found : h.get root=some ⟨_,old⟩) (image : MemoryImage p old)
    (bs : Roadmap.Bytes) (m : ByteView)
    (header : (mload m (p.address root)).val=bs.length)
    (payload : readBytes m (p.address root+32) bs.length=bs)
    (capacity : (MemoryShape.bytes bs.length).size≤(allocated.shape root).size) :
    ∃ u,update allocated p es ⟨root,_,old,found,image⟩ m=some u ∧
      HEq u.object.data (Source.Data.bytes (D:=E.layout) (l:=.memory) bs) := by
  let object := snapshotBytes p m (p.address root)
  have data : object.data=Source.Data.bytes (D:=E.layout) (l:=.memory) bs := by
    change Source.Data.bytes (readBytes m (p.address root+32) (mload m (p.address root)).val)=_
    rw [header,payload]
  have shape : object.shape=MemoryShape.bytes bs.length := by
    change MemoryShape.bytes (readBytes m (p.address root+32) (mload m (p.address root)).val).length=_
    rw [header,payload]
  have fits : object.shape.size≤(allocated.shape root).size := by rw [shape];exact capacity
  refine ⟨⟨⟨root,_,old,found,image⟩,object,fits⟩,?_,heq_of_eq data⟩
  unfold update NominalInventory.decode decodeInventoryObject
  dsimp only
  exact dif_pos fits

end Solidity.Yul.Adapters.P6ByteCopyPreparation
