import Solidity.Yul.Adapters.P6SnapshotCopy
import Solidity.Yul.Views.NominalInventoryDynamic

/-! Constructive preparation from actual canonical nominal words after a P6
copy. These are codec and capacity inputs, not assumed final Source/view laws.
Byte-span validity remains separate from canonical preparation and allocation. -/
namespace Solidity.Yul.Adapters.P6CopyPreparation
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage

/-- Byte equality may relate different physical bases. -/
theorem readBE_rebase (m m' : ByteView) (a b n : Nat)
    (same : ∀ i,i<n → m (a+i)=m' (b+i)) : readBE m a n=readBE m' b n := by
  first | (simp only [readBE]; done) | skip
  induction n with
  | zero => rfl
  | succ n ih =>
    change 256*readBE m a n+(m (a+n)).toNat=256*readBE m' b n+(m' (b+n)).toNat
    rw [ih (fun i hi => same i (by omega)),same n (by omega)]

/-- A full copied word decodes to the old source word, including overlap. -/
theorem copied_word {C : Contract} {Δ : Ctx} (μ : FrameMem C Δ)
    (source destination : ByteSpan μ.capacity) (same : source.length=destination.length)
    (word : source.length.val.toNat=32) :
    mload (frameBytes (P6ByteMemory.copySnapshot μ source destination same)) destination.offset.val.toNat=
      mload (frameBytes μ) source.offset.val.toNat := by
  apply Fin.ext
  apply readBE_rebase
  intro i hi
  have copied := P6ByteMemory.copy_readback μ source destination same
  rw [frame_snapshot_read] at copied
  have length : destination.length.val.toNat=32 := by rw [←same];exact word
  rw [length,word] at copied
  have selected :=  congrArg (fun bs : List UInt8 => bs[i]?) copied
  simpa only [Environment.readMemory,List.getElem?_map,List.getElem?_range,hi,if_true,Option.map_some,Option.some.injEq] using selected

/-- A represented nominal array with canonical changed values prepares its real
inventory update. The shape/capacity guard is discharged by the computed shape,
not a caller-supplied output view or inverse theorem. -/
theorem nominal_update_exists {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (es : List (MixedHeapEntry p))
    (root : Nat) (name : Source.DeclName) (k : Option Nat)
    (old : Source.Data E.layout (.array .memory (.udvt name) k))
    (found : h.get root=some ⟨_,old⟩) (image : MemoryImage p old)
    (n : Nat) (hl : ∀ z,k=some z → z=n) (bound : n<2^256)
    (values : Fin n → Source.Val E.layout (.udvt name)) (m : ByteView)
    (declared : NominalMemory.declaredUDVT E name=true)
    (supported : CanonicalScalarType E.layout (E.layout.underlying name))
    (header : arrayLengthChoice k m (p.address root)=n)
    (words : ∀ i,(values i).word=some (mload m (p.address root+arrayPayloadOffset k+i.val*32)))
    (capacity : (MemoryShape.array k.isNone n).size≤(allocated.shape root).size) :
    ∃ u,update allocated p es ⟨root,_,old,found,image⟩ m=some u ∧
      HEq u.object.data (memberArrayData E.layout (.udvt name) k n hl values) := by
  have canonical := snapshot_encode p name k n hl bound values m (p.address root) declared supported header words
  obtain ⟨object,decoded,data⟩ := Option.map_eq_some_iff.mp canonical
  have shape : object.shape=MemoryShape.array k.isNone n := by
    have actual := object.shaped
    rw [data] at actual
    exact memoryShape_unique actual (.array n hl _)
  have fits : object.shape.size≤(allocated.shape root).size := by rw [shape];exact capacity
  refine ⟨⟨⟨root,_,old,found,image⟩,object,fits⟩,?_,heq_of_eq data⟩
  unfold update NominalInventory.decode
  dsimp only
  rw [decoded]
  exact dif_pos fits

end Solidity.Yul.Adapters.P6CopyPreparation
