import Solidity.Backend.MemoryOps.PhysicalFrameImage
import Solidity.Yul.Adapters.MemoryBytes

/-! Bounded byte operations on the EXISTING typed invocation-frame image.
Capacity/physical Word fit/Source adequacy are distinct obligations. This module
adds operations, not a second source state or a target MCOPY interpreter. -/
namespace Solidity.Yul.Adapters.P6ByteMemory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
variable {C : Contract} {Γ : Ctx}

/-- Record a nonempty accessed span, with the actual rounded high-water mark.
Empty spans neither validate their offset nor change accounting. -/
def touch (μ : FrameMem C Γ) (s : ByteSpan μ.capacity) : FrameMem C Γ :=
  if empty : s.length.val.toNat=0 then μ else
  {μ with
    highWaterWords:=max μ.highWaterWords ((s.offset.val.toNat+s.length.val.toNat+31)/32)
    resident:=by
      have bound : s.offset.val.toNat+s.length.val.toNat≤μ.capacity := s.fits.resolve_left empty
      rcases μ.aligned with ⟨k,hk⟩
      have old:=μ.resident
      omega
    zeroAbove:=by
      intro i high
      apply μ.zeroAbove i
      omega}

theorem touch_capacity (μ : FrameMem C Γ) (s : ByteSpan μ.capacity) : (touch μ s).capacity=μ.capacity := by
  unfold touch
  split <;> rfl

theorem touch_image (μ : FrameMem C Γ) (s : ByteSpan μ.capacity) : frameBytes (touch μ s)=frameBytes μ := by
  unfold touch
  split <;> rfl

theorem touch_carrier (μ : FrameMem C Γ) (s : ByteSpan μ.capacity) :
    (touch μ s).st=μ.st ∧ (touch μ s).key=μ.key := by
  unfold touch
  split <;> exact ⟨rfl,rfl⟩

theorem touch_empty (μ : FrameMem C Γ) (s : ByteSpan μ.capacity) (empty : s.length.val.toNat=0) :
    touch μ s=μ := dif_pos empty

/-- Write exactly the supplied bounded bytes. The source snapshot, if any,
is supplied BEFORE this operation, so overlap never reads updated bytes. -/
def writeSpan (μ : FrameMem C Γ) (s : ByteSpan μ.capacity) (bytes : List UInt8)
    (length : bytes.length=s.length.val.toNat) : FrameMem C Γ :=
  if empty : s.length.val.toNat=0 then μ else
  {μ with
    data:=fun i=>if inside : s.offset.val.toNat≤i.val ∧ i.val<s.offset.val.toNat+s.length.val.toNat
      then bytes[i.val-s.offset.val.toNat]'(by omega) else μ.data i
    highWaterWords:=max μ.highWaterWords ((s.offset.val.toNat+s.length.val.toNat+31)/32)
    resident:=by
      have bound : s.offset.val.toNat+s.length.val.toNat≤μ.capacity := s.fits.resolve_left empty
      rcases μ.aligned with ⟨k,hk⟩
      have old:=μ.resident
      omega
    zeroAbove:=by
      intro i high
      have outside : ¬(s.offset.val.toNat≤i.val ∧ i.val<s.offset.val.toNat+s.length.val.toNat) := by omega
      rw [dif_neg outside]
      apply μ.zeroAbove i
      omega}

theorem write_capacity (μ : FrameMem C Γ) (s : ByteSpan μ.capacity) (bytes : List UInt8) (length) :
    (writeSpan μ s bytes length).capacity=μ.capacity := by
  unfold writeSpan
  split <;> rfl

theorem write_empty (μ : FrameMem C Γ) (s : ByteSpan μ.capacity) (bytes : List UInt8) (length)
    (empty : s.length.val.toNat=0) : writeSpan μ s bytes length=μ := dif_pos empty

/-- Complete physical byte equality, not just a selected projection. -/
theorem write_image (μ : FrameMem C Γ) (s : ByteSpan μ.capacity) (bytes : List UInt8) (length) :
    frameBytes (writeSpan μ s bytes length)=
      Environment.writeBytes (frameBytes μ) s.offset.val.toNat bytes := by
  by_cases empty : s.length.val.toNat=0
  · have nil : bytes=[] := List.eq_nil_iff_length_eq_zero.mpr (length.trans empty)
    rw [write_empty μ s bytes length empty,nil]
    rfl
  · have bound : s.offset.val.toNat+s.length.val.toNat≤μ.capacity := s.fits.resolve_left empty
    funext k
    unfold writeSpan
    rw [dif_neg empty]
    change (if h : k<μ.capacity then _ else 0)=_
    by_cases hk : k<μ.capacity
    · rw [dif_pos hk]
      dsimp only
      by_cases inside : s.offset.val.toNat≤k ∧ k<s.offset.val.toNat+s.length.val.toNat
      · rw [dif_pos inside]
        have add : s.offset.val.toNat+(k-s.offset.val.toNat)=k := by omega
        simpa only [add] using (Environment.writeBytes_at bytes s.offset.val.toNat
          (k-s.offset.val.toNat) (frameBytes μ) (by omega)).symm
      · rw [dif_neg inside,Environment.writeBytes_frame _ _ _ _ (by omega)]
        simp only [frameBytes,dif_pos hk]
    · rw [dif_neg hk,Environment.writeBytes_frame _ _ _ _ (by omega)]
      simp only [frameBytes,dif_neg hk]

/-- Logical side carrier, invocation key and capacity are preserved. -/
theorem write_carrier (μ : FrameMem C Γ) (s : ByteSpan μ.capacity) (bytes : List UInt8) (length) :
    (writeSpan μ s bytes length).st=μ.st ∧ (writeSpan μ s bytes length).key=μ.key := by
  unfold writeSpan
  split <;> exact ⟨rfl,rfl⟩

/-- Copy reads the immutable OLD source snapshot, then writes the destination.
Both nonempty source and destination ends contribute to access accounting. -/
def copySnapshot (μ : FrameMem C Γ) (source destination : ByteSpan μ.capacity)
    (same : source.length=destination.length) : FrameMem C Γ :=
  let written:=writeSpan μ destination (snapshot μ source) (by rw [snapshot_length,same])
  touch written ⟨source.offset,source.length,by rw [write_capacity];exact source.fits⟩

theorem copy_image (μ : FrameMem C Γ) (source destination : ByteSpan μ.capacity) (same) :
    frameBytes (copySnapshot μ source destination same)=
      Environment.writeBytes (frameBytes μ) destination.offset.val.toNat
        (Environment.readMemory (frameBytes μ) source.offset.val.toNat source.length.val.toNat) := by
  unfold copySnapshot
  rw [touch_image,write_image,frame_snapshot_read]

/-- The actual bounded frame update agrees with the lightweight byte-view
snapshot copy. Byte-map agreement does not erase access accounting. -/
theorem copy_view (μ : FrameMem C Γ) (source destination : ByteSpan μ.capacity) (same) :
    frameBytes (copySnapshot μ source destination same)=
      Views.mcopy (frameBytes μ) destination.offset.val.toNat source.offset.val.toNat
        destination.length.val.toNat := by
  rw [copy_image,←same]
  exact (MemoryBytes.copy_eq_write_read _ _ _ _ _).symm

theorem copy_empty (μ : FrameMem C Γ) (source destination : ByteSpan μ.capacity) (same)
    (empty : source.length.val.toNat=0) : copySnapshot μ source destination same=μ := by
  have destEmpty : destination.length.val.toNat=0 := by rw [←same];exact empty
  dsimp only [copySnapshot]
  unfold touch
  rw [dif_pos empty]
  exact write_empty _ _ _ _ destEmpty

theorem copy_carrier (μ : FrameMem C Γ) (source destination : ByteSpan μ.capacity) (same) :
    (copySnapshot μ source destination same).st=μ.st ∧
    (copySnapshot μ source destination same).key=μ.key := by
  dsimp only [copySnapshot]
  have carrier := write_carrier μ destination (snapshot μ source) (by rw [snapshot_length,same])
  exact ⟨(touch_carrier _ _).1.trans carrier.1,(touch_carrier _ _).2.trans carrier.2⟩

/-- Residual/gap/reserved bytes are preserved wherever the destination is
actually disjoint; no blanket reservation premise is silently omitted. -/
theorem copy_outside (μ : FrameMem C Γ) (source destination : ByteSpan μ.capacity) (same)
    (k : Nat) (outside : k<destination.offset.val.toNat ∨
      destination.offset.val.toNat+destination.length.val.toNat≤k) :
    frameBytes (copySnapshot μ source destination same) k=frameBytes μ k := by
  rw [copy_image]
  apply Environment.writeBytes_frame
  simpa only [Environment.readMemory,List.length_map,List.length_range,same] using outside

/-- Destination readback is exactly the OLD source snapshot, even when the
ranges overlap in either direction. -/
theorem copy_readback (μ : FrameMem C Γ) (source destination : ByteSpan μ.capacity) (same) :
    Environment.readMemory (frameBytes (copySnapshot μ source destination same))
      destination.offset.val.toNat destination.length.val.toNat=snapshot μ source := by
  rw [copy_image,←frame_snapshot_read]
  have length : (snapshot μ source).length=destination.length.val.toNat := by rw [snapshot_length,same]
  rw [←length]
  exact Environment.read_written _ _ _

/-- Exact nonempty read AND write access accounting. This is representation
accounting only, not a gas, allocation or active-memory-size observation. -/
theorem copy_highWater (μ : FrameMem C Γ) (source destination : ByteSpan μ.capacity) (same)
    (nonempty : source.length.val.toNat≠0) :
    (copySnapshot μ source destination same).highWaterWords=
      max (max μ.highWaterWords ((destination.offset.val.toNat+destination.length.val.toNat+31)/32))
        ((source.offset.val.toNat+source.length.val.toNat+31)/32) := by
  have dest : destination.length.val.toNat≠0 := by rw [←same];exact nonempty
  dsimp only [copySnapshot]
  unfold touch
  rw [dif_neg nonempty]
  change max (writeSpan μ destination (snapshot μ source) _).highWaterWords
    ((source.offset.val.toNat+source.length.val.toNat+31)/32)=_
  unfold writeSpan
  rw [dif_neg dest]

/-- Copying a span to itself preserves the COMPLETE byte map. Access metadata
may still record reading a formerly unaccessed zero range. -/
theorem copy_self_image (μ : FrameMem C Γ) (s : ByteSpan μ.capacity) :
    frameBytes (copySnapshot μ s s rfl)=frameBytes μ := by
  rw [copy_image]
  exact MemoryBytes.write_read_identity _ _ _

/-- Numeric conversion to the existing independent failure-slice Word. -/
def wireWord (w : Environment.Word) : Roadmap.Word :=
  ⟨w.val.toNat,by
    have range : 0≤w.val ∧ w.val<(2^256:Nat) := by
      have h:=w.property
      simpa only [PrimTy.inRange,decide_eq_true_eq] using h
    omega⟩

/-- Actual live REVERT after this copy reads the immutable OLD-source bytes.
The byte slice stops before its suffix; no implicit caller rollback is claimed. -/
theorem copy_revert (μ : FrameMem C Γ) (source destination : ByteSpan μ.capacity) (same)
    (tail : List Roadmap.Word) (suffix : Backend.Program) :
    Failure.Slice.run (.op .REVERT::suffix)
      ⟨wireWord destination.offset::wireWord destination.length::tail,
        frameBytes (copySnapshot μ source destination same)⟩=
      some (⟨tail,frameBytes (copySnapshot μ source destination same)⟩,
        some (.revert (snapshot μ source))) := by
  have live:=revert_live (frameBytes (copySnapshot μ source destination same))
    (wireWord destination.offset) (wireWord destination.length) tail suffix
  simpa only [wireWord,copy_readback] using live

/-- Canonical typed byte span for an actual MSTORE8 access. -/
def byteSpan (μ : FrameMem C Γ) (offset : Environment.Word) (fits : offset.val.toNat+1≤μ.capacity) :
    ByteSpan μ.capacity := ⟨offset,lenU 1 (by decide),Or.inr fits⟩

def store8 (μ : FrameMem C Γ) (offset value : Environment.Word) (fits : offset.val.toNat+1≤μ.capacity) :
    FrameMem C Γ := writeSpan μ (byteSpan μ offset fits) [UInt8.ofNat value.val.toNat] rfl

/-- Exact existing target MSTORE8 stack order and low-byte truncation. -/
theorem store8_target (μ : FrameMem C Γ) (offset value : Environment.Word)
    (fits : offset.val.toNat+1≤μ.capacity) (tail : List Environment.Word) :
    Environment.dataStep (.op .MSTORE8) ⟨offset::value::tail,frameBytes μ⟩=
      some ⟨tail,frameBytes (store8 μ offset value fits)⟩ := by
  unfold store8
  rw [write_image]
  rfl

/-- Existing MSTORE8 frame bytes and the byte-view operation agree on exact
low-byte truncation, with the original physical-fit premise unchanged. -/
theorem store8_view (μ : FrameMem C Γ) (offset value : Environment.Word)
    (fits : offset.val.toNat+1≤μ.capacity) :
    frameBytes (store8 μ offset value fits)=
      Views.mstore8 (frameBytes μ) offset.val.toNat (wireWord value) := by
  unfold store8
  rw [write_image]
  rfl

end Solidity.Yul.Adapters.P6ByteMemory
