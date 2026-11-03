import Solidity.Yul.Adapters.P6ByteMemory

namespace Solidity.Yul.Adapters.P6ByteMemory.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
private def C : Contract := {vars:=[]}
private def key (p : Pipeline) : FrameKey := ⟨8,2,p,3,lenU 1 (by decide),lenU 2 (by decide),lenU 0 (by decide)⟩
private def image (p : Pipeline) : FrameMem C [] :=
  {st:=State.init C,key:=key p,scalar:=by intro R i;cases i
   capacity:=160,aligned:=⟨5,rfl⟩
   data:=fun i=>if i.val<128 then (if i.val=127 then 170 else UInt8.ofNat i.val) else 0
   highWaterWords:=4,resident:=by decide
   zeroAbove:=by intro i high;exact if_neg (by omega)}
private def span (p : Pipeline) (offset length : Nat) (off : offset<2^256) (len : length<2^256)
    (fits : length=0 ∨ offset+length≤160) : ByteSpan (image p).capacity :=
  ⟨lenU offset off,lenU length len,by simpa only [lenU,Int.toNat_natCast] using fits⟩
private def src (p : Pipeline) := span p 24 12 (by decide) (by decide) (Or.inr (by decide))
private def dst (p : Pipeline) := span p 28 12 (by decide) (by decide) (Or.inr (by decide))
private def forward (p : Pipeline) := copySnapshot (image p) (src p) (dst p) rfl
private def backward (p : Pipeline) := copySnapshot (image p) (dst p) (src p) rfl

theorem overlap_forward (p : Pipeline) :
    Environment.readMemory (frameBytes (forward p)) 28 12=(List.range 12).map (fun j=>UInt8.ofNat (24+j)) := by
  have read:=copy_readback (image p) (src p) (dst p) rfl
  exact read.trans (by rfl)

theorem overlap_backward (p : Pipeline) :
    Environment.readMemory (frameBytes (backward p)) 24 12=(List.range 12).map (fun j=>UInt8.ofNat (28+j)) := by
  have read:=copy_readback (image p) (dst p) (src p) rfl
  exact read.trans (by rfl)

/-- Nonzero exterior sentinel and the exact free/zero-slot bytes remain framed.
These are actual disjoint ranges, not a blanket memory-safe claim. -/
theorem exterior (p : Pipeline) :
    frameBytes (forward p) 127=170 ∧
    (∀ k,64≤k → k<128 → frameBytes (forward p) k=frameBytes (image p) k) ∧
    (forward p).st=(image p).st ∧ (forward p).key=key p := by
  refine ⟨?_,?_,(copy_carrier (image p) (src p) (dst p) rfl).1,
    (copy_carrier (image p) (src p) (dst p) rfl).2⟩
  · change frameBytes (copySnapshot (image p) (src p) (dst p) rfl) 127=170
    rw [copy_outside (image p) (src p) (dst p) rfl 127 (Or.inr (by change 28+12≤127;decide))]
    rfl
  · intro k low high
    exact copy_outside (image p) (src p) (dst p) rfl k (Or.inr (by
      change 28+12≤k
      omega))

/-- The nonempty source alone can extend accessed words even when destination
is below the old high-water mark. All newly observed bytes are real zeros. -/
theorem source_access (p : Pipeline) :
    (copySnapshot (image p) (span p 140 4 (by decide) (by decide) (Or.inr (by decide)))
      (span p 0 4 (by decide) (by decide) (Or.inr (by decide))) rfl).highWaterWords=5 := by
  rw [copy_highWater _ _ _ _ (by change (4:Nat)≠0;decide)]
  change max (max 4 ((0+4+31)/32)) ((140+4+31)/32)=5
  decide

private def empty (p : Pipeline) : FrameMem C [] :=
  {st:=State.init C,key:=key p,scalar:=by intro R i;cases i
   capacity:=0,aligned:=⟨0,rfl⟩,data:=fun i=>Fin.elim0 i,highWaterWords:=0,resident:=by decide
   zeroAbove:=by intro i _;exact Fin.elim0 i}
private def endpoint (p : Pipeline) : ByteSpan (empty p).capacity :=
  ⟨lenU (2^256-1) (by decide),lenU 0 (by decide),Or.inl rfl⟩

theorem zero_capacity_max_offset (p : Pipeline) : copySnapshot (empty p) (endpoint p) (endpoint p) rfl=empty p :=
  copy_empty _ _ _ _ rfl

/-- Exact low-byte truncation, tail preservation and crossing the last
resident byte; capacity does not silently become a physical Word bound. -/
theorem low_byte (p : Pipeline) :
    Environment.dataStep (.op .MSTORE8)
      ⟨[lenU 159 (by decide),lenU 511 (by decide),lenU 77 (by decide)],frameBytes (image p)⟩=
      some ⟨[lenU 77 (by decide)],frameBytes (store8 (image p) (lenU 159 (by decide)) (lenU 511 (by decide)) (by change 159+1≤160;decide))⟩ ∧
    frameBytes (store8 (image p) (lenU 159 (by decide)) (lenU 511 (by decide)) (by change 159+1≤160;decide)) 159=255 := by
  refine ⟨store8_target _ _ _ _ _,?_⟩
  unfold store8
  rw [write_image]
  change Environment.writeBytes (frameBytes (image p)) 159 [UInt8.ofNat 511] (159+0)=255
  rw [Environment.writeBytes_at _ 159 0 _ (by decide)]
  decide +kernel

/-- An unsupported bounded nonempty span is not assigned a source/Yul verdict. -/
theorem missing_capacity : ¬∃ s : ByteSpan 32,s.offset.val.toNat=31 ∧ s.length.val.toNat=2 := by
  rintro ⟨s,off,len⟩
  have fits:=s.fits
  rw [off,len] at fits
  omega

/-- info: ([24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35], [28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39], 170, 5, 255) -/
#guard_msgs in
#eval (Environment.readMemory (frameBytes (forward .legacy)) 28 12,
  Environment.readMemory (frameBytes (backward .viaIR)) 24 12,
  frameBytes (forward .legacy) 127,
  (copySnapshot (image .legacy) (span .legacy 140 4 (by decide) (by decide) (Or.inr (by decide)))
    (span .legacy 0 4 (by decide) (by decide) (Or.inr (by decide))) rfl).highWaterWords,
  frameBytes (store8 (image .viaIR) (lenU 159 (by decide)) (lenU 511 (by decide)) (by change 159+1≤160;decide)) 159)

/- Wrong forward byte-at-a-time overlap, reversed range and erased padding
expectations are all discriminated against complete selected observations. -/
/-- info: (false, false, false, false) -/
#guard_msgs in
#eval (Environment.readMemory (frameBytes (forward .legacy)) 28 12==([24,25,26,27,24,25,26,27,24,25,26,27] : List UInt8),
  Environment.readMemory (frameBytes (forward .viaIR)) 28 12==([35,34,33,32,31,30,29,28,27,26,25,24] : List UInt8),
  frameBytes (forward .legacy) 127==0,
  (copySnapshot (image .viaIR) (span .viaIR 140 4 (by decide) (by decide) (Or.inr (by decide)))
    (span .viaIR 0 4 (by decide) (by decide) (Or.inr (by decide))) rfl).highWaterWords==4)

end Solidity.Yul.Adapters.P6ByteMemory.Controls
