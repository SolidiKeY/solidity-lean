import Solidity.Backend.MemoryOps.PhysicalFrameImage

/-! Actual bounded invocation-image clients, BOTH retained pipeline tags,
unaligned crossing stores, full32-byte snapshots, exterior sentinel, literal
zero capacity/empty endpoint and runtime capacity growth. These are the existing
typed frame and target byte operations, not Source transaction/gas semantics. -/
namespace Solidity.Backend.MemoryOps.Physical.FrameControls
open Evm.TryByteImage
private def C : Contract := {vars := []}
private def key (p : Pipeline) : FrameKey :=
  ⟨3,1,p,7,lenU 1 (by decide),lenU 2 (by decide),lenU 4 (by decide)⟩
private def image (p : Pipeline) : FrameMem C [] :=
  { st := State.init C
    key := key p
    scalar := by intro R i;cases i
    capacity := 96
    aligned := ⟨3,rfl⟩
    data := fun i => if i.val=95 then 170 else 0
    highWaterWords := 3
    resident := by decide
    zeroAbove := by intro i hi;have hh : i.val<96 := i.isLt;omega }
private def span (p : Pipeline) : WordSpan (image p).capacity :=
  ⟨lenU 31 (by decide),by change 31+32≤96;decide⟩
private def high : PrimTy.uint.Denote := lenU (2^248+255) (by decide)
private def selected (p : Pipeline) : ByteSpan (store32 (image p) (span p) high).capacity :=
  ⟨lenU 31 (by decide),lenU 32 (by decide),Or.inr (by change 31+32≤96;decide)⟩

/-- Offset31 crosses a physical word boundary. Both selected endpoint bytes
change; full snapshot byte order, ALL exterior bytes, source/key and tail stay
explicit. A retained pipeline tag is not a claim of Source evaluation order. -/
theorem unaligned_store (p : Pipeline) :
    Environment.cryptoStep (.op .MSTORE)
      ⟨(span p).offset::high::[lenU 7 (by decide),lenU 9 (by decide)],frameBytes (image p)⟩=
      some ⟨[lenU 7 (by decide),lenU 9 (by decide)],frameBytes (store32 (image p) (span p) high)⟩ ∧
    (store32 (image p) (span p) high).st=(image p).st ∧
    (store32 (image p) (span p) high).key=key p ∧
    (store32 (image p) (span p) high).highWaterWords=3 ∧
    frameBytes (store32 (image p) (span p) high)=
      Environment.writeBytes (frameBytes (image p)) 31 (Semantics.wordBytes high.val.toNat) ∧
    [frameBytes (image p) 31,frameBytes (image p) 62,frameBytes (image p) 95,
     frameBytes (store32 (image p) (span p) high) 31,
     frameBytes (store32 (image p) (span p) high) 62,
     frameBytes (store32 (image p) (span p) high) 95]=[0,0,170,1,255,170] ∧
    snapshot (store32 (image p) (span p) high) (selected p)=[1]++List.replicate 30 0++[255] ∧
    snapshot (store32 (image p) (span p) high) (selected p)≠
      ([1]++List.replicate 30 0++[255] : List UInt8).reverse := by
  obtain ⟨ht,hs,hk⟩ := frame_store32_target (image p) (span p) high [lenU 7 (by decide),lenU 9 (by decide)]
  have firstByte : frameBytes (store32 (image p) (span p) high) 31=1 := by
    rw [frameBytes_store32]
    change Environment.writeBytes (frameBytes (image p)) 31 (Semantics.wordBytes high.val.toNat) 31=1
    rw [Environment.writeBytes_at _ 31 0 _ (by rw [word_bytes_length];decide)]
    decide
  have lastByte : frameBytes (store32 (image p) (span p) high) 62=255 := by
    rw [frameBytes_store32]
    change Environment.writeBytes (frameBytes (image p)) 31 (Semantics.wordBytes high.val.toNat) (31+31)=255
    rw [Environment.writeBytes_at _ 31 31 _ (by rw [word_bytes_length];decide)]
    decide
  have exterior : frameBytes (store32 (image p) (span p) high) 95=170 := by
    rw [frameBytes_store32]
    rw [Environment.writeBytes_frame _ _ 95 _ (by rw [word_bytes_length];change 95<31 ∨ 31+32≤95;decide)]
    rfl
  have payload : snapshot (store32 (image p) (span p) high) (selected p)=[1]++List.replicate 30 0++[255] := by
    rw [frame_snapshot_read,frameBytes_store32]
    change Environment.readMemory (Environment.writeBytes (frameBytes (image p)) 31
      (Semantics.wordBytes high.val.toNat)) 31 32=_
    have readback : Environment.readMemory (Environment.writeBytes (frameBytes (image p)) 31
        (Semantics.wordBytes high.val.toNat)) 31 32=Semantics.wordBytes high.val.toNat := by
      simpa only [word_bytes_length] using Environment.read_written (Semantics.wordBytes high.val.toNat) 31 (frameBytes (image p))
    rw [readback]
    decide
  refine ⟨ht,hs,hk,?_,frameBytes_store32 (image p) (span p) high,?_,payload,?_⟩
  · change max 3 ((31+32+31)/32)=3
    decide
  · rw [firstByte,lastByte,exterior]
    rfl
  · rw [payload]
    decide

private def empty (p : Pipeline) : FrameMem C [] :=
  { st := State.init C
    key := key p
    scalar := by intro R i;cases i
    capacity := 0
    aligned := ⟨0,rfl⟩
    data := fun i => Fin.elim0 i
    highWaterWords := 0
    resident := by decide
    zeroAbove := by intro i _;exact Fin.elim0 i }
private def emptySpan (p : Pipeline) : ByteSpan (empty p).capacity :=
  ⟨lenU (2^256-1) (by decide),lenU 0 (by decide),Or.inl rfl⟩

/-- Literal zero-capacity empty reads succeed even at the largest offset.
Runtime zero-filled capacity extension changes no target byte. This is not
zero-length fixed Source admission or an allocation/gas theorem. -/
theorem empty_endpoint_growth (p : Pipeline) (n : Nat) :
    snapshot (empty p) (emptySpan p)=[] ∧
    Environment.readMemory (frameBytes (empty p)) (2^256-1) 0=[] ∧
    frameBytes (expandZero (empty p) n)=frameBytes (empty p) :=
  ⟨snapshot_empty (empty p) (emptySpan p) rfl,rfl,frameBytes_expandZero (empty p) n⟩

/-- This exact existing bounded WordSpan is uninhabitable. No target revert,
Source panic or blanket source exclusion follows from the representation fact. -/
theorem insufficient_capacity : ¬∃ a : WordSpan 32,a.offset.val.toNat=31 := by
  rintro ⟨a,ha⟩
  have fits : a.offset.val.toNat+32≤32 := a.fits
  rw [ha] at fits
  omega

/-- info: 'Solidity.Backend.MemoryOps.Physical.FrameControls.unaligned_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unaligned_store
/-- info: 'Solidity.Backend.MemoryOps.Physical.FrameControls.empty_endpoint_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_endpoint_growth
/-- info: 'Solidity.Backend.MemoryOps.Physical.FrameControls.insufficient_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms insufficient_capacity
end Solidity.Backend.MemoryOps.Physical.FrameControls
