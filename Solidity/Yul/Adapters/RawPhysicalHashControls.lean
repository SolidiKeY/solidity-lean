import Solidity.Yul.Adapters.RawPhysicalHash
import Solidity.Yul.Adapters.RawPhysicalInventoryControls

/-! The hash input crosses two raw cells and overlaps its output cell. Its old
bytes are pinned before the digest is stored. No preimage inequality is promoted
to hash inequality. Sibling raw words, padding and the caller stack tail survive.
These are kernel/target-slice controls, not compiler/EVM resource evidence. -/
namespace Solidity.Yul.Adapters.RawPhysicalHash.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open RawPhysicalInventory RawPhysicalInventory.Controls

def input (pipeline : Pipeline) : ByteSpan (stored pipeline).capacity :=
  ⟨lenU 64 (by decide),lenU 2 (by decide),Or.inr (by change 64+2≤192;decide)⟩
def destination (pipeline : Pipeline) : WordSpan (stored pipeline).capacity :=
  ⟨lenU 65 (by decide),by change 65+32≤192;decide⟩
def value (pipeline : Pipeline) := hashWord (stored pipeline) (input pipeline)
def updated (pipeline : Pipeline) := RawFrame.write dirty small (value pipeline)
def reached (pipeline : Pipeline) := storeHash (stored pipeline) (input pipeline) (destination pipeline) dirty small

theorem input_snapshot (pipeline : Pipeline) : snapshot (stored pipeline) (input pipeline)=[2,0] := by
  rw [frame_snapshot_read]
  have encoded := frame_bytes 33 dirty (image pipeline) (room pipeline)
  change frameBytes (stored pipeline)=_ at encoded
  rw [encoded]
  cases pipeline <;> decide +kernel

theorem input_value (pipeline : Pipeline) : value pipeline=P6ByteMemory.wireWord (Environment.digest [2,0]) := by
  unfold value hashWord
  rw [input_snapshot]

theorem whole (pipeline : Pipeline) (frame : Environment.Frame) (tail : List Environment.Word) :
    encode 33 (updated pipeline) (frameBytes (reached pipeline))=frameBytes (reached pipeline) ∧
    RawFrame.view (decode 33 dirty (frameBytes (reached pipeline)))=RawFrame.view (updated pipeline) ∧
    (reached pipeline).st=(image pipeline).st ∧ (reached pipeline).key=(image pipeline).key ∧
    Environment.runSlice frame (code (destination pipeline).offset)
      ⟨(input pipeline).offset::(input pipeline).length::tail,frameBytes (stored pipeline)⟩=
      some ⟨tail,frameBytes (reached pipeline)⟩ :=
  transport 33 dirty (image pipeline) (room pipeline) (input pipeline) (destination pipeline) small rfl frame tail

theorem raw_digest_and_siblings (pipeline : Pipeline) (frame : Environment.Frame) :
    RawFrame.view (decode 33 dirty (frameBytes (reached pipeline))) small=P6ByteMemory.wireWord (Environment.digest [2,0]) ∧
    RawFrame.view (decode 33 dirty (frameBytes (reached pipeline))) flag=word 2 ∧
    RawFrame.view (decode 33 dirty (frameBytes (reached pipeline))) selector=word (2^255+85) := by
  rw [(whole pipeline frame []).2.1]
  refine ⟨?_,rfl,rfl⟩
  exact (RawFrame.read_write dirty small _).trans (input_value pipeline)

theorem source_fields (pipeline : Pipeline) : (updated pipeline).clean=dirty.clean ∧
    (updated pipeline).world=dirty.world :=
  ⟨RawFrame.write_clean dirty small (value pipeline),RawFrame.write_world dirty small (value pipeline)⟩

theorem padding (pipeline : Pipeline) : frameBytes (reached pipeline) 191=0xa5 := by
  dsimp only [reached]
  rw [storeHash_bytes,RawPhysical.store_image]
  change Environment.writeBytes (frameBytes (stored pipeline)) 65 (Source.wordBytes (RawFrame.view (updated pipeline) small)) 191=0xa5
  rw [Environment.writeBytes_frame _ _ _ _ (Or.inr (by rw [Source.wordBytes_length];decide))]
  exact (nonaligned_and_padding pipeline).2.2.2.2.2.2.1

theorem actual_overlap (pipeline : Pipeline) :
    (input pipeline).offset.val.toNat<(destination pipeline).offset.val.toNat ∧
    (destination pipeline).offset.val.toNat<(input pipeline).offset.val.toNat+(input pipeline).length.val.toNat := by
  change 64<65 ∧ 65<64+2
  decide

theorem read_access_accounted (pipeline : Pipeline) :
    (reached pipeline).highWaterWords=
      max (RawPhysical.store (stored pipeline) (destination pipeline) (updated pipeline) small).highWaterWords
        ((64+2+31)/32) :=
  read_high (stored pipeline) (input pipeline) (destination pipeline) dirty small (by change (2 : Nat)≠0;decide)

def emptyInput (pipeline : Pipeline) : ByteSpan (stored pipeline).capacity :=
  ⟨lenU (2^256-1) (by decide),lenU 0 (by decide),Or.inl rfl⟩
theorem empty_hash_input (pipeline : Pipeline) : hashWord (stored pipeline) (emptyInput pipeline)=
    P6ByteMemory.wireWord (Environment.digest []) := by
  have bytes : snapshot (stored pipeline) (emptyInput pipeline)=[] := by
    rw [frame_snapshot_read]
    rfl
  unfold hashWord
  rw [bytes]

/-- Input above the old high-water and destination discriminates the read touch. -/
def extendedImage (pipeline : Pipeline) : FrameMem C [] :=
  {st:=(image pipeline).st,key:=(image pipeline).key,scalar:=(image pipeline).scalar
   capacity:=256,aligned:=⟨8,rfl⟩,data:=fun i=>if i.val<192 then 0xa5 else 0
   highWaterWords:=6,resident:=by decide,zeroAbove:=by intro i high;exact if_neg (by omega)}
def extendedRoom (pipeline : Pipeline) : 33+32*wordCellCount (localExternalTypes ctx)≤(extendedImage pipeline).highWaterWords*32 := by
  change 161≤192
  decide
def extendedStored (pipeline : Pipeline) := frameOf 33 dirty (extendedImage pipeline) (extendedRoom pipeline)
def highInput (pipeline : Pipeline) : ByteSpan (extendedStored pipeline).capacity :=
  ⟨lenU 224 (by decide),lenU 1 (by decide),Or.inr (by change 224+1≤256;decide)⟩
def lowDestination (pipeline : Pipeline) : WordSpan (extendedStored pipeline).capacity :=
  ⟨lenU 65 (by decide),by change 65+32≤256;decide⟩
theorem discriminating_read_accounting (pipeline : Pipeline) :
    (storeHash (extendedStored pipeline) (highInput pipeline) (lowDestination pipeline) dirty small).highWaterWords=8 ∧
    (RawPhysical.store (extendedStored pipeline) (lowDestination pipeline)
      (RawFrame.write dirty small (hashWord (extendedStored pipeline) (highInput pipeline))) small).highWaterWords=6 := by
  have read := read_high (extendedStored pipeline) (highInput pipeline) (lowDestination pipeline) dirty small
    (by change (1 : Nat)≠0;decide)
  rw [store_high] at read
  have written := store_high (extendedStored pipeline) (lowDestination pipeline)
    (RawFrame.write dirty small (hashWord (extendedStored pipeline) (highInput pipeline))) small
  have initialHigh : (extendedStored pipeline).highWaterWords=6 := rfl
  have low : (lowDestination pipeline).offset.val.toNat=65 := rfl
  have highOffset : (highInput pipeline).offset.val.toNat=224 := rfl
  have highLength : (highInput pipeline).length.val.toNat=1 := rfl
  rw [initialHigh,low,highOffset,highLength] at read
  rw [initialHigh,low] at written
  exact ⟨read.trans (by decide),written.trans (by decide)⟩

theorem wrong_preimage : ([2,0] : List UInt8)≠[0,2] ∧ ([2,0] : List UInt8)≠[2] := by decide

theorem code_bytes (pipeline : Pipeline) :
    ((code (destination pipeline).offset).map Backend.Instr.encode).flatten=
      [0x20,0x7f]++Source.beBytes 32 65++[0x52] := by
  cases pipeline <;> decide +kernel
end Solidity.Yul.Adapters.RawPhysicalHash.Controls
