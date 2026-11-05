import Solidity.Yul.Adapters.RawPhysicalUpdate
import Solidity.Backend.Environment.Composition

/-! Actual physical KECCAK256 result writeback into an H11 raw-local cell.
The input is the original frame snapshot, even when the destination overlaps
it. Existing KECCAK/PUSH/MSTORE semantics execute the code below; no new Yul
syntax, hash oracle, Source dirty-readback policy or compiler adequacy is added.
Gas, stack-capacity and whole target/world composition remain separate. -/
namespace Solidity.Yul.Adapters.RawPhysicalHash
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open RawPhysicalInventory
variable {ctx : Source.Ctx}

theorem word_roundtrip (value : Environment.Word) :
    lenU (P6ByteMemory.wireWord value).val (P6ByteMemory.wireWord value).isLt=value := by
  first | omega | decide | skip
  apply Subtype.ext
  have lower : 0≤value.1 := (of_decide_eq_true value.2).1
  change (value.1.toNat : Int)=value.1
  exact Int.toNat_of_nonneg lower

def hashWord {C : Contract} {Γ : Ctx} (image : FrameMem C Γ) (input : ByteSpan image.capacity) : Word :=
  P6ByteMemory.wireWord (Environment.digest (snapshot image input))

def code (destination : Environment.Word) : List Backend.Instr :=
  [.op .KECCAK256,Environment.push256 (P6ByteMemory.wireWord destination),.op .MSTORE]

/-- Exact executed local target slice, including read-before-write order and
complete memory/stack tail. Actual resource adequacy is not inferred. -/
theorem target {C : Contract} {Γ : Ctx} (targetFrame : Environment.Frame)
    (image : FrameMem C Γ) (input : ByteSpan image.capacity) (destination : WordSpan image.capacity)
    (state : RawFrame.State ctx) (cell : WordCell (localExternalTypes ctx)) (tail : List Environment.Word) :
    let updated := RawFrame.write state cell (hashWord image input)
    let reached := RawPhysical.store image destination updated cell
    Environment.runSlice targetFrame (code destination.offset)
      ⟨input.offset::input.length::tail,frameBytes image⟩=some ⟨tail,frameBytes reached⟩ := by
  first | omega | decide | skip
  dsimp only
  have hashed : Environment.cryptoStep (.op .KECCAK256)
      ⟨input.offset::input.length::tail,frameBytes image⟩=
      some (⟨Environment.digest (snapshot image input)::tail,frameBytes image⟩ : Environment.Slice) := by
    rw [frame_snapshot_read]
    rfl
  have written := RawPhysical.store_target image destination (RawFrame.write state cell (hashWord image input)) cell tail
  rw [RawFrame.read_write] at written
  change Environment.cryptoStep (.op .MSTORE)
    ⟨destination.offset::lenU (P6ByteMemory.wireWord (Environment.digest (snapshot image input))).val
      (P6ByteMemory.wireWord (Environment.digest (snapshot image input))).isLt::tail,frameBytes image⟩=_ at written
  rw [word_roundtrip] at written
  rw [Environment.runSlice_crypto targetFrame _ _ (by rfl)]
  simp only [code,Environment.runCrypto]
  rw [hashed]
  simp only [Option.bind_some]
  rw [Environment.push256,Environment.cryptoStep_constant,word_roundtrip]
  simp only [Option.bind_some]
  rw [written]
  rfl


/-- Transport the original input span through the actual store's unchanged
capacity before recording its read access. No new numeric span is invented. -/
def readArea {C : Contract} {Γ : Ctx} (image : FrameMem C Γ) (input : ByteSpan image.capacity)
    (destination : WordSpan image.capacity) (state : RawFrame.State ctx)
    (cell : WordCell (localExternalTypes ctx)) : ByteSpan (RawPhysical.store image destination state cell).capacity :=
  ⟨input.offset,input.length,by
    rw [show (RawPhysical.store image destination state cell).capacity=image.capacity from
      P6ByteMemory.write_capacity image (RawPhysical.span image destination) _ _]
    exact input.fits⟩

def storeHash {C : Contract} {Γ : Ctx} (image : FrameMem C Γ) (input : ByteSpan image.capacity)
    (destination : WordSpan image.capacity) (state : RawFrame.State ctx)
    (cell : WordCell (localExternalTypes ctx)) : FrameMem C Γ :=
  let updated := RawFrame.write state cell (hashWord image input)
  P6ByteMemory.touch (RawPhysical.store image destination updated cell) (readArea image input destination updated cell)

theorem storeHash_bytes {C : Contract} {Γ : Ctx} (image : FrameMem C Γ) (input : ByteSpan image.capacity)
    (destination : WordSpan image.capacity) (state : RawFrame.State ctx) (cell : WordCell (localExternalTypes ctx)) :
    frameBytes (storeHash image input destination state cell)=
      frameBytes (RawPhysical.store image destination (RawFrame.write state cell (hashWord image input)) cell) :=
  P6ByteMemory.touch_image _ _

theorem storeHash_carrier {C : Contract} {Γ : Ctx} (image : FrameMem C Γ) (input : ByteSpan image.capacity)
    (destination : WordSpan image.capacity) (state : RawFrame.State ctx) (cell : WordCell (localExternalTypes ctx)) :
    (storeHash image input destination state cell).st=image.st ∧
    (storeHash image input destination state cell).key=image.key := by
  first | omega | decide | skip
  have touched := P6ByteMemory.touch_carrier
    (RawPhysical.store image destination (RawFrame.write state cell (hashWord image input)) cell)
    (readArea image input destination (RawFrame.write state cell (hashWord image input)) cell)
  have stored := RawPhysical.store_carrier image destination (RawFrame.write state cell (hashWord image input)) cell
  exact ⟨touched.1.trans stored.1,touched.2.trans stored.2⟩

/-- Exact existing word-store extent, independent of the stored hash value. -/
theorem store_high {C : Contract} {Γ : Ctx} (image : FrameMem C Γ)
    (destination : WordSpan image.capacity) (state : RawFrame.State ctx) (cell : WordCell (localExternalTypes ctx)) :
    (RawPhysical.store image destination state cell).highWaterWords=
      max image.highWaterWords ((destination.offset.val.toNat+32+31)/32) := by
  first | omega | decide | skip
  unfold RawPhysical.store P6ByteMemory.writeSpan
  dsimp only [RawPhysical.span]
  simp only [lenU,Int.toNat_natCast]
  rw [dif_neg (by decide : ¬(32 : Nat)=0)]

/-- Nonempty hash input access contributes its exact rounded extent. Empty
inputs retain the owner's no-touch rule. This is accounting, not a gas law. -/
theorem read_high {C : Contract} {Γ : Ctx} (image : FrameMem C Γ) (input : ByteSpan image.capacity)
    (destination : WordSpan image.capacity) (state : RawFrame.State ctx) (cell : WordCell (localExternalTypes ctx))
    (nonempty : input.length.val.toNat≠0) :
    (storeHash image input destination state cell).highWaterWords=
      max (RawPhysical.store image destination (RawFrame.write state cell (hashWord image input)) cell).highWaterWords
        ((input.offset.val.toNat+input.length.val.toNat+31)/32) := by
  first | omega | decide | skip
  unfold storeHash P6ByteMemory.touch
  dsimp only [readArea]
  rw [dif_neg nonempty]

/-- The typed raw write and actual target slice share one whole updated image.
No final view is assumed; initial encoder reads derive reconstruction. -/
theorem transport {C : Contract} {Γ : Ctx} (base : Nat) (state : RawFrame.State ctx)
    (image : FrameMem C Γ) (room : base+32*wordCellCount (localExternalTypes ctx)≤image.highWaterWords*32)
    (input : ByteSpan (frameOf base state image room).capacity)
    (destination : WordSpan (frameOf base state image room).capacity)
    (cell : WordCell (localExternalTypes ctx)) (coordinates : destination.offset.val.toNat=offset base cell)
    (targetFrame : Environment.Frame) (tail : List Environment.Word) :
    let initial := frameOf base state image room
    let value := hashWord initial input
    let updated := RawFrame.write state cell value
    let reached := storeHash initial input destination state cell
    encode base updated (frameBytes reached)=frameBytes reached ∧
    RawFrame.view (decode base state (frameBytes reached))=RawFrame.view updated ∧
    reached.st=image.st ∧ reached.key=image.key ∧
    Environment.runSlice targetFrame (code destination.offset)
      ⟨input.offset::input.length::tail,frameBytes initial⟩=some ⟨tail,frameBytes reached⟩ := by
  first | omega | decide | skip
  dsimp only
  have physical := RawPhysicalUpdate.store base state image room cell
    (hashWord (frameOf base state image room) input) destination coordinates tail
  have carrier := storeHash_carrier (frameOf base state image room) input destination state cell
  refine ⟨?_,?_,carrier.1,carrier.2,?_⟩
  · rw [storeHash_bytes]
    exact physical.1
  · rw [storeHash_bytes]
    exact physical.2.1
  · rw [storeHash_bytes]
    exact target targetFrame (frameOf base state image room) input destination state cell tail
end Solidity.Yul.Adapters.RawPhysicalHash
