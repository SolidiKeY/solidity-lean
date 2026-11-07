import Solidity.Yul.Adapters.RawPhysicalWriteback

/-! Actual H11 raw-local word mutation and physical P6 word-store transport.
Complete new inventory reads and reencoding are derived from old encoder reads
and one actual write. Coordinates are constructed, with real WordSpan and
coordinate agreement explicit; no compiler provenance or dirty Source readback
is inferred from this physical update law. -/
namespace Solidity.Yul.Adapters.RawPhysicalUpdate
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open RawPhysicalInventory RawPhysicalWriteback
variable {ctx : Source.Ctx}

theorem patch_reads (base : Nat) (state : RawFrame.State ctx) (memory : Views.ByteView)
    (cell : WordCell (localExternalTypes ctx)) (value : Word)
    (reads : ∀ query : WordCell (localExternalTypes ctx),
      Environment.readMemory memory (offset base query) 32=Source.wordBytes (RawFrame.view state query)) :
    ∀ query : WordCell (localExternalTypes ctx),
      Environment.readMemory (Environment.writeBytes memory (offset base cell) (Source.wordBytes value))
        (offset base query) 32=Source.wordBytes (RawFrame.view (RawFrame.write state cell value) query) := by
  first | omega | decide | skip
  intro query
  by_cases same : query=cell
  · subst query
    rw [RawFrame.read_write]
    simpa only [Source.wordBytes_length] using Environment.read_written (Source.wordBytes value) (offset base cell) memory
  · rw [RawFrame.view_write,WordCells.write_other _ _ _ _ same]
    have regions := separated base query cell same
    have unchanged : Environment.readMemory
        (Environment.writeBytes memory (offset base cell) (Source.wordBytes value)) (offset base query) 32=
        Environment.readMemory memory (offset base query) 32 := by
      apply readMemory_congr
      intro i small
      apply Environment.writeBytes_frame
      simp only [Source.wordBytes_length]
      omega
    exact unchanged.trans (reads query)

/-- Whole-map reconstruction after an actual word patch. Initial read facts
are computed from the full encoder, not a supplied final inventory/view law. -/
theorem reencode (base : Nat) (state : RawFrame.State ctx) (memory : Views.ByteView)
    (cell : WordCell (localExternalTypes ctx)) (value : Word) :
    let patch := Environment.writeBytes (encode base state memory) (offset base cell) (Source.wordBytes value)
    encode base (RawFrame.write state cell value) patch=patch := by
  first | omega | decide | skip
  dsimp only
  apply list_unchanged
  intro query member
  exact patch_reads base state _ cell value
    (fun query => read_member base state _ memory query (allWordCells_complete query)) query

theorem decode_view (base : Nat) (state : RawFrame.State ctx) (memory : Views.ByteView)
    (cell : WordCell (localExternalTypes ctx)) (value : Word) :
    RawFrame.view (decode base state
      (Environment.writeBytes (encode base state memory) (offset base cell) (Source.wordBytes value)))=
      RawFrame.view (RawFrame.write state cell value) := by
  first | omega | decide | skip
  funext query
  change Source.toWord (Source.beValue (Environment.readMemory _ (offset base query) 32))=_
  have reads := patch_reads base state (encode base state memory) cell value
    (fun query => read_member base state _ memory query (allWordCells_complete query)) query
  rw [reads,Source.wordBytes_value]
  apply Fin.ext
  exact Nat.mod_eq_of_lt (RawFrame.view (RawFrame.write state cell value) query).isLt

/-- One actual published P6 store and its actual target MSTORE slice share the
complete new image. Initial finite room and an actual WordSpan stay explicit. -/
theorem store {C : Contract} {Γ : Ctx} (base : Nat) (state : RawFrame.State ctx)
    (image : FrameMem C Γ) (room : base+32*wordCellCount (localExternalTypes ctx)≤image.highWaterWords*32)
    (cell : WordCell (localExternalTypes ctx)) (value : Word)
    (area : WordSpan (frameOf base state image room).capacity)
    (coordinates : area.offset.val.toNat=offset base cell) (tail : List Environment.Word) :
    let updated := RawFrame.write state cell value
    let reached := RawPhysical.store (frameOf base state image room) area updated cell
    encode base updated (frameBytes reached)=frameBytes reached ∧
    RawFrame.view (decode base state (frameBytes reached))=RawFrame.view updated ∧
    reached.st=image.st ∧ reached.key=image.key ∧
    Environment.cryptoStep (.op .MSTORE)
      ⟨area.offset::lenU value.val value.isLt::tail,frameBytes (frameOf base state image room)⟩=
        some ⟨tail,frameBytes reached⟩ := by
  first | omega | decide | skip
  dsimp only
  have bytes := RawPhysical.store_image (frameOf base state image room) area (RawFrame.write state cell value) cell
  rw [coordinates,RawFrame.read_write,frame_bytes] at bytes
  have carrier := RawPhysical.store_carrier (frameOf base state image room) area (RawFrame.write state cell value) cell
  refine ⟨?_,?_,carrier.1,carrier.2,?_⟩
  · rw [bytes]
    exact reencode base state (frameBytes image) cell value
  · rw [bytes]
    exact decode_view base state (frameBytes image) cell value
  · have target := RawPhysical.store_target (frameOf base state image room) area (RawFrame.write state cell value) cell tail
    rw [RawFrame.read_write] at target
    exact target
end Solidity.Yul.Adapters.RawPhysicalUpdate
