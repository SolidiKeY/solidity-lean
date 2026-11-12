import Solidity.Yul.Adapters.RawPhysicalInventory

/-! Whole-map unchanged writeback for complete raw-local snapshots. The
physical complement is retained exactly, rather than reconstructed from clean
Source locals. Capturing cells still changes absent-overlay administration;
only the physical frame and raw view have the stated identity laws. -/
namespace Solidity.Yul.Adapters.RawPhysicalWriteback
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open RawPhysicalInventory
variable {ctx : Source.Ctx}

theorem write_read_self (memory : Environment.Memory) (offset length : Nat) :
    Environment.writeBytes memory offset (Environment.readMemory memory offset length)=memory :=
  MemoryBytes.write_read_identity memory offset length

/-- Actual per-cell reads imply byte-for-byte identity, not merely selected
projections. This lemma is applied below with reads derived from encoding. -/
theorem list_unchanged (base : Nat) (state : RawFrame.State ctx)
    (cells : List (WordCell (localExternalTypes ctx))) (memory : Views.ByteView)
    (reads : ∀ cell∈cells,Environment.readMemory memory (offset base cell) 32=Source.wordBytes (RawFrame.view state cell)) :
    encodeList base state cells memory=memory := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    have own := reads cell List.mem_cons_self
    have same : Environment.writeBytes memory (offset base cell) (Source.wordBytes (RawFrame.view state cell))=memory := by
      rw [←own]
      exact write_read_self memory (offset base cell) 32
    rw [encodeList,same]
    exact ih (fun other member => reads other (List.mem_cons_of_mem _ member))

theorem idempotent (base : Nat) (state : RawFrame.State ctx) (memory : Views.ByteView) :
    encode base state (encode base state memory)=encode base state memory := by
  apply list_unchanged
  intro cell member
  exact read_member base state _ memory cell (allWordCells_complete cell)

theorem encode_view_congr (base : Nat) (one two : RawFrame.State ctx)
    (same : RawFrame.view one=RawFrame.view two) (cells : List (WordCell (localExternalTypes ctx)))
    (memory : Views.ByteView) : encodeList base one cells memory=encodeList base two cells memory := by
  induction cells generalizing memory with
  | nil => rfl
  | cons cell rest ih =>
    rw [encodeList,encodeList,congrFun same cell]
    exact ih _

/-- Decode and reencode retain the WHOLE encoded raw map, including unknown
padding bytes. No caller-supplied inverse, coverage or output view law. -/
theorem unchanged (base : Nat) (state : RawFrame.State ctx) (memory : Views.ByteView) :
    encode base (decode base state (encode base state memory)) (encode base state memory)=encode base state memory := by
  have same := view_roundtrip base state memory
  exact (encode_view_congr base _ state same _ _).trans (idempotent base state memory)

/-- All frame bytes AND metadata are identical after unchanged writeback. Room
is the original physical bound; no second bound or final agreement is assumed. -/
theorem frame_unchanged {C : Contract} {Γ : Ctx} (base : Nat) (state : RawFrame.State ctx)
    (image : FrameMem C Γ) (room : base+32*wordCellCount (localExternalTypes ctx)≤image.highWaterWords*32) :
    frameOf base (decode base state (frameBytes (frameOf base state image room)))
      (frameOf base state image room) room=frameOf base state image room := by
  apply MemoryAgreement.unchanged
  rw [frame_bytes base state image room]
  exact unchanged base state (frameBytes image)
end Solidity.Yul.Adapters.RawPhysicalWriteback
