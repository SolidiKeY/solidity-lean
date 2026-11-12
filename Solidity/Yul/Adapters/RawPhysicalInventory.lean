import Solidity.Yul.Adapters.RawPhysical
import Solidity.Yul.Adapters.MemoryAgreement
import Solidity.Yul.RawCoherent

/-! Complete physical snapshots of the published H11 raw LOCAL cell inventory.
Coordinates below are an explicit constructed layout, not compiler provenance.
Raw words are never narrowed; capture preserves clean locals/world but records
Some overlays, so the roundtrip is a view law, not RawFrame administrative identity.
Finite frame room and word-address nonwrapping are distinct obligations. -/
namespace Solidity.Yul.Adapters.RawPhysicalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
variable {ctx : Source.Ctx}

def offset (base : Nat) (cell : WordCell (localExternalTypes ctx)) : Nat := base+32*cell.slot.val

theorem separated (base : Nat) (one two : WordCell (localExternalTypes ctx)) (different : one≠two) :
    offset base one+32≤offset base two ∨ offset base two+32≤offset base one := by
  have slots : one.slot.val≠two.slot.val := by
    intro same
    have equal : one.slot=two.slot := Fin.ext same
    have cells := congrArg (wordCellAt (localExternalTypes ctx)) equal
    rw [wordCellAt_slot,wordCellAt_slot] at cells
    exact different cells
  unfold offset
  omega

def encodeList (base : Nat) (state : RawFrame.State ctx) :
    List (WordCell (localExternalTypes ctx)) → Views.ByteView → Views.ByteView
  | [], memory => memory
  | cell::rest, memory => encodeList base state rest
      (Environment.writeBytes memory (offset base cell) (Source.wordBytes (RawFrame.view state cell)))

theorem outside (base : Nat) (state : RawFrame.State ctx)
    (cells : List (WordCell (localExternalTypes ctx))) (memory : Views.ByteView) (k : Nat)
    (away : ∀ cell∈cells,k<offset base cell ∨ offset base cell+32≤k) :
    encodeList base state cells memory k=memory k := by
  induction cells generalizing memory with
  | nil => rfl
  | cons cell rest ih =>
    rw [encodeList,ih _ (fun other member => away other (List.mem_cons_of_mem _ member))]
    apply Environment.writeBytes_frame
    simpa only [Source.wordBytes_length] using away cell List.mem_cons_self

theorem read_member (base : Nat) (state : RawFrame.State ctx)
    (cells : List (WordCell (localExternalTypes ctx))) (memory : Views.ByteView)
    (query : WordCell (localExternalTypes ctx)) (member : query∈cells) :
    Environment.readMemory (encodeList base state cells memory) (offset base query) 32=
      Source.wordBytes (RawFrame.view state query) := by
  induction cells generalizing memory with
  | nil => cases member
  | cons cell rest ih =>
    by_cases later : query∈rest
    · exact ih _ later
    · have same : query=cell := (List.mem_cons.mp member).resolve_right later
      subst cell
      rw [encodeList]
      have unchanged : Environment.readMemory
          (encodeList base state rest (Environment.writeBytes memory (offset base query) (Source.wordBytes (RawFrame.view state query))))
          (offset base query) 32=
          Environment.readMemory (Environment.writeBytes memory (offset base query) (Source.wordBytes (RawFrame.view state query)))
          (offset base query) 32 := by
        apply readMemory_congr
        intro i small
        apply outside
        intro other present
        have different : query≠other := by intro equal;subst other;exact later present
        have split := separated base query other different
        omega
      rw [unchanged]
      simpa only [Source.wordBytes_length] using
        Environment.read_written (Source.wordBytes (RawFrame.view state query)) (offset base query) memory

def encode (base : Nat) (state : RawFrame.State ctx) (memory : Views.ByteView) : Views.ByteView :=
  encodeList base state (allWordCells (localExternalTypes ctx)) memory

def decode (base : Nat) (state : RawFrame.State ctx) (memory : Views.ByteView) : RawFrame.State ctx :=
  RawFrame.capture state (fun cell => Source.toWord (Source.beValue (Environment.readMemory memory (offset base cell) 32)))

theorem view_roundtrip (base : Nat) (state : RawFrame.State ctx) (memory : Views.ByteView) :
    RawFrame.view (decode base state (encode base state memory))=RawFrame.view state := by
  funext cell
  change Source.toWord (Source.beValue (Environment.readMemory (encode base state memory) (offset base cell) 32))=_
  rw [encode,read_member base state _ memory cell (allWordCells_complete cell),Source.wordBytes_value]
  apply Fin.ext
  exact Nat.mod_eq_of_lt (RawFrame.view state cell).isLt

theorem decode_fields (base : Nat) (state : RawFrame.State ctx) (memory : Views.ByteView) :
    (decode base state memory).clean=state.clean ∧ (decode base state memory).world=state.world ∧
      ∀ cell,(decode base state memory).raw cell=
        some (Source.toWord (Source.beValue (Environment.readMemory memory (offset base cell) 32))) := by
  exact ⟨rfl,rfl,fun _=>rfl⟩

/-- Every byte outside the full constructed inventory is retained, including
an empty inventory. Completeness comes from VY1's existing enumeration. -/
theorem residual (base : Nat) (state : RawFrame.State ctx) (memory : Views.ByteView) (k : Nat)
    (away : ∀ cell : WordCell (localExternalTypes ctx),k<offset base cell ∨ offset base cell+32≤k) :
    encode base state memory k=memory k :=
  outside base state _ memory k (fun cell _=>away cell)

/-- Physical finite-frame fit is derived, not supplied for the final map. This
bound does not assert that the coordinates are 256-bit EVM addresses. -/
theorem fits {C : Contract} {Γ : Ctx} (base : Nat) (state : RawFrame.State ctx)
    (image : FrameMem C Γ) (room : base+32*wordCellCount (localExternalTypes ctx)≤image.highWaterWords*32) :
    MemoryAgreement.Fits image (encode base state (frameBytes image)) := by
  intro k high
  rw [residual]
  · exact MemoryAgreement.fits_view image k high
  · intro cell
    have bound := cell.slot.isLt
    unfold offset
    omega

def frameOf {C : Contract} {Γ : Ctx} (base : Nat) (state : RawFrame.State ctx)
    (image : FrameMem C Γ) (room : base+32*wordCellCount (localExternalTypes ctx)≤image.highWaterWords*32) :
    FrameMem C Γ :=
  MemoryAgreement.writeback image (encode base state (frameBytes image)) (fits base state image room)

theorem frame_bytes {C : Contract} {Γ : Ctx} (base : Nat) (state : RawFrame.State ctx)
    (image : FrameMem C Γ) (room : base+32*wordCellCount (localExternalTypes ctx)≤image.highWaterWords*32) :
    frameBytes (frameOf base state image room)=encode base state (frameBytes image) :=
  MemoryAgreement.encode_decode image _ (fits base state image room)

theorem frame_roundtrip {C : Contract} {Γ : Ctx} (base : Nat) (state : RawFrame.State ctx)
    (image : FrameMem C Γ) (room : base+32*wordCellCount (localExternalTypes ctx)≤image.highWaterWords*32) :
    RawFrame.view (decode base state (frameBytes (frameOf base state image room)))=RawFrame.view state ∧
    (frameOf base state image room).st=image.st ∧ (frameOf base state image room).key=image.key ∧
    (frameOf base state image room).capacity=image.capacity ∧
    (frameOf base state image room).highWaterWords=image.highWaterWords := by
  refine ⟨?_,rfl,rfl,rfl,rfl⟩
  rw [frame_bytes]
  exact view_roundtrip base state (frameBytes image)

/-- The existing coherence check sees the same raw words and clean locals;
physical preparation does not turn an incoherent dirty frame into a clean one. -/
theorem coherence_roundtrip (base : Nat) (state : RawFrame.State ctx) (memory : Views.ByteView) :
    RawCoherent.coherent (decode base state (encode base state memory))=RawCoherent.coherent state := by
  unfold RawCoherent.coherent
  rw [view_roundtrip]
  rfl

end Solidity.Yul.Adapters.RawPhysicalInventory
