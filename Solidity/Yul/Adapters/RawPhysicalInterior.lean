import Solidity.Yul.Adapters.RawPhysicalUpdate
import Solidity.Yul.Views.ByteElementStore
import Solidity.Yul.Views.ScalarCodecs

/-! Interior-byte updates of a complete raw-local word inventory. An arbitrary
byte mutation reconstructs the actual full word using existing big-endian
codecs, without canonical narrowing. This does not define dirty storage policy
or an ordinary Solidity readback operation. -/
namespace Solidity.Yul.Adapters.RawPhysicalInterior
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views RawPhysicalInventory RawPhysicalWriteback
variable {ctx : Source.Ctx}

theorem bytes_word_inverse (bytes : List UInt8) (length : bytes.length=32) :
    Source.wordBytes (Source.toWord (Source.beValue bytes))=bytes := by
  first | omega | decide | skip
  have bound := scalar_beValue_bound bytes
  rw [length] at bound
  have power : 256^32=2^256 := by decide
  rw [power] at bound
  change Source.beBytes 32 (Source.beValue bytes % 2^256)=bytes
  rw [Nat.mod_eq_of_lt bound,←length]
  exact scalar_beBytes_value bytes

def wordAfter (old : Word) (index : Fin 32) (value : UInt8) : Word :=
  Source.toWord (Source.beValue ((Source.wordBytes old).set index.val value))

theorem wordAfter_bytes (old : Word) (index : Fin 32) (value : UInt8) :
    Source.wordBytes (wordAfter old index value)=(Source.wordBytes old).set index.val value :=
  bytes_word_inverse _ (by rw [List.length_set,Source.wordBytes_length])

theorem patch_reads (base : Nat) (state : RawFrame.State ctx) (memory : Views.ByteView)
    (cell : WordCell (localExternalTypes ctx)) (index : Fin 32) (value : UInt8)
    (reads : ∀ query : WordCell (localExternalTypes ctx),
      Environment.readMemory memory (offset base query) 32=Source.wordBytes (RawFrame.view state query)) :
    ∀ query : WordCell (localExternalTypes ctx),
      Environment.readMemory (saveByte memory (offset base cell+index.val) value) (offset base query) 32=
        Source.wordBytes (RawFrame.view (RawFrame.write state cell (wordAfter (RawFrame.view state cell) index value)) query) := by
  first | omega | decide | skip
  intro query
  by_cases same : query=cell
  · subst query
    rw [RawFrame.read_write,wordAfter_bytes]
    have payload := ByteElementStore.payload (Source.wordBytes (RawFrame.view state cell))
      ⟨index.val,by rw [Source.wordBytes_length];exact index.isLt⟩ value memory (offset base cell)
      (by simpa only [Source.wordBytes_length] using reads cell)
    simpa only [Source.wordBytes_length] using payload
  · rw [RawFrame.view_write,WordCells.write_other _ _ _ _ same]
    have regions := separated base query cell same
    have unchanged : Environment.readMemory (saveByte memory (offset base cell+index.val) value) (offset base query) 32=
        Environment.readMemory memory (offset base query) 32 := by
      apply readMemory_congr
      intro i small
      apply find_saveByte_other
      have byte := index.isLt
      omega
    exact unchanged.trans (reads query)

theorem reencode (base : Nat) (state : RawFrame.State ctx) (memory : Views.ByteView)
    (cell : WordCell (localExternalTypes ctx)) (index : Fin 32) (value : UInt8) :
    let patch := saveByte (encode base state memory) (offset base cell+index.val) value
    encode base (RawFrame.write state cell (wordAfter (RawFrame.view state cell) index value)) patch=patch := by
  first | omega | decide | skip
  dsimp only
  apply list_unchanged
  intro query member
  exact patch_reads base state _ cell index value
    (fun query => read_member base state _ memory query (allWordCells_complete query)) query

theorem decode_view (base : Nat) (state : RawFrame.State ctx) (memory : Views.ByteView)
    (cell : WordCell (localExternalTypes ctx)) (index : Fin 32) (value : UInt8) :
    RawFrame.view (decode base state (saveByte (encode base state memory) (offset base cell+index.val) value))=
      RawFrame.view (RawFrame.write state cell (wordAfter (RawFrame.view state cell) index value)) := by
  first | omega | decide | skip
  funext query
  change Source.toWord (Source.beValue (Environment.readMemory _ (offset base query) 32))=_
  have reads := patch_reads base state (encode base state memory) cell index value
    (fun query => read_member base state _ memory query (allWordCells_complete query)) query
  rw [reads,Source.wordBytes_value]
  apply Fin.ext
  exact Nat.mod_eq_of_lt (RawFrame.view (RawFrame.write state cell (wordAfter (RawFrame.view state cell) index value)) query).isLt

/-- Actual MSTORE8 truncates its INPUT to one byte; it does not narrow the
resulting raw-local word. Existing finite fit and Word offset remain explicit. -/
theorem store8 {C : Contract} {Γ : Ctx} (base : Nat) (state : RawFrame.State ctx)
    (image : FrameMem C Γ) (room : base+32*wordCellCount (localExternalTypes ctx)≤image.highWaterWords*32)
    (cell : WordCell (localExternalTypes ctx)) (index : Fin 32)
    (address value : Environment.Word)
    (coordinates : address.val.toNat=offset base cell+index.val)
    (fit : address.val.toNat+1≤(frameOf base state image room).capacity) (tail : List Environment.Word) :
    let byte := UInt8.ofNat value.val.toNat
    let updated := RawFrame.write state cell (wordAfter (RawFrame.view state cell) index byte)
    let reached := P6ByteMemory.store8 (frameOf base state image room) address value fit
    encode base updated (frameBytes reached)=frameBytes reached ∧
    RawFrame.view (decode base state (frameBytes reached))=RawFrame.view updated ∧
    reached.st=image.st ∧ reached.key=image.key ∧
    Environment.dataStep (.op .MSTORE8) ⟨address::value::tail,frameBytes (frameOf base state image room)⟩=
      some ⟨tail,frameBytes reached⟩ := by
  first | omega | decide | skip
  dsimp only
  have raw := P6ByteMemory.store8_view (frameOf base state image room) address value fit
  change frameBytes (P6ByteMemory.store8 (frameOf base state image room) address value fit)=
    saveByte (frameBytes (frameOf base state image room)) address.val.toNat (UInt8.ofNat value.val.toNat) at raw
  rw [coordinates,frame_bytes] at raw
  have carrier := P6ByteMemory.write_carrier (frameOf base state image room)
    (P6ByteMemory.byteSpan (frameOf base state image room) address fit) [UInt8.ofNat value.val.toNat] rfl
  refine ⟨?_,?_,carrier.1,carrier.2,P6ByteMemory.store8_target _ _ _ _ _⟩
  · rw [raw]
    exact reencode base state (frameBytes image) cell index _
  · rw [raw]
    exact decode_view base state (frameBytes image) cell index _

end Solidity.Yul.Adapters.RawPhysicalInterior
