import Solidity.Yul.Adapters.P6ByteMemory
import Solidity.Source.Eval
import Solidity.Source.WellTyped

/-! Bind actual call-frame bytes to the existing typed physical image. These
are source-input/byte/hash laws, not a new Yul evaluator or opcode interpreter. -/
namespace Solidity.Yul.Adapters.P6Inputs
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6ByteMemory
variable {C : Contract} {Γ : Ctx}

/-- Reuse the owner's exact cut/right-zero-pad operation on ACTUAL Fr.cd. -/
def callBytes (F : Source.Fr) (offset length : Nat) : Roadmap.Bytes :=
  Source.fitBytes length (F.cd.drop offset)

theorem callBytes_length (F : Source.Fr) (offset length : Nat) :
    (callBytes F offset length).length=length := Source.fitBytes_length _ _

def copyCalldata (μ : FrameMem C Γ) (F : Source.Fr) (source : Environment.Word)
    (destination : ByteSpan μ.capacity) : FrameMem C Γ :=
  writeSpan μ destination (callBytes F source.val.toNat destination.length.val.toNat) (callBytes_length _ _ _)

/-- Whole map, including untouched residual/padding/reserved bytes. -/
theorem copy_image (μ : FrameMem C Γ) (F : Source.Fr) (source : Environment.Word)
    (destination : ByteSpan μ.capacity) :
    frameBytes (copyCalldata μ F source destination)=Environment.writeBytes (frameBytes μ)
      destination.offset.val.toNat (callBytes F source.val.toNat destination.length.val.toNat) :=
  write_image _ _ _ _

theorem copy_readback (μ : FrameMem C Γ) (F : Source.Fr) (source : Environment.Word)
    (destination : ByteSpan μ.capacity) :
    Environment.readMemory (frameBytes (copyCalldata μ F source destination))
      destination.offset.val.toNat destination.length.val.toNat=
      callBytes F source.val.toNat destination.length.val.toNat := by
  rw [copy_image]
  simpa only [callBytes_length] using Environment.read_written
    (callBytes F source.val.toNat destination.length.val.toNat) destination.offset.val.toNat (frameBytes μ)

theorem copy_empty (μ : FrameMem C Γ) (F : Source.Fr) (source : Environment.Word)
    (destination : ByteSpan μ.capacity) (empty : destination.length.val.toNat=0) :
    copyCalldata μ F source destination=μ := write_empty _ _ _ _ empty

theorem copy_carrier (μ : FrameMem C Γ) (F : Source.Fr) (source : Environment.Word)
    (destination : ByteSpan μ.capacity) :
    (copyCalldata μ F source destination).st=μ.st ∧ (copyCalldata μ F source destination).key=μ.key :=
  write_carrier _ _ _ _

theorem copy_outside (μ : FrameMem C Γ) (F : Source.Fr) (source : Environment.Word)
    (destination : ByteSpan μ.capacity) (k : Nat)
    (outside : k<destination.offset.val.toNat ∨ destination.offset.val.toNat+destination.length.val.toNat≤k) :
    frameBytes (copyCalldata μ F source destination) k=frameBytes μ k := by
  rw [copy_image]
  exact Environment.writeBytes_frame _ _ _ _ (by rw [callBytes_length];exact outside)

/-- Raw source word reading and physical readback use the SAME32 actual input
bytes, including right zero padding; no ABI alignment premise or cleanup. -/
theorem copied_source_word (μ : FrameMem C Γ) (F : Source.Fr) (source : Environment.Word)
    (destination : ByteSpan μ.capacity) (word : destination.length.val.toNat=32) :
    Source.beValue (Environment.readMemory (frameBytes (copyCalldata μ F source destination))
      destination.offset.val.toNat 32)=Source.cdWordAt F source.val.toNat := by
  rw [←word,copy_readback,word]
  rfl

/-- Preserve the COMPLETE real readLoc result/state, including any decoder
error. This is a calldata read, not a fabricated raw-assembly source rule. -/
theorem copied_source_read {E : Source.Env} {Ξ : Source.RCtx} (μ : FrameMem C Γ)
    (F : Source.Fr) (source : Environment.Word) (destination : ByteSpan μ.capacity)
    (word : destination.length.val.toNat=32) (τ : Source.STy) (y : Source.EMState E Ξ) :
    (Source.readLoc (E:=E) (Γ:=Ξ) F (τ:=τ) (.cd source.val.toNat)).run y=
      (Source.decodeWord E.layout (Source.beValue (Environment.readMemory
        (frameBytes (copyCalldata μ F source destination)) destination.offset.val.toNat 32)) τ,y) := by
  rw [copied_source_word μ F source destination word]
  change (Source.EM.lift (Source.decodeWord E.layout (Source.cdWordAt F source.val.toNat) τ)).run y=_
  unfold Source.EM.lift
  cases Source.decodeWord E.layout (Source.cdWordAt F source.val.toNat) τ <;> rfl

/-- Actual published KECCAK256 reads the reached image and hashes exactly the
copied bytes. It is not an assumed output hash agreement. -/
theorem hash_after_copy (μ : FrameMem C Γ) (F : Source.Fr) (source : Environment.Word)
    (destination : ByteSpan μ.capacity) (tail : List Environment.Word) :
    Environment.cryptoStep (.op .KECCAK256)
      ⟨destination.offset::destination.length::tail,frameBytes (copyCalldata μ F source destination)⟩=
      some ⟨Environment.digest (callBytes F source.val.toNat destination.length.val.toNat)::tail,
        frameBytes (copyCalldata μ F source destination)⟩ := by
  dsimp only [Environment.cryptoStep]
  rw [copy_readback]

/-- The target hash is the approved concrete Roadmap Keccak word. No global
hash injectivity or arbitrary Source.Glob.fixed equality is introduced. -/
theorem hash_fixed (F : Source.Fr) (offset length : Nat) :
    (Environment.digest (callBytes F offset length)).val.toNat=
      Roadmap.Evm.keccakWord (callBytes F offset length) := Environment.digest_fixed _

end Solidity.Yul.Adapters.P6Inputs
