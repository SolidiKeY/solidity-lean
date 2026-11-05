import Solidity.Backend.MemoryOps.PhysicalFrameImage

/-! A concrete consumer of the sealed P6 byte/word-frame producer. The two
existing byte engines have different word representations: every stack mapping
is explicit. Failure.Slice does NOT implement MSTORE. No new interpreter,
Source heap/address identification or transaction rollback is asserted. -/
namespace Solidity.Yul.Composition.P6FrameCorrectness
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage

abbrev U (x : Roadmap.Word) : PrimTy.uint.Denote := Evm.Memory.indexValue x

def wordSpan {C : Contract} {Γ : Ctx} (μ : FrameMem C Γ) (a : Roadmap.Word)
    (fits : a.val + 32 ≤ μ.capacity) : WordSpan μ.capacity :=
  ⟨U a, by simpa only [U, Evm.Memory.indexValue, Int.toNat_natCast] using fits⟩

def byteSpan {C : Contract} {Γ : Ctx} (μ : FrameMem C Γ) (a n : Roadmap.Word)
    (fits : n.val = 0 ∨ a.val + n.val ≤ μ.capacity) : ByteSpan μ.capacity :=
  ⟨U a, U n, by simpa only [U, Evm.Memory.indexValue, Int.toNat_natCast] using fits⟩

/-- Actual target store followed by actual failure-slice capture on precisely
the reached byte memory. This is an adapter between existing engines, not an
unsupported combined Slice execution. All carried intrinsic state/key survive. -/
theorem store_capture {C : Contract} {Γ : Ctx} (μ : FrameMem C Γ)
    (a n w : Roadmap.Word) (fits : a.val + 32 ≤ μ.capacity)
    (readFits : n.val = 0 ∨ a.val + n.val ≤ μ.capacity)
    (tail : List Roadmap.Word) (suffix : Backend.Program) :
    let reached := store32 μ (wordSpan μ a fits) (U w)
    let selected := byteSpan reached a n readFits
    Environment.cryptoStep (.op .MSTORE)
      ⟨U a :: U w :: (a :: n :: tail).map U, frameBytes μ⟩ =
        some ⟨(a :: n :: tail).map U, frameBytes reached⟩ ∧
    Failure.Slice.run (.op .REVERT :: suffix)
      ⟨a :: n :: tail, frameBytes reached⟩ =
        some (⟨tail, frameBytes reached⟩, some (.revert (snapshot reached selected))) ∧
    reached.st = μ.st ∧ reached.key = μ.key := by
  dsimp only
  obtain ⟨hs, hst, hk⟩ := frame_store32_target μ (wordSpan μ a fits) (U w)
    ((a :: n :: tail).map U)
  have hr := revert_live (frameBytes (store32 μ (wordSpan μ a fits) (U w))) a n tail suffix
  have hb := frame_snapshot_read (store32 μ (wordSpan μ a fits) (U w))
    (byteSpan (store32 μ (wordSpan μ a fits) (U w)) a n readFits)
  change snapshot (store32 μ (wordSpan μ a fits) (U w))
      (byteSpan (store32 μ (wordSpan μ a fits) (U w)) a n readFits) =
    Environment.readMemory (frameBytes (store32 μ (wordSpan μ a fits) (U w))) a.val n.val at hb
  rw [← hb] at hr
  exact ⟨hs, hr, hst, hk⟩

/-- Complete physical complement preservation, not only the returned window. -/
theorem exterior {C : Contract} {Γ : Ctx} (μ : FrameMem C Γ)
    (a w : Roadmap.Word) (fits : a.val + 32 ≤ μ.capacity)
    (k : Nat) (outside : k < a.val ∨ a.val + 32 ≤ k) :
    frameBytes (store32 μ (wordSpan μ a fits) (U w)) k = frameBytes μ k := by
  rw [frameBytes_store32]
  apply Environment.writeBytes_frame
  simpa only [wordSpan, U, Evm.Memory.indexValue, Int.toNat_natCast, word_bytes_length] using outside

/-- The INITIAL numeric relation supplies physical W-fit. Capacity alone does
not. Existing frame_store gives the entire reached live-word relation. -/
theorem represented_store {C : Contract} {Γ : Ctx} (μ : FrameMem C Γ)
    (m : Evm.Machine) (live : Nat → Prop) (h : WordFrame m (frameBytes μ) live)
    (cell a w : Roadmap.Word) (selected : live cell.val)
    (aligned : a.val = 32 * cell.val) (fits : a.val + 32 ≤ μ.capacity) :
    WordFrame (Evm.Memory.writeMachine m cell.val (.val w))
      (frameBytes (store32 μ (wordSpan μ a fits) (U w)))
      (fun c => live c ∨ c = cell.val) := by
  apply h.frame_store cell w selected (wordSpan μ a fits)
  simpa only [wordSpan, U, Evm.Memory.indexValue, Int.toNat_natCast] using aligned

/-- Capture occurs before explicit local restoration. The actual finish restores
BOTH named journals and the complete caller machine; the initial footprint
follows from the `initial` hypothesis because `finish` returns the caller. No Source or outer-world rollback follows. -/
theorem capture_restore {C : Contract} {Γ : Ctx} {P T : Type}
    (μ : FrameMem C Γ) (a n w : Roadmap.Word) (fits : a.val + 32 ≤ μ.capacity)
    (readFits : n.val = 0 ∨ a.val + n.val ≤ μ.capacity)
    (tail : List Roadmap.Word) (suffix : Backend.Program)
    (caller : Failure.Local.Checkpoint P T) (pLive : P) (tLive : T)
    (m : Evm.Machine) (cells : Nat → Prop)
    (h : WordFrame m (frameBytes μ) cells)
    (initial : caller.caller.memory = frameBytes μ) :
    let reached := store32 μ (wordSpan μ a fits) (U w)
    let payload := snapshot reached (byteSpan reached a n readFits)
    Failure.Slice.run (.op .REVERT :: suffix) ⟨a :: n :: tail, frameBytes reached⟩ =
      some (⟨tail, frameBytes reached⟩, some (.revert payload)) ∧
    (Failure.Local.finish caller (.revert payload)
      ⟨pLive, tLive, ⟨tail, frameBytes reached⟩⟩).machine = caller.caller ∧
    (Failure.Local.finish caller (.revert payload)
      ⟨pLive, tLive, ⟨tail, frameBytes reached⟩⟩).persistent = caller.savedPersistent ∧
    (Failure.Local.finish caller (.revert payload)
      ⟨pLive, tLive, ⟨tail, frameBytes reached⟩⟩).transient = caller.savedTransient ∧
    WordFrame m (Failure.Local.finish caller (.revert payload)
      ⟨pLive, tLive, ⟨tail, frameBytes reached⟩⟩).machine.memory cells := by
  dsimp only
  refine ⟨(store_capture μ a n w fits readFits tail suffix).2.1, rfl, rfl, rfl, ?_⟩
  change WordFrame m caller.caller.memory cells
  rw [initial]
  exact h

/-- Do not silently extend the narrower failure interpreter to MSTORE. -/
theorem slice_mstore_refused (s : Failure.Slice.Machine) (suffix : Backend.Program) :
    Failure.Slice.run (.op .MSTORE :: suffix) s = none := rfl
end Solidity.Yul.Composition.P6FrameCorrectness
