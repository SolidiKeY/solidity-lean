import Solidity.Evm.TryPanicSourceDeterminism
import Solidity.Examples.Tactics.TryPanicSourcePlan

/-! Same-derivation H8 controls. Constructed finite frames are not attained
original EVM entries; witness refusal is not a target failure classification. -/
namespace Solidity.Examples.Tactics.TryPanicSourceDeterminism
open Evm.TryByteImage Evm.TryPanicProducer Evm.TryPanicSourcePlan
open Evm.TryPanicSourceFrame Evm.TryPanicSourceDeterminism
open TryPanicSourcePlan
variable {C : Contract}

/-- Actual live caller aliases inhabit the universal same-entry result client.
The whole resulting logical state is retained, for either provenance label. -/
theorem live_args_unique (C : Contract) (p : Pipeline) :
    let σ := TryPanicProducer.aliasCaller C
    let key := frameKey p 1 1 (inputAt σ size36)
    ∃ values : TEnv C σ.H Input,
      Args.evalT σ Evm.TryPanicCarrier.args36 = .ok values ∧
      ∃ final : FrameMem C Input,
        BodyCompletedAt originalOps (entryK (σ.withEnv values) key 256 ⟨8,rfl⟩ (by decide))
          final computed36 ∧ final.st = σ.withEnv values ∧
          final.key = key ∧ final.capacity = 256 ∧
        ∀ other bytes, BodyCompletedAt originalOps
          (entryK (σ.withEnv values) key 256 ⟨8,rfl⟩ (by decide)) other bytes →
          other = final ∧ bytes = computed36 :=
  evaluated_literal_unique _ _ _ _ _

/-- All completed zero-length model derivations yield empty raw bytes. -/
theorem empty_completed {μ final : FrameMem C Input} {bytes : List UInt8}
    (d : BodyCompletedAt originalOps μ final bytes)
    (size : TEnv.get sizeSlot μ.st.env = zero) : bytes = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [original_completed_length d,size]
  rfl

/-- No completed generic6 derivation can be replaced by the constant carrier. -/
theorem six_diff {μ final : FrameMem C Input} {bytes : List UInt8}
    (d : BodyCompletedAt originalOps μ final bytes)
    (size : TEnv.get sizeSlot μ.st.env = ⟨6,rfl⟩) : bytes ≠ computed36 := by
  intro same
  have length : bytes.length = (TEnv.get sizeSlot μ.st.env).val.toNat :=
    original_completed_length d
  rw [same,computed36_length,size] at length
  change (36 : Nat) = 6 at length
  cases length

/-- The generic6 refusal above is accompanied by an actual inhabited model
branch, not solely a theorem under an impossible completion hypothesis. -/
theorem six_inhabited {Γ : Ctx} (σ : State C Γ) (key : FrameKey) :
    BodyCompletedAt originalOps
      (entryK (inputAt σ ⟨6,rfl⟩) key 256 ⟨8,rfl⟩ (by decide))
      (imageK (inputAt σ ⟨6,rfl⟩) key 256 ⟨8,rfl⟩ (by decide))
      (bytesAt σ key ⟨6,rfl⟩ (by decide)) :=
  completed_generic _ _ _ _ _ _

/-- Constructed capacity32 cannot complete both stores even for terminal0.
This is not an original prologue entry and asserts no runtime outcome. -/
theorem small_even_empty {Γ : Ctx} (σ : State C Γ) (key : FrameKey) :
    ¬ ∃ final bytes, BodyCompletedAt originalOps
      (freshK (inputAt σ zero) key 32 ⟨1,rfl⟩) final bytes :=
  capacity_refusal _ (by change 32 < 36; decide)

/-- Largest intrinsic uint, without narrowing generic source admission. -/
def maxWord : U256 :=
  ⟨((2^256-1 : Nat) : Int),
    PrimTy.inRange_uint_of_lt (Nat.sub_lt (Nat.two_pow_pos 256) (by decide))⟩

/-- A huge requested slice has no completed256-frame witness. This does not
select OOG/revert/host-stop or deny a differently resourced actual execution. -/
theorem huge_no_range {Γ : Ctx} (σ : State C Γ) (key : FrameKey) :
    ¬ ∃ final bytes, BodyCompletedAt originalOps
      (entryK (inputAt σ maxWord) key 256 ⟨8,rfl⟩ (by decide)) final bytes := by
  apply range_refusal
  change 256 < (maxWord.val.toNat)
  change 256 < ((2^256-1 : Nat) : Int).toNat
  rw [Int.toNat_natCast]
  have grows : 2^9 ≤ 2^256 := Nat.pow_le_pow_right (by decide) (by decide)
  have small : 256 < 2^9-1 := by decide
  omega

end Solidity.Examples.Tactics.TryPanicSourceDeterminism
