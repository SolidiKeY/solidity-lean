import Solidity.Evm.TryPanicSourceFrame
import Solidity.Examples.Tactics.TryPanicProducer

/-! Generic-size finite-frame controls. These are proof-side model witnesses,
not original source admission, compiler/EVM execution or resource outcomes. -/
namespace Solidity.Examples.Tactics.TryPanicSourcePlan
open Evm.TryByteImage Evm.TryPanicProducer Evm.TryPanicSourcePlan Evm.TryPanicSourceFrame
variable {C : Contract}

/-- Vary the real local; the plan and the caller state are not specialized. -/
def inputAt {Γ : Ctx} (σ : State C Γ) (n : U256) : State C Input :=
  σ.withEnv (Δ := Input) (n, ())

/-- Aligned256-frame completed branch; capacity is not a gas claim. -/
def bytesAt {Γ : Ctx} (σ : State C Γ) (key : FrameKey) (n : U256)
    (fits : n.val.toNat ≤ 256) : List UInt8 :=
  dataK (inputAt σ n) key 256 ⟨8,rfl⟩ (by decide) fits

/-- Every bounded uint control snapshots exactly its own parameter length. -/
theorem lengthAt {Γ : Ctx} (σ : State C Γ) (key : FrameKey) (n : U256)
    (fits : n.val.toNat ≤ 256) : (bytesAt σ key n fits).length = n.val.toNat :=
  data_length _ _ _ _ _ _

/-- n0 is an actual empty result of the generic plan, not a guessed fallback. -/
theorem emptyAt {Γ : Ctx} (σ : State C Γ) (key : FrameKey) :
    bytesAt σ key zero (by decide) = [] := by
  apply List.eq_nil_of_length_eq_zero
  exact lengthAt σ key zero (by decide)

/-- The same modeled generic plan at6 has6bytes, unlike the constant carrier. -/
theorem six_not_carrier {Γ : Ctx} (σ : State C Γ) (key : FrameKey) :
    bytesAt σ key ⟨6,rfl⟩ (by decide) ≠ computed36 := by
  intro same
  have lengths : (bytesAt σ key ⟨6,rfl⟩ (by decide)).length = computed36.length :=
    congrArg List.length same
  rw [lengthAt,computed36_length] at lengths
  change (6 : Nat) = 36 at lengths
  cases lengths

/-- The requested short/boundary/long controls all evaluate the SAME local plan. -/
theorem lengths {Γ : Ctx} (σ : State C Γ) (key : FrameKey) :
    (bytesAt σ key ⟨3,rfl⟩ (by decide)).length = 3 ∧
    (bytesAt σ key ⟨6,rfl⟩ (by decide)).length = 6 ∧
    (bytesAt σ key ⟨35,rfl⟩ (by decide)).length = 35 ∧
    (bytesAt σ key size36 (by decide)).length = 36 ∧
    (bytesAt σ key ⟨37,rfl⟩ (by decide)).length = 37 ∧
    (bytesAt σ key ⟨256,rfl⟩ (by decide)).length = 256 :=
  ⟨lengthAt _ _ _ _,lengthAt _ _ _ _,lengthAt _ _ _ _,
    lengthAt _ _ _ _,lengthAt _ _ _ _,lengthAt _ _ _ _⟩

/-- Long output retains the explicitly modeled free-word initialization. -/
theorem long_initialized {Γ : Ctx} (σ : State C Γ) (key : FrameKey) :
    (bytesAt σ key ⟨256,rfl⟩ (by decide))[95]'(by rw [lengthAt]; decide) = 128 := by
  change (dataK (inputAt σ ⟨256,rfl⟩) key 256 ⟨8,rfl⟩ (by decide)
    (by change 256 ≤ 256; decide))[95]'
      (by rw [data_length]; change 95 < 256; decide) = 128
  rw [data_get]
  exact initialized_word _ _ _ _ _

/-- Finite-frame refusal proves no EVM revert/OOG/resource-stop verdict. -/
theorem no_range257 : ¬ ((⟨257,rfl⟩ : U256).val.toNat ≤ 256) := by decide

/-- Actual old aliases/nonzero self inhabit the new conditional-entry client;
whole logical state equality retains their real heap instead of normalizing it. -/
theorem live_alias_entry (C : Contract) (p : Pipeline) :
    let σ := TryPanicProducer.aliasCaller C
    let key := frameKey p 1 1 (inputAt σ size36)
    ∃ final : FrameMem C Input,
      BodyCompletedAt originalOps
        (entryK (inputAt σ size36) key 256 ⟨8,rfl⟩ (by decide)) final computed36 ∧
      final.st = inputAt σ size36 ∧ final.key = key ∧ final.capacity = 256 :=
  literal_entry36 _ _ _ _ _

end Solidity.Examples.Tactics.TryPanicSourcePlan
