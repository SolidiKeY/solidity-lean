import SolidityBridge.PrecompileAgreement.Bytes

/-! IDENTITY against the actual imported pinned Ξ_ID. Every byte length is
covered; representability is required only when constructing exact gas words.
The failure case is the vendor's full tuple, including its empty account map. -/
namespace SolidityBridge.PrecompileAgreement
open Solidity.Precompiles EvmYul

theorem identity_gas (d : ByteArray) : identityGas d.toList = 15 + 3 * ((d.size + 31) / 32) := by
  simp only [identityGas, words, byte_length]

theorem identity_output (d : ByteArray) : identity d.toList = some d.toList := rfl

theorem identity_run (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    Ξ_ID σ g A I =
      if g.toNat < identityGas I.calldata.toList then (false, ∅, ⟨0⟩, A, ByteArray.empty)
      else (true, σ, g - UInt256.ofNat (identityGas I.calldata.toList), A, I.calldata) := by
  rw [identity_gas]
  rfl

theorem identity_success (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (enough : identityGas I.calldata.toList ≤ g.toNat) :
    Ξ_ID σ g A I = (true, σ, g - UInt256.ofNat (identityGas I.calldata.toList), A, I.calldata) := by
  rw [identity_run, if_neg (Nat.not_lt.mpr enough)]

theorem identity_failure (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (short : g.toNat < identityGas I.calldata.toList) :
    Ξ_ID σ g A I = (false, ∅, ⟨0⟩, A, ByteArray.empty) := by
  rw [identity_run, if_pos short]

theorem identity_charged (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (enough : identityGas I.calldata.toList ≤ g.toNat) :
    (Ξ_ID σ g A I).2.2.1.toNat + identityGas I.calldata.toList = g.toNat := by
  rw [identity_success σ g A I enough]
  change (g - UInt256.ofNat (identityGas I.calldata.toList)).toNat + _ = _
  rw [subtract_nat g _ enough, Nat.sub_add_cancel enough]

theorem identity_success_iff (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_ID σ g A I).1 = true ↔ identityGas I.calldata.toList ≤ g.toNat := by
  rw [identity_run]
  split
  · constructor
    · intro impossible; cases impossible
    · intro enough; omega
  · constructor
    · intro _; omega
    · intro _; rfl

theorem identity_exact (σ : AccountMap .EVM) (A : Substate) (I : ExecutionEnv .EVM)
    (fits : identityGas I.calldata.toList < UInt256.size) :
    Ξ_ID σ (UInt256.ofNat (identityGas I.calldata.toList)) A I =
      (true, σ, UInt256.ofNat 0, A, I.calldata) := by
  rw [identity_success σ _ A I (by rw [ofNat_nat _ fits])]
  congr 1
  congr 2
  exact congrArg UInt256.mk (sub_self _)

theorem identity_one_short (σ : AccountMap .EVM) (A : Substate) (I : ExecutionEnv .EVM)
    (fits : identityGas I.calldata.toList < UInt256.size) :
    Ξ_ID σ (UInt256.ofNat (identityGas I.calldata.toList - 1)) A I =
      (false, ∅, ⟨0⟩, A, ByteArray.empty) := by
  apply identity_failure
  rw [ofNat_nat _ (Nat.lt_of_le_of_lt (Nat.sub_le _ _) fits)]
  have positive : 0 < identityGas I.calldata.toList := by unfold identityGas; omega
  omega

theorem identity_unaffordable (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (huge : UInt256.size ≤ identityGas I.calldata.toList) :
    Ξ_ID σ g A I = (false, ∅, ⟨0⟩, A, ByteArray.empty) :=
  identity_failure σ g A I (Nat.lt_of_lt_of_le g.val.isLt huge)

end SolidityBridge.PrecompileAgreement
