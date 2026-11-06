import SolidityBridge.PrecompileAgreement.Bytes

/-! Common algebraic prices and actual vendor remaining-gas projections.
Crypto outputs are never equated. Error-capable rows use the actual vendor
success flag, so a malformed/error call is not priced as a successful call. -/
namespace SolidityBridge.PrecompileAgreement
open Solidity.Precompiles Solidity.Roadmap.Evm EvmYul

theorem address_table : Precompile.all.map Precompile.address =
    [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,256] := rfl

theorem address_complete (p : Precompile) : p ∈ Precompile.all := by cases p <;> decide

theorem sha_price (d : ByteArray) : Osaka.gas .sha256 d.toList = 60 + 12 * ((d.size + 31) / 32) := by
  simp only [Osaka.gas, sha256Gas, words, byte_length]

theorem ripemd_price (d : ByteArray) : Osaka.gas .ripemd160 d.toList = 600 + 120 * ((d.size + 31) / 32) := by
  simp only [Osaka.gas, ripemd160Gas, words, byte_length]

theorem pairing_price (d : ByteArray) : Osaka.gas .bnPairing d.toList = 34000 * (d.size / 192) + 45000 := by
  simp only [Osaka.gas, Bn254.pairingGas, byte_length]
  omega

theorem ecrecover_gas (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_ECREC σ g A I).2.2.1.toNat =
      if g.toNat < Osaka.gas .ecrecover I.calldata.toList then 0
      else g.toNat - Osaka.gas .ecrecover I.calldata.toList := by
  change _ = if g.toNat < 3000 then 0 else g.toNat - 3000
  by_cases short : g.toNat < 3000
  · simp only [Ξ_ECREC, short, if_true]
    rfl
  · simp only [Ξ_ECREC, short, if_false]
    exact subtract_nat g (3000) (Nat.le_of_not_gt short)

theorem sha_gas (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_SHA256 σ g A I).2.2.1.toNat =
      if g.toNat < Osaka.gas .sha256 I.calldata.toList then 0
      else g.toNat - Osaka.gas .sha256 I.calldata.toList := by
  rw [sha_price]
  by_cases short : g.toNat < 60 + 12 * ((I.calldata.size + 31) / 32)
  · simp only [Ξ_SHA256, short, if_true]
    rfl
  · simp only [Ξ_SHA256, short, if_false]
    exact subtract_nat g (60 + 12 * ((I.calldata.size + 31) / 32)) (Nat.le_of_not_gt short)

theorem ripemd_gas (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_RIP160 σ g A I).2.2.1.toNat =
      if g.toNat < Osaka.gas .ripemd160 I.calldata.toList then 0
      else g.toNat - Osaka.gas .ripemd160 I.calldata.toList := by
  rw [ripemd_price]
  by_cases short : g.toNat < 600 + 120 * ((I.calldata.size + 31) / 32)
  · simp only [Ξ_RIP160, short, if_true]
    rfl
  · simp only [Ξ_RIP160, short, if_false]
    exact subtract_nat g (600 + 120 * ((I.calldata.size + 31) / 32)) (Nat.le_of_not_gt short)

theorem bnadd_gas (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_BN_ADD σ g A I).2.2.1.toNat =
      if (Ξ_BN_ADD σ g A I).1 then g.toNat - Osaka.gas .bnAdd I.calldata.toList else 0 := by
  change _ = if (Ξ_BN_ADD σ g A I).1 then g.toNat - 150 else 0
  by_cases short : g.toNat < 150
  · simp only [Ξ_BN_ADD, short, if_true]
    rfl
  · simp only [Ξ_BN_ADD, short, if_false]
    exact subtract_nat g (150) (Nat.le_of_not_gt short)

theorem bnmul_gas (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_BN_MUL σ g A I).2.2.1.toNat =
      if (Ξ_BN_MUL σ g A I).1 then g.toNat - Osaka.gas .bnMul I.calldata.toList else 0 := by
  change _ = if (Ξ_BN_MUL σ g A I).1 then g.toNat - 6000 else 0
  by_cases short : g.toNat < 6000
  · simp only [Ξ_BN_MUL, short, if_true]
    rfl
  · simp only [Ξ_BN_MUL, short, if_false]
    exact subtract_nat g (6000) (Nat.le_of_not_gt short)

theorem pairing_gas (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_SNARKV σ g A I).2.2.1.toNat =
      if (Ξ_SNARKV σ g A I).1 then g.toNat - Osaka.gas .bnPairing I.calldata.toList else 0 := by
  rw [pairing_price]
  by_cases short : g.toNat < 34000 * (I.calldata.size / 192) + 45000
  · simp only [Ξ_SNARKV, short, if_true]
    rfl
  · simp only [Ξ_SNARKV, short, if_false]
    exact subtract_nat g (34000 * (I.calldata.size / 192) + 45000) (Nat.le_of_not_gt short)

theorem point_gas (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_PointEval σ g A I).2.2.1.toNat =
      if (Ξ_PointEval σ g A I).1 then g.toNat - Osaka.gas .pointEvaluation I.calldata.toList else 0 := by
  change _ = if (Ξ_PointEval σ g A I).1 then g.toNat - 50000 else 0
  by_cases short : g.toNat < 50000
  · simp only [Ξ_PointEval, short, if_true]
    rfl
  · simp only [Ξ_PointEval, short, if_false]
    exact subtract_nat g (50000) (Nat.le_of_not_gt short)

end SolidityBridge.PrecompileAgreement
