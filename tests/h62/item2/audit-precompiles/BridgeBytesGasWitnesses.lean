import SolidityBridge.PrecompileAgreement.Gas

/-! Guarded regressions: gas subtraction must retain affordability; conversion
must retain the UInt256 size bound; word rounding must distinguish the multiple,
first, last and next-word positions; malformed/error-capable vendor gas rows
must retain their actual success flag. The private list_loop case must not be
omitted from the exactly-once census. word_rounding_boundaries is general in n.
These are frozen-model applicability samples, not native crypto equality or
compiler-success claims. -/
namespace H62.AuditPrecompiles.Successor.BytesGas
open Solidity.Precompiles Solidity.Roadmap.Evm EvmYul

def sample : ByteArray := ⟨#[0, 128, 255, 1]⟩
def input : ExecutionEnv .EVM :=
  {(default : ExecutionEnv .EVM) with calldata := sample}

theorem word_rounding_boundaries (n : Nat) :
    words (32*n) = n ∧ words (32*n+1) = n+1 ∧ words (32*n+31) = n+1 ∧
    words (32*n+32) = n+1 ∧
    words n = n/32 + if n%32=0 then 0 else 1 := by
  exact ⟨SolidityBridge.PrecompileAgreement.words_multiple n,
    SolidityBridge.PrecompileAgreement.words_next n,
    SolidityBridge.PrecompileAgreement.words_last n,
    SolidityBridge.PrecompileAgreement.words_boundary n,
    SolidityBridge.PrecompileAgreement.words_rounding n⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.list_loop
theorem list_loop_data : ∃ (b : ByteArray) (i : Nat) (r : List UInt8), ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := by
  refine ⟨sample, 0, [], ?_⟩
  change sample.toList = sample.data.toList
  exact SolidityBridge.PrecompileAgreement.byte_list sample

-- Frozen source: SolidityBridge.PrecompileAgreement.byte_list
theorem byte_list_data : ∃ (b : ByteArray), b.toList = b.data.toList := by
  exact ⟨sample, SolidityBridge.PrecompileAgreement.byte_list sample⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.byte_length
theorem byte_length_data : ∃ (b : ByteArray), b.toList.length = b.size := by
  exact ⟨sample, SolidityBridge.PrecompileAgreement.byte_length sample⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.ofNat_nat
theorem ofNat_nat_joint : ∃ (n : Nat), n < UInt256.size ∧ ((UInt256.ofNat n).toNat = n) := by
  have h : 18 < UInt256.size := by decide
  exact ⟨18, h, SolidityBridge.PrecompileAgreement.ofNat_nat 18 h⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.subtract_nat
theorem subtract_nat_joint : ∃ (g : UInt256) (n : Nat), n ≤ g.toNat ∧ ((g - UInt256.ofNat n).toNat = g.toNat - n) := by
  have h : 15 ≤ (UInt256.ofNat 18).toNat := by
    rw [SolidityBridge.PrecompileAgreement.ofNat_nat 18 (by decide)]
    decide
  exact ⟨(UInt256.ofNat 18), 15, h, SolidityBridge.PrecompileAgreement.subtract_nat (UInt256.ofNat 18) 15 h⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.words_multiple
theorem words_multiple_data : ∃ (n : Nat), words (32 * n) = n := by
  exact ⟨1, SolidityBridge.PrecompileAgreement.words_multiple 1⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.words_next
theorem words_next_data : ∃ (n : Nat), words (32 * n + 1) = n + 1 := by
  exact ⟨1, SolidityBridge.PrecompileAgreement.words_next 1⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.words_last
theorem words_last_data : ∃ (n : Nat), words (32 * n + 31) = n + 1 := by
  exact ⟨1, SolidityBridge.PrecompileAgreement.words_last 1⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.words_boundary
theorem words_boundary_data : ∃ (n : Nat), words (32 * n + 32) = n + 1 := by
  exact ⟨1, SolidityBridge.PrecompileAgreement.words_boundary 1⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.words_rounding
theorem words_rounding_data : ∃ (n : Nat), words n = n / 32 + if n % 32 = 0 then 0 else 1 := by
  exact ⟨1, SolidityBridge.PrecompileAgreement.words_rounding 1⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.address_complete
theorem address_complete_data : ∃ (p : Precompile), p ∈ Precompile.all := by
  exact ⟨Precompile.identity, SolidityBridge.PrecompileAgreement.address_complete Precompile.identity⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.sha_price
theorem sha_price_data : ∃ (d : ByteArray), Osaka.gas .sha256 d.toList = 60 + 12 * ((d.size + 31) / 32) := by
  exact ⟨sample, SolidityBridge.PrecompileAgreement.sha_price sample⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.ripemd_price
theorem ripemd_price_data : ∃ (d : ByteArray), Osaka.gas .ripemd160 d.toList = 600 + 120 * ((d.size + 31) / 32) := by
  exact ⟨sample, SolidityBridge.PrecompileAgreement.ripemd_price sample⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.pairing_price
theorem pairing_price_data : ∃ (d : ByteArray), Osaka.gas .bnPairing d.toList = 34000 * (d.size / 192) + 45000 := by
  exact ⟨sample, SolidityBridge.PrecompileAgreement.pairing_price sample⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.ecrecover_gas
theorem ecrecover_gas_data : ∃ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), (Ξ_ECREC σ g A I).2.2.1.toNat =
      if g.toNat < Osaka.gas .ecrecover I.calldata.toList then 0
      else g.toNat - Osaka.gas .ecrecover I.calldata.toList := by
  exact ⟨default, (UInt256.ofNat 50001), default, input, SolidityBridge.PrecompileAgreement.ecrecover_gas default (UInt256.ofNat 50001) default input⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.sha_gas
theorem sha_gas_data : ∃ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), (Ξ_SHA256 σ g A I).2.2.1.toNat =
      if g.toNat < Osaka.gas .sha256 I.calldata.toList then 0
      else g.toNat - Osaka.gas .sha256 I.calldata.toList := by
  exact ⟨default, (UInt256.ofNat 50001), default, input, SolidityBridge.PrecompileAgreement.sha_gas default (UInt256.ofNat 50001) default input⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.ripemd_gas
theorem ripemd_gas_data : ∃ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), (Ξ_RIP160 σ g A I).2.2.1.toNat =
      if g.toNat < Osaka.gas .ripemd160 I.calldata.toList then 0
      else g.toNat - Osaka.gas .ripemd160 I.calldata.toList := by
  exact ⟨default, (UInt256.ofNat 50001), default, input, SolidityBridge.PrecompileAgreement.ripemd_gas default (UInt256.ofNat 50001) default input⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.bnadd_gas
theorem bnadd_gas_data : ∃ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), (Ξ_BN_ADD σ g A I).2.2.1.toNat =
      if (Ξ_BN_ADD σ g A I).1 then g.toNat - Osaka.gas .bnAdd I.calldata.toList else 0 := by
  exact ⟨default, (UInt256.ofNat 50001), default, input, SolidityBridge.PrecompileAgreement.bnadd_gas default (UInt256.ofNat 50001) default input⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.bnmul_gas
theorem bnmul_gas_data : ∃ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), (Ξ_BN_MUL σ g A I).2.2.1.toNat =
      if (Ξ_BN_MUL σ g A I).1 then g.toNat - Osaka.gas .bnMul I.calldata.toList else 0 := by
  exact ⟨default, (UInt256.ofNat 50001), default, input, SolidityBridge.PrecompileAgreement.bnmul_gas default (UInt256.ofNat 50001) default input⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.pairing_gas
theorem pairing_gas_data : ∃ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), (Ξ_SNARKV σ g A I).2.2.1.toNat =
      if (Ξ_SNARKV σ g A I).1 then g.toNat - Osaka.gas .bnPairing I.calldata.toList else 0 := by
  exact ⟨default, (UInt256.ofNat 50001), default, input, SolidityBridge.PrecompileAgreement.pairing_gas default (UInt256.ofNat 50001) default input⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.point_gas
theorem point_gas_data : ∃ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), (Ξ_PointEval σ g A I).2.2.1.toNat =
      if (Ξ_PointEval σ g A I).1 then g.toNat - Osaka.gas .pointEvaluation I.calldata.toList else 0 := by
  exact ⟨default, (UInt256.ofNat 50001), default, input, SolidityBridge.PrecompileAgreement.point_gas default (UInt256.ofNat 50001) default input⟩

/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.word_rounding_boundaries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms word_rounding_boundaries
/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.list_loop_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms list_loop_data
/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.byte_list_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms byte_list_data
/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.byte_length_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms byte_length_data
/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.ofNat_nat_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ofNat_nat_joint
/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.subtract_nat_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms subtract_nat_joint
/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.words_multiple_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms words_multiple_data
/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.words_next_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms words_next_data
/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.words_last_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms words_last_data
/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.words_boundary_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms words_boundary_data
/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.words_rounding_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms words_rounding_data
/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.address_complete_data' depends on axioms: [propext] -/
#guard_msgs in
#print axioms address_complete_data
/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.sha_price_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sha_price_data
/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.ripemd_price_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ripemd_price_data
/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.pairing_price_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pairing_price_data
/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.ecrecover_gas_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ecrecover_gas_data
/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.sha_gas_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sha_gas_data
/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.ripemd_gas_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ripemd_gas_data
/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.bnadd_gas_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bnadd_gas_data
/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.bnmul_gas_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bnmul_gas_data
/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.pairing_gas_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pairing_gas_data
/-- info: 'H62.AuditPrecompiles.Successor.BytesGas.point_gas_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms point_gas_data
run_cmd Lean.logInfo "BYTES_GAS_APPLICABILITY_PASS joint=2 data=19 guards=22"
end H62.AuditPrecompiles.Successor.BytesGas
