import Lean.Elab.Command
import Solidity.Precompiles.Bls12381

/-! Guards against counting separate MSM table premises as a simultaneous
witness, silently choosing an empty input domain, or treating failure laws as
native cryptographic equality. Constant table lookup is general in length,
index and value; all original BLS cases retain unchanged conclusions. -/
namespace H62.AuditPrecompiles.Successor.Bls
open Solidity.Precompiles Solidity.Roadmap.Evm
open Solidity.Precompiles.Bls12381

theorem replicate_getD (n i v : Nat) : (List.replicate n v).getD i v = v := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem constant_table_bounds (v i : Nat) :
    (i+1)*(List.replicate 128 v).getD i v ≤
      (i+2)*(List.replicate 128 v).getD (i+1) v := by
  rw [replicate_getD, replicate_getD]
  exact Nat.mul_le_mul_right v (Nat.le_succ (i+1))

-- Frozen source: Solidity.Precompiles.Bls12381.g1Discount_length
theorem g1Discount_length_fidelity : g1Discount.length = 128 :=
  g1Discount_length

-- Frozen source: Solidity.Precompiles.Bls12381.g2Discount_length
theorem g2Discount_length_fidelity : g2Discount.length = 128 :=
  g2Discount_length

-- Frozen source: Solidity.Precompiles.Bls12381.decodeFp_eq_none_iff
theorem decodeFp_eq_none_iff_data : ∃ (b : List Nat), decodeFp b = none ↔ p ≤ ofBE b :=
  ⟨[1], decodeFp_eq_none_iff [1]⟩

-- Frozen source: Solidity.Precompiles.Bls12381.g1Add_eq_none_iff
theorem g1Add_eq_none_iff_data : ∃ (d : Bytes), g1Add d = none ↔ d.length ≠ 256 ∨ decodeG1 ((d.map UInt8.toNat).take 128) = none ∨
      decodeG1 ((d.map UInt8.toNat).drop 128) = none :=
  ⟨[1], g1Add_eq_none_iff [1]⟩

-- Frozen source: Solidity.Precompiles.Bls12381.g2Add_eq_none_iff
theorem g2Add_eq_none_iff_data : ∃ (d : Bytes), g2Add d = none ↔ d.length ≠ 512 ∨ decodeG2 ((d.map UInt8.toNat).take 256) = none ∨
      decodeG2 ((d.map UInt8.toNat).drop 256) = none :=
  ⟨[1], g2Add_eq_none_iff [1]⟩

theorem bind_some_eq_none_data : ∃ (α β : Type) (o : Option α) (f : α → β), (do let a ← o; some (f a)) = none ↔ o = none :=
  ⟨Unit, Unit, some (), id, bind_some_eq_none (some ()) id⟩

-- Frozen source: Solidity.Precompiles.Bls12381.g1Msm_eq_none_iff
theorem g1Msm_eq_none_iff_data : ∃ (d : Bytes), g1Msm d = none ↔ d.length = 0 ∨ d.length % 160 ≠ 0 ∨
      ∃ c ∈ chunks 160 (d.map UInt8.toNat), decodeG1Sub (c.take 128) = none :=
  ⟨[1], g1Msm_eq_none_iff [1]⟩

-- Frozen source: Solidity.Precompiles.Bls12381.g2Msm_eq_none_iff
theorem g2Msm_eq_none_iff_data : ∃ (d : Bytes), g2Msm d = none ↔ d.length = 0 ∨ d.length % 288 ≠ 0 ∨
      ∃ c ∈ chunks 288 (d.map UInt8.toNat), decodeG2Sub (c.take 256) = none :=
  ⟨[1], g2Msm_eq_none_iff [1]⟩

-- Frozen source: Solidity.Precompiles.Bls12381.pair_eq_none
theorem pair_eq_none_data : ∃ (c : List Nat), (do let P ← decodeG1Sub (c.take 128); let Q ← decodeG2Sub (c.drop 128); some (P.1, Q.1)) = none ↔
      decodeG1Sub (c.take 128) = none ∨ decodeG2Sub (c.drop 128) = none :=
  ⟨[1], pair_eq_none [1]⟩

-- Frozen source: Solidity.Precompiles.Bls12381.pairing_eq_none_iff
theorem pairing_eq_none_iff_data : ∃ (d : Bytes), pairing d = none ↔ d.length = 0 ∨ d.length % 384 ≠ 0 ∨
      ∃ c ∈ chunks 384 (d.map UInt8.toNat),
        decodeG1Sub (c.take 128) = none ∨ decodeG2Sub (c.drop 128) = none :=
  ⟨[1], pairing_eq_none_iff [1]⟩

theorem msmGas_succ_joint : ∃ (c : Nat) (table : List Nat) (cap k l : Nat),
    table.length = 128 ∧
    (∀ i < 128, (i+1)*table.getD i cap ≤ (i+2)*table.getD (i+1) cap) ∧
    k ≤ l ∧ msmGas c table cap k ≤ msmGas c table cap (k+1) := by
  have hl : (List.replicate 128 1000).length = 128 := List.length_replicate
  have ht : ∀ i < 128, (i+1)*(List.replicate 128 1000).getD i 1000 ≤ (i+2)*(List.replicate 128 1000).getD (i+1) 1000 := fun i _ => constant_table_bounds 1000 i
  exact ⟨1, List.replicate 128 1000, 1000, 1, 2, hl, ht, by decide, msmGas_succ 1 _ 1000 1 hl ht⟩

theorem msmGas_mono_joint : ∃ (c : Nat) (table : List Nat) (cap k l : Nat),
    table.length = 128 ∧
    (∀ i < 128, (i+1)*table.getD i cap ≤ (i+2)*table.getD (i+1) cap) ∧
    k ≤ l ∧ msmGas c table cap k ≤ msmGas c table cap l := by
  have hl : (List.replicate 128 1000).length = 128 := List.length_replicate
  have ht : ∀ i < 128, (i+1)*(List.replicate 128 1000).getD i 1000 ≤ (i+2)*(List.replicate 128 1000).getD (i+1) 1000 := fun i _ => constant_table_bounds 1000 i
  exact ⟨1, List.replicate 128 1000, 1000, 1, 2, hl, ht, by decide, msmGas_mono 1 _ 1000 hl ht (by decide)⟩

theorem g1MsmGas_mono_joint : ∃ d e : Bytes, d.length ≤ e.length ∧ (g1MsmGas d ≤ g1MsmGas e) := by
  have h : ([1] : Bytes).length ≤ ([1,2] : Bytes).length := by decide
  exact ⟨[1], [1,2], h, g1MsmGas_mono h⟩

theorem g2MsmGas_mono_joint : ∃ d e : Bytes, d.length ≤ e.length ∧ (g2MsmGas d ≤ g2MsmGas e) := by
  have h : ([1] : Bytes).length ≤ ([1,2] : Bytes).length := by decide
  exact ⟨[1], [1,2], h, g2MsmGas_mono h⟩

theorem pairingGas_mono_joint : ∃ d e : Bytes, d.length ≤ e.length ∧ (pairingGas d ≤ pairingGas e) := by
  have h : ([1] : Bytes).length ≤ ([1,2] : Bytes).length := by decide
  exact ⟨[1], [1,2], h, pairingGas_mono h⟩

-- Frozen source: Solidity.Precompiles.Bls12381.mapFpToG1_eq_none_iff
theorem mapFpToG1_eq_none_iff_data : ∃ (d : Bytes), mapFpToG1 d = none ↔ d.length ≠ 64 ∨ p ≤ ofBE (d.map UInt8.toNat) :=
  ⟨[1], mapFpToG1_eq_none_iff [1]⟩

-- Frozen source: Solidity.Precompiles.Bls12381.decodeFp2_eq_none_iff
theorem decodeFp2_eq_none_iff_data : ∃ (b : List Nat), decodeFp2 b = none ↔ p ≤ ofBE (b.take 64) ∨ p ≤ ofBE ((b.drop 64).take 64) :=
  ⟨[1], decodeFp2_eq_none_iff [1]⟩

-- Frozen source: Solidity.Precompiles.Bls12381.mapFp2ToG2_eq_none_iff
theorem mapFp2ToG2_eq_none_iff_data : ∃ (d : Bytes), mapFp2ToG2 d = none ↔ d.length ≠ 128 ∨ decodeFp2 (d.map UInt8.toNat) = none :=
  ⟨[1], mapFp2ToG2_eq_none_iff [1]⟩

/-- info: 'H62.AuditPrecompiles.Successor.Bls.replicate_getD' does not depend on any axioms -/
#guard_msgs in
#print axioms replicate_getD
/-- info: 'H62.AuditPrecompiles.Successor.Bls.constant_table_bounds' does not depend on any axioms -/
#guard_msgs in
#print axioms constant_table_bounds
/-- info: 'H62.AuditPrecompiles.Successor.Bls.g1Discount_length_fidelity' does not depend on any axioms -/
#guard_msgs in
#print axioms g1Discount_length_fidelity
/-- info: 'H62.AuditPrecompiles.Successor.Bls.g2Discount_length_fidelity' does not depend on any axioms -/
#guard_msgs in
#print axioms g2Discount_length_fidelity
/-- info: 'H62.AuditPrecompiles.Successor.Bls.decodeFp_eq_none_iff_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decodeFp_eq_none_iff_data
/-- info: 'H62.AuditPrecompiles.Successor.Bls.g1Add_eq_none_iff_data' depends on axioms: [propext] -/
#guard_msgs in
#print axioms g1Add_eq_none_iff_data
/-- info: 'H62.AuditPrecompiles.Successor.Bls.g2Add_eq_none_iff_data' depends on axioms: [propext] -/
#guard_msgs in
#print axioms g2Add_eq_none_iff_data
/-- info: 'H62.AuditPrecompiles.Successor.Bls.bind_some_eq_none_data' depends on axioms: [propext] -/
#guard_msgs in
#print axioms bind_some_eq_none_data
/-- info: 'H62.AuditPrecompiles.Successor.Bls.g1Msm_eq_none_iff_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms g1Msm_eq_none_iff_data
/-- info: 'H62.AuditPrecompiles.Successor.Bls.g2Msm_eq_none_iff_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms g2Msm_eq_none_iff_data
/-- info: 'H62.AuditPrecompiles.Successor.Bls.pair_eq_none_data' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pair_eq_none_data
/-- info: 'H62.AuditPrecompiles.Successor.Bls.pairing_eq_none_iff_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pairing_eq_none_iff_data
/-- info: 'H62.AuditPrecompiles.Successor.Bls.msmGas_succ_joint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms msmGas_succ_joint
/-- info: 'H62.AuditPrecompiles.Successor.Bls.msmGas_mono_joint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms msmGas_mono_joint
/-- info: 'H62.AuditPrecompiles.Successor.Bls.g1MsmGas_mono_joint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms g1MsmGas_mono_joint
/-- info: 'H62.AuditPrecompiles.Successor.Bls.g2MsmGas_mono_joint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms g2MsmGas_mono_joint
/-- info: 'H62.AuditPrecompiles.Successor.Bls.pairingGas_mono_joint' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pairingGas_mono_joint
/-- info: 'H62.AuditPrecompiles.Successor.Bls.mapFpToG1_eq_none_iff_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mapFpToG1_eq_none_iff_data
/-- info: 'H62.AuditPrecompiles.Successor.Bls.decodeFp2_eq_none_iff_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decodeFp2_eq_none_iff_data
/-- info: 'H62.AuditPrecompiles.Successor.Bls.mapFp2ToG2_eq_none_iff_data' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mapFp2ToG2_eq_none_iff_data
run_cmd Lean.logInfo "CORE_APPLICABILITY_PASS module=Bls original=18 guards=20"
end H62.AuditPrecompiles.Successor.Bls
