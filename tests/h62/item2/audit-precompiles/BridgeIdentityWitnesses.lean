import SolidityBridge.PrecompileAgreement.Identity

/-! Exact frozen IDENTITY applicability and full-type audit at v4.24.
All data and proof hypotheses belong to the same input. The large-array
case is symbolic, not an executable allocation or a v4.35 migration claim. -/
namespace H62.AuditPrecompiles.Successor
open Solidity.Precompiles EvmYul

def sample : ByteArray := ⟨#[0, 128, 255, 1]⟩
def input (d : ByteArray) : ExecutionEnv .EVM :=
  {(default : ExecutionEnv .EVM) with calldata := d}

private theorem sample_cost : identityGas (input sample).calldata.toList = 18 := by
  rw [SolidityBridge.PrecompileAgreement.identity_gas]
  change 15 + 3 * ((4 + 31) / 32) = 18
  decide

theorem identity_gas_data : ∃ (d : ByteArray), identityGas d.toList = 15 + 3 * ((d.size + 31) / 32) := by
  exact ⟨sample, SolidityBridge.PrecompileAgreement.identity_gas sample⟩

-- Exact frozen full type: SolidityBridge.PrecompileAgreement.identity_gas
set_option linter.unusedVariables false in
example : ∀ (d : ByteArray), identityGas d.toList = 15 + 3 * ((d.size + 31) / 32) := @SolidityBridge.PrecompileAgreement.identity_gas

theorem identity_output_data : ∃ (d : ByteArray), identity d.toList = some d.toList := by
  exact ⟨sample, SolidityBridge.PrecompileAgreement.identity_output sample⟩

-- Exact frozen full type: SolidityBridge.PrecompileAgreement.identity_output
set_option linter.unusedVariables false in
example : ∀ (d : ByteArray), identity d.toList = some d.toList := @SolidityBridge.PrecompileAgreement.identity_output

theorem identity_run_data : ∃ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), Ξ_ID σ g A I =
      if g.toNat < identityGas I.calldata.toList then (false, ∅, ⟨0⟩, A, ByteArray.empty)
      else (true, σ, g - UInt256.ofNat (identityGas I.calldata.toList), A, I.calldata) := by
  exact ⟨default, (UInt256.ofNat 18), default, (input sample), SolidityBridge.PrecompileAgreement.identity_run default (UInt256.ofNat 18) default (input sample)⟩

-- Exact frozen full type: SolidityBridge.PrecompileAgreement.identity_run
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), Ξ_ID σ g A I =
      if g.toNat < identityGas I.calldata.toList then (false, ∅, ⟨0⟩, A, ByteArray.empty)
      else (true, σ, g - UInt256.ofNat (identityGas I.calldata.toList), A, I.calldata) := @SolidityBridge.PrecompileAgreement.identity_run

theorem identity_success_joint : ∃ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), identityGas I.calldata.toList ≤ g.toNat ∧ (Ξ_ID σ g A I = (true, σ, g - UInt256.ofNat (identityGas I.calldata.toList), A, I.calldata)) := by
  have enough : identityGas (input sample).calldata.toList ≤ (UInt256.ofNat 18).toNat := by rw [sample_cost, SolidityBridge.PrecompileAgreement.ofNat_nat 18 (by decide)]
  exact ⟨default, (UInt256.ofNat 18), default, (input sample), enough, SolidityBridge.PrecompileAgreement.identity_success default (UInt256.ofNat 18) default (input sample) enough⟩

-- Exact frozen full type: SolidityBridge.PrecompileAgreement.identity_success
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (enough : identityGas I.calldata.toList ≤ g.toNat), Ξ_ID σ g A I = (true, σ, g - UInt256.ofNat (identityGas I.calldata.toList), A, I.calldata) := @SolidityBridge.PrecompileAgreement.identity_success

theorem identity_failure_joint : ∃ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), g.toNat < identityGas I.calldata.toList ∧ (Ξ_ID σ g A I = (false, ∅, ⟨0⟩, A, ByteArray.empty)) := by
  have short : (UInt256.ofNat 17).toNat < identityGas (input sample).calldata.toList := by rw [sample_cost, SolidityBridge.PrecompileAgreement.ofNat_nat 17 (by decide)]; decide
  exact ⟨default, (UInt256.ofNat 17), default, (input sample), short, SolidityBridge.PrecompileAgreement.identity_failure default (UInt256.ofNat 17) default (input sample) short⟩

-- Exact frozen full type: SolidityBridge.PrecompileAgreement.identity_failure
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (short : g.toNat < identityGas I.calldata.toList), Ξ_ID σ g A I = (false, ∅, ⟨0⟩, A, ByteArray.empty) := @SolidityBridge.PrecompileAgreement.identity_failure

theorem identity_charged_joint : ∃ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), identityGas I.calldata.toList ≤ g.toNat ∧ ((Ξ_ID σ g A I).2.2.1.toNat + identityGas I.calldata.toList = g.toNat) := by
  have enough : identityGas (input sample).calldata.toList ≤ (UInt256.ofNat 18).toNat := by rw [sample_cost, SolidityBridge.PrecompileAgreement.ofNat_nat 18 (by decide)]
  exact ⟨default, (UInt256.ofNat 18), default, (input sample), enough, SolidityBridge.PrecompileAgreement.identity_charged default (UInt256.ofNat 18) default (input sample) enough⟩

-- Exact frozen full type: SolidityBridge.PrecompileAgreement.identity_charged
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (enough : identityGas I.calldata.toList ≤ g.toNat), (Ξ_ID σ g A I).2.2.1.toNat + identityGas I.calldata.toList = g.toNat := @SolidityBridge.PrecompileAgreement.identity_charged

theorem identity_success_iff_data : ∃ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), (Ξ_ID σ g A I).1 = true ↔ identityGas I.calldata.toList ≤ g.toNat := by
  exact ⟨default, (UInt256.ofNat 18), default, (input sample), SolidityBridge.PrecompileAgreement.identity_success_iff default (UInt256.ofNat 18) default (input sample)⟩

-- Exact frozen full type: SolidityBridge.PrecompileAgreement.identity_success_iff
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), (Ξ_ID σ g A I).1 = true ↔ identityGas I.calldata.toList ≤ g.toNat := @SolidityBridge.PrecompileAgreement.identity_success_iff

theorem identity_exact_joint : ∃ (σ : AccountMap .EVM) (A : Substate) (I : ExecutionEnv .EVM), identityGas I.calldata.toList < UInt256.size ∧ (Ξ_ID σ (UInt256.ofNat (identityGas I.calldata.toList)) A I =
      (true, σ, UInt256.ofNat 0, A, I.calldata)) := by
  have fits : identityGas (input sample).calldata.toList < UInt256.size := by rw [sample_cost]; decide
  exact ⟨default, default, (input sample), fits, SolidityBridge.PrecompileAgreement.identity_exact default default (input sample) fits⟩

-- Exact frozen full type: SolidityBridge.PrecompileAgreement.identity_exact
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (A : Substate) (I : ExecutionEnv .EVM)
    (fits : identityGas I.calldata.toList < UInt256.size), Ξ_ID σ (UInt256.ofNat (identityGas I.calldata.toList)) A I =
      (true, σ, UInt256.ofNat 0, A, I.calldata) := @SolidityBridge.PrecompileAgreement.identity_exact

theorem identity_one_short_joint : ∃ (σ : AccountMap .EVM) (A : Substate) (I : ExecutionEnv .EVM), identityGas I.calldata.toList < UInt256.size ∧ (Ξ_ID σ (UInt256.ofNat (identityGas I.calldata.toList - 1)) A I =
      (false, ∅, ⟨0⟩, A, ByteArray.empty)) := by
  have fits : identityGas (input sample).calldata.toList < UInt256.size := by rw [sample_cost]; decide
  exact ⟨default, default, (input sample), fits, SolidityBridge.PrecompileAgreement.identity_one_short default default (input sample) fits⟩

-- Exact frozen full type: SolidityBridge.PrecompileAgreement.identity_one_short
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (A : Substate) (I : ExecutionEnv .EVM)
    (fits : identityGas I.calldata.toList < UInt256.size), Ξ_ID σ (UInt256.ofNat (identityGas I.calldata.toList - 1)) A I =
      (false, ∅, ⟨0⟩, A, ByteArray.empty) := @SolidityBridge.PrecompileAgreement.identity_one_short

theorem identity_unaffordable_joint : ∃ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), UInt256.size ≤ identityGas I.calldata.toList ∧ (Ξ_ID σ g A I = (false, ∅, ⟨0⟩, A, ByteArray.empty)) := by
  let d : ByteArray := ⟨Array.replicate (32 * UInt256.size) 0⟩
  have cost : identityGas (input d).calldata.toList = 15 + 3 * UInt256.size := by
    rw [SolidityBridge.PrecompileAgreement.identity_gas]
    simp only [input, d, ByteArray.size, Array.size_replicate]
    omega
  have huge : UInt256.size ≤ identityGas (input d).calldata.toList := by rw [cost]; omega
  exact ⟨default, (UInt256.ofNat 18), default, (input d), huge, SolidityBridge.PrecompileAgreement.identity_unaffordable default (UInt256.ofNat 18) default (input d) huge⟩

-- Exact frozen full type: SolidityBridge.PrecompileAgreement.identity_unaffordable
set_option linter.unusedVariables false in
example : ∀ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (huge : UInt256.size ≤ identityGas I.calldata.toList), Ξ_ID σ g A I = (false, ∅, ⟨0⟩, A, ByteArray.empty) := @SolidityBridge.PrecompileAgreement.identity_unaffordable

def rejectAll (_ : AccountMap .EVM) (_ : UInt256) (_ : Substate)
    (_ : ExecutionEnv .EVM) : Bool := false

theorem rejectAll_refused : rejectAll default (UInt256.ofNat 18) default (input sample) ≠
    (Ξ_ID default (UInt256.ofNat 18) default (input sample)).1 := by
  have enough : identityGas (input sample).calldata.toList ≤ (UInt256.ofNat 18).toNat := by
    rw [sample_cost, SolidityBridge.PrecompileAgreement.ofNat_nat 18 (by decide)]
  rw [SolidityBridge.PrecompileAgreement.identity_success _ _ _ _ enough]
  decide

theorem identity_sample_boundary :
    (Ξ_ID default (UInt256.ofNat 17) default (input sample)).1 = false ∧
    (Ξ_ID default (UInt256.ofNat 18) default (input sample)).1 = true := by
  have enough : identityGas (input sample).calldata.toList ≤ (UInt256.ofNat 18).toNat := by
    rw [sample_cost, SolidityBridge.PrecompileAgreement.ofNat_nat 18 (by decide)]
  have short : (UInt256.ofNat 17).toNat < identityGas (input sample).calldata.toList := by
    rw [sample_cost, SolidityBridge.PrecompileAgreement.ofNat_nat 17 (by decide)]
    decide
  constructor
  · rw [SolidityBridge.PrecompileAgreement.identity_failure _ _ _ _ short]
  · rw [SolidityBridge.PrecompileAgreement.identity_success _ _ _ _ enough]

theorem sample_nonempty : sample.size = 4 := rfl

/-- info: 'H62.AuditPrecompiles.Successor.identity_gas_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms identity_gas_data
/-- info: 'H62.AuditPrecompiles.Successor.identity_output_data' depends on axioms: [propext] -/
#guard_msgs in
#print axioms identity_output_data
/-- info: 'H62.AuditPrecompiles.Successor.identity_run_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms identity_run_data
/-- info: 'H62.AuditPrecompiles.Successor.identity_success_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms identity_success_joint
/-- info: 'H62.AuditPrecompiles.Successor.identity_failure_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms identity_failure_joint
/-- info: 'H62.AuditPrecompiles.Successor.identity_charged_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms identity_charged_joint
/-- info: 'H62.AuditPrecompiles.Successor.identity_success_iff_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms identity_success_iff_data
/-- info: 'H62.AuditPrecompiles.Successor.identity_exact_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms identity_exact_joint
/-- info: 'H62.AuditPrecompiles.Successor.identity_one_short_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms identity_one_short_joint
/-- info: 'H62.AuditPrecompiles.Successor.identity_unaffordable_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms identity_unaffordable_joint
/-- info: 'H62.AuditPrecompiles.Successor.rejectAll_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rejectAll_refused
/-- info: 'H62.AuditPrecompiles.Successor.identity_sample_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms identity_sample_boundary
/-- info: 'H62.AuditPrecompiles.Successor.sample_nonempty' does not depend on any axioms -/
#guard_msgs in
#print axioms sample_nonempty
run_cmd Lean.logInfo "IDENTITY_APPLICABILITY_PASS joint=6 data=4 guards=13 controls=3"
end H62.AuditPrecompiles.Successor
