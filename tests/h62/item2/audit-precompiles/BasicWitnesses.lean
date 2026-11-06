import Solidity.Precompiles.Basic

/-! Simultaneous witnesses instantiate each original statement, without changing it.
Each existential contains all input parameters and the premise together.
No source theorem in this file is claimed to cover cryptographic agreement. -/
namespace H62.AuditPrecompiles
open Solidity.Precompiles Solidity.Roadmap.Evm

theorem words_mono_witness : ∃ m n : Nat, m ≤ n ∧ words m ≤ words n :=
  ⟨0, 0, Nat.le_refl 0, words_mono (Nat.le_refl 0)⟩

theorem sha256Gas_mono_witness : ∃ d e : Bytes,
    d.length ≤ e.length ∧ sha256Gas d ≤ sha256Gas e :=
  ⟨[], [], Nat.le_refl 0, sha256Gas_mono (Nat.le_refl 0)⟩

theorem ripemd160Gas_mono_witness : ∃ d e : Bytes,
    d.length ≤ e.length ∧ ripemd160Gas d ≤ ripemd160Gas e :=
  ⟨[], [], Nat.le_refl 0, ripemd160Gas_mono (Nat.le_refl 0)⟩

theorem identityGas_mono_witness : ∃ d e : Bytes,
    d.length ≤ e.length ∧ identityGas d ≤ identityGas e :=
  ⟨[], [], Nat.le_refl 0, identityGas_mono (Nat.le_refl 0)⟩

/-- Success on every supported IDENTITY input, with its exact observable bytes. -/
theorem identity_total (d : Bytes) : ∃ o : Bytes, identity d = some o ∧ o = d :=
  ⟨d, identity_eq d, rfl⟩

/-- Reject-all cannot meet the actual public IDENTITY equation. -/
theorem reject_all_not_identity :
    ¬ (∀ d : Bytes, (fun _ : Bytes => (none : Option Bytes)) d = some d) := by
  intro h
  have impossible : (none : Option Bytes) = some [] := h []
  cases impossible

/-- Always returning empty output cannot meet IDENTITY on a nonempty input. -/
theorem empty_output_not_identity :
    ¬ (∀ d : Bytes, (some [] : Option Bytes) = some d) := by
  intro h
  have impossible : (some [] : Option Bytes) = some [1] := h [1]
  cases impossible

#print axioms words_mono_witness
#print axioms sha256Gas_mono_witness
#print axioms ripemd160Gas_mono_witness
#print axioms identityGas_mono_witness
#print axioms identity_total
#print axioms reject_all_not_identity
#print axioms empty_output_not_identity
end H62.AuditPrecompiles
