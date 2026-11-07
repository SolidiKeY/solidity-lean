import Lean.Elab.Command
import Solidity.Precompiles.Osaka

/-! Guards against an Osaka applicability census dropping the LengthPriced
premise, replacing input-length order with separate witnesses, or conflating
malformed-input failure with insufficient gas. Nonempty inputs witness the
unchanged failure laws; gas_mono_joint retains both hypotheses on one pair.
This does not establish native crypto equality or compiler success. -/
namespace H62.AuditPrecompiles.Successor.Osaka
open Solidity.Precompiles Solidity.Roadmap.Evm

theorem fixed_gas_fidelity : Osaka.fixed.precompileGas = Osaka.gas :=
  Osaka.fixed_precompileGas

theorem run_failure_data : ∃ (p : Precompile) (d : Bytes),
    Osaka.run p d = none ↔ Osaka.Malformed p d :=
  ⟨.identity, [1], Osaka.run_eq_none_iff .identity [1]⟩

theorem fixed_failure_data : ∃ (p : Precompile) (d : Bytes),
    Osaka.fixed.precompile p d = none ↔ Osaka.Malformed p d :=
  ⟨.identity, [1], Osaka.fixed_precompile_eq_none_iff .identity [1]⟩

theorem gas_mono_joint : ∃ (p : Precompile) (d e : Bytes),
    Osaka.LengthPriced p ∧ d.length ≤ e.length ∧ Osaka.gas p d ≤ Osaka.gas p e := by
  have hp : Osaka.LengthPriced .identity := ⟨by decide, by decide⟩
  have h : ([1] : Bytes).length ≤ ([1, 2] : Bytes).length := by decide
  exact ⟨.identity, [1], [1, 2], hp, h, Osaka.gas_mono hp h⟩

theorem ecrecover_stipend_data : ∃ d : Bytes,
    pinned.stipend < Osaka.gas .ecrecover d :=
  ⟨[1], Osaka.ecrecover_exceeds_stipend [1]⟩

/-- info: 'H62.AuditPrecompiles.Successor.Osaka.fixed_gas_fidelity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fixed_gas_fidelity
/-- info: 'H62.AuditPrecompiles.Successor.Osaka.run_failure_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms run_failure_data
/-- info: 'H62.AuditPrecompiles.Successor.Osaka.fixed_failure_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fixed_failure_data
/-- info: 'H62.AuditPrecompiles.Successor.Osaka.gas_mono_joint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gas_mono_joint
/-- info: 'H62.AuditPrecompiles.Successor.Osaka.ecrecover_stipend_data' does not depend on any axioms -/
#guard_msgs in
#print axioms ecrecover_stipend_data
run_cmd Lean.logInfo "CORE_APPLICABILITY_PASS module=Osaka original=5 guards=5"
end H62.AuditPrecompiles.Successor.Osaka
