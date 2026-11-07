import Solidity.Lowering.StorageOps.SourceWordWriteControls

/-! Joint writable/ordinary/word Source write witnesses. Reuses the published
fixture and certificate, without supplying an address or world compiler. -/
namespace H62.StorageAudit.SourceWriteWitnesses
open Solidity Solidity.Backend.StorageOps Solidity.Lowering.StorageOps
open SourceWordWriteControls

theorem source_joint : frame.static = false ∧ env.transientRoot left = false := by
  decide

theorem word_joint : value.word = some (Evm.wmod 53) := by
  rfl

theorem complete_joint : frame.static = false ∧ env.transientRoot left = false ∧
    value.word = some (Evm.wmod 53) := by
  decide

/-- Published concrete certificate at the SAME writable/ordinary/coherent inputs. -/
theorem complete_reused :
    sourceRun = (.ok (), (.nil, SourceWordWrite.after frame left value state)) ∧
    targetRun = .ok (targetAfter 53) 0 ∧
    ((sourceRun.2.2.ex.world.accounts frame.this).storage.read left).bind Source.Val.word =
      some (Evm.wmod 53) ∧ (targetAfter 53).store.cells (.root 0) = Evm.wmod 53 :=
  SourceWordWriteControls.certificate

theorem failure_contrasts_reused : (staticRun, zeroRun, typeRun) =
    ((.error (.revert []), initial), (.error .timeout, initial),
     (.error (.stuck "storage cell type"), initial)) :=
  SourceWordWriteControls.failure_outcomes

/-- At storeVal zero fuel is checked before the static write refusal. -/
theorem static_zero_fuel :
    (Source.storeVal (E := env) (Γ := []) { frame with static := true }
      0 (env.cellTy left) left value).run initial = (.error .timeout, initial) := by
  rfl

/-- A scalar word observation alone does not supply destination type compatibility. -/
theorem word_is_not_type_compatibility :
    (.bool true : Source.Val env.layout .bool).word = some (Evm.wmod 1) ∧
    typeRun = (.error (.stuck "storage cell type"), initial) := by
  exact ⟨rfl, rfl⟩

/-- A different stack operand still executes; it cannot supply the chosen word agreement. -/
theorem wrong_operand_executes : wrongOperand = .ok (targetAfter 59) 0 ∧
    some (Evm.wmod 53) ≠ some (Evm.wmod 59) := by
  exact ⟨rfl, by decide⟩

/-- info: 'H62.StorageAudit.SourceWriteWitnesses.source_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms source_joint
/-- info: 'H62.StorageAudit.SourceWriteWitnesses.word_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_joint
/-- info: 'H62.StorageAudit.SourceWriteWitnesses.complete_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_joint
/-- info: 'H62.StorageAudit.SourceWriteWitnesses.complete_reused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_reused
/-- info: 'H62.StorageAudit.SourceWriteWitnesses.failure_contrasts_reused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms failure_contrasts_reused
/-- info: 'H62.StorageAudit.SourceWriteWitnesses.static_zero_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms static_zero_fuel
/-- info: 'H62.StorageAudit.SourceWriteWitnesses.word_is_not_type_compatibility' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_is_not_type_compatibility
/-- info: 'H62.StorageAudit.SourceWriteWitnesses.wrong_operand_executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_operand_executes
end H62.StorageAudit.SourceWriteWitnesses
