import Solidity.Lowering.V08.PayableControls

/-! Regression: a source payment flag alone does not inhabit funded-entry
premises. The existing funded world and genuine nonzero context jointly supply
funding, ordinary mode and receiver range. This is target entry-guard evidence;
the supplied body is not a Source body compilation or admission witness. -/
namespace H62.AuditV08Adapters.PayableGuardJoint
open Solidity ContractWorld
open Solidity.Lowering.V08
open PayableMetadata

/-- All four original payable-entry hypotheses share one supplied world/context. -/
theorem joint : payableOf? PayableControls.receiving = some true ∧
    Controls.paidCtx.value.1 ≤ (Controls.initial.funds Controls.paidCtx.sender).1 ∧
    Controls.paidCtx.isStatic = false ∧
    (Controls.initial.funds Controls.self).1 +
      (if Controls.paidCtx.sender = Controls.self then 0 else Controls.paidCtx.value.1) <
        ((2 ^ 256 : Nat) : Int) := by decide +kernel

/-- Exact original Option/isOk conclusion; no successful execution premise. -/
theorem actual_entered :
    (attach? PayableControls.receiving Controls.entry).map
      (fun attached => (Controls.initial.enter (k := ()) Controls.self Controls.paidCtx
        (Storage.init Controls.Cell) attached.payable).isOk) = some true :=
  source_payable_entered (k := ()) Controls.initial Controls.self Controls.paidCtx
    (Storage.init Controls.Cell) PayableControls.receiving Controls.entry
    joint.1 joint.2.1 joint.2.2.1 joint.2.2.2

/-- The same world/payment rejects the existing nonpayable source metadata. -/
theorem actual_nonpayable :
    (attach? (PayableControls.fallbackDecl false) Controls.entry).map
      (fun attached => Controls.initial.enter (k := ()) Controls.self Controls.paidCtx
        (Storage.init Controls.Cell) attached.payable) = some (.error .revert) :=
  source_nonpayable_rejected (k := ()) Controls.initial Controls.self Controls.paidCtx
    (Storage.init Controls.Cell) (PayableControls.fallbackDecl false) Controls.entry
    rfl (by decide +kernel)

/-- Replacing the funded world by a zero ledger violates the funding premise. -/
theorem zero_funds_refused :
    ¬ (Controls.paidCtx.value.1 ≤
      ((World.empty Controls.catalog (fun _ => ⟨0, by decide +kernel⟩)).funds
        Controls.paidCtx.sender).1) := by decide +kernel

/-- Successful guard evidence does not replace existing refusal of bad receives. -/
theorem malformed_refused : attach? PayableControls.badReceive Controls.entry = none :=
  PayableControls.malformed_receive_refused

#print axioms joint
#print axioms actual_entered
#print axioms actual_nonpayable
#print axioms zero_funds_refused
#print axioms malformed_refused
end H62.AuditV08Adapters.PayableGuardJoint
