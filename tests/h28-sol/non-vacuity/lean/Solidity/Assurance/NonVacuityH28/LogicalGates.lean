import Solidity.Assurance.NonVacuityH28.ScalarPremises
import Solidity.Assurance.NonVacuityH28.CallbackFrames

/-! Actual logical gate values and a universal-binder countercontrol.
These selectors are queried on the same nonempty programs used above. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics
variable (C : Contract)

theorem payment_syntax_gates :
    (Stmt.transfer (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)) : Stmt C [] []).hasTransfer = true ∧
    (callbackProgram C).hasTransfer = true ∧
    (Frames.seq (callbackProgram C) .nil).hasTransfer = true ∧
    (paymentSpec C).toFml.hasTransfer = true ∧
    (callbackProgram C).callsBack true = true ∧
    (callbackProgram C).callsBack false = false ∧
    (paymentSpec C).toFml.callsBack true = true ∧
    (paymentSpec C).toFml.callsBack false = false ∧
    (Stmt.transfer (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)) : Stmt C [] []).forksIn true = true ∧
    (Stmt.transfer (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)) : Stmt C [] []).forksIn false = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem frame_callback_gates (pay : Bool) :
    (Frames.seq (callbackProgram C) .nil).callsBack pay = pay := by
  cases pay <;> rfl

theorem calculus_context_gates :
    (Hyps.nil : Hyps C FlagCtx FlagCtx).boxOnly = true ∧
    ((Hyps.nil : Hyps C FlagCtx FlagCtx).upd .diamond (flagUpdate C)).boxOnly = false ∧
    ((Hyps.nil : Hyps C FlagCtx FlagCtx).upd .box (flagUpdate C)).boxOnly = true ∧
    (Fml.tt : Fml C []).modalFree = true ∧
    (assertionSpec C).toFml.modalFree = false ∧
    RuleSet.admits .solkey .diamond (Stmt.assert (.simple (.bool true)) : Stmt C [] []) = true ∧
    (Stmt.assert (.simple (.bool true)) : Stmt C [] []).keyStep .diamond = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The diamond's hidden binder cannot be replaced by an existential. -/
theorem universal_binder_control :
    (∃ b : Bool, b = true) ∧ ¬ Modality.forallB .diamond (fun b : Bool => b = true) := by
  refine ⟨⟨true, rfl⟩, ?_⟩
  intro all
  have h : false = true := all false
  cases h

/-- Update halt and typed-run halt are distinct predicates. Exhaustion is
accepted by the typed diamond; ordinary update failure is not. -/
theorem halt_gate_domains :
    Modality.box.onHalt ∧ ¬ Modality.diamond.onHalt ∧
    Modality.box.onTHalt .revert ∧ Modality.diamond.onTHalt .exhausted ∧
    ¬ Modality.diamond.onTHalt .revert := by
  refine ⟨True.intro, (fun h => h), True.intro, rfl, ?_⟩
  intro h
  cases h

end Solidity.Assurance.NonVacuityH28
