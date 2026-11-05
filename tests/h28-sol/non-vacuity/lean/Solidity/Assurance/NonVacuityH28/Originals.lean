import Solidity.Assurance.NonVacuityH28.Families
import Solidity.Assurance.NonVacuityH28.Calculus
import Solidity.Assurance.NonVacuityH28.Callbacks
import Solidity.Assurance.NonVacuityH28.TailSensitive

/-! Constructed inputs for the original induction and invariant contracts.
These applications supplement the exact Main-wrapper/source-original mapping. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics
variable (C : Contract)

theorem original_arms_input : Stmt.Sound C := Stmt.sound

theorem original_calculus_induction : Fml.Valid (assertionSpec C).toFml :=
  Proves.sound_of (original_arms_input C) (assertion_derivation C .all)

theorem original_callback_formula :
    ValidC (Invariant.top (C := C)) (paymentSpec C).toFml true :=
  ProvesC.fmlValid (payment_derivation C)

theorem original_noCallback_formula :
    ValidC (Invariant.top (C := C)) (paymentSpec C).toFml false :=
  ProvesC.fmlValid (noCallback_payment_derivation C)

/-- First-order and no-transfer conditions hold, and the actual initial
state satisfies the invariant. No invariant is assumed from a contradiction. -/
theorem original_invariant_inputs :
    (Invariant.top (C := C)).fml.FO = true ∧
    (Invariant.top (C := C)).fml.hasTransfer = false ∧
    holds (State.init C) (Invariant.top (C := C)).fml := ⟨rfl, rfl, True.intro⟩

theorem original_clean_tail : holds (State.init Tokens) tailFormula :=
  ValidTail.holds_of_clean tail_clean_valid (State.init Tokens) (Storage.init_cleanTail Tokens)

/-- An always-empty fragment recognizer disagrees on an actual nonempty
accepted program. This does not change the fixed compiler API. -/
theorem empty_fragment_acceptance_rejected :
    ¬ ∀ P : Prog C [] [], Evm.inFragP (Evm.Frag.init []) P = none := by
  intro empty
  have h := empty (requireProgram C true)
  rw [fragment_family C true] at h
  cases h

end Solidity.Assurance.NonVacuityH28
