import Solidity.Calculus.CallbackDerive
import Solidity.Calculus.CallbackSound
import Solidity.Calculus.Close
import Solidity.Calculus.Closers
import Solidity.Calculus.Surface

/-!
# Guarded payment formulas

Kernel controls for the conditional dispatcher rules. The antecedent is
normality of the same transfer, never a premise inserted into a bare diamond.
-/

namespace Solidity.Examples.Tactics.PaymentRules

open Semantics
local instance : InContract := ⟨StandardExample⟩
open scoped Scoped

/-- The fixed-recipient ledger invariant used by the callback controls. -/
def netInv9 : Invariant StandardExample := ⟨dl!{ net(9) <= 0 }, rfl⟩

/-- The callback dispatcher keeps normality, exit, and every invariant-preserving resumption. -/
theorem guarded_callback :
    ValidC netInv9 dl!{ net(9) <= 0 →
      (¬ [ (9).transfer(5); ] false) → ⟨ (9).transfer(5); ⟩ net(9) <= 0 } := by
  sol_prove

/-- The deterministic dispatcher preserves storage without introducing callback havoc. -/
theorem guarded_deterministic :
    ValidT .noCallback dl!{ balance == 7 →
      (¬ [ (9).transfer(5); ] false) → ⟨ (9).transfer(5); ⟩ balance == 7 } := by
  sol_prove

private abbrev funded : State StandardExample [] :=
  { State.ofStorage Storage.standardExample with selfBalance := ⟨10, rfl⟩ }
private abbrev poor : State StandardExample [] := { funded with selfBalance := ⟨3, rfl⟩ }
private abbrev refusing : State StandardExample [] :=
  { funded with tx := { ext := [(sendKey ⟨9, rfl⟩ ⟨5, rfl⟩, .other [])] } }

/-- Normality is satisfiable: a funded, accepted transfer has an unchanged callback resumption. -/
theorem funded_normality :
    holdsC .tt true funded dl!{ ¬ [ (9).transfer(5); ] false } := by
  intro h
  have paid : ExecS ((Fml.tt : Fml StandardExample []).stateInv true) funded
      (.transfer (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)))
      (.ok ⟨funded.pay ⟨9, rfl⟩ 5, List.prefix_refl _⟩) := by
    exact ExecS.transferResume (J := (Fml.tt : Fml StandardExample []).stateInv true)
      (σ := funded) (r := .simple (.lit 9 rfl)) (a := .simple (.lit 5 rfl))
      (o₁ := ⟨funded.pay ⟨9, rfl⟩ 5, List.prefix_refl _⟩) (st := funded.storage) (nt := (funded.pay ⟨9, rfl⟩ 5).net)
      (sb := (funded.pay ⟨9, rfl⟩ 5).selfBalance) rfl rfl trivial trivial
  exact h _ (.cons paid .nil) _ .nil trivial

/-- Insufficient funds cannot discharge the normality antecedent. -/
theorem poor_normality :
    ¬ holdsC .tt true poor dl!{ ¬ [ (9).transfer(5); ] false } := by
  intro h
  have accepted := holdsC_transfer_normal_accepted poor (.lit 9 rfl) (.lit 5 rfl) h
  change false = true at accepted
  cases accepted

/-- A callee revert cannot discharge normality even with sufficient funds. -/
theorem refused_normality :
    ¬ holdsC .tt true refusing dl!{ ¬ [ (9).transfer(5); ] false } := by
  intro h
  have accepted := holdsC_transfer_normal_accepted refusing (.lit 9 rfl) (.lit 5 rfl) h
  change false = true at accepted
  cases accepted

/-- The original bare transfer diamond is false in a fundedness countermodel. -/
theorem bare_diamond_refused :
    ¬ ValidC Invariant.top dl!{ ⟨ (9).transfer(5); ⟩ true } := by
  intro h
  have failed : ExecS ((Fml.tt : Fml StandardExample []).stateInv true) poor
      (.transfer (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl))) (.halt .revert) :=
    .transferHalt rfl rfl
  have bad := (h poor _ (.halt failed)).1
  cases bad

/-- A failed preceding diamond update cannot be discarded by a guarded formula rule. -/
theorem failed_diamond_prefix :
    ¬ ValidC Invariant.top dl![.diamond]{ { selfBalance := selfBalance - 1 }
      ((¬ [ (9).transfer(5); ] false) → ⟨ (9).transfer(5); ⟩ true) } := by
  intro h
  have bad := h (State.ofStorage Storage.standardExample)
  change False ∨ false = true at bad
  rcases bad with bad | bad
  · exact bad
  · cases bad

#print axioms Solidity.ProvesC.sound_of
#print axioms guarded_callback
#print axioms guarded_deterministic
#print axioms funded_normality
#print axioms bare_diamond_refused
#print axioms failed_diamond_prefix

end Solidity.Examples.Tactics.PaymentRules
