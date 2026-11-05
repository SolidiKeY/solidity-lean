import Solidity.Calculus.DecisionNumericFormula
import Solidity.Examples.DecisionUIntPrefix
import Solidity.Examples.DecisionLeafPreparation

/-!
# Actual numeric formula-bridge controls
Strict/optional equality, an unused binder and actual prepared atom checks.
The generic sequencing controls do not assert source translation for arbitrary
lower-level operands. No general node/cut bound or Covered theorem is claimed.
-/
namespace Solidity.Examples.DecisionNumericFormula
open Solidity.Decide
open Solidity.Examples.DecisionCoefficientBoundary (Bank)
open Solidity.Examples.DecisionUIntBridge
open Solidity.Examples.DecisionLeafPreparation (nested nested_numeric)
set_option Elab.async false

theorem partial_prepared_facts : ∃ ψ : LFml Bank,
    leafOf? partialLeaf = some (.all 0 .uint ψ) ∧
    (∀ c : Bool, ψ.Src c true) ∧ (∀ q ∈ ψ.parameters, q = ⟨.uint, 0⟩) ∧ ψ.condMax = 2 :=
  uintPrefix_prepared_facts (.user "x") decrement1_grammar decrement2_grammar

theorem partial_liftedExact : ∃ ψ : LFml Bank,
    leafOf? partialLeaf = some ψ ∧ ψ.liftedExact = true :=
  uintPrefix_prepared_liftedExact (.user "x") decrement1_grammar decrement2_grammar

theorem partial_all_waivers (w : Waivers) : partialLeaf.inTarget w = true :=
  uintPrefix_inTarget (.user "x") decrement1_grammar decrement2_grammar w

theorem partial_hashFree : partialLeaf.hasHash = false :=
  uintPrefix_hashFree (.user "x") decrement1_grammar decrement2_grammar

theorem partial_outcomes : holds zeroState partialBody ∧ ¬ holds oneState partialBody :=
  ⟨both_halting_equal, one_halting_unequal⟩

theorem partial_negative : ¬ Fml.Valid partialLeaf ∧ ∃ σ : State Bank [],
    decideGoal partialLeaf = .refuted σ ∧ ¬ Fml.holdsH σ partialLeaf :=
  ⟨partialLeaf_notValid, partialLeaf_refuted⟩

def literalTerm : Tm Bank [.val .uint] (.val .uint) := .app0 (.lit (uintOfNat 2))
def literalLeaf : Fml Bank [] := primitivePrefixEq (.user "unused") literalTerm literalTerm

theorem literal_leaf_exact : leafOf? literalLeaf = some
    (.all 0 .uint (.eq (.app0 (.lit (uintOfNat 2))) (.app0 (.lit (uintOfNat 2))))) := by rfl

theorem literal_empty_parameters : (leafOf? literalLeaf).map
    (fun ψ => ψ.stripAll.2.parameters) = some [] := by rfl

theorem literal_liftedExact : ∃ ψ : LFml Bank,
    leafOf? literalLeaf = some ψ ∧ ψ.liftedExact = true :=
  uintPrefix_prepared_liftedExact (.user "unused") (.lit _) (.lit _)

theorem literal_all_waivers (w : Waivers) : literalLeaf.inTarget w = true :=
  uintPrefix_inTarget (.user "unused") (.lit _) (.lit _) w

theorem literal_valid : Fml.Valid literalLeaf := by
  intro σ v
  rfl

private def provedCheck {C : Contract} : LeafVerdict C → Bool
  | .proved => true
  | _ => false
private theorem proved_of_check {C : Contract} (φ : Fml C [])
    (h : provedCheck (decideGoal φ) = true) : decideGoal φ = .proved := by
  cases hd : decideGoal φ with
  | proved => rfl
  | refuted σ => rw [hd] at h; cases h
  | unknown => rw [hd] at h; cases h

theorem literal_proved : decideGoal literalLeaf = .proved :=
  proved_of_check literalLeaf (by decide +kernel)
theorem literal_validH : Fml.ValidH literalLeaf := decideGoal_sound literal_proved

/-- Lower-level Num closure is tested separately from actual source translation. -/
theorem nested_prepared_parameters : ∀ q ∈
    (Fml.eqAt true decrement1 decrement2 nested (.err (s := .val .uint))).elim.condSimp.prenex.parameters,
    q = ⟨.uint, 0⟩ :=
  uintEq_prepared_parameters decrement1_grammar decrement2_grammar nested_numeric .err

theorem nested_lifting_weight :
    (Fml.eqAt true decrement1 decrement2 nested (.err (s := .val .uint))).elim.condSimp.prenex.condMax = 2 :=
  uintEq_prepared_condMax decrement1_grammar decrement2_grammar nested_numeric .err

theorem extra_atom_rejected : ¬ (LTm.var (p := .uint) 1 : LTm Bank (.val .uint)).Num
    (fun q => q = ⟨.uint, 0⟩) (fun _ => False) := by
  intro h
  have he : (⟨.uint, 1⟩ : Parameter) = ⟨.uint, 0⟩ := numeric_parameters h _ List.mem_cons_self
  exact (by decide +kernel : (⟨.uint, 1⟩ : Parameter) ≠ ⟨.uint, 0⟩) he

end Solidity.Examples.DecisionNumericFormula
