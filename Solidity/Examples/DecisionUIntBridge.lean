import Solidity.Calculus.DecisionUIntFormula
import Solidity.Examples.DecisionCoefficientBoundary

/-! # Inhabited source-bridge controls
Actual pushed locals, failed bindings, nonlinear syntax and partial arithmetic.
These do not assert a completed target/coverage bridge or define Residue. -/
namespace Solidity.Examples.DecisionUIntBridge
open Solidity.Decide
open Solidity.Examples.DecisionCoefficientBoundary (Bank)
set_option Elab.async false

def current : Tm Bank [.val .uint] (.val .uint) := .pvV .here

def decrement1 : Tm Bank [.val .uint] (.val .uint) :=
  .app2 (.binop .sub rfl) current (.app0 (.lit (uintOfNat 1)))
def decrement2 : Tm Bank [.val .uint] (.val .uint) :=
  .app2 (.binop .sub rfl) current (.app0 (.lit (uintOfNat 2)))

theorem current_grammar : current.UIntLinear := .local .here
theorem decrement1_grammar : decrement1.UIntLinear := .sub current_grammar (.lit _)
theorem decrement2_grammar : decrement2.UIntLinear := .sub current_grammar (.lit _)

def scope : SymS Bank [.val .uint] := (SymS.init (C := Bank)).pushQ .uint

theorem scope_numeric : UIntSourceLocs scope := UIntSourceLocs.pushQ UIntSourceLocs.init

theorem actual_term_translation : ∃ l : LTm Bank (.val .uint),
    decrement1.toLT scope = some l ∧ l.Src false true .num :=
  uintLinear_toLT decrement1_grammar scope scope_numeric

def partialBody : Fml Bank [.val .uint] := .eq decrement1 decrement2

theorem partialBody_grammar : partialBody.QFUIntLinear := .eq decrement1_grammar decrement2_grammar

theorem actual_formula_translation : ∃ ψ : LFml Bank,
    partialBody.toLS true scope = some ψ ∧ partialBody.toLS false scope = some ψ ∧
      ψ.Src false true := qfUIntLinear_toLS partialBody_grammar scope scope_numeric

def lowered (n : Nat) : LTm Bank (.val .uint) :=
  .app2 (.binop .sub rfl) (.var 0) (.app0 (.lit (uintOfNat n)))

/-- Both non-total operands retain optional equality, rather than requiring defined words. -/
theorem partialBody_optional_translation :
    partialBody.toLS true scope = some (LFml.optEq (lowered 1) (lowered 2)) := by
  rfl

def zeroState : State Bank [.val .uint] :=
  (State.init Bank).push (t := .val .uint) (uintOfNat 0)
def oneState : State Bank [.val .uint] :=
  (State.init Bank).push (t := .val .uint) (uintOfNat 1)

theorem zero_left_halts : decrement1.denote zeroState = none := by rfl
theorem zero_right_halts : decrement2.denote zeroState = none := by rfl

theorem both_halting_equal : holds zeroState partialBody := by
  change decrement1.denote zeroState = decrement2.denote zeroState
  rw [zero_left_halts, zero_right_halts]

theorem one_left_returns : decrement1.denote oneState = some (uintOfNat 0) := by rfl
theorem one_right_halts : decrement2.denote oneState = none := by rfl

theorem one_halting_unequal : ¬ holds oneState partialBody := by
  change ¬ decrement1.denote oneState = decrement2.denote oneState
  rw [one_left_returns, one_right_halts]
  exact nofun

def partialLeaf : Fml Bank [] := .all (.user "x") .uint partialBody

theorem partialLeaf_countermodel : ¬ holds (State.init Bank) partialLeaf := by
  intro h
  exact one_halting_unequal (h (uintOfNat 1))

theorem partialLeaf_notValid : ¬ Fml.Valid partialLeaf := by
  intro h
  exact partialLeaf_countermodel (h (State.init Bank))

theorem partialLeaf_covered : partialLeaf.Covered = true := by decide +kernel
theorem partialLeaf_target : partialLeaf.inTarget {} = true := by decide +kernel

theorem partialLeaf_refuted : ∃ σ : State Bank [],
    decideGoal partialLeaf = .refuted σ ∧ ¬ Fml.holdsH σ partialLeaf := by
  have hh : partialLeaf.hasHash = false := by decide +kernel
  have hn : decideGoal partialLeaf ≠ .unknown := decideGoal_complete partialLeaf_covered hh
  cases he : decideGoal partialLeaf with
  | proved => exact False.elim (partialLeaf_notValid ((Fml.validH_iff hh).mp (decideGoal_sound he)))
  | unknown => exact False.elim (hn he)
  | refuted σ => exact ⟨σ, rfl, decideGoal_refutes he⟩

def missingScope : SymS Bank [.val .uint] := (SymS.init (C := Bank)).push (t := .val .uint) none

theorem missing_lookup : current.toL missingScope = none := by rfl

theorem missing_scope_not_numeric : ¬ UIntSourceLocs missingScope := by
  intro h
  obtain ⟨l, hl, _⟩ := h .here
  change none = some l at hl
  cases hl

def nonlinear : Tm Bank [.val .uint] (.val .uint) := .app2 (.binop .mul rfl) current current

theorem nonlinear_outside_grammar : ¬ nonlinear.UIntLinear := by
  intro h
  cases h

def doublingBody : Fml Bank [.val .uint] :=
  .eq (.app2 (.binop .mul rfl) (.app0 (.lit (uintOfNat 2))) current)
    (.app2 (.binop .add rfl) current current)

theorem doublingBody_grammar : doublingBody.QFUIntLinear :=
  .eq (.mulL _ current_grammar) (.add current_grammar current_grammar)

def doublingLeaf : Fml Bank [] := .all (.user "x") .uint doublingBody

theorem doubling_exact_source : doublingLeaf = DecisionCoefficientBoundary.directTwo := rfl

theorem doubling_proved : decideGoal doublingLeaf = .proved := by
  rw [doubling_exact_source]
  exact DecisionCoefficientBoundary.directTwo_proved

theorem doubling_validH : Fml.ValidH doublingLeaf := decideGoal_sound doubling_proved

/-- Exercise negation, conjunction and implication around the partial local equation. -/
def combinedBody : Fml Bank [.val .uint] :=
  .imp (.and partialBody (.not (.eq current (.app0 (.lit (uintOfNat 0))))))
    (.eq current current)

theorem combinedBody_grammar : combinedBody.QFUIntLinear :=
  .imp (.and partialBody_grammar (.not (.eq current_grammar (.lit _))))
    (.eq current_grammar current_grammar)

theorem combinedBody_translation : ∃ ψ : LFml Bank,
    combinedBody.toLS true scope = some ψ ∧ combinedBody.toLS false scope = some ψ ∧
      ψ.Src false true := qfUIntLinear_toLS combinedBody_grammar scope scope_numeric

theorem combinedBody_negative_admission : combinedBody.target {} false false = true :=
  qfUIntLinear_target combinedBody_grammar {} false false

/-- A closed logical combination with two different halting arithmetic terms. -/
def closedCombo : Fml Bank [] :=
  .imp (.not (.eq (.app0 (.lit (uintOfNat 2))) (.app0 (.lit (uintOfNat 3)))))
    (.eq (.app2 (.binop .sub rfl) (.app0 (.lit (uintOfNat 0))) (.app0 (.lit (uintOfNat 1))))
      (.app2 (.binop .sub rfl) (.app0 (.lit (uintOfNat 0))) (.app0 (.lit (uintOfNat 2)))))

theorem closedCombo_grammar : closedCombo.QFUIntLinear :=
  .imp (.not (.eq (.lit _) (.lit _))) (.eq (.sub (.lit _) (.lit _)) (.sub (.lit _) (.lit _)))

theorem closedCombo_target (w : Waivers) : closedCombo.inTarget w = true :=
  qfUIntLinear_inTarget closedCombo_grammar w

private def provedFlag {C : Contract} : LeafVerdict C → Bool
  | .proved => true
  | _ => false

private theorem proved_of_flag {C : Contract} (φ : Fml C [])
    (h : provedFlag (decideGoal φ) = true) : decideGoal φ = .proved := by
  cases he : decideGoal φ with
  | proved => rfl
  | refuted σ => rw [he] at h; cases h
  | unknown => rw [he] at h; cases h

theorem closedCombo_proved : decideGoal closedCombo = .proved :=
  proved_of_flag closedCombo (by decide +kernel)

theorem closedCombo_validH : Fml.ValidH closedCombo := decideGoal_sound closedCombo_proved

end Solidity.Examples.DecisionUIntBridge
