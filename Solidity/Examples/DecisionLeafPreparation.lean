import Solidity.Calculus.DecisionLeafPreparation
import Solidity.Examples.DecisionUIntBridge

/-!
# Numeric preparation controls
Sequencing observes definedness, not Boolean truth. Preparation may add nodes;
these controls do not discharge formula bounds or generic target coverage.
-/
namespace Solidity.Examples.DecisionLeafPreparation
open Solidity.Decide
open Solidity.Examples.DecisionCoefficientBoundary (Bank)
open Solidity.Examples.DecisionUIntBridge (decrement1 decrement1_grammar)
set_option Elab.async false

def onlyZero : Parameter → Prop := fun q => q = ⟨.uint, 0⟩
def noEnv : EnvKey → Prop := fun _ => False

def falseGuard : LTm Bank (.val .uint) :=
  .seq (.app0 (.lit (p := .bool) false)) (.app0 (.lit (uintOfNat 7)))
def haltedGuard : LTm Bank (.val .uint) :=
  .seq (.err (s := .val .bool)) (.app0 (.lit (uintOfNat 7)))
def nested : LTm Bank (.val .uint) :=
  .seq (.seq (.var (p := .uint) 0) (.app0 (.lit (p := .bool) false)))
    (.app2 (.binop .add rfl) (.var 0) (.app0 (.lit (uintOfNat 1))))

theorem falseGuard_numeric : falseGuard.Num onlyZero noEnv := .seq (.lit _) (.lit _)
theorem haltedGuard_numeric : haltedGuard.Num onlyZero noEnv := .seq .err (.lit _)
theorem nested_numeric : nested.Num onlyZero noEnv :=
  .seq (.seq (.var 0 rfl) (.lit _)) (.add rfl (.var 0 rfl) (.lit _))

theorem falseGuard_prepared : (falseGuard.elim : LTm Bank (.val .uint)).condSimp.Num onlyZero noEnv :=
  numeric_prepared falseGuard_numeric
theorem haltedGuard_prepared : (haltedGuard.elim : LTm Bank (.val .uint)).condSimp.Num onlyZero noEnv :=
  numeric_prepared haltedGuard_numeric
theorem nested_prepared : (nested.elim : LTm Bank (.val .uint)).condSimp.Num onlyZero noEnv :=
  numeric_prepared nested_numeric

theorem falseGuard_returns (g : State Bank []) (ν : AEnv) :
    falseGuard.eval g ν = some (uintOfNat 7) := by rfl
theorem falseGuard_preparation_returns (g : State Bank []) (ν : AEnv) :
    (falseGuard.elim : LTm Bank (.val .uint)).condSimp.eval g ν = some (uintOfNat 7) := by rfl

theorem haltedGuard_halts (g : State Bank []) (ν : AEnv) : haltedGuard.eval g ν = none := by rfl
theorem haltedGuard_preparation_halts (g : State Bank []) (ν : AEnv) :
    (haltedGuard.elim : LTm Bank (.val .uint)).condSimp.eval g ν = none := by rfl

/-- Grammar closure does not establish size preservation. -/
theorem haltedGuard_grows :
    (haltedGuard.elim : LTm Bank (.val .uint)).nodes > haltedGuard.nodes := by decide +kernel

theorem both_halting_optional (g : State Bank []) (ν : AEnv) :
    (LFml.optEq haltedGuard (.err (s := .val .uint))).holds g ν := by
  apply (LFml.optEq_holds g ν haltedGuard (.err (s := .val .uint))).mpr
  rfl

theorem both_halting_strict_rejected (g : State Bank []) (ν : AEnv) :
    ¬ (LFml.eq haltedGuard (.err (s := .val .uint))).holds g ν := by
  intro h
  obtain ⟨v, hv, he⟩ := (LFml.holds_eq_iff g ν haltedGuard (.err (s := .val .uint))).mp h
  cases he

def timed : LTm Bank (.val .uint) := .app0 (.env .timestamp)
theorem timed_numeric : timed.Num (fun _ => False) (fun e => e = .timestamp) := .env _ rfl
theorem timed_prepared : (timed.elim : LTm Bank (.val .uint)).condSimp.Num
    (fun _ => False) (fun e => e = .timestamp) := numeric_prepared timed_numeric

theorem wrong_environment_rejected : ¬ (LTm.app0 (.env .msgValue) : LTm Bank (.val .uint)).Num
    (fun _ => False) (fun e => e = .timestamp) := by
  intro h
  cases h with
  | env e he => cases he

theorem fallback_outside_numeric : ¬ (LTm.orElse (.err (s := .val .uint))
    (.app0 (.lit (uintOfNat 7))) : LTm Bank (.val .uint)).Num onlyZero noEnv := by
  intro h
  cases h

theorem actual_source_prepared_numeric : ∃ l : LTm Bank (.val .uint),
    decrement1.toLT ((SymS.init (C := Bank)).pushQ .uint) = some l ∧
    (l.elim : LTm Bank (.val .uint)).condSimp.Num onlyZero noEnv :=
  uintLinear_prefix_prepared_numeric decrement1_grammar

end Solidity.Examples.DecisionLeafPreparation
