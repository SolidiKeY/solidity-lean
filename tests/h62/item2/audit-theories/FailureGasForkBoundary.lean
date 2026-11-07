import tests.h62.item2.«audit-theories».CoreTotality
import Solidity.Semantics.Nondeterminism.ForkStipend

/-!
Observable boundaries, not invented gas/data premises on the old core machine.
It maps both a source revert and panic to REVERT and carries no failure bytes,
gas-used counter or fork argument. The separate source stipend rule has a
numeric threshold and a fork-sensitive contrast. Its cost is NOT measured EVM
gas and does not prove the G43 Fitted/Enforced compiler obligation.
-/
namespace H62.AuditTheories.CompilerAudit
open Solidity Solidity.Evm
open Solidity.Semantics.Nondeterminism

/-- `require(false);` in the same intrinsic program language. -/
def rejectedRequire (C : Contract) : Solidity.Prog C [] [] :=
  .cons (.require (.simple (.bool false))) .nil

/-- `assert(false);` distinguishes the source panic from a plain revert. -/
def rejectedAssert (C : Contract) : Solidity.Prog C [] [] :=
  .cons (.assert (.simple (.bool false))) .nil

/-- The two different source failures are observable in the source result. -/
theorem source_failure_distinction (C : Contract) (σ : State C []) :
    Solidity.Prog.run σ (rejectedRequire C) = .error .revert ∧
      Solidity.Prog.run σ (rejectedAssert C) = .error .panic :=
  ⟨rfl, rfl⟩

/-- The core target observes both failures only as REVERT, without ABI bytes. -/
theorem target_failure_collision (C : Contract) :
    Evm.run (compileProg 0 (rejectedRequire C)) initialMachine = .revert ∧
      Evm.run (compileProg 0 (rejectedAssert C)) initialMachine = .revert :=
  ⟨rfl, rfl⟩

/-- This checked collision forbids inferring byte-exact panic/revert behavior
from the core compiler's failure classification. -/
theorem failure_boundary (C : Contract) (σ : State C []) :
    Solidity.Prog.run σ (rejectedRequire C) ≠ Solidity.Prog.run σ (rejectedAssert C) ∧
      Evm.run (compileProg 0 (rejectedRequire C)) initialMachine =
        Evm.run (compileProg 0 (rejectedAssert C)) initialMachine := by
  refine ⟨?_, rfl⟩
  intro h
  cases h

/-- Exactly the same bool fixture, packaged for the source stipend rule. -/
def boolBody (C : Contract) (value : Bool) : Stipend.Body C := ⟨boolProgram C value⟩

/-- Its source rule cost is two units, independently of the literal value. -/
theorem bool_rule_cost (C : Contract) (value : Bool) :
    Stipend.progCost (boolProgram C value) = some 2 := rfl

/-- The complete numeric source-rule threshold is 50*2+300=400. -/
theorem bool_rule_threshold (C : Contract) (value : Bool) (stipend : Nat) :
    Stipend.fitsWith Stipend.osakaCold stipend (boolBody C value) = true ↔
      400 ≤ stipend := by
  change decide (400 ≤ stipend) = true ↔ 400 ≤ stipend
  simp only [decide_eq_true_eq]

/-- A one-unit boundary control for the SOURCE rule, not target gas usage. -/
theorem bool_rule_boundary (C : Contract) (value : Bool) :
    Stipend.fitsWith Stipend.osakaCold 400 (boolBody C value) = true ∧
      Stipend.fitsWith Stipend.osakaCold 399 (boolBody C value) = false :=
  ⟨rfl, rfl⟩

/-- Osaka's source rule admits the actual compiled bool fixture. -/
theorem bool_osaka_fits (C : Contract) (value : Bool) :
    (ForkSpec.osaka.stipendRule C).fits (boolBody C value) := rfl

/-- The custom zero-stipend contrast refuses that same fixture. -/
theorem bool_no_stipend_refused (C : Contract) (value : Bool) :
    ¬ (ForkSpec.noStipend.stipendRule C).fits (boolBody C value) := by
  intro h
  cases h

/-- The core IR succeeds even though the separate zero-stipend rule refuses:
its success cannot be used as a fork/gas-aware execution theorem. -/
theorem ir_success_is_not_stipend_fitting (C : Contract) (value : Bool) :
    (∃ m', Evm.run (compileProg 0 (boolProgram C value)) initialMachine = .ok m' 0) ∧
      ¬ (ForkSpec.noStipend.stipendRule C).fits (boolBody C value) := by
  obtain ⟨m', hr, _, _⟩ := bool_target_success C value
  exact ⟨⟨m', hr⟩, bool_no_stipend_refused C value⟩

/-- The target pin recognizes Osaka only; the Prague record is a limited
source contrast and has no target pin. No cross-fork compilation is claimed. -/
theorem fork_pin_boundary :
    ForkSpec.osaka.pin? = some Solidity.Roadmap.Evm.osaka ∧
      ForkSpec.prague.pin? = none ∧ ForkSpec.noStipend.fork = .custom :=
  ⟨ForkSpec.osaka_pin, rfl, rfl⟩

#print axioms source_failure_distinction
#print axioms target_failure_collision
#print axioms failure_boundary
#print axioms bool_rule_cost
#print axioms bool_rule_threshold
#print axioms bool_rule_boundary
#print axioms bool_osaka_fits
#print axioms bool_no_stipend_refused
#print axioms ir_success_is_not_stipend_fitting
#print axioms fork_pin_boundary
end H62.AuditTheories.CompilerAudit
