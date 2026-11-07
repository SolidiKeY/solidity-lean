import Solidity.Calculus.DecisionCompoundCertificate
import Solidity.Examples.DecisionCompoundFieldReason

/-! # Defined and partial compound-field countermodel controls
The generic certificate uses full optional Theory readings and the existing
producer child heap. The real global route now consumes the typed Answer.
-/
namespace Solidity.Examples.DecisionCompoundCertificate
open Solidity.Decide Solidity.Decide.ResidueReason
open Solidity.Examples.Decision Solidity.Examples.DecisionCompoundFieldReason
set_option Elab.async false

def originalWitness : NonliteralUIntFreshField memStructBuried :=
  (nonliteralUIntFreshField? memStructBuried).get (by decide +kernel)
def anotherWitness : NonliteralUIntFreshField anotherSum :=
  (nonliteralUIntFreshField? anotherSum).get (by decide +kernel)
def partialWitness : NonliteralUIntFreshField partialRhs :=
  (nonliteralUIntFreshField? partialRhs).get (by decide +kernel)

/-- All RHS choices retain exactly the original producer heap before the parent. -/
theorem exact_states :
    originalWitness.counterState (State.init StandardExample) = gapMemStruct_state ∧
    anotherWitness.counterState (State.init StandardExample) = gapMemStruct_state ∧
    partialWitness.counterState (State.init StandardExample) = gapMemStruct_state := by
  exact ⟨rfl, rfl, rfl⟩

/-- Two successful RHS readings and one genuinely undefined Theory reading. -/
theorem optional_rhs_controls :
    originalWitness.rhs.denote ((originalWitness.counterState (State.init StandardExample)).push none) =
      some (uintOfNat 1) ∧
    anotherWitness.rhs.denote ((anotherWitness.counterState (State.init StandardExample)).push none) =
      some (uintOfNat 5) ∧
    partialWitness.rhs.denote ((partialWitness.counterState (State.init StandardExample)).push none) = none := by
  decide +kernel

/-- Ordinary countermodels come from the source-class certificate, without halting premises. -/
theorem ordinary_countermodels :
    ¬ holds (originalWitness.counterState (State.init StandardExample)) memStructBuried ∧
    ¬ holds (anotherWitness.counterState (State.init StandardExample)) anotherSum ∧
    ¬ holds (partialWitness.counterState (State.init StandardExample)) partialRhs :=
  ⟨originalWitness.counterState_refutes _, anotherWitness.counterState_refutes _,
    partialWitness.counterState_refutes _⟩

/-- The identical states refute the exact existing hash interpretation. -/
theorem hash_countermodels :
    ¬ Fml.holdsH (originalWitness.counterState (State.init StandardExample)) memStructBuried ∧
    ¬ Fml.holdsH (anotherWitness.counterState (State.init StandardExample)) anotherSum ∧
    ¬ Fml.holdsH (partialWitness.counterState (State.init StandardExample)) partialRhs :=
  ⟨originalWitness.counterState_refutesH _, anotherWitness.counterState_refutesH _,
    partialWitness.counterState_refutesH _⟩

/-- Real typed Answer components are consumed by the certified global route. -/
theorem answer_components : Nonempty (MemoryWitness.Answer memStructBuried) ∧
    Nonempty (MemoryWitness.Answer anotherSum) ∧ Nonempty (MemoryWitness.Answer partialRhs) :=
  ⟨⟨originalWitness.answer⟩, ⟨anotherWitness.answer⟩, ⟨partialWitness.answer⟩⟩

/-- The undefined RHS is still target syntax; no exclusion is added. -/
theorem targets : memStructBuried.inTarget {} = true ∧ anotherSum.inTarget {} = true ∧
    partialRhs.inTarget {} = true := by decide +kernel

/-- All three assigned sources now reach the actual certified global refutation. -/
theorem actual_refuted :
    (∃ σ : State StandardExample [], decideGoal memStructBuried = .refuted σ ∧ ¬ Fml.holdsH σ memStructBuried) ∧
    (∃ σ : State StandardExample [], decideGoal anotherSum = .refuted σ ∧ ¬ Fml.holdsH σ anotherSum) ∧
    (∃ σ : State StandardExample [], decideGoal partialRhs = .refuted σ ∧ ¬ Fml.holdsH σ partialRhs) :=
  ⟨originalWitness.refuted, anotherWitness.refuted, partialWitness.refuted⟩

/-- Coverage comes from the exact source class, without a supplied coverage premise. -/
theorem actual_covered : memStructBuried.Covered = true ∧ anotherSum.Covered = true ∧
    partialRhs.Covered = true :=
  ⟨originalWitness.covered, anotherWitness.covered, partialWitness.covered⟩

end Solidity.Examples.DecisionCompoundCertificate
