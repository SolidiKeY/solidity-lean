import Solidity.Calculus.DecisionCompoundCertificate
import Solidity.Examples.DecisionCompoundFieldReason

/-! # Defined and partial compound-field countermodel controls
The generic certificate uses full optional Theory readings and the existing
producer child heap. The global pipeline is deliberately still unchanged here.
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

/-- Real typed Answers are ready without changing a global observation. -/
theorem answer_components : Nonempty (MemoryWitness.Answer memStructBuried) ∧
    Nonempty (MemoryWitness.Answer anotherSum) ∧ Nonempty (MemoryWitness.Answer partialRhs) :=
  ⟨⟨originalWitness.answer⟩, ⟨anotherWitness.answer⟩, ⟨partialWitness.answer⟩⟩

/-- The undefined RHS is still target syntax; no exclusion is added. -/
theorem targets : memStructBuried.inTarget {} = true ∧ anotherSum.inTarget {} = true ∧
    partialRhs.inTarget {} = true := by decide +kernel

/-- Until the actual pipeline consumes the Answer, all three global pins remain unknown. -/
theorem current_unknowns : decideGoal memStructBuried = .unknown ∧
    decideGoal anotherSum = .unknown ∧ decideGoal partialRhs = .unknown := by
  exact ⟨rfl, rfl, rfl⟩

end Solidity.Examples.DecisionCompoundCertificate
