import Solidity.Roadmap.V16.CreationLibrarySpec

/-! Actual finite constructor success controls. They do not claim Source
admission, account installation, gas adequacy, or a full compiler pipeline. -/
namespace Solidity.H62.AuditRoadmap.CreationWitnesses
open Solidity.Backend.Creation
open Solidity.Backend.Executable.CreationReturnProducer.Controls

/-- Same actual execution as the frozen complete-return specification. -/
theorem supported_constructor_success : ∃ output,
    Exec first.payload first.payload [] [] (.returned output) ∧ output.length = 105 := by
  obtain ⟨output, firstRun, _, _, length, _⟩ :=
    Solidity.Roadmap.V16.CreationLibrarySpec.actual_runs
  exact ⟨output, firstRun, length⟩

/-- A semantics rejecting every return cannot describe this supported code. -/
theorem reject_all_returns_excluded :
    ¬ (∀ output, ¬ Exec first.payload first.payload [] [] (.returned output)) := by
  intro rejects
  obtain ⟨output, actual, _⟩ := supported_constructor_success
  exact rejects output actual

/-- Determinism separates an actual supported return from always reverting. -/
theorem always_revert_excluded :
    ¬ ∃ data, Exec first.payload first.payload [] [] (.reverted data) := by
  intro bad
  obtain ⟨data, actual⟩ := bad
  have impossible : Outcome.returned first.runtime = .reverted data :=
    first_returns.deterministic actual
  cases impossible

end Solidity.H62.AuditRoadmap.CreationWitnesses
#print axioms Solidity.H62.AuditRoadmap.CreationWitnesses.supported_constructor_success
#print axioms Solidity.H62.AuditRoadmap.CreationWitnesses.reject_all_returns_excluded
#print axioms Solidity.H62.AuditRoadmap.CreationWitnesses.always_revert_excluded
