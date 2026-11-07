import Solidity.Language.EnvironmentFields.Consequences
import Solidity.Language.EnvironmentFields.FrozenControls

namespace Solidity.Roadmap.FullScope.V1.Controls

open Solidity.Roadmap Solidity.Roadmap.FullScope Solidity.Roadmap.FullScope.RunIndexed

/-- The backward theorem has a live gas query and actual nonempty success bytes. -/
theorem backward_live :
    ∃ run : SourceIndex source () artifact, domain.Eligible run ∧
      run.execution = ⟨[.scalar .gasleft 5], some (.success [5])⟩ :=
  backward_exact d1 (resolved := ()) rfl (⟨(), (5 : Word)⟩ : TargetIndex target artifact)
    ⟨trivial, trivial⟩ trivial (o := .success [5]) rfl

/-- An exact completed prefix cannot silently change raw success bytes. -/
theorem different_completed_bytes_refused :
    ¬ (⟨[.scalar .gasleft 5], some (.success [6])⟩ : Prefix Observation Outcome).Le
      ⟨[.scalar .gasleft 5], some (.success [5])⟩ := by
  intro below
  have bad := congrArg Prefix.final (below.final_eq rfl)
  cases bad

#print axioms backward_completes
#print axioms backward_exact
#print axioms backward_live
#print axioms different_completed_bytes_refused

end Solidity.Roadmap.FullScope.V1.Controls
