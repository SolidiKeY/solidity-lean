import Solidity.Roadmap.V16.TransportControls

/-! V17 ordered validation client of the exact staged V16 checkpoint.
This uses the existing inhabited G01/G07 instance; it is neither a compiler
certificate nor evidence of arbitrary source/EVM agreement. No event, outcome,
resource predicate or execution semantics is replaced. The ordered pair uses
the actual composed certificate for success and the existing identity certificate
for revert, preserving both complete outcomes.
Build only in the explicitly bound private candidate containing the producer.
-/
namespace Solidity.Roadmap.V17.ParallelInterface
open Solidity.Roadmap Solidity.Roadmap.Controls

/-- Each entry comes from the existing producer's actual certificate need. -/
def observations : List (Option Outcome) :=
  [(toyLang.sem (.succeed [7]) quietEnv
      (V16.Checks.twoPass.need (.succeed [7]) trivial quietEnv ⟨1, false⟩)).final,
   (toyLang.sem (idPass.run (.fail [9]) trivial) quietEnv
      (idCert.need (.fail [9]) trivial quietEnv ⟨1, false⟩)).final]

/-- Both inhabited paths are kept, in their original order and with exact bytes. -/
theorem observations_exact :
    observations = [some (.success [7]), some (.revert [9])] := by
  unfold observations
  rw [V16.Checks.combination_success, V16.Checks.revert_at_need]

/-- Reordering independent component reports changes exact observation agreement. -/
theorem swapped_refused :
    observations ≠ [some (.revert [9]), some (.success [7])] := by
  rw [observations_exact]
  intro h
  cases h

/-- An erased revert payload cannot be silently accepted by aggregation. -/
theorem erased_revert_refused :
    observations ≠ [some (.success [7]), some (.revert [])] := by
  rw [observations_exact]
  intro h
  cases h

/-- Dropping a completed component also changes the retained ordered result. -/
theorem missing_component_refused : observations ≠ [some (.success [7])] := by
  rw [observations_exact]
  intro h
  cases h

end Solidity.Roadmap.V17.ParallelInterface
