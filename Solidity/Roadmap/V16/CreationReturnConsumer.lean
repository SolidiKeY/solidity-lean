import Solidity.Backend.Executable.CreationReturnInterfaceV1Controls

/-! Scoped G50/G51 consumer of the actual finite constructor-copy execution.
Postconditions observe the COMPLETE returned byte list. No Source constructor,
account installation, gas/resource adequacy or fetched external EVM bridge is
claimed. In particular the pending CreationReturnInterfaceV1.Producer is NOT
assumed or constructed: executions below come from combined_installs itself. -/
namespace Solidity.Roadmap.V16.CreationReturnConsumer
open Solidity.Backend Solidity.Backend.Creation

/-- Every actual outcome of this constructor agrees with its proved RETURN.
This is a fact about the existing constructor execution, not arbitrary initcode. -/
theorem outcome_exact (a : Artifact Lib) (links : LinkTable a)
    (table : ImmutableTable a.runtime.length Key) (addresses : Lib → Vector UInt8 20)
    (compatible : Creation.compatible table links.sites = true) (result : Outcome)
    (actual : let b := combinedArtifact a links table addresses compatible
      Exec b.payload b.payload [] [] result) :
    result = .returned (combinedArtifact a links table addresses compatible).runtime :=
  actual.deterministic (combined_installs a links table addresses compatible)

/-- The actual execution supplies the output witness; a caller need only
establish its postcondition on the complete linked/immutable runtime image. -/
theorem returned_post (a : Artifact Lib) (links : LinkTable a)
    (table : ImmutableTable a.runtime.length Key) (addresses : Lib → Vector UInt8 20)
    (compatible : Creation.compatible table links.sites = true)
    (post : List UInt8 → Prop) :
    let b := combinedArtifact a links table addresses compatible
    (∃ output, Exec b.payload b.payload [] [] (.returned output) ∧ post output) ↔
      post b.runtime := by
  constructor
  · rintro ⟨output, actual, holds⟩
    have eq : output = (combinedArtifact a links table addresses compatible).runtime :=
      Outcome.returned.inj (outcome_exact a links table addresses compatible _ actual)
    exact eq ▸ holds
  · intro holds
    exact ⟨_, combined_installs a links table addresses compatible, holds⟩

/-- Refutation also uses the actual artifact and the same complete
observation; selecting a matching suffix does not satisfy this postcondition. -/
theorem reject_post (a : Artifact Lib) (links : LinkTable a)
    (table : ImmutableTable a.runtime.length Key) (addresses : Lib → Vector UInt8 20)
    (compatible : Creation.compatible table links.sites = true)
    (post : List UInt8 → Prop)
    (wrong : ¬ post (combinedArtifact a links table addresses compatible).runtime) :
    let b := combinedArtifact a links table addresses compatible
    ¬ ∃ output, Exec b.payload b.payload [] [] (.returned output) ∧ post output :=
  fun actual => wrong ((returned_post a links table addresses compatible post).mp actual)

/-- A genuine constructor RETURN cannot be relabelled a revert, even with
arbitrary revert data. This does not rule out failures of other constructors. -/
theorem not_reverted (a : Artifact Lib) (links : LinkTable a)
    (table : ImmutableTable a.runtime.length Key) (addresses : Lib → Vector UInt8 20)
    (compatible : Creation.compatible table links.sites = true) (data : List UInt8) :
    let b := combinedArtifact a links table addresses compatible
    ¬ Exec b.payload b.payload [] [] (.reverted data) := by
  intro b actual
  cases outcome_exact a links table addresses compatible _ actual

namespace Controls
open Solidity.Backend.Executable.CreationPatchOrder.Controls

/-- Reuses the published nonempty, two-link/two-immutable input. The full
105-byte ordered image, argument exclusion and first-byte/window observation
are simultaneous postconditions of ONE actual constructor run. -/
theorem complete_image :
    let b := combinedArtifact artifact links imms addresses compatible_tables
    ∃ output, Exec b.payload b.payload [] [] (.returned output) ∧
      output = expected ∧ output ≠ expected ++ artifact.args ∧
      output ≠ expected.drop 1 := by
  apply (returned_post artifact links imms addresses compatible_tables _).mpr
  rw [exact_runtime]
  exact ⟨rfl, no_argument_leak, nonzero_prefix_matters⟩

/-- Wrong final image: constructor arguments do not leak into returned runtime. -/
theorem wrong_arguments :
    let b := combinedArtifact artifact links imms addresses compatible_tables
    ¬ ∃ output, Exec b.payload b.payload [] [] (.returned output) ∧
      output = expected ++ artifact.args := by
  apply reject_post artifact links imms addresses compatible_tables
  exact no_argument_leak

/-- Wrong observation window: observing only the image after its first byte is not
observing the constructor's complete returned runtime. -/
theorem wrong_window :
    let b := combinedArtifact artifact links imms addresses compatible_tables
    ¬ ∃ output, Exec b.payload b.payload [] [] (.returned output) ∧
      output = expected.drop 1 := by
  apply reject_post artifact links imms addresses compatible_tables
  rw [exact_runtime]
  exact nonzero_prefix_matters

/-- Same concrete populated input, with the opposite outcome constructor. -/
theorem wrong_failure (data : List UInt8) :
    let b := combinedArtifact artifact links imms addresses compatible_tables
    ¬ Exec b.payload b.payload [] [] (.reverted data) :=
  not_reverted artifact links imms addresses compatible_tables data

end Controls
end Solidity.Roadmap.V16.CreationReturnConsumer

/-- info: 'Solidity.Roadmap.V16.CreationReturnConsumer.outcome_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.CreationReturnConsumer.outcome_exact

/-- info: 'Solidity.Roadmap.V16.CreationReturnConsumer.returned_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.CreationReturnConsumer.returned_post

/-- info: 'Solidity.Roadmap.V16.CreationReturnConsumer.reject_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.CreationReturnConsumer.reject_post

/-- info: 'Solidity.Roadmap.V16.CreationReturnConsumer.not_reverted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.CreationReturnConsumer.not_reverted

/-- info: 'Solidity.Roadmap.V16.CreationReturnConsumer.Controls.complete_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.CreationReturnConsumer.Controls.complete_image

/-- info: 'Solidity.Roadmap.V16.CreationReturnConsumer.Controls.wrong_arguments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.CreationReturnConsumer.Controls.wrong_arguments

/-- info: 'Solidity.Roadmap.V16.CreationReturnConsumer.Controls.wrong_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.CreationReturnConsumer.Controls.wrong_window

/-- info: 'Solidity.Roadmap.V16.CreationReturnConsumer.Controls.wrong_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.CreationReturnConsumer.Controls.wrong_failure
