import Solidity.Roadmap.V16.CreationReturnConsumer
import Solidity.Backend.Executable.CreationReturnProducerControls

/-! Complete constructor-return postconditions under referenced-library changes.
This consumes actual finite constructor executions and the published exact
library-observation theorem. No Source constructor, account installation,
fetched CREATE, gas or transaction adequacy follows. -/
namespace Solidity.Roadmap.V16.CreationLibrarySpec
open Solidity.Backend Solidity.Backend.Creation
open CreationReturnConsumer

/-- All postconditions on complete actual constructor returns agree exactly when every referenced address agrees. No desired execution is a premise. -/
theorem complete_spec_iff :
    ∀ (a : Solidity.Backend.Creation.Artifact Lib) (links : Solidity.Backend.Creation.LinkTable a)
    (table : Solidity.Backend.Creation.ImmutableTable a.runtime.length Key)
    (left right : Lib → Vector UInt8 20)
    (h : Solidity.Backend.Creation.compatible table links.sites = true),
    let l := Solidity.Backend.Creation.combinedArtifact a links table left h
    let r := Solidity.Backend.Creation.combinedArtifact a links table right h
    (∀ post : List UInt8 → Prop,
      (∃ output, Solidity.Backend.Creation.Exec l.payload l.payload [] [] (.returned output) ∧ post output) ↔
      (∃ output, Solidity.Backend.Creation.Exec r.payload r.payload [] [] (.returned output) ∧ post output)) ↔
      ∀ s ∈ links.sites, (left s.library).toList = (right s.library).toList := by
  intro a links table left right h l r
  constructor
  · intro all
    have chosen := (all (fun output => output = l.runtime)).mp
      ⟨l.runtime, Solidity.Backend.Creation.combined_installs a links table left h, rfl⟩
    have equal : r.runtime = l.runtime :=
      (Solidity.Roadmap.V16.CreationReturnConsumer.returned_post a links table right h _).mp chosen
    exact (Solidity.Backend.Executable.CreationReturnProducer.runtime_equal_iff a links table left right h).mp equal.symm
  · intro same post
    have equal := (Solidity.Backend.Executable.CreationReturnProducer.runtime_equal_iff a links table left right h).mpr same
    have lp := Solidity.Roadmap.V16.CreationReturnConsumer.returned_post a links table left h post
    have rp := Solidity.Roadmap.V16.CreationReturnConsumer.returned_post a links table right h post
    dsimp only at lp rp
    rw [lp, rp, equal]


/-- A populated 105-byte constructor fixture preserves all complete-return specifications despite a genuinely different unused address. -/
theorem unused_client :
    Solidity.Backend.Executable.CreationReturnProducer.Controls.first.runtime.length = 105 ∧ Solidity.Backend.Executable.CreationReturnProducer.Controls.first.args = [202,254] ∧
 Solidity.Backend.Executable.CreationPatchOrder.Controls.addresses true ≠ Solidity.Backend.Executable.CreationReturnProducer.Controls.changedUnused true ∧
 (∀ post : List UInt8 → Prop, (∃ output, Solidity.Backend.Creation.Exec Solidity.Backend.Executable.CreationReturnProducer.Controls.first.payload Solidity.Backend.Executable.CreationReturnProducer.Controls.first.payload [] [] (.returned output) ∧ post output) ↔ (∃ output, Solidity.Backend.Creation.Exec Solidity.Backend.Executable.CreationReturnProducer.Controls.second.payload Solidity.Backend.Executable.CreationReturnProducer.Controls.second.payload [] [] (.returned output) ∧ post output)) := by
  refine ⟨Solidity.Backend.Executable.CreationReturnProducer.Controls.populated.1, Solidity.Backend.Executable.CreationReturnProducer.Controls.populated.2.1, Solidity.Backend.Executable.CreationReturnProducer.Controls.inputs_distinct, ?_⟩
  apply (Solidity.Roadmap.V16.CreationLibrarySpec.complete_spec_iff Solidity.Backend.Executable.CreationReturnProducer.Controls.oneArtifact Solidity.Backend.Executable.CreationReturnProducer.Controls.oneLinks Solidity.Backend.Executable.CreationPatchOrder.Controls.imms Solidity.Backend.Executable.CreationPatchOrder.Controls.addresses Solidity.Backend.Executable.CreationReturnProducer.Controls.changedUnused Solidity.Backend.Executable.CreationReturnProducer.Controls.one_compatible).mpr
  intro site member
  have sameSite : site = Solidity.Backend.Executable.CreationPatchOrder.Controls.s := List.mem_singleton.mp member
  subst site
  rfl

/-- Swapping referenced addresses fails the new all-postcondition equivalence, despite equal-length runtime images. -/
theorem referenced_rejected :
    ¬ (∀ post : List UInt8 → Prop,
 (∃ output, Solidity.Backend.Creation.Exec (Solidity.Backend.Creation.combinedArtifact Solidity.Backend.Executable.CreationPatchOrder.Controls.artifact Solidity.Backend.Executable.CreationPatchOrder.Controls.links Solidity.Backend.Executable.CreationPatchOrder.Controls.imms Solidity.Backend.Executable.CreationPatchOrder.Controls.addresses Solidity.Backend.Executable.CreationPatchOrder.Controls.compatible_tables).payload (Solidity.Backend.Creation.combinedArtifact Solidity.Backend.Executable.CreationPatchOrder.Controls.artifact Solidity.Backend.Executable.CreationPatchOrder.Controls.links Solidity.Backend.Executable.CreationPatchOrder.Controls.imms Solidity.Backend.Executable.CreationPatchOrder.Controls.addresses Solidity.Backend.Executable.CreationPatchOrder.Controls.compatible_tables).payload [] [] (.returned output) ∧ post output) ↔
 (∃ output, Solidity.Backend.Creation.Exec Solidity.Backend.Executable.CreationLinkIdentity.Controls.alternate.payload Solidity.Backend.Executable.CreationLinkIdentity.Controls.alternate.payload [] [] (.returned output) ∧ post output)) := by
  intro all
  exact Solidity.Backend.Executable.CreationReturnProducer.Controls.referenced_difference
    ((Solidity.Roadmap.V16.CreationLibrarySpec.complete_spec_iff Solidity.Backend.Executable.CreationPatchOrder.Controls.artifact Solidity.Backend.Executable.CreationPatchOrder.Controls.links Solidity.Backend.Executable.CreationPatchOrder.Controls.imms Solidity.Backend.Executable.CreationPatchOrder.Controls.addresses Solidity.Backend.Executable.CreationLinkIdentity.Controls.swapped Solidity.Backend.Executable.CreationPatchOrder.Controls.compatible_tables).mp all)

/-- An actual complete-runtime equality postcondition succeeds on one constructor and is rejected on the swapped constructor. -/
theorem distinguishing_post :
    (∃ output, Solidity.Backend.Creation.Exec (Solidity.Backend.Creation.combinedArtifact Solidity.Backend.Executable.CreationPatchOrder.Controls.artifact Solidity.Backend.Executable.CreationPatchOrder.Controls.links Solidity.Backend.Executable.CreationPatchOrder.Controls.imms Solidity.Backend.Executable.CreationPatchOrder.Controls.addresses Solidity.Backend.Executable.CreationPatchOrder.Controls.compatible_tables).payload (Solidity.Backend.Creation.combinedArtifact Solidity.Backend.Executable.CreationPatchOrder.Controls.artifact Solidity.Backend.Executable.CreationPatchOrder.Controls.links Solidity.Backend.Executable.CreationPatchOrder.Controls.imms Solidity.Backend.Executable.CreationPatchOrder.Controls.addresses Solidity.Backend.Executable.CreationPatchOrder.Controls.compatible_tables).payload [] [] (.returned output) ∧ output = Solidity.Backend.Executable.CreationPatchOrder.Controls.expected) ∧
 ¬ (∃ output, Solidity.Backend.Creation.Exec Solidity.Backend.Executable.CreationLinkIdentity.Controls.alternate.payload Solidity.Backend.Executable.CreationLinkIdentity.Controls.alternate.payload [] [] (.returned output) ∧ output = Solidity.Backend.Executable.CreationPatchOrder.Controls.expected) := by
  constructor
  · exact ⟨Solidity.Backend.Executable.CreationPatchOrder.Controls.expected, Solidity.Backend.Executable.CreationPatchOrder.Controls.constructor_returns, rfl⟩
  · exact Solidity.Roadmap.V16.CreationReturnConsumer.reject_post Solidity.Backend.Executable.CreationPatchOrder.Controls.artifact Solidity.Backend.Executable.CreationPatchOrder.Controls.links Solidity.Backend.Executable.CreationPatchOrder.Controls.imms Solidity.Backend.Executable.CreationLinkIdentity.Controls.swapped Solidity.Backend.Executable.CreationPatchOrder.Controls.compatible_tables (fun output => output = Solidity.Backend.Executable.CreationPatchOrder.Controls.expected) Solidity.Backend.Executable.CreationLinkIdentity.Controls.same_length_distinct_runtime.2


/-- The new specification family constructs two actual constructor runs with the SAME complete 105-byte output and its live linked-address window. -/
theorem actual_runs :
    ∃ output, Solidity.Backend.Creation.Exec Solidity.Backend.Executable.CreationReturnProducer.Controls.first.payload Solidity.Backend.Executable.CreationReturnProducer.Controls.first.payload [] [] (.returned output) ∧
 Solidity.Backend.Creation.Exec Solidity.Backend.Executable.CreationReturnProducer.Controls.second.payload Solidity.Backend.Executable.CreationReturnProducer.Controls.second.payload [] [] (.returned output) ∧
 output = Solidity.Backend.Executable.CreationReturnProducer.Controls.first.runtime ∧ output.length = 105 ∧
 (output.drop 33).take 20 = (Solidity.Backend.Executable.CreationPatchOrder.Controls.addresses false).toList := by
  have family := Solidity.Roadmap.V16.CreationLibrarySpec.unused_client.2.2.2
  obtain ⟨output, second, equal⟩ := (family (fun out => out = Solidity.Backend.Executable.CreationReturnProducer.Controls.first.runtime)).mp ⟨Solidity.Backend.Executable.CreationReturnProducer.Controls.first.runtime, Solidity.Backend.Executable.CreationReturnProducer.Controls.first_returns, rfl⟩
  subst output
  exact ⟨Solidity.Backend.Executable.CreationReturnProducer.Controls.first.runtime, Solidity.Backend.Executable.CreationReturnProducer.Controls.first_returns, second, rfl, Solidity.Backend.Executable.CreationReturnProducer.Controls.populated.1, Solidity.Backend.Executable.CreationReturnProducer.Controls.populated.2.2⟩

end Solidity.Roadmap.V16.CreationLibrarySpec

/-- info: 'Solidity.Roadmap.V16.CreationLibrarySpec.complete_spec_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.CreationLibrarySpec.complete_spec_iff

/-- info: 'Solidity.Roadmap.V16.CreationLibrarySpec.unused_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.CreationLibrarySpec.unused_client

/-- info: 'Solidity.Roadmap.V16.CreationLibrarySpec.referenced_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.CreationLibrarySpec.referenced_rejected

/-- info: 'Solidity.Roadmap.V16.CreationLibrarySpec.distinguishing_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.CreationLibrarySpec.distinguishing_post

/-- info: 'Solidity.Roadmap.V16.CreationLibrarySpec.actual_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.CreationLibrarySpec.actual_runs
