import Solidity.Lowering.V08.WorldCatalogueControls

/-! Guards confusing an individually inhabited catalogue/reset/image premise
with a coherent world model, or treating Image as clock/admission adequacy.
The existing populated two-slot fixture is reused unchanged, including its toy
history-insensitive ledger. No canonical ledger, SourceSpec or body producer is
constructed. Empty accounts and zero funds cannot satisfy its populated Image. -/
namespace H62.AuditV08Adapters.WorldImageJoint
open Solidity Solidity.Lowering.V08
open WorldResetControls WorldCatalogueControls

/-- Catalogue data and all reset/image/clock premises share the SAME assembly.
Inputs carries data, so it is existentially bound rather than treated as Prop. -/
def Joint (p : Roadmap.Pipeline) : Prop :=
  ∃ prepared : WorldCatalogue.Inputs (SourceEnvironmentControls.global p)
      kindOf relation SourceEnvironmentControls.populated,
    WorldCatalogue.assemble prepared environment SourceEnvironmentControls.populated.events
      (EnvironmentProjection.liftWord (SourceEnvironmentControls.global p).timestamp) = world p ∧
    WorldImage.ResetInputs relation ∧
    WorldImage.Image (SourceEnvironmentControls.global p) kindOf relation environment
      SourceEnvironmentControls.populated.events SourceEnvironmentControls.populated (world p) ∧
    WorldImage.TimeAligned (SourceEnvironmentControls.global p) (world p)

theorem joint (p : Roadmap.Pipeline) : Joint p :=
  ⟨inputs p, rfl, slots, initial_image p, rfl⟩

/-- Both original image_reset hypotheses are actual simultaneous witnesses;
clock agreement remains a separate conclusion for this same chosen timestamp. -/
theorem reset_actual (p : Roadmap.Pipeline) :
    WorldImage.Image (SourceEnvironmentControls.global p) kindOf relation environment
      SourceEnvironmentControls.populated.events
      (SourceTransient.endExecution SourceEnvironmentControls.populated) (world p).resetTransient ∧
    WorldImage.TimeAligned (SourceEnvironmentControls.global p) (world p).resetTransient :=
  ⟨WorldImage.image_reset slots (initial_image p), rfl⟩

def zeroWord : Semantics.Word := ⟨0, by decide⟩
def noAccounts (p : Roadmap.Pipeline) : ContractWorld.World catalog :=
  {world p with accounts := fun _ => none}
def noFunds (p : Roadmap.Pipeline) : ContractWorld.World catalog :=
  {world p with funds := fun _ => zeroWord}
def wrongClock (p : Roadmap.Pipeline) : ContractWorld.World catalog :=
  WorldCatalogue.assemble (inputs p) environment SourceEnvironmentControls.populated.events zeroWord

/-- Reject the empty-account model against the genuinely installed source code. -/
theorem empty_accounts_refused (p : Roadmap.Pipeline) :
    ¬ WorldImage.Image (SourceEnvironmentControls.global p) kindOf relation environment
      SourceEnvironmentControls.populated.events SourceEnvironmentControls.populated (noAccounts p) := by
  intro h
  have installed := h.accounts (EnvironmentProjection.liftAddress SourceEnvironmentControls.self)
  dsimp only [WorldImage.AccountImage] at installed
  rw [EnvironmentProjection.lower_lift_address, source_code, if_pos rfl] at installed
  obtain ⟨name, kind, stored, selected, linked, impossible, represented⟩ := installed
  change none = some _ at impossible
  cases impossible

/-- The relative ledger's nonzero sender balance rules out zero target funds. -/
theorem zero_funds_refused (p : Roadmap.Pipeline) :
    ¬ WorldImage.Image (SourceEnvironmentControls.global p) kindOf relation environment
      SourceEnvironmentControls.populated.events SourceEnvironmentControls.populated (noFunds p) := by
  intro h
  have atSender := congrFun h.funds (EnvironmentProjection.liftAddress SourceEnvironmentControls.sender)
  have observed := congrArg Subtype.val atSender
  change (0 : Int) = 100 at observed
  cases observed

/-- Image deliberately covers no clock. This valid Image is NOT TimeAligned. -/
theorem wrong_clock_image (p : Roadmap.Pipeline) :
    WorldImage.Image (SourceEnvironmentControls.global p) kindOf relation environment
      SourceEnvironmentControls.populated.events SourceEnvironmentControls.populated (wrongClock p) :=
  WorldCatalogue.assembled_image (inputs p) environment SourceEnvironmentControls.populated.events zeroWord

theorem wrong_clock_refused (p : Roadmap.Pipeline) :
    ¬ WorldImage.TimeAligned (SourceEnvironmentControls.global p) (wrongClock p) := by
  intro h
  have observed := congrArg Subtype.val h
  change (0 : Int) = 12345 at observed
  cases observed

#print axioms joint
#print axioms reset_actual
#print axioms empty_accounts_refused
#print axioms zero_funds_refused
#print axioms wrong_clock_image
#print axioms wrong_clock_refused
end H62.AuditV08Adapters.WorldImageJoint
