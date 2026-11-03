import Solidity.Lowering.P8.SourcePrograms
import Solidity.Frontend.Admission.ProgramObservations
import Solidity.Frontend.Admission.TypedStatementPolicy

/-! Whole-output observation admission after actual checked frontend and
Source elaboration. This adds a fail-closed observation guard; it is not
exact all-feature/profile extraction, dispatch reachability or SourceSpec. -/
namespace Solidity.Lowering.P8.SourceObservationAdmission
open Source Roadmap.Frontend Frontend.Admission
open SourcePrograms

def checkProgram {E : Env} (P : Program E) : Bool :=
  (programObservations P).all ObservationSite.allowed

/-- Checks every actual elaborated output, without selecting a subset. -/
def check (es : Programs) : Bool := es.all fun e => checkProgram e.2.prog

/-- Independent actual carried-field occurrence judgment at every unit. -/
def Allowed (es : Programs) : Prop :=
  ∀ e ∈ es, ∀ site, ProgramSite e.2.prog site → site.allowed = true

/-- Leaves original order, names and dependent program values untouched. -/
def accept (i : Input) (p : CheckedSyntax.Parsed) (r : SourceResolutions.Packet)
    (cert : CheckedSyntax.Cert) : Option Programs := do
  let es ← SourcePrograms.accept i p r cert
  if check es then some es else none

abbrev Sound : Prop := ∀ i p r cert es, accept i p r cert = some es →
  i.Ok ∧ CheckedSyntax.Parses i p ∧ SourceResolutions.Resolves p r ∧
  SourceMetadata.ComponentOK r ∧ UnitsElaborate r.units es ∧ Allowed es ∧
  SourcePrograms.accept i p r cert = some es

theorem sound : Sound := by
  intro i p r cert es h
  unfold Solidity.Lowering.P8.SourceObservationAdmission.accept at h
  cases hs : Solidity.Lowering.P8.SourcePrograms.accept i p r cert with
  | none => simp only [hs, bind, Option.bind] at h; cases h
  | some outputs =>
    simp only [hs, bind, Option.bind] at h
    split at h
    · rename_i ha
      cases h
      obtain ⟨hi, hp, hr, hm, he⟩ := Solidity.Lowering.P8.SourcePrograms.accept_sound i p r cert es hs
      refine ⟨hi, hp, hr, hm, he, ?_, rfl⟩
      intro e hin site hsite
      have hc := List.all_eq_true.mp ha e hin
      exact (Solidity.Frontend.Admission.accepted_program_iff e.2.prog).mp hc site hsite
    · cases h

theorem check_all : ∀ es : Programs, check es = true := by
  intro es
  apply List.all_eq_true.mpr
  intro e he
  exact Solidity.Frontend.Admission.TypedObservationPolicy.program_allowed e.2.prog

/-- Routine exact-guard equivalence, not full approved-profile equivalence.
Implemented below without asserting full profile equivalence. -/
abbrev ExactObservationGuard : Prop := ∀ es, check es = true ↔ Allowed es
/-- info: 'Solidity.Lowering.P8.SourceObservationAdmission.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sound
theorem exact_observation_guard : Solidity.Lowering.P8.SourceObservationAdmission.ExactObservationGuard := by
  intro es
  constructor
  · intro h e he site hs
    exact (Solidity.Frontend.Admission.accepted_program_iff e.2.prog).mp (List.all_eq_true.mp h e he) site hs
  · intro h
    apply List.all_eq_true.mpr
    intro e he
    exact (Solidity.Frontend.Admission.accepted_program_iff e.2.prog).mpr (fun site hs => h e he site hs)

/-- info: 'Solidity.Lowering.P8.SourceObservationAdmission.exact_observation_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exact_observation_guard
theorem accept_eq_upstream : ∀ i p r c, Solidity.Lowering.P8.SourceObservationAdmission.accept i p r c = Solidity.Lowering.P8.SourcePrograms.accept i p r c := by
  intro i p r c
  unfold Solidity.Lowering.P8.SourceObservationAdmission.accept
  cases h : Solidity.Lowering.P8.SourcePrograms.accept i p r c <;>
    simp only [bind, Option.bind, Solidity.Lowering.P8.SourceObservationAdmission.check_all, ↓reduceIte] <;> rfl

/-- info: 'Solidity.Lowering.P8.SourceObservationAdmission.accept_eq_upstream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accept_eq_upstream
end Solidity.Lowering.P8.SourceObservationAdmission
