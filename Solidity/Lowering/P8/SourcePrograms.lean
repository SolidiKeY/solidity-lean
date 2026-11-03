import Solidity.Lowering.P8.SourceMetadata
import Solidity.Lowering.P9.ElaborationAdmission

/-! Actual Source elaboration after checked original-byte/frontend stages.
Every unit is processed in order; no profile-completeness, imported-name
execution, SourceSpec or public solc-JSON compiler agreement is asserted. -/
namespace Solidity.Lowering.P8.SourcePrograms
open Solidity.Source Solidity.Roadmap.Frontend
open CheckedSyntax SourceResolutions

abbrev Programs := List (String × Elaborated)

/-- Independent graph of the upstream Source elaborator at every position. -/
def UnitsElaborate : List (String × Resolution) → Programs → Prop
  | [], [] => True
  | u :: us, e :: es => e.1 = u.1 ∧ elaborate u.2 = some e.2 ∧ UnitsElaborate us es
  | _, _ => False

def elaborateUnits : List (String × Resolution) → Option Programs
  | [] => some []
  | u :: us => do
    let e ← elaborate u.2
    let es ← elaborateUnits us
    pure ((u.1, e) :: es)

/-- Validates all original frontend certificates before elaborating all units.
Failure is retained; a failed unit is never dropped from the result. -/
def accept (i : Input) (p : Parsed) (r : Packet) (cert : CheckedSyntax.Cert) :
    Option Programs :=
  if SourceMetadata.checkInput i p r cert then elaborateUnits r.units else none

theorem elaborateUnits_sound : ∀ us es, elaborateUnits us = some es → UnitsElaborate us es := by
  intro us
  induction us with
  | nil =>
    intro es h
    cases h
    trivial
  | cons u us ih =>
    intro es h
    cases he : elaborate u.2 with
    | none => simp only [elaborateUnits, he] at h; cases h
    | some e =>
      cases ht : elaborateUnits us with
      | none => simp only [elaborateUnits, he, ht] at h; cases h
      | some rest =>
        simp only [elaborateUnits, he, ht] at h
        cases h
        exact ⟨rfl, he, ih rest ht⟩

/-- A failed later unit cannot be silently removed, irrespective of the
head unit's result or the head program's internal proof data. -/
theorem elaborateUnits_tail_failure (u : String × Resolution) (us : List (String × Resolution))
    (h : elaborateUnits us = none) : elaborateUnits (u :: us) = none := by
  cases he : elaborate u.2 <;> simp only [elaborateUnits, he, h, bind, pure, Option.bind] <;> rfl

theorem accept_sound (i : Input) (p : Parsed) (r : Packet) (cert : CheckedSyntax.Cert)
    (es : Programs) (h : accept i p r cert = some es) :
    i.Ok ∧ Parses i p ∧ SourceResolutions.Resolves p r ∧ SourceMetadata.ComponentOK r ∧
      UnitsElaborate r.units es := by
  unfold accept at h
  split at h
  · rename_i hc
    obtain ⟨hi, hp, hr, hm⟩ := SourceMetadata.input_sound i p r cert hc
    exact ⟨hi, hp, hr, hm, elaborateUnits_sound r.units es h⟩
  · cases h

/-- Untrusted parse candidates are rechecked by accept; no existing public
compiler is rerouted, and no candidate completeness is asserted. -/
def produce (i : Input) : Option Programs := do
  let candidate ← CheckedSyntax.produce i
  accept i candidate.1 (SourceResolutions.produce candidate.1) candidate.2

/-- Routine candidate-wrapper transport, not an exported correctness proof. -/
abbrev ProduceInputSound : Prop :=
  ∀ i es, produce i = some es → ∃ p cert,
    i.Ok ∧ Parses i p ∧ SourceResolutions.Resolves p (SourceResolutions.produce p) ∧
    SourceMetadata.ComponentOK (SourceResolutions.produce p) ∧
    UnitsElaborate (SourceResolutions.produce p).units es ∧
    accept i p (SourceResolutions.produce p) cert = some es

/-- Open output identity packaging; no proof is supplied.
The single-unit identity theorem is the published P9.elaborate_program. -/
def UnitsRealize : List (String × Resolution) → Programs → Prop
  | [], [] => True
  | u :: us, e :: es => e.1 = u.1 ∧ e.2.res = u.2 ∧
      HEq e.2.prog (progOf u.2.env) ∧ UnitsRealize us es
  | _, _ => False

abbrev UnitsProgramIdentity : Prop :=
  ∀ us es, UnitsElaborate us es → UnitsRealize us es

/-- info: 'Solidity.Lowering.P8.SourcePrograms.elaborateUnits_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms elaborateUnits_sound
/-- info: 'Solidity.Lowering.P8.SourcePrograms.accept_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accept_sound
/-- info: 'Solidity.Lowering.P8.SourcePrograms.elaborateUnits_tail_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms elaborateUnits_tail_failure
end Solidity.Lowering.P8.SourcePrograms
