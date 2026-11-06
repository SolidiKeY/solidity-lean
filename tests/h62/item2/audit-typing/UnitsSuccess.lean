import Solidity.Frontend.Static.Certificates
import Solidity.Frontend.Static.UnitsExamples

namespace H62.AuditTyping.UnitsSuccess
open Solidity.Source
open Solidity.Frontend.Static
open Solidity.Frontend.Static.UnitsExamples
open Solidity.Roadmap.Frontend (Checker)

abbrev ResolutionChecker := Checker (UnitSet × List Remapping) Unit
  (fun pr _ => UnitsOK pr.1 pr.2)

/-- Explicit success for every supported resolution input, with a certificate.
The support predicate is independent of the candidate checker. -/
def SupportedSuccess (c : ResolutionChecker) : Prop :=
  ∀ P R, UnitsOK P R → ∃ cert : c.Cert, c.check (P, R) () cert = true

theorem units_success : SupportedSuccess unitsChecker := by
  intro P R h
  exact ⟨(), unitsChecker_complete P R h⟩

-- The existing fixture has two real functions f(bool)/f(uint8) in two
-- compilation units imported by a third. Reuse original producer fixtures.
theorem overload_program_accepted : unitsChecker.check (freeOverloads, []) () () = true :=
  unitsChecker_complete freeOverloads [] freeOverloads_ok

theorem supported_program_nonempty : freeOverloads.units.length = 3 := rfl

/-- The original soundness-only Checker structure admits reject-all. -/
def alwaysReject : ResolutionChecker where
  Cert := Unit
  check _ _ _ := false
  sound _ _ _ h := by cases h

theorem reject_all_fails_success : ¬ SupportedSuccess alwaysReject := by
  intro h
  obtain ⟨cert, accepted⟩ := h freeOverloads [] freeOverloads_ok
  cases accepted

/-- Preserve a real static failure boundary: a missing import is rejected. -/
theorem missing_import_rejected : unitsChecker.check (missing, []) () () = false := by decide

-- All original inputs, including the actual UnitsOK proof, are supplied.
theorem complete_inputs : ∃ (P : UnitSet) (R : List Remapping),
    ∃ (_h : UnitsOK P R), True :=
  ⟨freeOverloads, [], freeOverloads_ok, True.intro⟩

end H62.AuditTyping.UnitsSuccess
