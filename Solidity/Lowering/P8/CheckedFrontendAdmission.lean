import Solidity.Lowering.P8.FrozenInterface

/-! Executable admission derived from the existing checked frontend contract.
The CheckedFrontend argument is an explicit pending producer fact, not an
inhabitant or proof of concrete Source adequacy. No SourceSpec is fabricated.
This derives soundness/completeness/agreement instead of assuming them twice. -/
namespace Solidity.Lowering.P8.CheckedFrontendAdmission
open Solidity.Roadmap P8a

variable {S : Spec}

def frontend (checked : CheckedFrontend S) (i : S.Input) : Option S.Resolved :=
  (checked.produce i).map Prod.fst

theorem frontend_iff (checked : CheckedFrontend S) (i : S.Input) (r : S.Resolved) :
    frontend checked i = some r ↔ S.Admitted i r := by
  constructor
  · intro accepted
    cases produced : checked.produce i with
    | none =>
      simp only [frontend, produced, Option.map_none] at accepted
      cases accepted
    | some pair =>
      rcases pair with ⟨resolved,cert⟩
      have same : resolved = r := Option.some.inj (by
        simpa only [frontend, produced, Option.map_some] using accepted)
      subst resolved
      exact checked.checked i r cert (checked.accepted i r cert produced)
  · intro admitted
    obtain ⟨cert,produced⟩ := checked.complete i r admitted
    simp only [frontend, produced, Option.map_some]

/-- A real Option algorithm with proofs derived from the supplied checker's
published laws. No separate Admission or frontend-agreement premise is used. -/
def admission (checked : CheckedFrontend S) : Admission S where
  frontend := frontend checked
  sound := fun i r h => (frontend_iff checked i r).mp h
  complete := fun i r h => (frontend_iff checked i r).mpr h

theorem frontend_agrees (checked : CheckedFrontend S) (i : S.Input) :
    (admission checked).frontend i = (checked.produce i).map Prod.fst := by rfl

theorem rejection_iff (checked : CheckedFrontend S) (i : S.Input) :
    frontend checked i = none ↔ ∀ r, ¬ S.Admitted i r := by
  constructor
  · intro rejected r admitted
    have accepted := (frontend_iff checked i r).mpr admitted
    rw [rejected] at accepted
    cases accepted
  · intro refused
    cases result : frontend checked i with
    | none => rfl
    | some r => exact False.elim (refused r ((frontend_iff checked i r).mp result))

/-- Uniqueness of admitted resolutions, not the stronger parse/resolution
Unambiguous field of SourceSpec, which remains a separate producer fact. -/
theorem admitted_unique (checked : CheckedFrontend S) (i : S.Input)
    (r r' : S.Resolved) (h : S.Admitted i r) (h' : S.Admitted i r') : r = r' := by
  exact Option.some.inj (((frontend_iff checked i r).mpr h).symm.trans
    ((frontend_iff checked i r').mpr h'))

theorem certificate (checked : CheckedFrontend S) (i : S.Input) (r : S.Resolved)
    (accepted : frontend checked i = some r) :
    ∃ cert, checked.produce i = some (r,cert) ∧ checked.check i r cert = true := by
  obtain ⟨cert,produced⟩ := checked.complete i r ((frontend_iff checked i r).mp accepted)
  exact ⟨cert,produced,checked.accepted i r cert produced⟩

/-- A refused certificate cannot be the actual produced receipt. This keeps
fail-closed checker behavior separate from existence of another certificate. -/
theorem check_false_refuses (checked : CheckedFrontend S) (i : S.Input)
    (r : S.Resolved) (cert : checked.Cert) (refused : checked.check i r cert = false) :
    checked.produce i ≠ some (r,cert) := by
  intro produced
  have accepted := checked.accepted i r cert produced
  rw [refused] at accepted
  cases accepted

/-- Uses EXACT extraction hypotheses: both execution and observation roots,
all features and their combinations. This does not construct a RootModel. -/
theorem accepted_extraction (checked : CheckedFrontend S) (roots : RootModel S)
    (extractor : Extractor roots) (i : S.Input) (r : S.Resolved)
    (accepted : frontend checked i = some r) :
    (∀ root, root ∈ (extractor.extract r).roots ↔
      roots.executionRoot r root ∨ roots.observationRoot r root) ∧
    (∀ feature, feature ∈ (extractor.extract r).features ↔
      ∃ root ∈ (extractor.extract r).roots, roots.featureAt r root feature) ∧
    roots.classify r (extractor.extract r).features = true := by
  obtain ⟨parsed,parse,resolve,well,profile⟩ := (frontend_iff checked i r).mp accepted
  exact ⟨(extractor.extract r).roots_exact, (extractor.extract r).features_exact,
    (extractor.extract r).classification_exact.mpr profile⟩

theorem classification_false_refuses (checked : CheckedFrontend S) (roots : RootModel S)
    (extractor : Extractor roots) (i : S.Input) (r : S.Resolved)
    (refused : roots.classify r (extractor.extract r).features = false) :
    frontend checked i ≠ some r := by
  intro accepted
  have classified := (accepted_extraction checked roots extractor i r accepted).2.2
  rw [refused] at classified
  cases classified

/-- Both-pipeline certificate closure follows from the full semantic field,
not merely the proved component metadata/settings closure. -/
theorem pipeline_certificate (checked : CheckedFrontend S)
    (pipelines : S.AllPipelines) (i : S.Input) (r : S.Resolved)
    (accepted : frontend checked i = some r) (q : Pipeline) :
    ∃ r' cert, checked.produce (S.setPipeline i q) = some (r',cert) ∧
      checked.check (S.setPipeline i q) r' cert = true := by
  obtain ⟨r',admitted⟩ := pipelines i q ⟨r,(frontend_iff checked i r).mp accepted⟩
  exact ⟨r', certificate checked (S.setPipeline i q) r' ((frontend_iff checked _ _).mpr admitted)⟩

/-- info: 'Solidity.Lowering.P8.CheckedFrontendAdmission.frontend_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms frontend_iff
/-- info: 'Solidity.Lowering.P8.CheckedFrontendAdmission.rejection_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms rejection_iff
/-- info: 'Solidity.Lowering.P8.CheckedFrontendAdmission.check_false_refuses' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms check_false_refuses
/-- info: 'Solidity.Lowering.P8.CheckedFrontendAdmission.classification_false_refuses' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms classification_false_refuses
/-- info: 'Solidity.Lowering.P8.CheckedFrontendAdmission.admitted_unique' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted_unique
/-- info: 'Solidity.Lowering.P8.CheckedFrontendAdmission.accepted_extraction' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_extraction
/-- info: 'Solidity.Lowering.P8.CheckedFrontendAdmission.pipeline_certificate' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pipeline_certificate
end Solidity.Lowering.P8.CheckedFrontendAdmission
