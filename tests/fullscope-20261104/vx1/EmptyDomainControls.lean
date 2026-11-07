import Solidity.Language.EnvironmentFields.FrozenControls

/-!
# Admitted inputs do not imply eligible executions

An explicit limitation witness for V1.Contract: keeping the source and target
execution functions and the nontrivial creation/layout/assembly witnesses,
replace only Allowed by False. Compilation/admission still hold while every
execution eligibility domain is empty. This does not alter or strengthen V1.
-/

namespace Solidity.Roadmap.FullScope.V1.Controls.EmptyDomains

open Solidity.Roadmap Solidity.Roadmap.FullScope Solidity.Roadmap.FullScope.RunIndexed

-- Keep concrete operational meanings, oracle readers and resources unchanged.
def source : Source :=
  { Controls.source with lang := { Controls.source.lang with Allowed := fun _ => False } }

def target : Target :=
  { Controls.target with lang := { Controls.target.lang with Allowed := fun _ => False } }

def domain : SourceRuns source where
  Admitted := fun _ => True
  Specified := fun resolved art run => Controls.legal (resolved := resolved) (art := art)
    (⟨run.environment, run.resource, run.oracle⟩)
  Legal := fun resolved art run => Controls.legal (resolved := resolved) (art := art)
    (⟨run.environment, run.resource, run.oracle⟩)
  queries := fun _ art run => Controls.transcript art run.oracle
  observations := fun _ art run _ => Controls.transcript_observations art run.oracle
  reads := fun _ art run _ query value observed =>
    Controls.transcript_reads art run.oracle query value observed

def machine : TargetRuns target where
  queries := fun art run => Controls.transcript art (fun _ => run.resource)
  observations := fun art run => Controls.transcript_observations art (fun _ => run.resource)
  reads := fun art run query value observed =>
    Controls.transcript_reads art (fun _ => run.resource) query value observed

def aligned : Alignment source target :=
  fun _ _ sourceRun targetRun => sourceRun.resource = targetRun.resource

def certificate : D1 source target domain machine Controls.compiler id aligned where
  admission := fun _ => ⟨fun _ => rfl, fun _ => trivial⟩
  envSound := fun _ impossible => False.elim impossible
  envOnto := fun _ impossible => False.elim impossible
  legality := fun _ _ _ _ => Iff.rfl
  sourceResourceCoverage := by
    intro resolved art compiled env resource impossible admissible
    exact False.elim impossible
  need := fun _ _ _ run _ _ _ _ => run.resource
  sourceCoverage := by
    intro resolved art compiled run eligible env impossible sameEnv
    exact False.elim impossible
  targetCoverage := by
    intro resolved art compiled run eligible
    exact False.elim eligible.1
  forward := by
    intro resolved art compiled run eligible env impossible sameEnv forward guard
    exact False.elim impossible
  backward := by
    intro resolved art compiled run eligible guard
    exact False.elim eligible.1

/-- The whole existing bundle still has real D2/D3/D4 witnesses. -/
def bundle : Contract source target domain machine Controls.compiler id aligned .exact
    Controls.creation Controls.physical Controls.boundary :=
  ⟨certificate, ⟨(), trivial⟩, Controls.d2, Controls.d3, Controls.d4⟩

theorem admitted_and_compiled :
    domain.Admitted () ∧ Controls.compiler () = some Controls.artifact :=
  ⟨trivial, rfl⟩

theorem no_source_eligible {resolved : source.Resolved} {art : Artifact}
    (run : SourceIndex source resolved art) : ¬ domain.Eligible run :=
  fun eligible => eligible.2.1

theorem no_target_eligible {art : Artifact} (run : TargetIndex target art) :
    ¬ run.Eligible := fun eligible => eligible.1

/-- Negative control: an admitted/compiled bundle does not supply a live source run. -/
theorem no_live_source_success :
    ¬ ∃ run : SourceIndex source () Controls.artifact,
      domain.Eligible run ∧ run.execution.final = some (.success [5]) := by
  rintro ⟨run, eligible, _⟩
  exact no_source_eligible run eligible

#print axioms bundle
#print axioms admitted_and_compiled
#print axioms no_source_eligible
#print axioms no_target_eligible
#print axioms no_live_source_success

end Solidity.Roadmap.FullScope.V1.Controls.EmptyDomains
