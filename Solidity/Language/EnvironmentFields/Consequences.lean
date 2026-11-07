import Solidity.Language.EnvironmentFields.Frozen

/-!
# Completion consequences of the frozen run-indexed certificate

The backward direction is as exact at a completed prefix as the forward
lemma in Frozen. These are consequences of the existing certificate, not
production instances or additional public premises.
-/

namespace Solidity.Roadmap.FullScope.V1

open Solidity.Roadmap Solidity.Roadmap.FullScope Solidity.Roadmap.FullScope.RunIndexed

/-- Every eligible guarded completed target run has an eligible guarded source
run with the identical completed observation, under the selected mode. -/
theorem backward_completes {source : Source} {target : Target}
    {domain : SourceRuns source} {machine : TargetRuns target}
    {compiler : source.Resolved → Option Artifact}
    {environment : target.lang.Env → source.lang.Env} {aligned : Alignment source target}
    {mode : Mode}
    (certificate : Certificate source target domain machine compiler environment aligned mode)
    {resolved : source.Resolved} {art : Artifact} (compiled : compiler resolved = some art)
    (run : TargetIndex target art) (eligible : run.Eligible)
    (guard : target.lang.Guard (target.load art) run.environment run.resource)
    {o : Outcome} (completes : (mode.observe run.execution).final = some o) :
    ∃ sourceRun : SourceIndex source resolved art, domain.Eligible sourceRun ∧
      Coupled domain machine environment aligned .backward sourceRun run ∧
      source.lang.Guard sourceRun.program sourceRun.environment sourceRun.resource ∧
      mode.observe sourceRun.execution = mode.observe run.execution := by
  obtain ⟨sourceRun, sourceEligible, coupled, sourceGuard, below⟩ :=
    certificate.backward resolved art compiled run eligible guard
  exact ⟨sourceRun, sourceEligible, coupled, sourceGuard, below.final_eq completes⟩

/-- In exact mode the completed target's entire observation list and outcome,
including ordered logs and bytes, are those of the source witness. -/
theorem backward_exact {source : Source} {target : Target}
    {domain : SourceRuns source} {machine : TargetRuns target}
    {compiler : source.Resolved → Option Artifact}
    {environment : target.lang.Env → source.lang.Env} {aligned : Alignment source target}
    (certificate : D1 source target domain machine compiler environment aligned)
    {resolved : source.Resolved} {art : Artifact} (compiled : compiler resolved = some art)
    (run : TargetIndex target art) (eligible : run.Eligible)
    (guard : target.lang.Guard (target.load art) run.environment run.resource)
    {o : Outcome} (completes : run.execution.final = some o) :
    ∃ sourceRun : SourceIndex source resolved art, domain.Eligible sourceRun ∧
      sourceRun.execution = run.execution := by
  obtain ⟨sourceRun, sourceEligible, _, _, same⟩ :=
    backward_completes certificate compiled run eligible guard completes
  exact ⟨sourceRun, sourceEligible, same⟩

end Solidity.Roadmap.FullScope.V1
