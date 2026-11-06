import Solidity.Roadmap.Controls

/-! Additive audit only. Frozen interfaces are unchanged.
The contradiction theorem below records an impossible simultaneous witness,
not a defect in the intentionally negative frozen theorem.
The positive control is explicitly the published toy instance, not a proof
about the production compiler or a real Osaka gas schedule.
-/
namespace Solidity.H62.AuditRoadmap
open Solidity.Roadmap Solidity.Roadmap.Controls

/-- Exact impossibility of jointly inhabiting the three hypotheses of
`Solidity.Roadmap.PublicCorrectness.not_alwaysRevert`. -/
theorem no_simultaneous_not_alwaysRevert_witness
    {I : IntrinsicSpec} {S : SourceSpec} {V : EvmSpec}
    {compiler : S.Input → Option Artifact} {envAbs : V.lang.Env → S.lang.Env}
    {X : StateExport S I V} :
    ¬ (∃ (_h : PublicCorrectness S V compiler envAbs X) (_hv : S.NonVacuous),
      ∀ i art e rt d, compiler i = some art → V.lang.Allowed e → V.lang.Admissible rt →
        (V.lang.sem (V.load art) e rt).final ≠ some (.success d)) := by
  intro hw
  obtain ⟨h, hv, hrev⟩ := hw
  exact h.not_alwaysRevert hv hrev

/-- Reject-all compilers fail the unchanged public contract when its source
has the unchanged non-vacuity certificate. -/
theorem reject_all_excluded
    {I : IntrinsicSpec} {S : SourceSpec} {V : EvmSpec}
    {envAbs : V.lang.Env → S.lang.Env} {X : StateExport S I V}
    (hv : S.NonVacuous) :
    ¬ PublicCorrectness S V (fun _ => none) envAbs X := by
  intro h
  obtain ⟨i, art, hc⟩ := h.compiles hv
  cases hc

/-- The two global premises of the frozen success theorem are jointly
inhabited by the same published toy instance, and yield observable nonempty
success at allowed environment and admissible resource. -/
theorem toy_joint_success :
    PublicCorrectness toySource toyEvm toyCompiler id toyExport ∧
    toySource.NonVacuous ∧
    ∃ i art e rt d, toyCompiler i = some art ∧ toyEvm.lang.Allowed e ∧
      toyEvm.lang.Admissible rt ∧ d ≠ [] ∧
      (toyEvm.lang.sem (toyEvm.load art) e rt).final = some (.success d) :=
  ⟨toy_publicCorrectness, toySource_nonVacuous,
    toy_publicCorrectness.succeeds toySource_nonVacuous⟩

/-- The toy's explicit source resource-failure bit changes a successful
execution into an observable empty revert. This is not a real gas-cost law. -/
theorem toy_failure_boundary (d : Bytes) :
    (Toy.quiet d).run false = ⟨[], some (.success d)⟩ ∧
    (Toy.quiet d).run true = ⟨[], some (.revert [])⟩ := ⟨rfl, rfl⟩

/-- H69: the toy source intentionally emits no events; assumed membership
in the output event list is therefore jointly impossible. -/
theorem no_toy_event_witness :
    ¬ ∃ (p : Toy) (r : Bound) (x : Event), x ∈ (Toy.run p r.exhausted).events := by
  intro hw
  obtain ⟨p, r, x, hm⟩ := hw
  exact toy_no_event hm

/-- H69: the compiled toy has the same intentional event-absence control. -/
theorem no_toy_evm_event_witness :
    ¬ ∃ (art : Artifact) (x : Event),
      x ∈ ((decode (mainRuntime art)).run false).events := by
  intro hw
  obtain ⟨art, x, hm⟩ := hw
  exact toyEvm_no_event hm

end Solidity.H62.AuditRoadmap

#print axioms Solidity.H62.AuditRoadmap.no_simultaneous_not_alwaysRevert_witness
#print axioms Solidity.H62.AuditRoadmap.reject_all_excluded
#print axioms Solidity.H62.AuditRoadmap.toy_joint_success
#print axioms Solidity.H62.AuditRoadmap.toy_failure_boundary

#print axioms Solidity.H62.AuditRoadmap.no_toy_event_witness
#print axioms Solidity.H62.AuditRoadmap.no_toy_evm_event_witness
