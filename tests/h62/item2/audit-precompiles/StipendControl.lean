import Solidity.Stipend.Rule

/-! Negative control for the frozen abstract G43 obligation. This does not claim
an implementation of a compiler or its execution. It shows the obligation alone
cannot rule out the abstract zero-gas/always-failure assignment. -/
namespace H62.AuditPrecompiles
open Solidity Solidity.Stipend Solidity.Roadmap.Evm

theorem obligation_accepts_always_failure (C : Contract) :
    Obligation C (fun _ => 0) (fun _ => True) := by
  constructor
  · intro b _
    show 0 < pinned.stipend
    decide
  · intro b _
    exact True.intro

/-- The negative control has an admitted source body, so it is not an empty domain. -/
theorem always_failure_with_admitted_body (C : Contract) :
    Obligation C (fun _ => 0) (fun _ => True) ∧
    (rule C).fits ⟨(.nil : Prog C [] [])⟩ :=
  ⟨obligation_accepts_always_failure C, empty_fits⟩

#print axioms obligation_accepts_always_failure
#print axioms always_failure_with_admitted_body
end H62.AuditPrecompiles
