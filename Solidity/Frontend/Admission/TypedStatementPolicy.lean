import Solidity.Frontend.Admission.TypedExpressionPolicy

/-! Actual structural statement and Program observation-policy closure.
Conditional builder interfaces are retained, then instantiated with checked
container proofs. This does not establish full feature/profile or SourceSpec
adequacy. -/
namespace Solidity.Frontend.Admission.TypedObservationPolicy
open Source

abbrev StatementBuilder : Prop := ConversionsPolicy → OptionalPolicy → StatementPolicy

theorem statement_from_containers : StatementBuilder := by
  intro hc ho E R M k Γ Γ' s
  induction s using Solidity.Source.RStmt.rec
    (motive_2 := fun _ _ _ b => (Solidity.Frontend.Admission.itemsObservations b).all Solidity.Frontend.Admission.ObservationSite.allowed = true)
  all_goals intros
  all_goals first
    | assumption
    | rw [Solidity.Frontend.Admission.stmtObservations]
    | rw [Solidity.Frontend.Admission.itemsObservations]
  all_goals simp_all only [List.all_append, List.all_cons, List.all_nil, Bool.and_true,
    Solidity.Frontend.Admission.TypedObservationPolicy.expression_allowed, ho.1, ho.2]
  all_goals simp only [Solidity.Frontend.Admission.ObservationSite.allowed, Solidity.Frontend.Admission.ObservationSite.status] <;> decide

/-- Builder shape: complete output closure from both routine proof inputs
(discharged by `closed_policies`). -/
abbrev ProgramBuilder : Prop := ConversionsPolicy → OptionalPolicy → WholeProgramPolicy

theorem program_from_containers : ProgramBuilder := by
  intro hc ho E P
  apply (Solidity.Frontend.Admission.accepted_program_iff P).mpr
  have body (b : Solidity.Source.RBody E) : ∀ site ∈ Solidity.Frontend.Admission.bodyObservations b, site.allowed = true := by
    have hi : (Solidity.Frontend.Admission.itemsObservations b.items).all Solidity.Frontend.Admission.ObservationSite.allowed = true :=
      Solidity.Frontend.Admission.TypedObservationPolicy.statement_from_containers hc ho (Solidity.Source.RStmt.block b.items)
    intro site hs
    rcases List.mem_append.mp hs with hs | hs
    · exact List.all_eq_true.mp hi site hs
    · obtain ⟨m, _, hm⟩ := List.mem_flatMap.mp hs
      exact List.all_eq_true.mp (hc m.args) site hm
  intro site hs
  rcases hs with ⟨d, _, hb | hcst⟩ | ⟨c, _, hb | hi | ha⟩
  · obtain ⟨b, _, hs⟩ := hb
    exact body b site hs
  · obtain ⟨i, _, hs⟩ := hcst
    exact List.all_eq_true.mp (Solidity.Frontend.Admission.TypedObservationPolicy.expression_allowed i.e) site hs
  · obtain ⟨b, _, hs⟩ := hb
    exact body b site hs
  · obtain ⟨i, _, hs⟩ := hi
    exact List.all_eq_true.mp (Solidity.Frontend.Admission.TypedObservationPolicy.expression_allowed i.e) site hs
  · obtain ⟨a, _, hs⟩ := ha
    exact List.all_eq_true.mp (hc a.args) site hs

/-- Unconditional statement and whole-Program observation-policy claims. -/
abbrev ClosedPolicies : Prop := StatementPolicy ∧ WholeProgramPolicy

theorem closed_policies : ClosedPolicies := by
  exact ⟨statement_from_containers conversions_allowed optional_allowed,
    program_from_containers conversions_allowed optional_allowed⟩

theorem statement_allowed : StatementPolicy := closed_policies.1
theorem program_allowed : WholeProgramPolicy := closed_policies.2

/-- info: 'Solidity.Frontend.Admission.TypedObservationPolicy.closed_policies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms closed_policies
/-- info: 'Solidity.Frontend.Admission.TypedObservationPolicy.statement_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms statement_allowed
/-- info: 'Solidity.Frontend.Admission.TypedObservationPolicy.program_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms program_allowed


/-- info: 'Solidity.Frontend.Admission.TypedObservationPolicy.statement_from_containers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms statement_from_containers
/-- info: 'Solidity.Frontend.Admission.TypedObservationPolicy.program_from_containers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms program_from_containers
end Solidity.Frontend.Admission.TypedObservationPolicy
