import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand

namespace Solidity.Backend.Scalar.H62Audit.CommandChecks
private theorem dependentFixture (n : Nat) (h : n = 7) : n = 7 := h
private theorem unusedFixture (_n : Nat) : True := True.intro
private theorem boundedFixture (n : Nat) (h : n < 8) : n < 8 := h
private theorem negativeFixture : ¬ False := fun h => h
private def HiddenPremise : Prop := ∀ n : Nat, n = 0 → True
private theorem hiddenFixture : HiddenPremise := fun _ _ => True.intro

example : jointType% dependentFixture := jointProof% dependentFixture [7, rfl]
example : jointType% unusedFixture := jointProof% unusedFixture [19]
example : jointType% negativeFixture := jointProof% negativeFixture []

/-- Different inputs cannot be used to prove different premises of one witness. -/
example : True := by
  fail_if_success have _ : jointType% dependentFixture := jointProof% dependentFixture [8, rfl]
  exact True.intro

/-- Unused frozen binders still require an argument. -/
example : True := by
  fail_if_success have _ : jointType% unusedFixture := jointProof% unusedFixture []
  exact True.intro

/-- An infeasible chosen input cannot be manufactured by this helper. -/
example : True := by
  fail_if_success have _ : jointType% boundedFixture := jointProof% boundedFixture [8, by decide]
  exact True.intro

/-- A custom alias hiding hypotheses is rejected, never awarded coverage. -/
example : True := by
  fail_if_success have _ : jointType% hiddenFixture := by intro n h; exact True.intro
  exact True.intro
end Solidity.Backend.Scalar.H62Audit.CommandChecks
