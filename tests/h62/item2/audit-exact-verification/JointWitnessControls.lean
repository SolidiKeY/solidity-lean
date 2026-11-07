import tests.h62.item2.«audit-exact-verification».JointWitness

namespace Solidity.H62.ExactAudit.JointControls
abbrev HiddenFalse := False → True
/-- Synthetic control, outside the frozen interface census. -/
theorem hidden_false : HiddenFalse := fun h => h.elim

/-- error: missing witness binder(s) for Solidity.H62.ExactAudit.JointControls.hidden_false: False → True -/
#guard_msgs in
#joint_inputs rejected_hidden_false for Solidity.H62.ExactAudit.JointControls.hidden_false := []

run_cmd do
  if (← Lean.getEnv).contains `Solidity.H62.ExactAudit.JointControls.rejected_hidden_false then
    throwError "rejected control leaked a witness declaration"

/-- A feasible dependent premise supplies an actual joint tuple. -/
theorem dependent (n : Nat) (h : n = 1) : n = 1 := h
#joint_inputs dependent_inputs for Solidity.H62.ExactAudit.JointControls.dependent := [1, rfl]
#print axioms dependent_inputs
end Solidity.H62.ExactAudit.JointControls
