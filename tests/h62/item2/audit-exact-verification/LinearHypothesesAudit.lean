import Solidity.Calculus.LinearHypotheses
import tests.h62.item2.«audit-exact-verification».JointWitness

namespace Solidity.H62.ExactAudit.LinearHypotheses
open Solidity.Linear

#joint_inputs hypotheses_hold_inputs for Solidity.Linear.AFml.hypotheses_hold := [(fun _ => 1), AFml.and .tt .tt, And.intro True.intro True.intro, AFml.tt, by decide]
#print axioms hypotheses_hold_inputs

/-- An implication from a nonempty conjunction produces a real certificate. -/
theorem supported_projection_succeeds :
    (AFml.hypVerify? (.imp (.and .tt .tt) .tt)).isSome = true := rfl

/-- Rejecting every formula would violate that same observable success. -/
theorem reject_all_projection_control :
    (none : Option (PLift (AFml.Valid (.imp (.and .tt .tt) .tt)))).isSome ≠ true := by decide

/-- The bounded fast path distinguishes exhaustion from a negative verdict. -/
theorem zero_fuel_has_no_certificate : (AFml.hypProof? 0 [] .tt).isNone = true := rfl

#print axioms supported_projection_succeeds
#print axioms reject_all_projection_control
#print axioms zero_fuel_has_no_certificate
end Solidity.H62.ExactAudit.LinearHypotheses
