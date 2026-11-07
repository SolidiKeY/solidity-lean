import Solidity.Examples.Tactics.Recovery
import tests.h62.item2.«audit-exact-verification».JointWitness

namespace Solidity.H62.ExactAudit.Recovery
open Solidity
open Solidity.Examples.Tactics.Recovery

-- Both original declarations are unconditional: the joint tuple is empty.
#joint_inputs generator_inputs for Solidity.Examples.Tactics.Recovery.recover_generator := []
#joint_inputs address_inputs for Solidity.Examples.Tactics.Recovery.recover_address := []
#print axioms generator_inputs
#print axioms address_inputs

/-- An invalid recovery parity is an observable failure. -/
theorem invalid_parity_rejected : Secp256k1.recoverPoint 0 29 rOne rOne = none := rfl

/-- A reject-all recovery function cannot meet the existing successful vector. -/
theorem reject_all_recovery_control :
    (none : Option Secp256k1.Point) ≠ some Secp256k1.generator := by
  intro h
  cases h

#print axioms invalid_parity_rejected
#print axioms reject_all_recovery_control
end Solidity.H62.ExactAudit.Recovery
