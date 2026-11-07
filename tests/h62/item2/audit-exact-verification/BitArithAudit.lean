import Solidity.Calculus.BitArith
import tests.h62.item2.«audit-exact-verification».JointWitness

namespace Solidity.H62.ExactAudit.BitArith

#joint_inputs and_split_inputs for Solidity.Decide.BitArith.and_split := [5, 3]
#print axioms and_split_inputs

#joint_inputs or_split_inputs for Solidity.Decide.BitArith.or_split := [5, 3]
#print axioms or_split_inputs

#joint_inputs xor_split_inputs for Solidity.Decide.BitArith.xor_split := [5, 3]
#print axioms xor_split_inputs

#joint_inputs and_add_or_inputs for Solidity.Decide.BitArith.and_add_or := [3, 5, 3, by decide]
#print axioms and_add_or_inputs

#joint_inputs and_or_eq_inputs for Solidity.Decide.BitArith.and_or_eq := [5, 3]
#print axioms and_or_eq_inputs

#joint_inputs xor_add_and_inputs for Solidity.Decide.BitArith.xor_add_and := [3, 5, 3, by decide]
#print axioms xor_add_and_inputs

#joint_inputs xor_and_eq_inputs for Solidity.Decide.BitArith.xor_and_eq := [5, 3]
#print axioms xor_and_eq_inputs

#joint_inputs mulMod_double_inputs for Solidity.Decide.BitArith.mulMod_double := [5, 3, 7]
#print axioms mulMod_double_inputs

#joint_inputs mulMod_succ_inputs for Solidity.Decide.BitArith.mulMod_succ := [5, 3, 7]
#print axioms mulMod_succ_inputs

#joint_inputs ediv_iff_inputs for Solidity.Decide.BitArith.ediv_iff := [3, by decide, -7, -3]
#print axioms ediv_iff_inputs

#joint_inputs tdiv_pos_iff_inputs for Solidity.Decide.BitArith.tdiv_pos_iff := [3, by decide, -7, -2]
#print axioms tdiv_pos_iff_inputs

#joint_inputs tdiv_iff_inputs for Solidity.Decide.BitArith.tdiv_iff := [-7, -3, 2, by decide]
#print axioms tdiv_iff_inputs

#joint_inputs tmod_bounds_inputs for Solidity.Decide.BitArith.tmod_bounds := [-7, 3]
#print axioms tmod_bounds_inputs

#joint_inputs tdiv_bounds_inputs for Solidity.Decide.BitArith.tdiv_bounds := [3, 2, 4, by decide, by decide, by decide, by decide]
#print axioms tdiv_bounds_inputs

#joint_inputs tdiv_neg_one_inputs for Solidity.Decide.BitArith.tdiv_neg_one := [-7]
#print axioms tdiv_neg_one_inputs

#joint_inputs tmod_neg_one_inputs for Solidity.Decide.BitArith.tmod_neg_one := [-7]
#print axioms tmod_neg_one_inputs

end Solidity.H62.ExactAudit.BitArith
