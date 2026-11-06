import Solidity.Examples.Tactics.JoinWalk
import tests.h62.item2.«audit-calculus».DagJoint

/-! These eleven original declarations have no leading input telescope.
Their quantified validity/negation is the CONCLUSION, which is not reduced
into inputs. One shared True proof accounts for all empty joint telescopes;
these are closed-declaration checks, not eleven new input-bearing witnesses
or compiler totality claims. -/
namespace H62.AuditCalculus.JoinWalk
theorem closed_input : True := True.intro

#verify_joint_dag Solidity.Examples.Tactics.JoinWalk.rootW2 with closed_input
#verify_joint_dag Solidity.Examples.Tactics.JoinWalk.rootW4 with closed_input
#verify_joint_dag Solidity.Examples.Tactics.JoinWalk.rootW8 with closed_input
#verify_joint_dag Solidity.Examples.Tactics.JoinWalk.rootS2 with closed_input
#verify_joint_dag Solidity.Examples.Tactics.JoinWalk.rootS3 with closed_input
#verify_joint_dag Solidity.Examples.Tactics.JoinWalk.rootC7 with closed_input
#verify_joint_dag Solidity.Examples.Tactics.JoinWalk.rootC12 with closed_input
#verify_joint_dag Solidity.Examples.Tactics.JoinWalk.overflowCountermodel with closed_input
#verify_joint_dag Solidity.Examples.Tactics.JoinWalk.divisionCountermodel with closed_input
#verify_joint_dag Solidity.Examples.Tactics.JoinWalk.correlationCountermodel with closed_input
#verify_joint_dag Solidity.Examples.Tactics.JoinWalk.untakenDivision with closed_input


end H62.AuditCalculus.JoinWalk
