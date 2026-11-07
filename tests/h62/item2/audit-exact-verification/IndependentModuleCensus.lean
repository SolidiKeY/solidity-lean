import Solidity.Calculus.BitArith
import Solidity.Calculus.LinearDecision
import Solidity.Calculus.LinearHypotheses
import Solidity.Calculus.LinearSyntax
import Solidity.Calculus.VisitedSet
import Solidity.Examples.Tactics.Recovery
import tests.h62.item2.«audit-exact-verification».JointWitness

-- No source theorem declarations occur in LinearSyntax. All compiler-generated
-- theorem declarations are still emitted and remain unclassified until audited.
#audit_module_theorems Solidity.Calculus.BitArith
#audit_module_theorems Solidity.Calculus.LinearDecision
#audit_module_theorems Solidity.Calculus.LinearHypotheses
#audit_module_theorems Solidity.Calculus.LinearSyntax
#audit_module_theorems Solidity.Calculus.VisitedSet
#audit_module_theorems Solidity.Examples.Tactics.Recovery
