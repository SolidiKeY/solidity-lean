import Solidity.Tools.Inspect
import Solidity.Tools.ProofTree
import Solidity.Tools.Taclet
import Solidity.Tools.InspectToday

/-!
# The inspection commands, scoped and today's

What a file that inspects both calculi imports: `#wp`, `#step`
(`Tools/Inspect.lean`), `#proof_tree`, `#proof_node`, `#proof_tree_json`
(`Tools/ProofTree.lean`) on scoped formulas, `#taclet` (`Tools/Taclet.lean`),
and the same commands on today's formulas read without the switch
(`Tools/InspectToday.lean`).  W4 replaces it by its first two imports in the
files that import it.
-/
