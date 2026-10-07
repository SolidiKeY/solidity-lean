import Solidity.Frontend.Import
import Solidity.Calculus.Close
import Solidity.Tools.Show

/-!
# Loops from solc's AST

solkey's loops, as its `TestSuite.sol` writes them past `ed7849d5b6`, in a
contract of their own (`tests/solc/Loops.sol`; the TestSuite fixture stays at
the pinned checkout).  solc drops the `/// @custom:key` lines above a loop;
`scripts/solc-ast.mjs` reads them from the source by the loop's `src`
offset, as solkey's `LoopSpecCompiler` does, and keeps them as the loop's
`loopSpec`, which the front end prints above the loop (`SolcJson.loopSpec`).
-/

solc_import "../../../tests/solc/Loops.ast.json" hash 0x5ad98bbdfad3e035 as Solc.Loops

namespace Solidity.Examples.LoopsImport

/-- info: 6 functions (4 diamond, 2 box, 0 skip): 6 elaborated, 0 skipped, 0 excluded, 0 unsupported -/
#guard_msgs in
#eval IO.println (Solidity.Frontend.ImportRow.summary Solc.Loops.report)

/-- info: require(n >= 0);
uint i = 0;
/// @custom:key invariant i <= n while (i < n) { i = i + 1; }
assert(i == n); -/
#guard_msgs in
#eval IO.println (Prog.show Solc.Loops.invariantCountsToBound)

/-- solkey's `invariantCountsToBound`, its `box` obligation: the loop's
invariant proves the `assert` after it. -/
theorem invariantCountsToBound :
    Valid (Fml.modal .box Solc.Loops.invariantCountsToBound .tt) := by
  unfold Solc.Loops.invariantCountsToBound
  sol_symex
  sol_close

/-- `invariantBreak`: the invariant holds at the head the `break` leaves
from too. -/
theorem invariantBreak : Valid (Fml.modal .box Solc.Loops.invariantBreak .tt) := by
  unfold Solc.Loops.invariantBreak
  sol_symex
  sol_close

/-- `whileCountsUp`, under the diamond, unwound three times (`unwind 3`, a
clause only Lean reads). -/
theorem whileCountsUp : Valid (Fml.modal .diamond Solc.Loops.whileCountsUp .tt) := by
  unfold Solc.Loops.whileCountsUp
  sol_symex
  sol_close

end Solidity.Examples.LoopsImport
