import Solidity.Calculus.Closers
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface

/-!
# solkey open problems: `SolcControlFlow`

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/semantics/open/SolcControlFlow.sol>.
Changes: none (comments dropped).  A function solkey tags `@custom:key box` or specifies has the obligation `spec!{f}`; an untagged
one solkey's diamond, `msg.value == 0 → wt(storage) → ⟨ f(); ⟩ true`.
-/

namespace Solidity.Examples.SolkeyOpen.SolcControlFlow

def SolcControlFlow : Contract := contract!{
  function conditionalTuple(bool cond) internal pure returns (uint, uint) { return cond ? (1, 2) : (3, 4); }
  function conditionalExpressionTuples(uint p) public pure {
    require(p <= 1);
    (uint u, uint v) = conditionalTuple(p == 1);
    if (p == 1) { assert(u == 1 && v == 2); } else { assert(u == 3 && v == 4); }
  }
}

local instance : InContract := ⟨SolcControlFlow⟩
open scoped Scoped

-- Unknown: the front end refuses the `return` of a conditional whose branches are tuples, as solkey
-- does ("refused as a return of 1 value from a function with 2 return values").
/-- error: Solidity elaboration failed: `return` of one value from a function that returns 2 -/
#guard_msgs in #check spec!{ conditionalExpressionTuples }

end Solidity.Examples.SolkeyOpen.SolcControlFlow
