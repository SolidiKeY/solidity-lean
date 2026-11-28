import Solidity.Semantics.Run
import Solidity.Syntax.Splice

/-!
# A `constant` and an `immutable` are assignable after deployment

Claim: the elaborator types assignments solc 0.8.38 rejects, and the run
changes the values.

* `K = 2;` with `uint constant K = 1;` — solc: "Cannot assign to a constant
  variable."
* `I = 7;` in an ordinary function, with `uint immutable I;` — solc:
  "Cannot write to immutable here: Immutable variables can only be
  initialized inline or assigned directly in the constructor."

Culprit: `Solidity/Syntax/Contract.lean:37` (a `constant` or an `immutable` is
a storage root whose initializer the constructor runs) with no write check in
the elaborator. `Language.Feature.immutables` is `limited`. Suggested fix:
record `constant`/`immutable` on the contract and refuse an assignment, a
compound assignment, `++`/`--` or `delete` of one outside the constructor (and
of a `constant` anywhere).
-/

namespace Solidity.Examples.RedTeam.Typing.ConstantWrite
open Solidity

def Konst : Contract := contract!{
  uint constant K = 1;
  uint immutable I;
  function wk() public { K = 2; }
  function wi() public { I = 7; }
}

/-- `K = 1; wk(); wi(); assert(K == 2); assert(I == 7);` — the first write
stands for the deployment's initializer, which `Storage.init` does not run. -/
def run := sol[Konst]{ K = 1; wk(); wi(); assert(K == 2); assert(I == 7); }

/-- The constant now holds `2`, the immutable `7`. -/
theorem run_ok : (Prog.run (State.ofStorage (Storage.init Konst)) run).halt? = none := by
  decide +kernel

end Solidity.Examples.RedTeam.Typing.ConstantWrite
