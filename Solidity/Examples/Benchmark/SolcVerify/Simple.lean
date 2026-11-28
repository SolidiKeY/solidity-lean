import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Run

/-!
# solc-verify: a contract invariant

Source: <https://github.com/SRI-CSL/solidity/blob/8ea107cecd90ffff0d6a8f276b434b5ac9aa043b/test/solc-verify/specs/Simple.sol>.
Changes: the contract `@notice invariant` is `invariant`; `x = y = 0;`,
which `contract!{ … }` does not parse, is `y = 0; x = y;`.
-/

namespace Solidity.Examples.Benchmark.SolcVerify.Simple

/-- The source contract, with its clauses. -/
def Simple : Contract := contract!{
  invariant x == y;
  uint x;
  uint y;
  constructor() {
    y = 0;
    x = y;
  }
  function add(uint amount) public {
    x += amount;
    y += amount;
  }
  function add_incorrect(uint amount) public {
    x += amount;
    y -= amount;
  }
  function add_incorrect_2(uint amount) public {
    x += amount;
    add(amount);
    y += amount;
  }
}
local instance : InContract := ⟨Simple⟩
open scoped Scoped

/-- The constructor establishes `x == y`. Proved. -/
theorem constructor_spec : ⊢ spec!{ constructor } := by sol_prove
/-- `add` keeps `x == y`. Proved. -/
theorem add_spec : ⊢ spec!{ add } := by sol_prove
/-- `add_incorrect_2` keeps `x == y`. Proved: the call to `add` is inlined,
so no invariant is owed at it; solc-verify owes it when entering `add`, where
it fails. -/
theorem add_incorrect_2_spec : ⊢ spec!{ add_incorrect_2 } := by sol_prove
/- `add_incorrect(1)` from `x == y == 1`: refuted, `x == 2`, `y == 0`. -/
/--
info: ok
x = 2
y = 0
-/
#guard_msgs in #run Simple.add_incorrect(1) with x := 1, y := 1

end Solidity.Examples.Benchmark.SolcVerify.Simple
