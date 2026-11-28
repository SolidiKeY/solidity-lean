import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Run

/-!
# solc-verify: overflow in a specification

Source: <https://github.com/SRI-CSL/solidity/blob/8ea107cecd90ffff0d6a8f276b434b5ac9aa043b/test/solc-verify/overflow/OverflowSpec.sol> (run with `--arithmetic mod-overflow`).
Changes: the contract `@notice invariant` is `invariant`. Arithmetic is
checked (0.8), where solc-verify's flag wraps and reports overflow. The
implicit constructor has no obligation.
-/

namespace Solidity.Examples.Benchmark.SolcVerify.OverflowSpec

/-- The source contract, with its clauses. -/
def Overflow : Contract := contract!{
  invariant x == y + 1;
  uint8 x = 1;
  uint8 y = 0;
  function inc() public {
    x++;
    y++;
  }
  function set() public {
    x = 0;
    y = 255;
  }
}
local instance : InContract := ⟨Overflow⟩
open scoped Scoped

/-- `inc` keeps `x == y + 1`: an `x++` past `255` reverts. Proved (solc-verify
flags the overflow, which reverts here). -/
theorem inc_spec : ⊢ spec!{ inc } := by sol_prove
/- `set()`: refuted, `x == 0`, `y == 255`, and `y + 1` overflows `uint8`: the
clause's equation is false (and `0 != 256` unbounded). -/
/--
info: ok
x = 0
y = 255
-/
#guard_msgs in #run Overflow.set()

end Solidity.Examples.Benchmark.SolcVerify.OverflowSpec
