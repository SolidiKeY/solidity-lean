import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Run

/-!
# solc-verify: `do … while` invariants

Source: <https://github.com/SRI-CSL/solidity/blob/8ea107cecd90ffff0d6a8f276b434b5ac9aa043b/test/solc-verify/specs/DoWhile.sol> (contract `C`, named `DoWhile` here).
Changes: `@notice invariant` is `@custom:key invariant`. The natural
specification is that no `assert` fails (`[ f(); ] true`). solc-verify
proves `f1` and flags the invariants of `f2`–`f4`.

All four are unknown. Each run is `ok` (`f2`–`f4` have no `assert`, so their
boxes hold), but the invariant rule takes the annotated invariant, and it
is not inductive in `f2` (entry: `x == 1`, `i == 0`), `f3` (`x` lags `i`) and
`f4` (`x = 1`), solc-verify's errors. In `f1` the exit leaf
`x == i, !(i < 10) ⟹ x == 10` needs `i <= 10` (Boogie infers it), and the
step leaf `{i := i + 1}{x := i} ⟹ x == i` stays open: its loop guard prints
as an escape `‹Tm.app2 (Op2.binop BinOp.lt …)›`. Missing: interval inference
for the invariant rule, and the closer for the `do`-loop's `first` flag.
-/

namespace Solidity.Examples.Benchmark.SolcVerify.DoWhile

/-- The source contract, with its clauses. -/
def DoWhile : Contract := contract!{
  function f1() public pure {
    uint i = 0;
    uint x = 0;
    /// @custom:key invariant x == i
    do {
      i++;
      x = i;
    } while(i < 10);
    assert(x == 10);
  }
  function f2() public pure {
    uint i = 0;
    uint x = 1;
    /// @custom:key invariant x == i
    do {
      i++;
      x = i;
    } while(i < 10);
  }
  function f3() public pure {
    uint i = 0;
    uint x = 0;
    /// @custom:key invariant x == i
    do {
      x = i;
      i++;
    } while(i < 10);
  }
  function f4() public pure {
    uint i = 0;
    uint x = 0;
    /// @custom:key invariant x == i
    do {
      i++;
      x = 1;
    } while(i < 10);
  }
}
local instance : InContract := ⟨DoWhile⟩
open scoped Scoped

/--
info: ok
-/
#guard_msgs in #run DoWhile.f1()
/--
info: ok
-/
#guard_msgs in #run DoWhile.f4()
/-- `f1`'s obligation, unknown. -/
def f1_target := spec!{ f1 }

end Solidity.Examples.Benchmark.SolcVerify.DoWhile
