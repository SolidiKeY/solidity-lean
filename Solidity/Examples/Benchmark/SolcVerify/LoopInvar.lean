import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Run

/-!
# solc-verify: loop invariants

Source: <https://github.com/SRI-CSL/solidity/blob/8ea107cecd90ffff0d6a8f276b434b5ac9aa043b/test/solc-verify/specs/LoopInvar.sol> (contract `LoopInvar`).
Changes: `@notice invariant` is `@custom:key invariant`. The natural
specification of these `pure` functions is that no `assert` fails: the
obligation `[ f(); ] true` (a panic fails a box). solc-verify proves
`correct` and `forLoop` and flags the other three.
-/

namespace Solidity.Examples.Benchmark.SolcVerify.LoopInvar

/-- The source contract, with its clauses. -/
def LoopInvar : Contract := contract!{
  function correct() public pure {
    int i = 0;
    int x = 0;
    /// @custom:key invariant i == x
    while (i < 10) {
      i++;
      x++;
    }
    assert(x == i);
  }
  function cannotProveWithoutInvariant() public pure {
    int i = 0;
    int x = 0;
    while (i < 10) {
      i++;
      x++;
    }
    assert(x == i);
  }
  function doesNotHoldOnEntry() public pure {
    int i = 0;
    {
      int x = 1;
      /// @custom:key invariant i == x
      while (i < 10) {
        i++;
        x++;
      }
      assert(x == i);
    }
  }
  function isNotMaintainedByLoop() public pure {
    int i = 0;
    int x = 0;
    /// @custom:key invariant i == x
    while (i < 10) {
      i++;
    }
    assert(x == i);
  }
  function forLoop() public pure {
    int x = 0;
    /// @custom:key invariant i == x
    for (int i = 0; i < 10; i++) {
      x++;
    }
    assert(x <= 10);
  }
}
local instance : InContract := ⟨LoopInvar⟩
open scoped Scoped

/-- `correct`: the invariant `i == x` gives `x == i` at exit. Proved. -/
theorem correct_spec : ⊢ spec!{ correct } := by
  sol_derive
  all_goals
    sol_leaf
    sol_spec
/-- `cannotProveWithoutInvariant`: proved here (solc-verify cannot, lacking
an invariant): the loop's bound is concrete and the strategy unwinds it. -/
theorem cannotProveWithoutInvariant_spec : ⊢ spec!{ cannotProveWithoutInvariant } := by
  sol_prove
/- `doesNotHoldOnEntry`: refuted, the loop ends with `x == 11`, `i == 10`. -/
/--
info: panic (an `assert` failed)
-/
#guard_msgs in #run LoopInvar.doesNotHoldOnEntry()
/- `isNotMaintainedByLoop`: refuted, the loop ends with `x == 0`, `i == 10`. -/
/--
info: panic (an `assert` failed)
-/
#guard_msgs in #run LoopInvar.isNotMaintainedByLoop()
/- `forLoop`: unknown. The run is `ok`; the annotated invariant `i == x`
leaves the exit leaf `x == i, !(i < 10) ⟹ x <= 10`, false without `i <= 10`,
which solc-verify's Boogie infers. Missing: loop-invariant inference (an
interval bound) beside the invariant rule. -/
/--
info: ok
-/
#guard_msgs in #run LoopInvar.forLoop()
/-- `forLoop`'s obligation, unknown. -/
def forLoop_target := spec!{ forLoop }

end Solidity.Examples.Benchmark.SolcVerify.LoopInvar
