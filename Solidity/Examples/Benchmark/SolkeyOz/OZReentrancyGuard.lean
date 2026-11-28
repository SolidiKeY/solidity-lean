import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Benchmark: `OZReentrancyGuard`
Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/contracts/real-world/OZReentrancyGuard.sol>
(solkey's flattening of OpenZeppelin v5.0.0 `utils/ReentrancyGuard.sol` and
`mocks/ReentrancyMock.sol`).
Changes: only the spelling of `contract!{ … }` (a branch is a block ending
in `;`) and solkey's `@custom:key` clauses: the two contract invariants
first, each function's clauses above it.  `_count` is declared before its
callers, since a function calls only the functions declared before it.  The
modifier is inlined (`Examples/Benchmark/Syntax.lean`).
Verdicts: `constructor`, `callback`, `countLocalRecursive`,
`guardedCheckEntered`, `unguardedCheckNotEntered`: proved.  The invariants
join every obligation (premise and conclusion).  In `countLocalRecursive`
the recursive call re-enters `nonReentrant` with `_status == ENTERED` and
reverts, so only `n == 0` runs return; that leaf needs `n >= 0, !(n > 0) ⟹
n == 0`, which `sol_prove` leaves and `sol_auto`'s leaf search closes (the
single-declaration replay `sol_prove?` suggests is past `maxHeartbeats`).
-/
namespace Solidity.Examples.Benchmark.SolkeyOz.OZReentrancyGuard
/-- `OZReentrancyGuard.sol` with solkey's clauses. -/
def OZReentrancyGuard : Contract := contract!{
  invariant NOT_ENTERED == 1 && ENTERED == 2;
  invariant _status == 1 && counter >= 0;
  uint256 private constant NOT_ENTERED = 1;
  uint256 private constant ENTERED = 2;
  uint256 private _status;
  uint256 public counter;
  constructor() { _status = NOT_ENTERED; counter = 0; }
  modifier nonReentrant() {
    if (_status == ENTERED) { revert(); };
    _status = ENTERED;
    _;
    _status = NOT_ENTERED;
  }
  function _reentrancyGuardEntered() internal view returns (bool) { return _status == ENTERED; }
  function _count() private { counter += 1; }
  ensures counter == \old(counter) + 1;
  function callback() external nonReentrant { _count(); }
  requires n >= 0;
  ensures n == 0 && counter == \old(counter);
  function countLocalRecursive(uint256 n) public nonReentrant {
    if (n > 0) {
      _count();
      countLocalRecursive(n - 1);
    };
  }
  ensures counter == \old(counter);
  function guardedCheckEntered() public nonReentrant { require(_reentrancyGuardEntered()); }
  ensures counter == \old(counter);
  function unguardedCheckNotEntered() public view { require(!_reentrancyGuardEntered()); }
}
local instance : InContract := ⟨OZReentrancyGuard⟩
open scoped Scoped
/-- the invariants `NOT_ENTERED == 1 && ENTERED == 2`, `_status == 1 && counter >= 0` after deployment. -/
theorem spec_constructor : ⊢ spec!{ constructor } := by sol_prove
/-- `ensures counter == \old(counter) + 1`. -/
theorem spec_callback : ⊢ spec!{ callback } := by sol_prove
/-- `requires n >= 0`, `ensures n == 0 && counter == \old(counter)`. -/
theorem spec_countLocalRecursive : ⊢ spec!{ countLocalRecursive } := by sol_auto
/-- `ensures counter == \old(counter)`. -/
theorem spec_guardedCheckEntered : ⊢ spec!{ guardedCheckEntered } := by sol_prove
/-- `ensures counter == \old(counter)`. -/
theorem spec_unguardedCheckNotEntered : ⊢ spec!{ unguardedCheckNotEntered } := by sol_prove
end Solidity.Examples.Benchmark.SolkeyOz.OZReentrancyGuard
