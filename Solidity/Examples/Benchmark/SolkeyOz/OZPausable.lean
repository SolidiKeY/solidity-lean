import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `OZPausable`

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/contracts/real-world/OZPausable.sol>
(solkey's flattening of OpenZeppelin v5.0.0 `utils/Pausable.sol` and
`mocks/PausableMock.sol`).  Not the v4.9.6 `Governance/Pausable.lean`: this
one is the mock, with `normalProcess`, `drasticMeasure` and a counter.

Changes: only the spelling of `contract!{ … }` (a branch is a block ending
in `;`) and solkey's `@custom:key` clauses written above the functions they
annotate.  The modifiers are inlined (`Examples/Benchmark/Syntax.lean`).

Verdicts: see the theorems.
-/

namespace Solidity.Examples.Benchmark.SolkeyOz.OZPausable

/-- `OZPausable.sol` with solkey's clauses. -/
def OZPausable : Contract := contract!{
  bool private _paused;
  bool public drasticMeasureTaken;
  uint256 public count;
  ensures _paused == false && drasticMeasureTaken == false && count == 0;
  constructor() {
    _paused = false;
    drasticMeasureTaken = false;
    count = 0;
  }
  modifier whenNotPaused() {
    if (_paused) {
      revert();
    };
    _;
  }
  modifier whenPaused() {
    if (!_paused) {
      revert();
    };
    _;
  }
  ensures p == _paused;
  function paused() public view virtual returns (bool p) {
    return _paused;
  }
  function _requireNotPaused() internal view virtual {
    if (paused()) {
      revert();
    };
  }
  function _requirePaused() internal view virtual {
    if (!paused()) {
      revert();
    };
  }
  function _pause() internal virtual whenNotPaused {
    _paused = true;
  }
  function _unpause() internal virtual whenPaused {
    _paused = false;
  }
  ensures \old(_paused) == false && count == \old(count) + 1 && _paused == false;
  function normalProcess() external whenNotPaused {
    count++;
  }
  ensures \old(_paused) == true && drasticMeasureTaken == true && _paused == true;
  function drasticMeasure() external whenPaused {
    drasticMeasureTaken = true;
  }
  ensures \old(_paused) == false && _paused == true;
  function pause() external {
    _pause();
  }
  ensures \old(_paused) == true && _paused == false;
  function unpause() external {
    _unpause();
  }
}

local instance : InContract := ⟨OZPausable⟩

open scoped Scoped

/-- `ensures _paused == false && drasticMeasureTaken == false && count == 0`. -/
theorem spec_constructor : ⊢ spec!{ constructor } := by
  sol_prove

/-- `ensures p == _paused`. -/
theorem spec_paused : ⊢ spec!{ paused } := by
  sol_prove

/-- `ensures \old(_paused) == false && count == \old(count) + 1 && _paused == false`. -/
theorem spec_normalProcess : ⊢ spec!{ normalProcess } := by
  sol_prove

/-- `ensures \old(_paused) == true && drasticMeasureTaken == true && _paused == true`. -/
theorem spec_drasticMeasure : ⊢ spec!{ drasticMeasure } := by
  sol_prove

/-- `ensures \old(_paused) == false && _paused == true`. -/
theorem spec_pause : ⊢ spec!{ pause } := by
  sol_prove

/-- `ensures \old(_paused) == true && _paused == false`. -/
theorem spec_unpause : ⊢ spec!{ unpause } := by
  sol_prove

end Solidity.Examples.Benchmark.SolkeyOz.OZPausable
