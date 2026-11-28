import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `OZCounters`

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/contracts/real-world/OZCounters.sol>
(solkey's port of OpenZeppelin v4.9.0 `utils/Counters.sol`, the library
inlined into a contract holding one `Counter`).

Changes: only the spelling of `contract!{ … }` and solkey's `@custom:key`
clauses written above the functions they annotate.

Verdicts: `current`, `reset`: proved.  `increment`, `decrement`: unknown.
Both clauses are true (the `requires` keeps `+= 1` below `2^256 - 1`, the
`require(value > 0)` keeps `value - 1` at or above zero), but the leaf keeps
the wrapping operation (`se2 +% 1`, `se1 -% 1`) and the closer has no law
rewriting a wrapping `+%`/`-%` to the exact one under a range premise; the
obligations are kept below as `def`s.
-/

namespace Solidity.Examples.Benchmark.SolkeyOz.OZCounters

/-- `OZCounters.sol` with solkey's clauses. -/
def OZCounters : Contract := contract!{
  struct Counter {
    uint256 _value;
  }
  invariant _counter._value >= 0;
  Counter private _counter;
  ensures c == _counter._value && _counter._value == \old(_counter._value);
  function current() public view returns (uint256 c) {
    return _counter._value;
  }
  requires _counter._value < 115792089237316195423570985008687907853269984665640564039457584007913129639935;
  ensures _counter._value == \old(_counter._value) + 1;
  function increment() public {
    unchecked {
      _counter._value += 1;
    };
  }
  ensures \old(_counter._value) > 0 && _counter._value == \old(_counter._value) - 1;
  function decrement() public {
    uint256 value = _counter._value;
    require(value > 0);
    unchecked {
      _counter._value = value - 1;
    };
  }
  ensures _counter._value == 0;
  function reset() public {
    _counter._value = 0;
  }
}

local instance : InContract := ⟨OZCounters⟩

open scoped Scoped

/-- `ensures c == _counter._value && _counter._value == \old(_counter._value)`. -/
theorem spec_current : ⊢ spec!{ current } := by
  sol_prove

/-- UNKNOWN: `ensures _counter._value == \old(_counter._value) + 1`; the leaf
keeps `se2 +% 1` under `_counter._value < 2^256 - 1` (no wrapping-add closer). -/
def increment_obligation := spec!{ increment }

/-- UNKNOWN: `ensures \old(_counter._value) > 0 && _counter._value ==
\old(_counter._value) - 1`; the leaf keeps `se1 -% 1` under `se1 > 0` (no
wrapping-sub closer). -/
def decrement_obligation := spec!{ decrement }

/-- `ensures _counter._value == 0`. -/
theorem spec_reset : ⊢ spec!{ reset } := by
  sol_prove

end Solidity.Examples.Benchmark.SolkeyOz.OZCounters
