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
Verdicts: `current`, `increment`, `decrement`, `reset`: proved.  The
unchecked `+= 1` and `value - 1` leave a wrapping `+%`/`-%` in their leaf,
which `sol_prove` alone does not close; its leaf closer (`sol_leaf`,
`sol_close`, found by `sol_prove?`) does, from the `requires` and the
`require(value > 0)`.
-/
namespace Solidity.Examples.Benchmark.SolkeyOz.OZCounters
/-- `OZCounters.sol` with solkey's clauses. -/
def OZCounters : Contract := contract!{
  struct Counter { uint256 _value; }
  invariant _counter._value >= 0;
  Counter private _counter;
  ensures c == _counter._value && _counter._value == \old(_counter._value);
  function current() public view returns (uint256 c) { return _counter._value; }
  requires _counter._value < 115792089237316195423570985008687907853269984665640564039457584007913129639935;
  ensures _counter._value == \old(_counter._value) + 1;
  function increment() public { unchecked { _counter._value += 1; }; }
  ensures \old(_counter._value) > 0 && _counter._value == \old(_counter._value) - 1;
  function decrement() public {
    uint256 value = _counter._value;
    require(value > 0);
    unchecked { _counter._value = value - 1; };
  }
  ensures _counter._value == 0;
  function reset() public { _counter._value = 0; }
}
local instance : InContract := ⟨OZCounters⟩
open scoped Scoped
/-- `ensures c == _counter._value && _counter._value == \old(_counter._value)`. -/
theorem spec_current : ⊢ spec!{ current } := by sol_prove
/-- `requires _counter._value < 2^256 - 1`,
`ensures _counter._value == \old(_counter._value) + 1`. -/
theorem spec_increment : ⊢ spec!{ increment } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close
/-- `ensures \old(_counter._value) > 0 && _counter._value == \old(_counter._value) - 1`. -/
theorem spec_decrement : ⊢ spec!{ decrement } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close
/-- `ensures _counter._value == 0`. -/
theorem spec_reset : ⊢ spec!{ reset } := by sol_prove
end Solidity.Examples.Benchmark.SolkeyOz.OZCounters
