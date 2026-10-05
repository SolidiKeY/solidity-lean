import Solidity.Calculus.Derive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.Spec

/-!
# Benchmark: `Counter`

Source: <https://raw.githubusercontent.com/Cyfrin/solidity-by-example.github.io/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/first-app/Counter.sol>
(solkey's `keyext.solidity.examples/benchmark/Counter.sol`).

Changes: none but the spelling of `contract!{ … }` (the comments are Lean's)
and solkey's `@custom:key` clauses, written above the functions as its file
has them.  The functions are internal functions here, and a call inlines one
(`Examples/Tactics/Calls.lean`).

The clauses are proved twice.  `spec!{f}` is the obligation solkey's
`SolidityProblemSynthesizer` builds from them (`Calculus/Spec.lean`), derived
as `⊢` (`spec_inc`, `spec_dec`): the snapshot `{ old := storage }` joins the
context (`Proves.updIntro`), the program runs, and each leaf closes by
the closer (`LFml.close`), all in one kernel evaluation (`sol_prove`,
`Calculus/Derive.lean`).  Before it, the same clauses by hand, also by
`sol_prove`, the premise `c == count` rewriting `count` to `c` (KeY's
`applyEq`): `ensures count == \old(count) + 1` with a parameter `c` for
the old value, and no `requires count >= 1`, which the box does not need (a `dec()` that
underflows reverts, and a reverted run satisfies every box formula).

```solidity
contract Counter {
    uint256 public count;

    // Function to get the current count
    function get() public view returns (uint256) {
        return count;
    }

    // Function to increment count by 1
    function inc() public {
        count += 1;
    }

    // Function to decrement count by 1
    function dec() public {
        // This function will fail if count = 0
        count -= 1;
    }
}
```
-/

namespace Solidity.Examples.Benchmark.Counter

open Proves

/-- `Counter.sol`, as published, with solkey's clauses. -/
def Counter : Contract := contract!{
  uint256 public count;
  function get() public view returns (uint256) {
    return count;
  }
  ensures count == \old(count) + 1;
  function inc() public {
    count += 1;
  }
  requires count >= 1;
  ensures count == \old(count) - 1;
  function dec() public {
    count -= 1;
  }
}

local instance : InContract := ⟨Counter⟩

/-- `inc()`: `ensures count == \old(count) + 1`. -/
theorem inc_spec : ⊢ dl!{ c == count → [ inc(); ] count == c + 1 } := by
  sol_prove

/-- `dec()`: `ensures count == \old(count) - 1` (when it does not revert). -/
theorem dec_spec : ⊢ dl!{ c == count → [ dec(); ] count == c - 1 } := by
  sol_prove

/-- `get()` returns `count`. -/
theorem get_spec : ⊢ dl!{ [ uint y = get(); ] y == count } := by
  sol_prove

/-! ## The clauses as obligations

`dec()`'s obligation, as solkey's synthesizer states it: the layout,
`msg.value == 0` (`dec` is not `payable`), the `requires`, the snapshot
`old := storage`, the call, the `ensures` read against both storages. -/

/--
info: dl{
  ((0 <= select(storage, count) ∧
            select(storage, count) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) ∧
        msg.value = 0 ∧ select(storage, count) >= 1) →
    { old := storage } [ dec(); ] select(storage, count) = select(old, count) - 1 } : Fml Counter
-/
#guard_msgs in #check spec!{ dec }

/-- `inc()`: `ensures count == \old(count) + 1`. -/
theorem spec_inc : ⊢ spec!{ inc } := by
  sol_prove
/-- `dec()`: `requires count >= 1`, `ensures count == \old(count) - 1`. -/
theorem spec_dec : ⊢ spec!{ dec } := by
  sol_prove

end Solidity.Examples.Benchmark.Counter
