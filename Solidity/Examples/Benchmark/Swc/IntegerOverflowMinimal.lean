import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Run

/-!
# SWC-101: `IntegerOverflowMinimal` (vulnerable)

Source: SWC registry, `integer_overflow_minimal.sol`, pinned revision:
<https://github.com/SmartContractSecurity/SWC-registry/blob/1b6227074ecd180b374e4844153afdda0332f979/entries/docs/SWC-101.md#integer_overflow_minimalsol>.

Changes: the source is `pragma solidity ^0.4.19`, whose `-=` wraps; the
same wrapping is spelled `unchecked { … }` here.  The initializer
`count = 1` is not part of the per-function obligation (it would only fix the
initial store) and is dropped.  The natural clause: `run` debits `input`.

```solidity
contract IntegerOverflowMinimal {
    uint public count = 1;
    function run(uint256 input) public {
        count -= input;
    }
}
```

Verdict: `run` refuted (a kernel-checked run below, from the initial
`count = 1`, wraps to `2^256 - 1`).  The fixed variant is
`Swc/IntegerOverflowMinimalFixed.lean`.
-/

namespace Solidity.Examples.Benchmark.Swc.IntegerOverflowMinimal

/-- `integer_overflow_minimal.sol`, the 0.4 wrapping `-=` as `unchecked`. -/
def IntegerOverflowMinimal : Contract := contract!{
  uint public count;
  ensures count == \old(count) - input;
  function run(uint256 input) public {
    unchecked { count -= input; };
  }
}

local instance : InContract := ⟨IntegerOverflowMinimal⟩
open scoped Scoped

/-- `run`: `ensures count == \old(count) - input`, refuted below. -/
def run_obligation : Fml IntegerOverflowMinimal [] := spec!{ run }

/-- The source's initial store, `count = 1`. -/
private def initialStore : Storage IntegerOverflowMinimal :=
  .cons (.prim (uintOfNat 1)) .nil

/-- Refuted: from `count = 1`, `run(2)` returns with `count = 2^256 - 1`,
not `1 - 2 = -1`. -/
example :
    ((Prog.run (State.ofStorage initialStore)
      (sol{ run(2); uint c = count; })).toOption.map
        fun o => o.st.env.1.1) = some (2 ^ 256 - 1) := by
  decide +kernel

end Solidity.Examples.Benchmark.Swc.IntegerOverflowMinimal
