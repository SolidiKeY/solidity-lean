import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `Enum` (solkey real-world)

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/contracts/real-world/Enum.sol>
(after Solidity by Example's `enum/Enum.sol`, revision `5bcdca02`).

Changes: none but the spelling of `contract!{ … }` (solkey already drops
the comments and names `get`'s result `s`).  An enum member is its
position, a `uint` (`Examples/Benchmark/Syntax.lean`).  Verdicts: every
function proved (`spec_get`, `spec_set`, `spec_cancel`, `spec_reset`).

```solidity
contract Enum {
    enum Status { Pending, Shipped, Accepted, Rejected, Canceled }
    Status public status;

    /// @custom:key ensures \result == status && status == \old(status)
    function get() public view returns (Status s) { return status; }

    /// @custom:key ensures status == _status
    function set(Status _status) public { status = _status; }

    /// @custom:key ensures status == Status.Canceled
    function cancel() public { status = Status.Canceled; }

    /// @custom:key ensures status == Status.Pending
    function reset() public { delete status; }
}
```
-/

namespace Solidity.Examples.Benchmark.SolkeyData.Enum

/-- `Enum.sol`, as solkey publishes it, with its clauses. -/
def Enum : Contract := contract!{
  enum Status { Pending, Shipped, Accepted, Rejected, Canceled }
  Status public status;
  ensures \result == status && status == \old(status);
  function get() public view returns (Status s) {
    return status;
  }
  ensures status == _status;
  function set(Status _status) public {
    status = _status;
  }
  ensures status == Status.Canceled;
  function cancel() public {
    status = Status.Canceled;
  }
  ensures status == Status.Pending;
  function reset() public {
    delete status;
  }
}

local instance : InContract := ⟨Enum⟩

open scoped Scoped

/-- `get()`: `ensures \result == status && status == \old(status)`. -/
theorem spec_get : ⊢ spec!{ get } := by
  sol_prove
/-- `set(_status)`: `ensures status == _status`. -/
theorem spec_set : ⊢ spec!{ set } := by
  sol_prove
/-- `cancel()`: `ensures status == Status.Canceled`. -/
theorem spec_cancel : ⊢ spec!{ cancel } := by
  sol_prove
/-- `reset()`: `ensures status == Status.Pending`. -/
theorem spec_reset : ⊢ spec!{ reset } := by
  sol_prove

end Solidity.Examples.Benchmark.SolkeyData.Enum
