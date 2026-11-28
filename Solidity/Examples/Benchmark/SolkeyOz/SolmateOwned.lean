import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `SolmateOwned`

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/contracts/real-world/SolmateOwned.sol>
(solkey's port of <https://github.com/transmissions11/solmate/blob/v7/src/auth/Owned.sol>).

Changes: the modifier's `virtual` is dropped (`contract!{ … }` reads no
attribute on a modifier); otherwise only the spelling of `contract!{ … }` and solkey's
`@custom:key` clauses written above the functions they annotate; the
modifier is inlined (`Examples/Benchmark/Syntax.lean`).

Verdicts: `constructor`, `setOwner`: proved.
-/

namespace Solidity.Examples.Benchmark.SolkeyOz.SolmateOwned

/-- `SolmateOwned.sol` with solkey's clauses. -/
def SolmateOwned : Contract := contract!{
  address public owner;
  modifier onlyOwner() {
    require(msg.sender == owner);
    _;
  }
  ensures owner == _owner;
  constructor(address _owner) {
    owner = _owner;
  }
  ensures \old(owner) == msg.sender && owner == newOwner;
  function setOwner(address newOwner) public onlyOwner {
    owner = newOwner;
  }
}

local instance : InContract := ⟨SolmateOwned⟩

open scoped Scoped

/-- `ensures owner == _owner`. -/
theorem spec_constructor : ⊢ spec!{ constructor } := by
  sol_prove

/-- `ensures \old(owner) == msg.sender && owner == newOwner`. -/
theorem spec_setOwner : ⊢ spec!{ setOwner } := by
  sol_prove

end Solidity.Examples.Benchmark.SolkeyOz.SolmateOwned
