import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: solkey `FunctionModifier`

Source: <https://github.com/SolidiKeY/solkey/blob/50a1469c8c34abf522c7027e47e6f53292d6920a/keyext.solidity.examples/contracts/real-world/FunctionModifier.sol>,
itself from solidity-by-example's `function-modifier/FunctionModifier.sol`
(commit `5bcdca02`).

Changes: none but the spelling of `contract!{ … }` and solkey's
`@custom:key` clauses written above the functions; `requires i >= 0` holds
for every typed `uint` and is not restated.
-/

namespace Solidity.Examples.Benchmark.SolkeyMisc.FunctionModifier

/-- solkey's `FunctionModifier.sol`, with its clauses. -/
def FunctionModifier : Contract := contract!{
  address public owner;
  uint256 public x = 10;
  bool public locked;
  ensures owner == msg.sender && x == 10 && !locked;
  constructor() {
    owner = msg.sender;
  }
  modifier onlyOwner() {
    require(msg.sender == owner);
    _;
  }
  modifier validAddress(address _addr) {
    require(_addr != address(0));
    _;
  }
  ensures \old(owner) == msg.sender && _newOwner != address(0);
  ensures owner == _newOwner && x == \old(x) && locked == \old(locked);
  function changeOwner(address _newOwner) public onlyOwner validAddress(_newOwner) {
    owner = _newOwner;
  }
  modifier noReentrancy() {
    require(!locked);
    locked = true;
    _;
    locked = false;
  }
  requires i <= x;
  ensures !\old(locked) && i <= 1 && x == \old(x) - i && !locked && owner == \old(owner);
  function decrement(uint256 i) public noReentrancy {
    x -= i;
    if (i > 1) {
      decrement(i - 1);
    }
  }
}

local instance : InContract := ⟨FunctionModifier⟩

open scoped Scoped

/-- `changeOwner(_newOwner)`: both clauses. -/
theorem spec_changeOwner : ⊢ spec!{ changeOwner } := by
  sol_prove

/-- `decrement(i)`: the guarded recursive call reverts, so `i <= 1`. -/
theorem spec_decrement : ⊢ spec!{ decrement } := by
  sol_prove

end Solidity.Examples.Benchmark.SolkeyMisc.FunctionModifier
