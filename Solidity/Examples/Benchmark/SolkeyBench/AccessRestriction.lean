import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `AccessRestriction`

Source: <https://github.com/SolidiKeY/solkey/blob/50a1469c8c34abf522c7027e47e6f53292d6920a/keyext.solidity.examples/contracts/benchmark/AccessRestriction.sol>.
-/

namespace Solidity.Examples.Benchmark.SolkeyBench.AccessRestriction

def AccessRestriction : Contract := contract!{
  uint timeNow;
  address public owner;
  uint public creationTime;
  constructor() {
    owner = msg.sender;
    creationTime = timeNow;
  }
  ensures \old(owner) == msg.sender && owner == newOwner;
  function changeOwner(address newOwner) public {
    if (msg.sender != owner) revert();
    owner = newOwner;
  }
  ensures \old(owner) == msg.sender && timeNow >= creationTime + 3628800 && owner == address(0);
  function disown() public {
    if (msg.sender != owner) revert();
    if (timeNow < creationTime + 6 weeks) revert();
    delete owner;
  }
  ensures msg.value >= 200000000000000000000 && owner == newOwner;
  ensures net(msg.sender) == \old(net(msg.sender)) + 200000000000000000000;
  function forceOwnerChange(address newOwner) public payable {
    if (msg.value < 200 ether) revert();
    owner = newOwner;
    if (uint160(owner) & 0 == 1) return;
    if (msg.value > 200 ether) msg.sender.transfer(msg.value - 200 ether);
  }
}

local instance : InContract := ⟨AccessRestriction⟩

open scoped Scoped

theorem spec_changeOwner : ⊢ spec!{ changeOwner } := by sol_prove
theorem spec_disown : ⊢ spec!{ disown } := by sol_prove
theorem spec_forceOwnerChange : ⊢ spec!{ forceOwnerChange } := by sol_prove

end Solidity.Examples.Benchmark.SolkeyBench.AccessRestriction
