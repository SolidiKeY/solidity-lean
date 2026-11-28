import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Patterns benchmark: hand-written mutex guard

Sources: Solidity by Example, "Re-Entrancy", pinned revision: the guard
<https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/hacks/re-entrancy/ReEntrancyGuard.sol>
applied, as the page's preventative technique says, to its `EtherStore`
<https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/hacks/re-entrancy/ReEntrancy.sol>.

Changes: the two contracts are one (the guard's `locked` and `noReentrant`
beside `EtherStore`), `withdraw` carries `noReentrant`, and
`msg.sender.call` is `payable(msg.sender).call`. Messages are dropped by
elaboration. Natural `@custom:key` clauses: `withdraw` starts unlocked,
releases the lock and clears the caller's balance; `deposit` credits it.

Verdicts: deposit, withdraw, getBalance proved.
-/
namespace Solidity.Examples.Benchmark.Patterns.Mutex
def EtherStore : Contract := contract!{
  bool internal locked;
  mapping(address => uint256) public balances;
  modifier noReentrant() {
    require(!locked, "No re-entrancy");
    locked = true;
    _;
    locked = false;
  }
  ensures balances[msg.sender] == \old(balances[msg.sender]) + msg.value && (locked <-> \old(locked));
  function deposit() public payable {
    balances[msg.sender] += msg.value;
  }
  ensures !\old(locked) && !locked && \old(balances[msg.sender]) > 0 && balances[msg.sender] == 0;
  function withdraw() public noReentrant {
    uint256 bal = balances[msg.sender];
    require(bal > 0);
    (bool sent,) = payable(msg.sender).call{value: bal}("");
    require(sent, "Failed to send Ether");
    balances[msg.sender] = 0;
  }
  ensures \result == address(this).balance;
  function getBalance() public view returns (uint256) {
    return address(this).balance;
  }
}
local instance : InContract := ⟨EtherStore⟩
open scoped Scoped
theorem spec_deposit : ⊢ spec!{ deposit } := by
  sol_auto
theorem spec_withdraw : ⊢ spec!{ withdraw } := by
  sol_prove
theorem spec_getBalance : ⊢ spec!{ getBalance } := by
  sol_prove
end Solidity.Examples.Benchmark.Patterns.Mutex
