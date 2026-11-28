import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: solkey `Account`

Source: <https://github.com/SolidiKeY/solkey/blob/50a1469c8c34abf522c7027e47e6f53292d6920a/keyext.solidity.examples/contracts/real-world/Account.sol>,
itself from solidity-by-example's `error/Account.sol` (commit `5bcdca02`).

Changes: none but the spelling of `contract!{ … }` and solkey's
`@custom:key` clauses written above the functions.  The contract invariant
`balance >= 0` and the `requires _amount >= 0` clauses hold for every typed
`uint` and are not restated.
-/

namespace Solidity.Examples.Benchmark.SolkeyMisc.Account

/-- solkey's `Account.sol`, with its clauses. -/
def Account : Contract := contract!{
  uint256 public balance;
  uint256 public constant MAX_UINT = 2 ** 256 - 1;
  ensures balance == \old(balance) + _amount;
  function deposit(uint256 _amount) public {
    uint256 oldBalance = balance;
    uint256 newBalance = balance + _amount;
    require(newBalance >= oldBalance);
    balance = newBalance;
    assert(balance >= oldBalance);
  }
  ensures \old(balance) >= _amount && balance == \old(balance) - _amount;
  function withdraw(uint256 _amount) public {
    uint256 oldBalance = balance;
    require(balance >= _amount);
    if (balance < _amount) {
      revert();
    }
    balance -= _amount;
    assert(balance <= oldBalance);
  }
}

local instance : InContract := ⟨Account⟩

open scoped Scoped

/-- `deposit(_amount)`: `ensures balance == \old(balance) + _amount`. -/
theorem spec_deposit : ⊢ spec!{ deposit } := by
  sol_prove

/-- `withdraw(_amount)`: `ensures \old(balance) >= _amount && balance == \old(balance) - _amount`. -/
theorem spec_withdraw : ⊢ spec!{ withdraw } := by
  sol_prove
  all_goals (sol_leaf; sol_close)

end Solidity.Examples.Benchmark.SolkeyMisc.Account
