import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Run

/-!
# Benchmark: solkey `TimeLock`

Source: <https://github.com/SolidiKeY/solkey/blob/50a1469c8c34abf522c7027e47e6f53292d6920a/keyext.solidity.examples/contracts/real-world/TimeLock.sol>,
itself from solidity-by-example's `hacks/overflow/Overflow.sol` (commit
`5bcdca02`), ported by solkey to 0.8 with `block.timestamp` as the state
variable `timeNow`.

Changes: none but the spelling of `contract!{ … }` and solkey's
`@custom:key` clauses; the invariants (`>= 0`) and `requires … >= 0`
hold for every typed `uint`.  The low-level `msg.sender.call{value: amount}("")`
with `require(sent)` is `msg.sender.transfer(amount)` (a failed send
reverts either way).
-/

namespace Solidity.Examples.Benchmark.SolkeyMisc.TimeLock

/-- solkey's `TimeLock.sol`, with its clauses. -/
def TimeLock : Contract := contract!{
  mapping(address => uint256) public balances;
  mapping(address => uint256) public lockTime;
  uint256 timeNow;
  ensures balances[msg.sender] == \old(balances[msg.sender]) + msg.value;
  ensures lockTime[msg.sender] == timeNow + 604800;
  function deposit() external payable {
    balances[msg.sender] += msg.value;
    lockTime[msg.sender] = timeNow + 1 weeks;
  }
  ensures lockTime[msg.sender] == \old(lockTime[msg.sender]) + _secondsToIncrease;
  ensures balances[msg.sender] == \old(balances[msg.sender]);
  function increaseLockTime(uint256 _secondsToIncrease) public {
    lockTime[msg.sender] += _secondsToIncrease;
  }
  ensures \old(balances[msg.sender]) > 0 && timeNow > \old(lockTime[msg.sender]) && balances[msg.sender] == 0;
  ensures lockTime[msg.sender] == \old(lockTime[msg.sender]);
  ensures net(msg.sender) == \old(net(msg.sender)) - \old(balances[msg.sender]);
  function withdraw() public {
    require(balances[msg.sender] > 0);
    require(timeNow > lockTime[msg.sender]);
    uint256 amount = balances[msg.sender];
    balances[msg.sender] = 0;
    msg.sender.transfer(amount);
  }
}

local instance : InContract := ⟨TimeLock⟩

open scoped Scoped

/-- `deposit()`: both clauses. -/
theorem spec_deposit : ⊢ spec!{ deposit } := by
  sol_prove
  all_goals (sol_leaf; sol_close)

/-- `increaseLockTime(s)`: both clauses. -/
theorem spec_increaseLockTime : ⊢ spec!{ increaseLockTime } := by
  sol_prove
  all_goals (sol_leaf; sol_close)

/-- `withdraw()`'s clauses, as solkey states them. -/
def withdraw_obligation : Fml TimeLock [] := spec!{ withdraw }

/-- A store: `2` holds `5`, unlocked since time `1`. -/
private def store : Storage TimeLock :=
  .cons (.map (.cons (uintOfNat 2) (.prim (uintOfNat 5)) .nil) (.prim (uintOfNat 0)))
    (.cons (.map .nil (.prim (uintOfNat 0))) (.cons (.prim (uintOfNat 1)) .nil))

/-- Refuted: `ensures net(msg.sender) == \old(net(msg.sender)) - \old(balances[msg.sender])`
fails when the contract withdraws from itself (`msg.sender == this`): the
withdrawal returns, the balance is cleared, and the self-payment books nothing,
so the entry stays `0`, not `-5`. -/
example :
    ((Prog.run { State.ofStorage store with
        selfBalance := uintOfNat 5,
        tx := { msgSender := uintOfNat 2, selfAddress := uintOfNat 2 } }
      (sol{ withdraw(); })).toOption.map
        fun o => (Semantics.lookupBy (uintOfNat 2 : PrimTy.uint.Denote) o.st.net).getD 0) = some 0 := by
  decide +kernel

end Solidity.Examples.Benchmark.SolkeyMisc.TimeLock
