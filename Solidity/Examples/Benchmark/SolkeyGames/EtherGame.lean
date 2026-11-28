import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Run
import Solidity.Tools.Counterexample

/-!
# Benchmark: `EtherGame`

Source: solkey's
<https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/contracts/real-world/EtherGame.sol>,
itself from
<https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/hacks/self-destruct/PreventForceEther.sol>
(the fix of the forced-ether game: it counts deposits in `balance` instead of
reading `address(this).balance`).
Changes: none but the spelling of `contract!{ … }`; `7 ether` and `1 ether`
are written in wei, as solkey's clause writes them.
The verdicts read `⊢` over every typed state (`Fml.Valid`), which includes
a state where `msg.sender == this`: the contract calling itself, which the
published contract never does.  A ledger clause that
assumes the payment leaves the contract is false there, since a payment to
oneself books nothing (`State.pay`, `Semantics/Run.lean`); such
a clause is refuted by a kernel-checked counterexample at that state, and
the clause is kept as solkey states it.

`TARGET_AMOUNT` is a `constant`, which the model keeps as a storage root
the constructor initializes (`Contract.inits`); a function's obligation
ranges over every value of it, and the clauses hold for each.

Verdicts: `deposit` proved; `claimReward` refuted (`claimReward_refuted`:
a winner that is the contract itself).
-/

namespace Solidity.Examples.Benchmark.SolkeyGames.EtherGame

def EtherGame : Contract := contract!{
  invariant balance >= 0 && balance <= TARGET_AMOUNT;
  uint256 public constant TARGET_AMOUNT = 7000000000000000000;
  uint256 public balance;
  address public winner;
  ensures msg.value == 1000000000000000000 && balance == \old(balance) + msg.value;
  ensures balance == TARGET_AMOUNT -> winner == msg.sender;
  ensures balance < TARGET_AMOUNT -> winner == \old(winner);
  function deposit() public payable {
    require(msg.value == 1000000000000000000);
    balance += msg.value;
    require(balance <= TARGET_AMOUNT);
    if (balance == TARGET_AMOUNT) {
      winner = msg.sender;
    }
  }
  ensures msg.sender == winner && winner == \old(winner) && balance == 0;
  ensures net(msg.sender) == \old(net(msg.sender)) - \old(balance);
  function claimReward() public {
    require(msg.sender == winner);
    uint256 amount = balance;
    balance = 0;
    (bool sent, ) = msg.sender.call{value: amount}("");
    require(sent);
  }
}

local instance : InContract := ⟨EtherGame⟩
open scoped Scoped

/-- `deposit()`: `msg.value` is one ether, the balance grows by it, the
sender wins at the target and the winner is kept below it. -/
theorem spec_deposit : ⊢ spec!{ deposit } := by
  sol_prove
  all_goals sol_leaf
  all_goals sol_close

/-- `claimReward()`'s `ensures net(msg.sender) == \old(net(msg.sender)) -
\old(balance)` fails for a winner that is the contract: it pays itself. -/
theorem claimReward_refuted : ¬ (⊢ spec!{ claimReward }) := by
  sol_refute

end Solidity.Examples.Benchmark.SolkeyGames.EtherGame
