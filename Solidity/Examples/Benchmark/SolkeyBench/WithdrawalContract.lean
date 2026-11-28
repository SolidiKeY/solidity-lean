import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `WithdrawalContract`

Source: <https://github.com/SolidiKeY/solkey/blob/50a1469c8c34abf522c7027e47e6f53292d6920a/keyext.solidity.examples/contracts/benchmark/WithdrawalContract.sol>.
-/

namespace Solidity.Examples.Benchmark.SolkeyBench.WithdrawalContract

def WithdrawalContract : Contract := contract!{
  invariant mostSent >= 0;
  invariant \forall address a; pendingWithdrawals[a] >= 0;
  address public richest;
  uint public mostSent;
  mapping(address => uint) pendingWithdrawals;
  ensures richest == msg.sender && mostSent == msg.value;
  constructor() payable {
    richest = msg.sender;
    mostSent = msg.value;
  }
  ensures \old(mostSent) < msg.value;
  ensures richest == msg.sender && mostSent == msg.value;
  ensures pendingWithdrawals[\old(richest)] == \old(pendingWithdrawals[richest]) + msg.value;
  ensures \forall address a; a != \old(richest) -> pendingWithdrawals[a] == \old(pendingWithdrawals[a]);
  function becomeRichest() public payable {
    if (msg.value <= mostSent) revert();
    pendingWithdrawals[richest] += msg.value;
    richest = msg.sender;
    mostSent = msg.value;
  }
  ensures pendingWithdrawals[msg.sender] == 0;
  ensures net(msg.sender) == \old(net(msg.sender)) - \old(pendingWithdrawals[msg.sender]);
  ensures \forall address a; a != msg.sender -> pendingWithdrawals[a] == \old(pendingWithdrawals[a]);
  function withdraw() public {
    uint amount = pendingWithdrawals[msg.sender];
    pendingWithdrawals[msg.sender] = 0;
    msg.sender.transfer(amount);
  }
}

local instance : InContract := ⟨WithdrawalContract⟩

open scoped Scoped

theorem spec_constructor : ⊢ spec!{ constructor } := by sol_prove
theorem spec_becomeRichest : ⊢ spec!{ becomeRichest } := by sol_prove
theorem spec_withdraw : ⊢ spec!{ withdraw } := by sol_prove

end Solidity.Examples.Benchmark.SolkeyBench.WithdrawalContract
