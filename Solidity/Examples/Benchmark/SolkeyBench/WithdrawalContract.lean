import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `WithdrawalContract`

Source: <https://github.com/SolidiKeY/solkey/blob/50a1469c8c34abf522c7027e47e6f53292d6920a/keyext.solidity.examples/contracts/benchmark/WithdrawalContract.sol>.

Changes: none beyond `contract!{ … }` spelling; the `@custom:key` clauses are written above their functions, invariants first. `payable(x)` is the identity on an address and is dropped (as in `Benchmark/EtherWallet.lean`); `if (c) s;` gets braces. The documentation-only NatSpec line is dropped.

Verdicts are on the declarations below: a `theorem` is proved, a `def …_obligation` is unknown (its stuck goal and the missing closer or rule in its docstring).
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
    if (msg.value <= mostSent) { revert(); }
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
/-- Unknown: after the payable snapshot and three saves, the credit to \old(richest) and the mapping frame stay open; mapping-frame and snapshot closure missing (cf. Escrow.withdraw). -/
def becomeRichest_obligation : Fml WithdrawalContract [] := spec!{ becomeRichest }
/-- Unknown: as `Fund.withdraw`: the cleared entry, the debit against oldNet and the mapping frame after save then pay; mapping-frame and snapshot closure missing (cf. Escrow.withdraw), pay ledger rule missing. -/
def withdraw_obligation : Fml WithdrawalContract [] := spec!{ withdraw }

end Solidity.Examples.Benchmark.SolkeyBench.WithdrawalContract
