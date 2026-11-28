import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Patterns benchmark: pull-payment withdrawal

Source: Solidity documentation v0.8.28, Common Patterns, "Withdrawal from
Contracts" (`WithdrawalContract`):
<https://github.com/ethereum/solidity/blob/v0.8.28/docs/common-patterns.rst>.

Changes: none but the spelling of `contract!{ … }` (the unbraced `if` body
braced); the error is dropped by
elaboration and `revert NotEnoughEther()` is `revert();`. `transfer` uses
this model's payment semantics. Natural `@custom:key` clauses: an outbid
richest is credited, not paid; a withdrawal clears the caller's credit and pays
it (the ledger `net(a)` counts what `a` paid in, so a payment lowers it).

Verdicts: constructor and withdraw proved; becomeRichest unknown.
-/
namespace Solidity.Examples.Benchmark.Patterns.Withdrawal
def WithdrawalContract : Contract := contract!{
  address public richest;
  uint public mostSent;
  mapping(address => uint) pendingWithdrawals;
  error NotEnoughEther();
  ensures richest == msg.sender && mostSent == msg.value;
  constructor() payable {
    richest = msg.sender;
    mostSent = msg.value;
  }
  ensures richest == msg.sender && mostSent == msg.value && msg.value > \old(mostSent);
  ensures \forall address a; a == \old(richest) -> pendingWithdrawals[a] == \old(pendingWithdrawals[a]) + msg.value;
  function becomeRichest() public payable {
    if (msg.value <= mostSent) { revert NotEnoughEther(); }
    pendingWithdrawals[richest] += msg.value;
    richest = msg.sender;
    mostSent = msg.value;
  }
  ensures pendingWithdrawals[msg.sender] == 0;
  ensures richest == \old(richest) && mostSent == \old(mostSent);
  ensures msg.sender != this -> net(msg.sender) == \old(net(msg.sender)) - \old(pendingWithdrawals[msg.sender]);
  function withdraw() public {
    uint amount = pendingWithdrawals[msg.sender];
    pendingWithdrawals[msg.sender] = 0;
    payable(msg.sender).transfer(amount);
  }
}
local instance : InContract := ⟨WithdrawalContract⟩
open scoped Scoped
theorem spec_constructor : ⊢ spec!{ constructor } := by
  sol_prove
/-- Unknown: the old richest's credit is stated over a quantified address
(`\old` does not nest). After `save(pendingWithdrawals[ie1], … + msg.value)`
with `ie1 = find(storage, richest)` and two more saves, `sol_auto` leaves the
quantified mapping leaf: instantiation at `\old(richest)` with the
read-over-save frame against the snapshot is missing. -/
def becomeRichest_obligation : Fml WithdrawalContract [] := spec!{ becomeRichest }
theorem spec_withdraw : ⊢ spec!{ withdraw } := by
  sol_auto
end Solidity.Examples.Benchmark.Patterns.Withdrawal
