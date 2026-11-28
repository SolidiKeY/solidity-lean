import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `AccessRestriction`

Source: <https://github.com/SolidiKeY/solkey/blob/50a1469c8c34abf522c7027e47e6f53292d6920a/keyext.solidity.examples/contracts/benchmark/AccessRestriction.sol>.

Changes beyond `contract!{ … }` spelling; the `@custom:key` clauses are written above their functions, invariants first. `payable(x)` is the identity on an address and is dropped (as in `Benchmark/EtherWallet.lean`); `if (c) s;` gets braces. The modifiers `onlyBy`, `onlyAfter`, `costs` are inlined at their uses, with `200 ether` and `6 weeks` substituted for their parameters; the state initializers `owner = msg.sender`, `creationTime = timeNow` become the constructor.

Verdicts are on the declarations below: a `theorem` is proved, a `def …_obligation` is unknown (its stuck goal and the missing closer or rule in its docstring).
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
    if (msg.sender != owner) { revert(); }
    owner = newOwner;
  }
  ensures \old(owner) == msg.sender && timeNow >= creationTime + 3628800 && owner == address(0);
  function disown() public {
    if (msg.sender != owner) { revert(); }
    if (timeNow < creationTime + 6 weeks) { revert(); }
    delete owner;
  }
  ensures msg.value >= 200000000000000000000 && owner == newOwner;
  ensures net(msg.sender) == \old(net(msg.sender)) + 200000000000000000000;
  function forceOwnerChange(address newOwner) public payable {
    if (msg.value < 200 ether) { revert(); }
    owner = newOwner;
    if (uint160(owner) & 0 == 1) { return; }
    if (msg.value > 200 ether) { msg.sender.transfer(msg.value - 200 ether); }
  }
}

local instance : InContract := ⟨AccessRestriction⟩

open scoped Scoped

theorem spec_changeOwner : ⊢ spec!{ changeOwner } := by sol_prove
/-- Unknown: owner == address(0) after delAt(storage, owner) (delete) is not closed; read-after-delete closer missing. -/
def disown_obligation : Fml AccessRestriction [] := spec!{ disown }
/-- Unknown: the unreachable branch uint160(owner) & 0 == 1 is not refuted (bitwise-and closer missing), and the refund branch needs net after pay(msg.sender, msg.value - 200 ether); calculus pay rule that books net for the payee is missing (pay(se,v) leaf stays open; cf. RefundEscrow.beneficiaryWithdraw). A caller that is the contract itself books nothing, so the net clause may fail there. -/
def forceOwnerChange_obligation : Fml AccessRestriction [] := spec!{ forceOwnerChange }

end Solidity.Examples.Benchmark.SolkeyBench.AccessRestriction
