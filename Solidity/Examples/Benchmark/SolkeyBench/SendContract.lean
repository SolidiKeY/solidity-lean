import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `SendContract`

Source: <https://github.com/SolidiKeY/solkey/blob/50a1469c8c34abf522c7027e47e6f53292d6920a/keyext.solidity.examples/contracts/benchmark/SendContract.sol>.

Changes: none beyond `contract!{ … }` spelling; the `@custom:key` clauses are written above their functions, invariants first. `payable(x)` is the identity on an address and is dropped (as in `Benchmark/EtherWallet.lean`); `if (c) s;` gets braces. `address payable` is `address`.

Verdicts are on the declarations below: a `theorem` is proved, a `def …_obligation` is unknown (its stuck goal and the missing closer or rule in its docstring).
-/

namespace Solidity.Examples.Benchmark.SolkeyBench.SendContract

def SendContract : Contract := contract!{
  invariant mostSent >= 0;
  address public richest;
  uint public mostSent;
  ensures richest == msg.sender && mostSent == msg.value;
  constructor() payable {
    richest = msg.sender;
    mostSent = msg.value;
  }
  requires richest != this;
  ensures \old(mostSent) < msg.value;
  ensures richest == msg.sender && mostSent == msg.value;
  ensures \old(richest) != msg.sender -> net(\old(richest)) == \old(net(richest)) - msg.value;
  function becomeRichest() public payable {
    if (msg.value <= mostSent) { revert(); }
    richest.transfer(msg.value);
    richest = msg.sender;
    mostSent = msg.value;
  }
}

local instance : InContract := ⟨SendContract⟩

open scoped Scoped

theorem spec_constructor : ⊢ spec!{ constructor } := by sol_prove
/-- Unknown: the net debit of \old(richest) after pay(richest, msg.value) and two saves; calculus pay rule that books net for the payee is missing (pay(se,v) leaf stays open; cf. RefundEscrow.beneficiaryWithdraw). -/
def becomeRichest_obligation : Fml SendContract [] := spec!{ becomeRichest }

end Solidity.Examples.Benchmark.SolkeyBench.SendContract
