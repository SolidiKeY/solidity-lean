import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `SendContract`

Source: <https://github.com/SolidiKeY/solkey/blob/50a1469c8c34abf522c7027e47e6f53292d6920a/keyext.solidity.examples/contracts/benchmark/SendContract.sol>.
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
    if (msg.value <= mostSent) revert();
    richest.transfer(msg.value);
    richest = msg.sender;
    mostSent = msg.value;
  }
}

local instance : InContract := ⟨SendContract⟩

open scoped Scoped

theorem spec_constructor : ⊢ spec!{ constructor } := by sol_prove
theorem spec_becomeRichest : ⊢ spec!{ becomeRichest } := by sol_prove

end Solidity.Examples.Benchmark.SolkeyBench.SendContract
