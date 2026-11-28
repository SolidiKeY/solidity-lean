import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `Fund`

Source: <https://github.com/SolidiKeY/solkey/blob/50a1469c8c34abf522c7027e47e6f53292d6920a/keyext.solidity.examples/contracts/benchmark/Fund.sol>.
-/

namespace Solidity.Examples.Benchmark.SolkeyBench.Fund

def Fund : Contract := contract!{
  invariant \forall address a; shares[a] >= 0;
  mapping(address => uint) shares;
  ensures shares[msg.sender] == 0;
  ensures net(msg.sender) == \old(net(msg.sender)) - \old(shares[msg.sender]);
  ensures \forall address a; a != msg.sender -> shares[a] == \old(shares[a]);
  function withdraw() public {
    uint share = shares[msg.sender];
    shares[msg.sender] = 0;
    msg.sender.transfer(share);
  }
}

local instance : InContract := ⟨Fund⟩

open scoped Scoped

theorem spec_withdraw : ⊢ spec!{ withdraw } := by sol_prove

end Solidity.Examples.Benchmark.SolkeyBench.Fund
