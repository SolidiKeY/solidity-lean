import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `Fund`

Source: <https://github.com/SolidiKeY/solkey/blob/50a1469c8c34abf522c7027e47e6f53292d6920a/keyext.solidity.examples/contracts/benchmark/Fund.sol>.

Changes: none beyond `contract!{ … }` spelling; the `@custom:key` clauses are written above their functions, invariants first. `payable(x)` is the identity on an address and is dropped (as in `Benchmark/EtherWallet.lean`); `if (c) s;` gets braces.

Verdicts are on the declarations below: a `theorem` is proved, a `def …_obligation` is unknown (its stuck goal and the missing closer or rule in its docstring).
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

/-- Unknown: after save then pay(msg.sender, share), the cleared entry, the debit against oldNet and the mapping frame stay open; mapping-frame and snapshot closure missing (cf. Escrow.withdraw), pay ledger rule missing. A caller that is the contract itself pays itself and books nothing, so the net clause may fail there. -/
def withdraw_obligation : Fml Fund [] := spec!{ withdraw }

end Solidity.Examples.Benchmark.SolkeyBench.Fund
