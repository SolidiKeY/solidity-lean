import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Run
import Solidity.Tools.Counterexample

/-!
# Benchmark: `EtherStore`

Source: solkey's
<https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/contracts/real-world/EtherStore.sol>,
itself from
<https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/hacks/re-entrancy/ReEntrancy.sol>
(the re-entrancy victim: it pays before it zeroes the balance).
Changes: none but the spelling of `contract!{ … }`.
-/

namespace Solidity.Examples.Benchmark.SolkeyGames.EtherStore

def EtherStore : Contract := contract!{
  invariant \forall address a; balances[a] >= 0 && balances[a] == net(a);
  mapping(address => uint256) public balances;
  ensures balances[msg.sender] == \old(balances[msg.sender]) + msg.value;
  function deposit() public payable {
    balances[msg.sender] += msg.value;
  }
  ensures \old(balances[msg.sender]) > 0 && balances[msg.sender] == 0;
  ensures net(msg.sender) == \old(net(msg.sender)) - \old(balances[msg.sender]);
  function withdraw() public {
    uint256 bal = balances[msg.sender];
    require(bal > 0);
    (bool sent, ) = msg.sender.call{value: bal}("");
    require(sent);
    balances[msg.sender] = 0;
  }
}

local instance : InContract := ⟨EtherStore⟩
open scoped Scoped

/-- Unknown: `sol_prove` leaves one leaf, the invariant
`∀ a; balances[a] == net(a)` after `save(storage, balances[msg.sender], …)`
and the booking `store(net, at(msg.sender), …)`; the closer does not
instantiate the quantified premise at the saved key against the stored
ledger entry (`sol_close` stops in its bounded search). -/
def deposit_obligation : Fml EtherStore [] := spec!{ deposit }

/-- The contract `0` calling itself with a credit of `1`, its ledger entry
`1` as the invariant has it, and funds `1`. -/
def selfCall : State EtherStore [] :=
  { storage := .cons (.map (.cons (uintOfNat 0) (.prim (uintOfNat 1)) .nil) (.prim (uintOfNat 0))) .nil,
    H := [], heap := Heap.empty, env := (), net := [(uintOfNat 0, 1)], selfBalance := uintOfNat 1,
    tx := {} }

/-- From `selfCall`, `withdraw()` returns with the credit `0` and the ledger
entry still `1`: the invariant `balances[a] == net(a)` and the `ensures`
`net(msg.sender) == \old(net(msg.sender)) - \old(balances[msg.sender])` fail. -/
example :
    ((Prog.run selfCall (sol{ withdraw(); })).toOption.map fun o =>
      (((o.st.storage.find (SRef.ofRoot "balances" rfl |>.append (.key (uintOfNat 0) .nil))).map
        (·.view.val)), (Semantics.lookupBy (uintOfNat 0) o.st.net).getD 0)) = some (some 0, 1) := by
  decide +kernel

end Solidity.Examples.Benchmark.SolkeyGames.EtherStore
