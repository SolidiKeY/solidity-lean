import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Run
import Solidity.Tools.Counterexample

/-!
# Benchmark: `KingOfEther`

Source: solkey's
<https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/contracts/real-world/KingOfEther.sol>,
itself from
<https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/hacks/denial-of-service/PreventDenialOfService.sol>
(the pull-payment fix of the denial-of-service game).
Changes: none but the spelling of `contract!{ … }`.
The verdicts read `⊢` over every typed state (`Fml.Valid`), which includes
a state where `msg.sender == this`: the contract calling itself, which the
published contract never does.  A ledger clause that
assumes the payment leaves the contract is false there, since a payment to
oneself books nothing (`State.pay`, `Semantics/Run.lean`); such
a clause is refuted by a kernel-checked counterexample at that state, and
the clause is kept as solkey states it.

Verdicts: `claimThrone` proved; `withdraw` refuted (`withdraw_refuted`:
the contract, not king, withdrawing its own credit of `1`).
-/

namespace Solidity.Examples.Benchmark.SolkeyGames.KingOfEther

def KingOfEther : Contract := contract!{
  invariant balance >= 0;
  invariant \forall address a; balances[a] >= 0;
  address public king;
  uint256 public balance;
  mapping(address => uint256) public balances;
  ensures msg.value > \old(balance) && king == msg.sender && balance == msg.value;
  ensures balances[\old(king)] == \old(balances[king]) + \old(balance);
  ensures \forall address a; a != \old(king) -> balances[a] == \old(balances[a]);
  ensures net(msg.sender) == \old(net(msg.sender)) + msg.value;
  function claimThrone() external payable {
    require(msg.value > balance);
    uint256 b = balance;
    address k = king;
    balances[k] += b;
    balance = msg.value;
    king = msg.sender;
  }
  ensures msg.sender != king && king == \old(king) && balance == \old(balance);
  ensures balances[msg.sender] == 0;
  ensures net(msg.sender) == \old(net(msg.sender)) - \old(balances[msg.sender]);
  function withdraw() public {
    require(msg.sender != king);
    uint256 amount = balances[msg.sender];
    balances[msg.sender] = 0;
    (bool sent, ) = msg.sender.call{value: amount}("");
    require(sent);
  }
}

local instance : InContract := ⟨KingOfEther⟩
open scoped Scoped

/-- `claimThrone()`: `ensures msg.value > \old(balance) && king == msg.sender
&& balance == msg.value`, the old king credited `\old(balance)`, every other
credit kept, and the sender's ledger entry booked `msg.value`. -/
theorem spec_claimThrone : ⊢ spec!{ claimThrone } := by
  sol_prove
  all_goals sol_leaf
  all_goals sol_close

/-- The king `5`, the contract `0` calling itself with a credit of `1` and
funds `1`. -/
def selfCall : State KingOfEther [] :=
  { storage := .cons (.prim (uintOfNat 5)) (.cons (.prim (uintOfNat 0))
      (.cons (.map (.cons (uintOfNat 0) (.prim (uintOfNat 1)) .nil) (.prim (uintOfNat 0))) .nil)),
    H := [], heap := Heap.empty, env := (), net := [], selfBalance := uintOfNat 1, tx := {} }

/-- Every credit is a `uint`, so at least `0`. -/
theorem balances_nonneg : ⊢ dl!{ ∀ uint a; balances[a] >= 0 } := by
  sol_prove

/-- `withdraw()`'s `ensures net(msg.sender) == \old(net(msg.sender)) -
\old(balances[msg.sender])` fails from `selfCall`: the call pays the
contract itself, and its ledger entry stays. -/
theorem withdraw_refuted : ¬ (⊢ spec!{ withdraw }) := by
  apply Proves.not_of_not_valid
  apply Fml.not_valid_of_peel [] selfCall
  apply Fml.not_holds_imp_of_eval3 (Tools.poolDom [])
  · repeat' apply Fml.holds_and_intro
    all_goals first
      | sol_decl_facts
      | exact balances_nonneg.fmlValid _
      | exact Fml.eval3_tt (dom := Tools.poolDom []) (by decide +kernel)
  · decide +kernel

end Solidity.Examples.Benchmark.SolkeyGames.KingOfEther
