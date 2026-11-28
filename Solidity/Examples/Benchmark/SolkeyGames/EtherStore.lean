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
The verdicts read `⊢` over every typed state (`Fml.Valid`), which includes
a state where `msg.sender == this`: the contract calling itself, which the
published contract never does.  A ledger clause that
assumes the payment leaves the contract is false there, since a payment to
oneself books nothing (`State.pay`, `Semantics/Run.lean`); such
a clause is refuted by a kernel-checked counterexample at that state, and
the clause is kept as solkey states it.

The re-entrancy itself (the payment before `balances[msg.sender] = 0`) is
solkey's open goal under `-O transferSemantics:withCallback`; it is not
stated here, and the verdicts read the default payment, without callbacks.

Verdicts: `deposit` unknown (`deposit_obligation`); `withdraw` refuted
(`withdraw_refuted`: the contract withdrawing its own credit of `1`).
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

/-- `withdraw()` refuted from `selfCall`, where the invariant holds. -/
theorem withdraw_refuted : ¬ (⊢ spec!{ withdraw }) := by
  apply Proves.not_of_not_valid
  apply Fml.not_valid_of_peel [] selfCall
  apply Fml.not_holds_imp_of_eval3 (Tools.poolDom [])
  · repeat' apply Fml.holds_and_intro
    all_goals first
      | sol_decl_facts
      | exact Fml.eval3_tt (dom := Tools.poolDom []) (by decide +kernel)
      | skip
    -- `∀ a; balances[a] == net(a)`: at `0` both are `1`, elsewhere both `0`.
    intro v
    by_cases hv : v = uintOfNat 0
    · subst hv; exact Fml.eval3_tt (dom := Tools.poolDom []) (by decide +kernel)
    · simp [holds, Tm.denote, Fml.peel, selfCall, State.push, hv, Op2.denote, Op0.denote,
        State.glob, TEnv.get, Semantics.lookupBy, Op1.denote, Storage.obs, binopT, SLoc.app_ref,
        SVal.obs_word, SVal.wordOf, SRef.append, SFields.get, SVal.findM, SRef.ofRoot, Path.append,
        Path.index, SMap.toList]
      exact ⟨by decide +kernel, rfl⟩
  · decide +kernel

/-- From `selfCall`, `withdraw()` returns with the credit `0` and the ledger
entry still `1`: the invariant `balances[a] == net(a)` and the `ensures`
`net(msg.sender) == \old(net(msg.sender)) - \old(balances[msg.sender])` fail. -/
example :
    ((Prog.run selfCall (sol{ withdraw(); })).toOption.map fun o =>
      (((o.st.storage.find (SRef.ofRoot "balances" rfl |>.append (.key (uintOfNat 0) .nil))).map
        (·.view.val)), (Semantics.lookupBy (uintOfNat 0) o.st.net).getD 0)) = some (some 0, 1) := by
  decide +kernel

end Solidity.Examples.Benchmark.SolkeyGames.EtherStore
