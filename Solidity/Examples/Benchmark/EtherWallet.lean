import Solidity.Calculus.Derive
import Solidity.Calculus.Close

/-!
# Benchmark: `EtherWallet`

Source: solkey's `keyext.solidity.examples/benchmark/EtherWallet.sol`, itself
from
<https://raw.githubusercontent.com/Cyfrin/solidity-by-example.github.io/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/app/ether-wallet/EtherWallet.sol>.
Changes from the published text, as solkey's benchmark file makes them: the
`require` message is dropped (a string literal).  Here besides:
`payable(msg.sender)` and `payable(…)` are the identity on a `uint` and are
written without the conversion (stream A's `payable(x)`); the `payable`
`receive()` is dropped, since nothing here calls it.  The constructor is
the contract's (`Contract.ctor`), and the runs deploy the wallet with it
(`Contract.deploy`).  `getBalance()`, which
solkey's copy drops because `address(this).balance` crashed its parser, is
back (`getBalance`).

`@custom:key ensures net(owner) == \old(net(owner)) - _amount` is
`withdrawNet`, at a value of the old entry, and a run (`withdrawRunNet`).
The payment runs with `transferNoCallbackBox`, as solkey's net rules do, which
books the ledger and leaves `address(this).balance`; with callbacks the
recipient could change the ledger before control returns
(`Semantics/Callback.lean`).
-/

namespace Solidity.Examples.Benchmark.EtherWallet

open Proves

def EtherWallet : Contract := contract!{
  address owner;
  constructor() {
    owner = msg.sender;
  }
  function withdraw(uint _amount) {
    require(msg.sender == owner);
    msg.sender.transfer(_amount);
  }
  function getBalance() returns (uint) {
    return address(this).balance;
  }
}

local instance : InContract := ⟨EtherWallet⟩

/-- `constructor()`: the caller is the owner, from any storage. -/
theorem ctor : ⊢ dl!{ [ constructor(); ] owner == msg.sender } := by
  sol_prove

/-- A deployment, from the empty storage: it returns, the deployer the
owner. -/
theorem deployOwner :
    ⊨ dl!{ { storage := mtSt ‖ net := store(mtSt, at(msg.sender), msg.value) ‖
        selfBalance := msg.value }
      ⟨ constructor(); ⟩ owner == msg.sender } := by
  sol_symex
  sol_close_mt

/-- `ensures msg.sender == owner && owner == \old(owner)`. -/
theorem withdrawOwner :
    ⊢ dl!{ [ uint o = owner; withdraw(x); ] msg.sender == o && owner == o } := by
  sol_prove

/-- `ensures net(owner) == \old(net(owner)) - _amount`, the old entry `40`:
the owner's entry is `10` after `withdraw(30)`, and anyone else's call
reverts.  An owner that is the wallet itself pays itself, and books nothing. -/
theorem withdrawNet :
    ⊢ dl!{ owner != this → net(owner) = 40 → [ withdraw(30); ] net(owner) = 10 } := by
  sol_prove
  all_goals
    refine close ?_
    sol_symex
    sol_close

/-- `getBalance()` returns the funds. -/
theorem getBalanceFunds :
    ⊢ dl!{ [ uint f = address(this).balance; uint g = getBalance(); ] g == f } := by
  sol_prove

/-! ## Runs: the ledger

`7` deploys the wallet, sends it `100` wei, and withdraws `30`. -/

/-- The wallet `7` deploys, then holding `100` (what the dropped
`receive()` would take). -/
def deployed : Semantics.Res Semantics.State := do
  let σ ← EtherWallet.deploy sol{ constructor(); } { msgSender := 7 }
  pure { σ with selfBalance := 100 }

/-- `ensures net(owner) == \old(net(owner)) - _amount`: `7`'s entry is `30`
less, and the funds as the transaction found them. -/
theorem withdrawRunNet :
    (do let σ ← Prog.run (← deployed) (sol{ withdraw(30); } : Prog EtherWallet)
        pure (σ.getNet 7, σ.selfBalance)) = .ok (-30, 100) := by
  simp only [deployed, Contract.deploy, Contract.deployState, Contract.initStorage, EtherWallet,
    List.map, Semantics.defaultForTy]
  rfl

/-- More than the funds: the ledger books it all the same.  That the contract
can pay is not the ledger's to check; on the EVM the payment is refused and
the call reverts (`Evm.compile_correct`). -/
theorem withdrawRunOverdrawn :
    (do let σ ← Prog.run (← deployed) (sol{ withdraw(130); } : Prog EtherWallet)
        pure (σ.getNet 7)) = .ok (-130) := by
  simp only [deployed, Contract.deploy, Contract.deployState, Contract.initStorage, EtherWallet,
    List.map, Semantics.defaultForTy]
  rfl

/-- Anyone but the owner: `withdraw` reverts. -/
theorem withdrawRunOther :
    (do Prog.run { (← deployed) with tx := { msgSender := 3 } } (sol{ withdraw(30); } : Prog EtherWallet)) =
      .error .revert := by
  simp only [deployed, Contract.deploy, Contract.deployState, Contract.initStorage, EtherWallet,
    List.map, Semantics.defaultForTy]
  rfl

end Solidity.Examples.Benchmark.EtherWallet
