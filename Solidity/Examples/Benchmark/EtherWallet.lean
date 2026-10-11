import Solidity.Tools.Run
import Solidity.Calculus.NFmlDerive
import Solidity.Calculus.NFmlClose
import Solidity.Calculus.Surface
import Solidity.Calculus.Deploy
import Solidity.Calculus.Closers
import Solidity.Tools.Inspect

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
(`Contract.deployT`, checked by the kernel).  `getBalance()`, which
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

open scoped Scoped

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

def ctorCore := (sol{ constructor(); } : Prog EtherWallet [] _)
def withdrawCore := (sol{ withdraw(30); } : Prog EtherWallet [] _)
def overdrawCore := (sol{ withdraw(130); } : Prog EtherWallet [] _)

/-- The wallet `7` deploys (`Contract.deployT`), then holding `100`
(what the dropped `receive()` would take). -/
noncomputable def deployed : Option (State EtherWallet []) :=
  (Contract.deployT EtherWallet ctorCore { msgSender := ⟨7, rfl⟩ }).toOption.map
    fun σ => { σ with selfBalance := ⟨100, rfl⟩ }

/-- `ensures net(owner) == \old(net(owner)) - _amount`: `7`'s entry is `30`
less, and the funds as the transaction found them. -/
theorem withdrawRunNet :
    (deployed.bind fun σ => (Prog.run σ withdrawCore).toOption.map
      fun o => ((Semantics.lookupBy 7 o.st.net).getD 0, o.st.selfBalance.1)) = some (-30, 100) := by
  decide +kernel

/-- More than the funds: the ledger books it all the same.  That the contract
can pay is not the ledger's to check; on the EVM the payment is refused and
the call reverts (`Evm.compile_correct`). -/
theorem withdrawRunOverdrawn :
    (deployed.bind fun σ => (Prog.run σ overdrawCore).toOption.map
      fun o => (Semantics.lookupBy 7 o.st.net).getD 0) = some (-130) := by
  decide +kernel

/-- Anyone but the owner: `withdraw` reverts. -/
theorem withdrawRunOther :
    (deployed.map fun σ => (Prog.run { σ with tx := { msgSender := ⟨3, rfl⟩ } }
      withdrawCore).halt?) = some (some .revert) := by
  decide +kernel

end Solidity.Examples.Benchmark.EtherWallet
